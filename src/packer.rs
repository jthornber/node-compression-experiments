use anyhow::Result;
use bitstream_io::{BigEndian, BitWrite, BitWriter};
use std::collections::{BTreeMap, VecDeque};
use std::fmt::Write;
use std::io::{self};
use std::string::String;
use thinp::thin::ir::{self, Map, MetadataVisitor, Visit};

use crate::varint::*;

//------------------------------------------

fn highest_set_bit_position(n: u8) -> u8 {
    if n == 0 {
        1 // this is for the instruction coding, we must have at least 1 bit
    } else {
        8 - n.leading_zeros() as u8
    }
}

pub fn u64_sub_to_i64(a: u64, b: u64) -> i64 {
    match a.cmp(&b) {
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => {
            let diff = a - b;
            if diff > i64::MAX as u64 {
                i64::MAX
            } else {
                diff as i64
            }
        }
        std::cmp::Ordering::Less => {
            let diff = b - a;
            if diff > i64::MAX as u64 {
                i64::MIN
            } else {
                -(diff as i64)
            }
        }
    }
}

#[test]
fn test_u64_sub_to_i64() {
    assert_eq!(u64_sub_to_i64(5, 3), 2);
    assert_eq!(u64_sub_to_i64(3, 5), -2);
    assert_eq!(u64_sub_to_i64(u64::MAX, u64::MAX - 1), 1);
    assert_eq!(u64_sub_to_i64(0, 1), -1);
    assert_eq!(u64_sub_to_i64(u64::MAX, 0), i64::MAX);
    assert_eq!(u64_sub_to_i64(0, u64::MAX), i64::MIN);
    assert_eq!(u64_sub_to_i64(u64::MAX, u64::MAX), 0);
    assert_eq!(u64_sub_to_i64(0, i64::MAX as u64 + 1), i64::MIN);
}

//------------------------------------------

pub fn zigzag_encode(n: i64) -> u64 {
    ((n << 1) ^ (n >> 63)) as u64
}

pub fn zigzag_decode(n: u64) -> i64 {
    ((n >> 1) as i64) ^ (-(n as i64 & 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zigzag_codec() {
        let test_cases = [
            0,
            1,
            -1,
            2,
            -2,
            i64::MAX,
            i64::MIN,
            i64::MAX - 1,
            i64::MIN + 1,
            1234567,
            -1234567,
        ];

        for &value in &test_cases {
            let encoded = zigzag_encode(value);
            let decoded = zigzag_decode(encoded);
            assert_eq!(value, decoded, "ZigZag codec failed for value: {}", value);
        }
    }
}

//------------------------------------------

type BitStream = BitWriter<Vec<u8>, BigEndian>;

//------------------------------------------

#[derive(Debug, Ord, PartialOrd, PartialEq, Eq)]
enum Instruction {
    SetKeyframe {
        thin: u64,
        data: u64,
        snap_time: u32,
    },
    IncThin(u64),
    DecThin(u64), // shouldn't need this in the real thing
    IncData(u64),
    DecData(u64),

    Len(u64),
    LenSmall(u8),
    Emit,        // adds len to both thin and data
    NewReg(i64), // Pushes a new reg which becomes the new reg[0], payload is the new time delta
    SwitchReg(u64),
    Shift(u8),
    Halt,
}

struct InstrStream {
    bits_written: usize,
    writer: BitWriter<Vec<u8>, BigEndian>,
    instr_stats: BTreeMap<u8, InstrStats>,
    debug: bool,
}

impl InstrStream {
    fn new(debug: bool) -> Self {
        Self {
            bits_written: 0,
            writer: BitWriter::endian(Vec::new(), BigEndian),
            instr_stats: BTreeMap::new(),
            debug,
        }
    }

    fn len(&self) -> usize {
        (self.bits_written + 7) / 8
    }

    fn write_bits(&mut self, bits: u32, value: u32) -> Result<()> {
        self.writer.write(bits, value)?;
        self.bits_written += bits as usize;
        Ok(())
    }

    fn write_varint_(&mut self, v: u64) -> Result<()> {
        // FIXME: many operands can't be 0
        let v = v - 1;

        if v <= 1 {
            // 1-bit prefix 0, followed by 1 bit (0-1)
            self.write_bits(1, 0)?;
            self.write_bits(1, v as u32)?;
        } else if v <= 5 {
            // 2-bit prefix 10, followed by 2 bits (2-5)
            self.write_bits(2, 0b10)?;
            self.write_bits(2, (v - 2) as u32)?;
        } else if v <= 21 {
            // 3-bit prefix 110, followed by 4 bits (6-21)
            self.write_bits(3, 0b110)?;
            self.write_bits(4, (v - 6) as u32)?;
        } else if v <= 277 {
            // 4-bit prefix 1110, followed by 8 bits (22-277)
            self.write_bits(4, 0b1110)?;
            self.write_bits(8, (v - 22) as u32)?;
        } else if v <= 65813 {
            // 5-bit prefix 11110, followed by 16 bits (278-65813)
            self.write_bits(5, 0b11110)?;
            self.write_bits(16, (v - 278) as u32)?;
        } else {
            // 5-bit prefix 11111, followed by standard varint encoding
            self.write_bits(5, 0b11111)?;
            let mut value = v;
            while value > 0x7F {
                self.write_bits(8, ((value & 0x7f) | 0x80) as u32)?;
                value >>= 7;
            }
            self.write_bits(8, value as u32)?;
        }
        Ok(())
    }

    fn write_varint(&mut self, mut v: u64) -> Result<()> {
        if v < 16 {
            return self.write_bits(5, v as u32);
        } else {
            self.write_bits(1, 1)?;
            // self.write_bits(5, 0b10000 | (v & 0b1111) as u32)?;
            // v >>= 4;
        }

        while v > 0x7F {
            self.write_bits(8, ((v & 0x7f) | 0x80) as u32)?;
            v >>= 7;
        }
        self.write_bits(8, v as u32)?;
        Ok(())
    }

    fn write_signed_varint(&mut self, v: i64) -> Result<()> {
        self.write_bits(1, if v < 0 { 1 } else { 0 })?;
        self.write_varint(v.abs() as u64)?;
        Ok(())
    }

    fn write_instr(&mut self, instr: &Instruction, comment: Option<String>) -> Result<()> {
        use Instruction::*;

        assert!(*instr != Len(0));

        let start_len = self.bits_written;
        let i_code;

        // emit: 0
        // inc data: 10
        // len: 1100
        // len small: 1111
        // switch reg: 1110
        // dec data: 11011
        // shift: 110101
        // inc thin: 1101001
        // new reg: 11010001
        // dec thin: 110100001
        // halt: 1101000000
        // key frame: 1101000001
        match instr {
            SetKeyframe {
                thin,
                data,
                snap_time,
            } => {
                self.write_bits(10, 0b1101_0000_01)?;
                self.write_varint(*thin)?;
                self.write_varint(*data)?;
                self.write_varint(*snap_time as u64)?;
                i_code = 0;
            }
            IncThin(delta) => {
                self.write_bits(7, 0b1101_001)?;
                self.write_varint(*delta)?;
                i_code = 1;
            }
            DecThin(delta) => {
                self.write_bits(9, 0b1101_0000_1)?;
                self.write_varint(*delta)?;
                i_code = 2;
            }
            IncData(delta) => {
                self.write_bits(2, 0b10)?;
                self.write_varint(*delta)?;
                i_code = 3;
            }
            DecData(delta) => {
                self.write_bits(5, 0b1101_1)?;
                self.write_varint(*delta)?;
                i_code = 4;
            }

            Len(len) => {
                self.write_bits(4, 0b1100)?;
                self.write_varint(*len)?;
                i_code = 10;
            }
            LenSmall(len) => {
                assert!(*len < 4);
                self.write_bits(4, 0b1111)?;
                self.write_bits(2, *len as u32)?;
                i_code = 11;
            }

            Emit => {
                self.write_bits(1, 0b0)?;
                i_code = 5;
            }
            NewReg(delta_time) => {
                self.write_bits(8, 0b1101_0001)?;
                self.write_signed_varint(*delta_time)?;
                i_code = 6;
            }
            SwitchReg(reg) => {
                assert!(*reg < 16);
                self.write_bits(4, 0b1110)?;
                self.write_bits(4, *reg as u32)?;
                i_code = 7;
            }
            Shift(count) => {
                //assert!(*count < 8);
                self.write_bits(6, 0b1101_01)?;
                self.write_varint(*count as u64)?;
                i_code = 8;
            }
            Halt => {
                self.write_bits(10, 0b1101_0000_00)?;
                i_code = 9;
            }
        }

        let stats = self.instr_stats.entry(i_code).or_insert(InstrStats {
            count: 0,
            total_bits: 0,
        });
        stats.count += 1;
        stats.total_bits += self.bits_written - start_len;

        if self.debug {
            let bits = self.bits_written - start_len;
            let instr = format_instr(&instr);

            if let Some(comment) = comment {
                println!("{:<5} {:}\t\t;; {}", bits, instr, comment);
            } else {
                println!("{:<5} {:}", bits, instr);
            }
        }

        Ok(())
    }

    fn complete(mut self) -> (Vec<u8>, BTreeMap<u8, InstrStats>) {
        self.writer.byte_align();
        self.writer.flush();
        (self.writer.into_writer(), self.instr_stats)
    }
}

//------------------------------------------

#[derive(Clone)]
struct InstrStats {
    count: usize,
    total_bits: usize,
}

// Walks all the mappings building up nodes.  It then records
// details about the nodes (eg, nr entries, nr_nodes) and throws
// them away.
pub struct Packer {
    debug: bool,
    mappings: VecDeque<Map>,

    nr_nodes: usize,
    nr_mapped_blocks: u64,

    // (nr_entries, nr nodes with this count)
    entry_counts: BTreeMap<usize, usize>,

    instr_stats: BTreeMap<u8, InstrStats>,
}

impl Default for Packer {
    fn default() -> Self {
        Self {
            debug: true,
            mappings: VecDeque::new(),
            nr_nodes: 0,
            nr_mapped_blocks: 0,
            entry_counts: BTreeMap::new(),
            instr_stats: BTreeMap::new(),
        }
    }
}

#[derive(Copy, Clone)]
struct Register {
    data: u64,
    snap_time: u32,
}

fn format_hex(bytes: &[u8]) -> String {
    let mut s = String::new();

    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }

    s
}

fn format_instr(instr: &Instruction) -> String {
    use Instruction::*;

    match instr {
        SetKeyframe {
            thin,
            data,
            snap_time,
        } => format!("keyframe {}, {}, {}", thin, data, snap_time),
        IncThin(delta) => format!("thin +{}", delta),
        DecThin(delta) => format!("thin -{}", delta),
        IncData(delta) => format!("data +{}", delta),
        DecData(delta) => format!("data -{}", delta),

        Len(len) => format!("len {}", len),
        LenSmall(len) => format!("len {}", len),
        Emit => format!("emit"), // adds len to both thin and data
        NewReg(time) => format!("push {:+}", time), // Pushes a new reg which becomes the new reg[0]
        SwitchReg(reg) => format!("reg {}", reg),
        Shift(count) => format!("shift {}", count),
        Halt => format!("halt"),
    }
}

impl Packer {
    // Builds a fake node, removing just enough entries from the mappings queue.
    // Then adjusts the stats.
    fn build_node(&mut self) -> Result<()> {
        use Instruction::*;

        let header_size = 32;

        let mut w = InstrStream::new(self.debug);
        let mut nr_entries = 0;
        let mut nr_mapped_blocks = 0;

        // Emit the key frame.
        let mut reg = 0;
        let mut regs = VecDeque::new();
        let mut current_thin = 0;
        let mut current_len = 0;
        let mut shift = 0;
        let mut last_shift = 0;
        if let Some(m) = self.mappings.pop_front() {
            w.write_instr(
                &SetKeyframe {
                    thin: m.thin_begin,
                    data: m.data_begin,
                    snap_time: m.time,
                },
                None,
            )?;
            w.write_instr(&Len(m.len >> shift), None)?;
            current_len = m.len;
            w.write_instr(&Emit, None)?;

            current_thin = m.thin_begin + m.len;
            regs.push_front(Register {
                data: m.data_begin + m.len,
                snap_time: m.time,
            });
        }

        while let Some(m) = self.mappings.pop_front() {
            let new_shift = (current_thin | m.thin_begin | regs[reg].data | m.data_begin | m.len)
                .trailing_zeros();
            if new_shift != shift {
                if new_shift > shift && last_shift != new_shift {
                    last_shift = new_shift;
                } else {
                    shift = new_shift;
                    w.write_instr(&Shift(shift as u8), None)?;
                }
            }
            if current_thin != m.thin_begin {
                if m.thin_begin > current_thin {
                    w.write_instr(&IncThin((m.thin_begin - current_thin) >> shift), None)?;
                } else {
                    w.write_instr(&DecThin((current_thin - m.thin_begin) >> shift), None)?
                }
                current_thin = m.thin_begin;
            }

            if regs[reg].snap_time != m.time {
                // see if this time is already in the reg file
                let mut found = None;
                for (i, r) in regs.iter().enumerate() {
                    if r.snap_time == m.time {
                        found = Some(i);
                        break;
                    }
                }

                if let Some(new_reg) = found {
                    w.write_instr(&SwitchReg(new_reg as u64), None)?;
                    reg = new_reg;
                } else {
                    w.write_instr(
                        &NewReg(u64_sub_to_i64(m.time as u64, regs[reg].snap_time as u64)),
                        None,
                    )?;
                    regs.push_front(regs[reg].clone());
                    if regs.len() > 16 {
                        regs.pop_back();
                    }
                    reg = 0;
                    regs[reg].snap_time = m.time;
                }
            }

            if regs[reg].data != m.data_begin {
                if m.data_begin > regs[reg].data {
                    w.write_instr(&IncData((m.data_begin - regs[reg].data) >> shift), None)?;
                } else {
                    w.write_instr(&DecData((regs[reg].data - m.data_begin) >> shift), None)?;
                }
                regs[reg].data = m.data_begin;
            }

            if current_len != m.len {
                let len = m.len >> shift;
                if len < 4 {
                    w.write_instr(&LenSmall(len as u8), None)?;
                } else {
                    w.write_instr(&Len(m.len >> shift), None)?;
                }
                current_len = m.len;
            }

            current_thin += m.len;
            regs[reg].data += m.len;

            if self.debug {
                let comment = format!(
                    "thin={}, data={}, time={}, len={}",
                    m.thin_begin, m.data_begin, m.time, m.len
                );
                w.write_instr(&Emit, Some(comment))?;
                println!("");
            } else {
                w.write_instr(&Emit, None)?;
            }

            nr_entries += 1;
            nr_mapped_blocks += m.len;

            if w.len() > 4096 - header_size {
                break;
            }
        }
        w.write_instr(&Halt, None)?;

        let (bytes, stats) = w.complete();

        // Merge stats into self.instr_stats
        for (instr, new_stats) in stats {
            let entry = self.instr_stats.entry(instr).or_insert(InstrStats {
                count: 0,
                total_bits: 0,
            });
            entry.count += new_stats.count;
            entry.total_bits += new_stats.total_bits;
        }

        // increment the entry count bucket with nr_entries
        *self.entry_counts.entry(nr_entries).or_insert(0) += 1;
        self.nr_nodes += 1;
        self.nr_mapped_blocks += nr_mapped_blocks;

        // use zstd::bulk::compress;
        // let compressed = compress(&bytes, 0)?;
        // println!("len = {}, compressed = {}", bytes.len(), compressed.len());

        Ok(())
    }

    // Build a node if we've got enough mappings to guarantee a full node.
    fn maybe_build_node(&mut self) -> Result<()> {
        if self.mappings.len() > 10000 {
            self.build_node()
        } else {
            Ok(())
        }
    }

    // Force all mappings to be consumed, eg, we're switching devices.
    fn build_all_nodes(&mut self) -> Result<()> {
        while !self.mappings.is_empty() {
            self.build_node()?;
        }
        Ok(())
    }

    // Indicate we've got to the end of the current device or shared section.
    fn new_node(&mut self) -> Result<()> {
        self.build_all_nodes()
    }

    // FIXME: convert to 4k blocks
    fn push_mapping(&mut self, m: &Map) {
        // Assume 32k blocks, which is 4k * 8
        let m = Map {
            thin_begin: m.thin_begin * 8,
            data_begin: m.data_begin * 8,
            time: m.time,
            len: m.len * 8,
        };
        self.mappings.push_back(m);
    }

    fn instr_name(instr: u8) -> &'static str {
        match instr {
            0 => "key frame ",
            1 => "inc thin  ",
            2 => "dec thin  ",
            3 => "inc data  ",
            4 => "dec data  ",
            5 => "emit      ",
            6 => "new reg   ",
            7 => "switch reg",
            8 => "shift     ",
            9 => "halt      ",
            10 => "len       ",
            11 => "len small ",
            _ => panic!("unknown instruction"),
        }
    }

    pub fn print_results(&self) {
        println!("Nr mapped blocks: {}", self.nr_mapped_blocks);
        println!(
            "Total number of nodes: {} ({:.2} meg)",
            self.nr_nodes,
            (4096.0 * self.nr_nodes as f64) / (1024.0 * 1024.0)
        );

        let (mean, _std_dev) = self.calculate_stats();

        println!("Mean entries per node: {:.2}", mean);
        println!(
            "Mean run length: {:.2}",
            self.nr_mapped_blocks as f64 / (self.nr_nodes as f64 * mean * 8.0)
        );
        println!("Mean bytes per entry: {:.2}", (4096.0 - 32.0) / mean);

        let mut instr_stats = Vec::new();
        for (k, v) in &self.instr_stats {
            instr_stats.push((k, v.clone()));
        }

        instr_stats.sort_by(|a, b| b.1.total_bits.cmp(&a.1.total_bits));
        for (instr, stats) in instr_stats {
            println!(
                "{:16}: count {:8}, mean bits {:6.1}, total bytes {:10}",
                Self::instr_name(*instr),
                stats.count,
                stats.total_bits as f64 / (stats.count as f64),
                (stats.total_bits as f64 / 8.0) as u64
            );
        }
    }

    fn calculate_stats(&self) -> (f64, f64) {
        let total_entries: usize = self
            .entry_counts
            .iter()
            .map(|(&entries, &count)| entries * count)
            .sum();

        let total_nodes: usize = self.entry_counts.values().sum();

        let mean = total_entries as f64 / total_nodes as f64;

        let variance = self
            .entry_counts
            .iter()
            .map(|(&entries, &count)| {
                let diff = entries as f64 - mean;
                diff * diff * count as f64
            })
            .sum::<f64>()
            / total_nodes as f64;

        let std_dev = variance.sqrt();

        (mean, std_dev)
    }
}

impl MetadataVisitor for Packer {
    fn superblock_b(&mut self, _sb: &ir::Superblock) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    fn superblock_e(&mut self) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    fn def_shared_b(&mut self, _name: &str) -> Result<ir::Visit> {
        // Most of the refs in complex thinp1 metadata is for a single node, so ~100 entries.
        // Which leaves us with very underfull nodes.  So I'm knocking out the new_node() call
        // to merge everything together.  Will give more meaningful results, even if it's wrong.
        // self.new_node()?;
        Ok(Visit::Continue)
    }

    fn def_shared_e(&mut self) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    // A device contains a number of 'map' or 'ref' items.
    fn device_b(&mut self, _d: &ir::Device) -> Result<Visit> {
        // self.new_node()?;
        Ok(Visit::Continue)
    }

    fn device_e(&mut self) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    fn map(&mut self, m: &ir::Map) -> Result<Visit> {
        self.push_mapping(m);
        self.maybe_build_node()?;
        Ok(Visit::Continue)
    }

    fn ref_shared(&mut self, _name: &str) -> Result<Visit> {
        // self.new_node()?;
        Ok(Visit::Continue)
    }

    fn eof(&mut self) -> Result<Visit> {
        self.new_node()?;
        Ok(Visit::Continue)
    }
}

//------------------------------------------
