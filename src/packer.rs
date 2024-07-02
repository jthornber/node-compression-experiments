use anyhow::Result;
use byteorder::WriteBytesExt;
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

pub fn write_varint_with_field<W: io::Write>(
    writer: &mut W,
    field: u8,
    bits: u8,
    mut value: u64,
) -> io::Result<()> {
    let shift = 8 - bits;
    let mask = (1 << (shift - 1)) - 1;

    if value <= ((1 << (shift - 1)) - 1) {
        // pack it with the field in a single byte
        writer.write_u8((field << shift) | value as u8)?;
    } else {
        // Write first byte with field and continuation bit
        writer.write_u8((field << shift) | (1 << (shift - 1)) | ((value & mask) as u8))?;
        value >>= shift - 1;

        // Write remaining bytes as in the original varint encoding
        while value > 0x7F {
            writer.write_u8(((value & 0x7F) | 0x80) as u8)?;
            value >>= 7;
        }
        writer.write_u8(value as u8)?;
    }

    Ok(())
}

pub fn write_varint_with_field_signed<W: io::Write>(
    writer: &mut W,
    field: u8,
    bits: u8,
    value: i64,
) -> io::Result<()> {
    // ZigZag encode the signed value
    let encoded = zigzag_encode(value);
    write_varint_with_field(writer, field, bits, encoded)
}

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

    Emit(u64),   // adds len to both thin and data
    NewReg(i64), // Pushes a new reg which becomes the new reg[0], payload is the new time delta
    SwitchReg(u64),
    Shift(u8),
    Halt,
}

//------------------------------------------

#[derive(Clone)]
struct InstrStats {
    count: usize,
    total_bytes: usize,
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
            debug: false,
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

        Emit(len) => format!("emit {}", len), // adds len to both thin and data
        NewReg(time) => format!("push {:+}", time), // Pushes a new reg which becomes the new reg[0]
        SwitchReg(reg) => format!("reg {}", reg),
        Shift(count) => format!("shift {}", count),
        Halt => format!("halt"),
    }
}

impl Packer {
    fn pack_instr_(
        &mut self,
        w: &mut Vec<u8>,
        instr: &Instruction,
        comment: Option<String>,
    ) -> Result<()> {
        use Instruction::*;

        assert!(*instr != Emit(0));

        let start_len = w.len();

        let mut update_stats = |code, len| {
            let stats = self.instr_stats.entry(code).or_insert(InstrStats {
                count: 0,
                total_bytes: 0,
            });
            stats.count += 1;
            stats.total_bytes += len - start_len;
        };

        // emit: 11
        // inc data: 0
        // switch reg: 101
        // dec data: 1001
        // shift: 1000 1
        // inc thin: 1000 01
        // new reg: 1000 001
        // dec thin: 1000 0001
        // halt: 0000 0000
        // key frame: 1000 0000
        match instr {
            SetKeyframe {
                thin,
                data,
                snap_time,
            } => {
                write_varint_with_field(w, 0b1000_0000, 8, *thin)?;
                write_varint(w, *data)?;
                write_varint(w, *snap_time as u64)?;

                update_stats(0, w.len());
            }
            IncThin(delta) => {
                write_varint_with_field(w, 0b1000_01, 6, *delta)?;
                update_stats(1, w.len());
            }
            DecThin(delta) => {
                write_varint_with_field(w, 0b1000_0001, 8, *delta)?;
                update_stats(2, w.len());
            }
            IncData(delta) => {
                write_varint_with_field(w, 0b0, 1, *delta)?;
                update_stats(3, w.len());
            }
            DecData(delta) => {
                write_varint_with_field(w, 0b1001, 4, *delta)?;
                update_stats(4, w.len());
            }
            Emit(len) => {
                write_varint_with_field(w, 0b11, 2, *len)?;
                update_stats(5, w.len());
            }
            NewReg(delta_time) => {
                write_varint_with_field_signed(w, 0b1000_01, 6, *delta_time)?;
                update_stats(6, w.len());
            }
            SwitchReg(reg) => {
                assert!(*reg < 32);
                w.write_u8(0b101 << 5 | *reg as u8)?;
                update_stats(7, w.len());
            }
            Shift(count) => {
                // FIXME: more than 8 instrs, so should huffman encode
                w.write_u8(0b1000_1 << 3 | *count)?;
                update_stats(8, w.len());
            }
            Halt => {
                // FIXME: more than 8 instrs, so should huffman encode
                w.write_u8(0b00000000)?;
                update_stats(9, w.len());
            }
        }

        if self.debug {
            let hex = format_hex(&w[start_len..w.len()]);
            let instr = format_instr(&instr);

            if let Some(comment) = comment {
                println!("{:25}{:}\t\t;; {}", hex, instr, comment);
            } else {
                println!("{:25}{:}", hex, instr);
            }
        }

        Ok(())
    }

    fn pack_instr(&mut self, w: &mut Vec<u8>, instr: &Instruction) -> Result<()> {
        self.pack_instr_(w, instr, None)
    }

    // Builds a fake node, removing just enough entries from the mappings queue.
    // Then adjusts the stats.
    fn build_node(&mut self) -> Result<()> {
        use Instruction::*;

        let header_size = 32;

        let mut w: Vec<u8> = Vec::new();
        let mut nr_entries = 0;
        let mut nr_mapped_blocks = 0;

        // Emit the key frame.
        let mut reg = 0;
        let mut regs = VecDeque::new();
        let mut current_thin = 0;
        let mut shift = 0;
        let mut last_shift = 0;
        if let Some(m) = self.mappings.pop_front() {
            self.pack_instr(
                &mut w,
                &SetKeyframe {
                    thin: m.thin_begin,
                    data: m.data_begin,
                    snap_time: m.time,
                },
            )?;
            self.pack_instr(&mut w, &Emit(m.len >> shift))?;

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
                    self.pack_instr(&mut w, &Shift(shift as u8))?;
                }
            }
            if current_thin != m.thin_begin {
                if m.thin_begin > current_thin {
                    self.pack_instr(&mut w, &IncThin((m.thin_begin - current_thin) >> shift))?;
                } else {
                    self.pack_instr(&mut w, &DecThin((current_thin - m.thin_begin) >> shift))?
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
                    self.pack_instr(&mut w, &SwitchReg(new_reg as u64))?;
                    reg = new_reg;
                } else {
                    self.pack_instr(
                        &mut w,
                        &NewReg(u64_sub_to_i64(m.time as u64, regs[reg].snap_time as u64)),
                    )?;
                    regs.push_front(regs[reg].clone());
                    if regs.len() > 32 {
                        regs.pop_back();
                    }
                    reg = 0;
                    regs[reg].snap_time = m.time;
                }
            }

            if regs[reg].data != m.data_begin {
                if m.data_begin > regs[reg].data {
                    self.pack_instr(&mut w, &IncData((m.data_begin - regs[reg].data) >> shift))?;
                } else {
                    self.pack_instr(&mut w, &DecData((regs[reg].data - m.data_begin) >> shift))?;
                }
                regs[reg].data = m.data_begin;
            }

            current_thin += m.len;
            regs[reg].data += m.len;

            if self.debug {
                let comment = format!(
                    "thin={}, data={}, time={}, len={}",
                    m.thin_begin, m.data_begin, m.time, m.len
                );
                self.pack_instr_(&mut w, &Emit(m.len >> shift), Some(comment))?;
                println!("");
            } else {
                self.pack_instr(&mut w, &Emit(m.len >> shift))?;
            }

            nr_entries += 1;
            nr_mapped_blocks += m.len;

            if w.len() > 4096 - header_size {
                break;
            }
        }
        self.pack_instr(&mut w, &Halt)?;

        // increment the entry count bucket with nr_entries
        *self.entry_counts.entry(nr_entries).or_insert(0) += 1;
        self.nr_nodes += 1;
        self.nr_mapped_blocks += nr_mapped_blocks;

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

        instr_stats.sort_by(|a, b| b.1.total_bytes.cmp(&a.1.total_bytes));
        for (instr, stats) in instr_stats {
            println!(
                "{:16}: count {:8}, mean bytes {:6.2}, total bytes {:10}",
                Self::instr_name(*instr),
                stats.count,
                stats.total_bytes as f64 / stats.count as f64,
                stats.total_bytes
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
