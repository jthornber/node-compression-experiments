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

#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Debug)]
enum Sign {
    PLUS,
    MINUS,
}

#[derive(Debug, Ord, PartialOrd, PartialEq, Eq)]
enum Instruction {
    SetKeyframe {
        thin: u64,
        data: u64,
        snap_time: u32,
    },
    NewReg(Sign, u64), // Pushes a new reg which becomes the new reg[0], payload is the new time delta
    Shift(u8),
    Repeat(u64),
    Halt,

    // These get represented as bits within the emit instr
    SwitchReg(u64),
    DeltaThin(Sign, u64),
    DeltaData(Sign, u64),
    Len(u64),
    Emit, // adds len to both thin and data
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ISet {
    switch_reg: bool,
    delta_thin: bool,
    delta_data: bool,
    len: bool,
}

impl ISet {
    fn new() -> Self {
        Self {
            switch_reg: false,
            delta_thin: false,
            delta_data: false,
            len: false,
        }
    }

    fn clear(&mut self) {
        self.switch_reg = false;
        self.delta_thin = false;
        self.delta_data = false;
        self.len = false;
    }
}

struct ISetAggregator {
    last: ISet,
    count: usize,
}

impl ISetAggregator {
    fn new() -> Self {
        Self {
            last: ISet::new(),
            count: 0,
        }
    }

    fn push(&mut self, iset: &ISet) -> Option<(usize, ISet)> {
        if self.count > 0 {
            if *iset == self.last {
                self.count += 1;
                None
            } else {
                let mut last = iset.clone();
                std::mem::swap(&mut self.last, &mut last);
                let count = self.count;
                self.count = 1;
                Some((count, last))
            }
        } else {
            self.last = *iset;
            self.count = 1;
            None
        }
    }

    fn complete(&mut self) -> Option<(usize, ISet)> {
        if self.count > 0 {
            let count = self.count;
            let mut last = ISet::new();
            std::mem::swap(&mut self.last, &mut last);
            self.count = 0;
            Some((count, last))
        } else {
            None
        }
    }
}

struct InstrStream {
    bits_written: usize,
    opcode_writer: BitWriter<Vec<u8>, BigEndian>,
    arg_writer: BitWriter<Vec<u8>, BigEndian>,
    instr_stats: BTreeMap<u8, InstrStats>,

    iset: ISet,
    isets: ISetAggregator,

    debug: bool,
}

#[derive(Copy, Clone)]
enum Stream {
    OPCODE,
    ARGS,
}

use Stream::*;

impl InstrStream {
    fn new(debug: bool) -> Self {
        Self {
            bits_written: 0,
            opcode_writer: BitWriter::endian(Vec::new(), BigEndian),
            arg_writer: BitWriter::endian(Vec::new(), BigEndian),
            instr_stats: BTreeMap::new(),

            iset: ISet::new(),
            isets: ISetAggregator::new(),

            debug,
        }
    }

    fn len(&self) -> usize {
        (self.bits_written + 7) / 8
    }

    fn write_bits(&mut self, bits: u32, value: u32, stream: Stream) -> Result<()> {
        match stream {
            OPCODE => {
                self.opcode_writer.write(bits, value)?;
            }
            ARGS => {
                self.arg_writer.write(bits, value)?;
            }
        }

        self.bits_written += bits as usize;
        Ok(())
    }

    fn write_varint(&mut self, mut v: u64, stream: Stream) -> Result<()> {
        if v < 16 {
            return self.write_bits(5, v as u32, stream);
        } else {
            self.write_bits(1, 1, stream)?;
        }

        while v > 0x7F {
            self.write_bits(8, ((v & 0x7f) | 0x80) as u32, stream)?;
            v >>= 7;
        }
        self.write_bits(8, v as u32, stream)?;
        Ok(())
    }

    fn write_signed_varint(&mut self, sign: Sign, v: u64, stream: Stream) -> Result<()> {
        self.write_bits(1, sign as u32, stream)?;
        self.write_varint(v, stream)?;
        Ok(())
    }

    fn emit_(&mut self, count: usize, iset: &ISet) -> Result<()> {
        assert!(count != 0);

        // println!("count {}, iset {:?}", count, iset);
        if count > 1 {
            self.write_bits(3, 0b110, OPCODE)?;
            self.write_varint(count as u64, ARGS)?;
        }

        self.write_bits(1, 0b0, OPCODE)?;
        self.write_bits(1, iset.switch_reg as u32, OPCODE)?;
        self.write_bits(1, iset.delta_thin as u32, OPCODE)?;
        self.write_bits(1, iset.delta_data as u32, OPCODE)?;
        self.write_bits(1, iset.len as u32, OPCODE)?;

        Ok(())
    }

    fn write_instr(&mut self, instr: &Instruction, comment: Option<String>) -> Result<()> {
        use Instruction::*;

        assert!(*instr != Len(0));

        let start_len = self.bits_written;
        let i_code;

        match instr {
            SetKeyframe {
                thin,
                data,
                snap_time,
            } => {
                self.write_bits(4, 0b1111, OPCODE)?;
                self.write_varint(*thin, ARGS)?;
                self.write_varint(*data, ARGS)?;
                self.write_varint(*snap_time as u64, ARGS)?;
                i_code = 0;
            }
            DeltaThin(sign, delta) => {
                self.write_signed_varint(*sign, *delta, ARGS)?;
                self.iset.delta_thin = true;
                i_code = 1;
            }
            DeltaData(sign, delta) => {
                self.write_signed_varint(*sign, *delta, ARGS)?;
                self.iset.delta_data = true;
                i_code = 2;
            }

            Len(len) => {
                self.write_varint(*len, ARGS)?;
                self.iset.len = true;
                i_code = 3;
            }

            Emit => {
                if let Some((count, iset)) = self.isets.push(&self.iset) {
                    self.emit_(count, &iset)?;
                }

                self.iset.clear();

                i_code = 4;
            }
            NewReg(sign, delta_time) => {
                self.write_bits(3, 0b100, OPCODE)?;
                self.write_signed_varint(*sign, *delta_time, ARGS)?;
                i_code = 5;
            }
            SwitchReg(reg) => {
                assert!(*reg < 16);
                self.write_bits(4, *reg as u32, ARGS)?;
                self.iset.switch_reg = true;
                i_code = 6;
            }
            Shift(count) => {
                self.write_bits(3, 0b101, OPCODE)?;
                self.write_varint(*count as u64, ARGS)?;
                i_code = 7;
            }
            Halt => {
                self.write_bits(4, 0b1110, OPCODE)?;
                i_code = 8;
            }
            Repeat(count) => {
                self.write_bits(3, 0b110, OPCODE)?;
                self.write_varint(*count as u64, ARGS)?;
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

    fn complete(mut self) -> Result<(Vec<u8>, Vec<u8>, BTreeMap<u8, InstrStats>)> {
        if let Some((count, iset)) = self.isets.complete() {
            self.emit_(count, &iset)?;
        }

        self.opcode_writer.byte_align();
        self.opcode_writer.flush();

        self.arg_writer.byte_align();
        self.arg_writer.flush();
        Ok((
            self.opcode_writer.into_writer(),
            self.arg_writer.into_writer(),
            self.instr_stats,
        ))
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
        DeltaThin(Sign::PLUS, delta) => format!("thin +{}", delta),
        DeltaThin(Sign::MINUS, delta) => format!("thin -{}", delta),
        DeltaData(Sign::PLUS, delta) => format!("data +{}", delta),
        DeltaData(Sign::MINUS, delta) => format!("data -{}", delta),

        Len(len) => format!("len {}", len),
        Emit => format!("emit"), // adds len to both thin and data
        NewReg(Sign::PLUS, time) => format!("push +{}", time), // Pushes a new reg which becomes the new reg[0]
        NewReg(Sign::MINUS, time) => format!("push -{}", time), // Pushes a new reg which becomes the new reg[0]
        SwitchReg(reg) => format!("reg {}", reg),
        Shift(count) => format!("shift {}", count),
        Halt => format!("halt"),
        Repeat(count) => format!("repeat {}", count),
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
                    w.write_instr(
                        &DeltaThin(Sign::PLUS, (m.thin_begin - current_thin) >> shift),
                        None,
                    )?;
                } else {
                    w.write_instr(
                        &DeltaThin(Sign::MINUS, (current_thin - m.thin_begin) >> shift),
                        None,
                    )?
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
                    if m.time > regs[reg].snap_time {
                        w.write_instr(
                            &NewReg(Sign::PLUS, m.time as u64 - regs[reg].snap_time as u64),
                            None,
                        )?;
                    } else {
                        w.write_instr(
                            &NewReg(Sign::MINUS, regs[reg].snap_time as u64 - m.time as u64),
                            None,
                        )?;
                    }
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
                    w.write_instr(
                        &DeltaData(Sign::PLUS, (m.data_begin - regs[reg].data) >> shift),
                        None,
                    )?;
                } else {
                    w.write_instr(
                        &DeltaData(Sign::MINUS, (regs[reg].data - m.data_begin) >> shift),
                        None,
                    )?;
                }
                regs[reg].data = m.data_begin;
            }

            if current_len != m.len {
                let len = m.len >> shift;
                w.write_instr(&Len(m.len >> shift), None)?;
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

        let (opcode_bytes, arg_bytes, stats) = w.complete()?;

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
            1 => "delta thin",
            2 => "delta data",
            3 => "len       ",
            4 => "emit      ",
            5 => "new reg   ",
            6 => "switch reg",
            7 => "shift     ",
            8 => "halt      ",
            9 => "repeat    ",
            _ => panic!("unknown instruction"),
        }
    }

    pub fn print_results(&self) {
        println!("Nr mapped blocks: {}", self.nr_mapped_blocks / 8);
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
