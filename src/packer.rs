use anyhow::Result;
use byteorder::{LittleEndian, WriteBytesExt};
use std::collections::{BTreeMap, VecDeque};
use std::io::{self, Write};
use thinp::thin::ir::{self, Map, MetadataVisitor, Visit};

use crate::varint::*;

//------------------------------------------

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

pub fn write_varint_with_field<W: Write>(
    writer: &mut W,
    field: u8,
    mut value: u64,
) -> io::Result<()> {
    if field > 0b111 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Field must be 3 bits or less",
        ));
    }

    if value <= 0x0F {
        // If value fits in 4 bits, pack it with the field in a single byte
        writer.write_u8(((field & 0b111) << 5) | (value as u8 & 0x0F))?;
    } else {
        // Write first byte with field and continuation bit
        writer.write_u8(((field & 0b111) << 5) | 0x10 | ((value & 0x0F) as u8))?;
        value >>= 4;

        // Write remaining bytes as in the original varint encoding
        while value > 0x7F {
            writer.write_u8(((value & 0x7F) | 0x80) as u8)?;
            value >>= 7;
        }
        writer.write_u8(value as u8)?;
    }

    Ok(())
}

pub fn write_varint_with_field_signed<W: Write>(
    writer: &mut W,
    field: u8,
    value: i64,
) -> io::Result<()> {
    if field > 0b111 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Field must be 3 bits or less",
        ));
    }

    // ZigZag encode the signed value
    let encoded = zigzag_encode(value);

    if encoded <= 0x0F {
        // If encoded value fits in 4 bits, pack it with the field in a single byte
        writer.write_u8(((field & 0b111) << 5) | (encoded as u8 & 0x0F))?;
    } else {
        // Write first byte with field and continuation bit
        writer.write_u8(((field & 0b111) << 5) | 0x10 | ((encoded & 0x0F) as u8))?;
        let mut remaining = encoded >> 4;

        // Write remaining bytes as in the original varint encoding
        while remaining > 0x7F {
            writer.write_u8(((remaining & 0x7F) | 0x80) as u8)?;
            remaining >>= 7;
        }
        writer.write_u8(remaining as u8)?;
    }

    Ok(())
}

//------------------------------------------

#[derive(Debug, Ord, PartialOrd, PartialEq, Eq)]
enum Instruction {
    SetKeyframe {
        thin: u64,
        data: u64,
        snap_time: u32,
    },
    DeltaThin(i64),
    SetData(u64),
    DeltaData(i64),
    SetSnapTime(u64),

    Emit(u64), // adds len to both thin and data
    NewReg,    // Pushes a new reg which becomes the new reg[0]
    SwitchReg(u64),
}

//------------------------------------------

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

impl Packer {
    fn pack_instr(&mut self, w: &mut Vec<u8>, instr: &Instruction) -> Result<()> {
        use Instruction::*;

        let start_len = w.len();

        let mut update_stats = |code, len: usize| {
            let stats = self.instr_stats.entry(code).or_insert(InstrStats {
                count: 0,
                total_bytes: 0,
            });
            stats.count += 1;
            stats.total_bytes += len - start_len;
        };

        if self.debug {
            println!("    {:?}", instr);
        }
        match instr {
            SetKeyframe {
                thin,
                data,
                snap_time,
            } => {
                write_varint_with_field(w, 0, *thin)?;
                write_varint(w, *data)?;
                write_varint(w, *snap_time as u64)?;

                update_stats(0, w.len());
            }
            DeltaThin(delta) => {
                write_varint_with_field_signed(w, 1, *delta)?;
                update_stats(1, w.len());
            }
            SetData(data) => {
                write_varint_with_field(w, 2, *data)?;
                update_stats(2, w.len());
            }
            DeltaData(delta) => {
                write_varint_with_field_signed(w, 3, *delta)?;
                update_stats(3, w.len());
            }
            SetSnapTime(time) => {
                write_varint_with_field(w, 4, *time as u64)?;
                update_stats(4, w.len());
            }
            Emit(len) => {
                write_varint_with_field(w, 5, *len)?;
                update_stats(5, w.len());
            }
            NewReg => {
                w.write_u8(6)?;
                update_stats(6, w.len());
            }
            SwitchReg(reg) => {
                assert!(*reg < 32);
                w.write_u8(7 << 5 | *reg as u8)?;
                update_stats(7, w.len());
            }
        }

        Ok(())
    }

    // Builds a fake node, removing just enough entries from the mappings queue.
    // Then adjusts the stats.
    fn build_node(&mut self) -> Result<()> {
        use Instruction::*;

        let header_size = 32;
        let new_reg_threshold = 4096 * 256;

        let mut w: Vec<u8> = Vec::new();
        let mut nr_entries = 0;
        let mut nr_mapped_blocks = 0;

        // Emit the key frame.
        let mut reg = 0;
        let mut regs = VecDeque::new();
        let mut current_thin = 0;
        if let Some(m) = self.mappings.pop_front() {
            self.pack_instr(
                &mut w,
                &SetKeyframe {
                    thin: m.thin_begin,
                    data: m.data_begin,
                    snap_time: m.time,
                },
            )?;

            current_thin = m.thin_begin + m.len;
            regs.push_front(Register {
                data: m.data_begin + m.len,
                snap_time: m.time,
            });
        }

        while let Some(m) = self.mappings.pop_front() {
            if self.debug {
                println!(
                    "current: thin {}, data {}, time {}",
                    current_thin, regs[reg].data, regs[reg].snap_time,
                );
                println!(
                    "m:       thin {}, data {}, time {}, len {}",
                    m.thin_begin, m.data_begin, m.time, m.len
                );
            }

            if current_thin != m.thin_begin {
                self.pack_instr(
                    &mut w,
                    &DeltaThin(u64_sub_to_i64(m.thin_begin, current_thin)),
                )?;
                current_thin = m.thin_begin;
            }

            // Choose the closest register
            let (nearest_reg, nearest_diff) = regs
                .iter()
                .enumerate()
                .map(|(i, r)| (i, u64_sub_to_i64(m.data_begin, r.data).abs()))
                .min_by_key(|&(_, diff)| diff)
                .unwrap();

            let near_enough = nearest_diff < new_reg_threshold;
            if nearest_reg != reg && near_enough {
                self.pack_instr(&mut w, &SwitchReg(nearest_reg as u64))?;
                reg = nearest_reg;

                // Apply a small delta if needed after switching
                let delta = u64_sub_to_i64(m.data_begin, regs[reg].data);
                if delta != 0 {
                    self.pack_instr(&mut w, &DeltaData(delta))?;
                }
            } else if near_enough {
                // continue with this reg
                let delta = u64_sub_to_i64(m.data_begin, regs[reg].data);
                self.pack_instr(&mut w, &DeltaData(delta))?;
            } else {
                // create new reg
                self.pack_instr(&mut w, &NewReg)?;
                let r = regs[reg].clone();
                regs.push_front(r);
                if regs.len() > 32 {
                    regs.pop_back();
                }
                reg = 0;

                let delta = u64_sub_to_i64(m.data_begin, regs[reg].data);
                self.pack_instr(&mut w, &DeltaData(delta))?;
                regs[reg].data = m.data_begin;
            }
            regs[reg].data = m.data_begin;

            if regs[reg].snap_time != m.time {
                self.pack_instr(&mut w, &SetSnapTime(m.time as u64))?;
                regs[reg].snap_time = m.time;
            }

            current_thin += m.len;
            regs[reg].data += m.len;
            self.pack_instr(&mut w, &Emit(m.len))?;

            if w.len() > 4096 - header_size {
                self.mappings.push_front(m.clone());
                break;
            }

            nr_entries += 1;
            nr_mapped_blocks += m.len;
        }

        // increment the entry count bucket with nr_entries
        *self.entry_counts.entry(nr_entries).or_insert(0) += 1;
        self.nr_nodes += 1;
        self.nr_mapped_blocks += nr_mapped_blocks;

        Ok(())
    }

    // Build a node if we've got enough mappings to guarantee a full node.
    fn maybe_build_node(&mut self) -> Result<()> {
        if self.mappings.len() > 1000 {
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
        self.mappings.push_back(m.clone());
    }

    fn instr_name(instr: u8) -> &'static str {
        match instr {
            0 => "key frame ",
            1 => "delta thin",
            2 => "set data  ",
            3 => "delta data",
            4 => "set time  ",
            5 => "emit      ",
            6 => "new reg   ",
            7 => "switch reg",
            _ => panic!("unknown instruction"),
        }
    }

    pub fn print_results(&self) {
        println!("Nr mapped blocks: {}", self.nr_mapped_blocks);
        println!(
            "Total number of nodes: {}, {:.2}m",
            self.nr_nodes,
            (4096.0 * self.nr_nodes as f64) / (1024.0 * 1024.0)
        );

        let (mean, std_dev) = self.calculate_stats();

        println!("Entries per node:");
        println!("  Mean: {:.2}", mean);
        println!("  Standard Deviation: {:.2}", std_dev);

        for (instr, stats) in &self.instr_stats {
            println!(
                "{}: count {}, mean bytes {}",
                Self::instr_name(*instr),
                stats.count,
                stats.total_bytes as f64 / stats.count as f64
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
        eprintln!("superblock");
        Ok(Visit::Continue)
    }

    fn superblock_e(&mut self) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    fn def_shared_b(&mut self, _name: &str) -> Result<ir::Visit> {
        self.new_node()?;
        Ok(Visit::Continue)
    }

    fn def_shared_e(&mut self) -> Result<Visit> {
        Ok(Visit::Continue)
    }

    // A device contains a number of 'map' or 'ref' items.
    fn device_b(&mut self, _d: &ir::Device) -> Result<Visit> {
        self.new_node()?;
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
        self.new_node()?;
        Ok(Visit::Continue)
    }

    fn eof(&mut self) -> Result<Visit> {
        self.new_node()?;
        Ok(Visit::Continue)
    }
}

//------------------------------------------
