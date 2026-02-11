//! Liveness analysis for virtual registers.
//!
//! Computes live ranges by building a CFG from the linear instruction list,
//! running backward dataflow to get per-block live_in/live_out sets, then
//! merging into per-VReg [start, end) intervals.

use std::collections::{HashMap, HashSet};

use crate::{OpKind, RegAllocInst, VReg};

/// A live range for a single VReg: [start, end) in instruction indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveRange {
    pub vreg: VReg,
    pub start: u32,
    pub end: u32,
}

/// A basic block in the linear instruction stream.
struct Block {
    start: u32,
    end: u32,
    label: Option<u32>,
    successors: Vec<usize>,
}

/// Build basic blocks from a linear instruction stream.
/// Blocks are split at Label pseudo-instructions and after terminators.
fn build_blocks<I: RegAllocInst>(insts: &[I]) -> Vec<Block> {
    if insts.is_empty() {
        return vec![];
    }

    let mut blocks = Vec::new();
    let mut block_start = 0u32;
    let mut label = insts[0].label_id();

    for (i, inst) in insts.iter().enumerate() {
        let i = i as u32;

        // A label after block_start begins a new block.
        if i > block_start {
            if let Some(lid) = inst.label_id() {
                blocks.push(Block {
                    start: block_start,
                    end: i - 1,
                    label,
                    successors: vec![],
                });
                block_start = i;
                label = Some(lid);
                continue;
            }
        }

        // A terminator ends the current block.
        if inst.is_terminator() {
            blocks.push(Block {
                start: block_start,
                end: i,
                label,
                successors: vec![],
            });
            block_start = i + 1;
            label = if (i + 1) < insts.len() as u32 {
                insts[(i + 1) as usize].label_id()
            } else {
                None
            };
        }
    }

    // Trailing instructions without a terminator.
    if block_start < insts.len() as u32 {
        blocks.push(Block {
            start: block_start,
            end: insts.len() as u32 - 1,
            label,
            successors: vec![],
        });
    }

    // Resolve successors: branch targets + fallthrough.
    let label_to_block: HashMap<u32, usize> = blocks
        .iter()
        .enumerate()
        .filter_map(|(idx, b)| b.label.map(|l| (l, idx)))
        .collect();

    let mut targets = Vec::new();
    for bi in 0..blocks.len() {
        let last = blocks[bi].end as usize;
        targets.clear();
        insts[last].branch_targets(&mut targets);

        let mut succs = Vec::new();
        for &t in &targets {
            if let Some(&si) = label_to_block.get(&t) {
                succs.push(si);
            }
        }

        // Add fallthrough successor if the last instruction can fall through.
        if insts[last].falls_through() && bi + 1 < blocks.len() {
            succs.push(bi + 1);
        }

        blocks[bi].successors = succs;
    }

    blocks
}

/// Compute gen/kill sets for a block.
/// gen = VRegs used before being defined in the block.
/// kill = VRegs defined in the block.
fn block_gen_kill<I: RegAllocInst>(insts: &[I], block: &Block) -> (HashSet<VReg>, HashSet<VReg>) {
    let mut gen_set = HashSet::new();
    let mut kill_set = HashSet::new();
    let mut ops = Vec::new();

    for idx in block.start..=block.end {
        ops.clear();
        insts[idx as usize].reg_operands(&mut ops);

        for op in &ops {
            match op.kind {
                OpKind::Use => {
                    if !kill_set.contains(&op.vreg) {
                        gen_set.insert(op.vreg);
                    }
                }
                OpKind::Def => {
                    kill_set.insert(op.vreg);
                }
                OpKind::UseDef => {
                    if !kill_set.contains(&op.vreg) {
                        gen_set.insert(op.vreg);
                    }
                    kill_set.insert(op.vreg);
                }
            }
        }
    }

    (gen_set, kill_set)
}

/// Compute live ranges for all VRegs in the instruction stream.
///
/// Returns one `LiveRange` per VReg with a conservative [first_def, last_use+1)
/// interval. VRegs that are live across block boundaries get their ranges
/// extended to cover the full span.
pub fn compute_live_ranges<I: RegAllocInst>(insts: &[I], vreg_count: u32) -> Vec<LiveRange> {
    if insts.is_empty() || vreg_count == 0 {
        return vec![];
    }

    let blocks = build_blocks(insts);
    if blocks.is_empty() {
        return vec![];
    }

    // Compute gen/kill per block.
    let gen_kill: Vec<(HashSet<VReg>, HashSet<VReg>)> =
        blocks.iter().map(|b| block_gen_kill(insts, b)).collect();

    // Backward dataflow: iterate until fixed point.
    let n = blocks.len();
    let mut live_in: Vec<HashSet<VReg>> = vec![HashSet::new(); n];
    let mut live_out: Vec<HashSet<VReg>> = vec![HashSet::new(); n];

    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..n).rev() {
            // live_out[bi] = union of live_in[succ] for all successors
            let mut new_out = HashSet::new();
            for &si in &blocks[bi].successors {
                new_out.extend(&live_in[si]);
            }

            // live_in[bi] = gen[bi] ∪ (live_out[bi] - kill[bi])
            let (ref gen_set, ref kill_set) = gen_kill[bi];
            let mut new_in = gen_set.clone();
            for v in &new_out {
                if !kill_set.contains(v) {
                    new_in.insert(*v);
                }
            }

            if new_in != live_in[bi] || new_out != live_out[bi] {
                changed = true;
                live_in[bi] = new_in;
                live_out[bi] = new_out;
            }
        }
    }

    // Build per-VReg intervals by walking instructions.
    // For each VReg, track [first_def, last_use+1).
    // Extend through blocks where the VReg is live_in or live_out.
    let mut starts = vec![u32::MAX; vreg_count as usize];
    let mut ends = vec![0u32; vreg_count as usize];

    // First pass: mark instruction-level defs and uses.
    let mut ops = Vec::new();
    for (i, inst) in insts.iter().enumerate() {
        let i = i as u32;
        ops.clear();
        inst.reg_operands(&mut ops);
        for op in &ops {
            let v = op.vreg.0 as usize;
            match op.kind {
                OpKind::Def => {
                    starts[v] = starts[v].min(i);
                    ends[v] = ends[v].max(i + 1);
                }
                OpKind::Use => {
                    starts[v] = starts[v].min(i);
                    ends[v] = ends[v].max(i + 1);
                }
                OpKind::UseDef => {
                    starts[v] = starts[v].min(i);
                    ends[v] = ends[v].max(i + 1);
                }
            }
        }
    }

    // Second pass: extend ranges for VRegs live across block boundaries.
    for (bi, block) in blocks.iter().enumerate() {
        for v in &live_in[bi] {
            let idx = v.0 as usize;
            starts[idx] = starts[idx].min(block.start);
        }
        for v in &live_out[bi] {
            let idx = v.0 as usize;
            ends[idx] = ends[idx].max(block.end + 1);
        }
    }

    // Collect ranges for VRegs that were actually used.
    let mut ranges = Vec::new();
    for v in 0..vreg_count {
        let vi = v as usize;
        if starts[vi] != u32::MAX {
            ranges.push(LiveRange {
                vreg: VReg(v),
                start: starts[vi],
                end: ends[vi],
            });
        }
    }

    // Sort by start point (for linear scan).
    ranges.sort_by_key(|r| r.start);
    ranges
}
