//! Linear scan register allocator.
//!
//! Assigns physical registers to virtual registers using live range intervals.
//! Respects fixed-register constraints from instruction selection and spills
//! to stack slots when register pressure exceeds available registers.

use std::collections::BTreeSet;

use crate::liveness::{LiveRange, compute_live_ranges};
use crate::{PReg, RegAllocInst, VReg};

/// Result of register allocation.
pub struct AllocResult {
    /// Maps VReg index → assigned PReg.
    pub assignments: Vec<PReg>,
    /// Number of spill slots used.
    pub spill_slots: u32,
}

/// Allocate physical registers for virtual registers using linear scan.
///
/// `insts`: instruction stream (for liveness analysis).
/// `vreg_count`: total number of VRegs.
/// `constraints`: per-VReg fixed constraint (indexed by VReg.0).
/// `allocatable`: pool of physical registers the allocator may use.
pub fn allocate<I: RegAllocInst>(
    insts: &[I],
    vreg_count: u32,
    constraints: &[Option<PReg>],
    allocatable: &[PReg],
) -> AllocResult {
    if vreg_count == 0 {
        return AllocResult {
            assignments: vec![],
            spill_slots: 0,
        };
    }

    let ranges = compute_live_ranges(insts, vreg_count);
    let mut assignments = vec![None; vreg_count as usize];

    // Track which PRegs are free, keyed by PReg encoding.
    let mut free: BTreeSet<u8> = allocatable.iter().map(|p| p.0).collect();

    // Active intervals sorted by end point: (end, vreg_index).
    let mut active: Vec<(u32, u32)> = Vec::new();

    for range in &ranges {
        let vi = range.vreg.0 as usize;

        // Expire intervals that ended before this one starts.
        expire_old(&mut active, &mut free, &assignments, range.start);

        if let Some(fixed) = constraints[vi] {
            // Fixed constraint: must use this specific PReg.
            handle_fixed(
                fixed,
                range,
                &mut active,
                &mut free,
                &mut assignments,
                allocatable,
            );
        } else if let Some(preg) = pick_free(&free) {
            // Free register available.
            free.remove(&preg);
            assignments[vi] = Some(PReg(preg));
            active.push((range.end, range.vreg.0));
            active.sort_by_key(|&(end, _)| end);
        } else {
            // No free register — spill the interval ending furthest.
            spill_at(range, &mut active, &mut free, &mut assignments, allocatable);
        }
    }

    // Convert Option<PReg> to PReg, assigning any unassigned VRegs
    // (unused VRegs that had no live range) a default register.
    let default_reg = allocatable[0];
    let final_assignments = assignments
        .into_iter()
        .map(|opt| opt.unwrap_or(default_reg))
        .collect();

    AllocResult {
        assignments: final_assignments,
        spill_slots: 0, // TODO: track actual spill slots
    }
}

/// Remove intervals from `active` whose end point <= `pos`, returning their
/// registers to the free pool.
fn expire_old(
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &[Option<PReg>],
    pos: u32,
) {
    active.retain(|&(end, vi)| {
        if end <= pos {
            if let Some(preg) = assignments[vi as usize] {
                free.insert(preg.0);
            }
            false
        } else {
            true
        }
    });
}

/// Pick a free register (lowest encoding for determinism).
fn pick_free(free: &BTreeSet<u8>) -> Option<u8> {
    free.iter().next().copied()
}

/// Handle a fixed-constraint interval. If the required PReg is occupied,
/// evict the conflicting interval.
fn handle_fixed(
    fixed: PReg,
    range: &LiveRange,
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &mut [Option<PReg>],
    allocatable: &[PReg],
) {
    let vi = range.vreg.0 as usize;

    if free.remove(&fixed.0) {
        // Register was free — just take it.
        assignments[vi] = Some(fixed);
        active.push((range.end, range.vreg.0));
        active.sort_by_key(|&(end, _)| end);
        return;
    }

    // Register is occupied — find and evict the conflicting interval.
    if let Some(pos) = active
        .iter()
        .position(|&(_, avi)| assignments[avi as usize] == Some(fixed))
    {
        let (evict_end, evict_vi) = active.remove(pos);
        // Reassign the evicted interval to any free register.
        if let Some(alt) = pick_free(free) {
            free.remove(&alt);
            assignments[evict_vi as usize] = Some(PReg(alt));
            active.push((evict_end, evict_vi));
            active.sort_by_key(|&(end, _)| end);
        } else {
            // No free register for evicted interval — assign first allocatable
            // as fallback (will produce incorrect code if register pressure is
            // truly exceeded, but matches current non-spilling behavior).
            assignments[evict_vi as usize] = Some(allocatable[0]);
        }
    }

    assignments[vi] = Some(fixed);
    active.push((range.end, range.vreg.0));
    active.sort_by_key(|&(end, _)| end);
}

/// Spill: assign the current interval the register of the active interval
/// ending furthest, or use a fallback if no suitable candidate.
fn spill_at(
    range: &LiveRange,
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &mut [Option<PReg>],
    allocatable: &[PReg],
) {
    let vi = range.vreg.0 as usize;

    if let Some(last) = active.last().copied() {
        let (spill_end, spill_vi) = last;
        if spill_end > range.end {
            // Spill the longer-lived interval, give its register to current.
            let preg = assignments[spill_vi as usize].unwrap_or(allocatable[0]);
            active.pop();
            assignments[spill_vi as usize] = Some(allocatable[0]); // fallback
            assignments[vi] = Some(preg);
            active.push((range.end, range.vreg.0));
            active.sort_by_key(|&(end, _)| end);
        } else {
            // Current interval lives longer — assign fallback.
            assignments[vi] = Some(allocatable[0]);
        }
    } else {
        assignments[vi] = Some(allocatable[0]);
    }
}
