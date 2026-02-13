//! Linear scan register allocator.
//!
//! Assigns physical registers to virtual registers using live range intervals.
//! Respects fixed-register constraints from instruction selection and spills
//! to stack slots when register pressure exceeds available registers.
//! Handles call clobbers: values live across calls are assigned to
//! callee-saved registers only.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::liveness::{LiveRange, compute_live_ranges};
use crate::{PReg, RegAllocInst};

/// Result of register allocation.
pub struct AllocResult {
    /// Maps VReg index → assigned PReg.
    pub assignments: Vec<PReg>,
    /// Number of spill slots used.
    pub spill_slots: u32,
    /// Callee-saved registers that were actually assigned to live ranges.
    /// The caller must save/restore these in the prologue/epilogue.
    pub used_callee_saved: Vec<PReg>,
    /// VRegs that were spilled to stack slots.
    /// Maps VReg index → spill slot number (0-based).
    pub spill_map: HashMap<u32, u32>,
}

/// Allocate physical registers for virtual registers using linear scan.
///
/// `insts`: instruction stream (for liveness analysis).
/// `vreg_count`: total number of VRegs.
/// `constraints`: per-VReg fixed constraint (indexed by VReg.0).
/// `allocatable`: pool of physical registers the allocator may use.
/// `callee_saved`: subset of `allocatable` that are callee-saved (must be
///   preserved across calls). The allocator prefers these for ranges spanning
///   calls and reports which ones were actually used.
/// `spill_reg`: physical register reserved for spill loads/stores (must NOT
///   be in `allocatable`).
pub fn allocate<I: RegAllocInst>(
    insts: &[I],
    vreg_count: u32,
    constraints: &[Option<PReg>],
    allocatable: &[PReg],
    callee_saved: &[PReg],
    spill_reg: PReg,
) -> AllocResult {
    if vreg_count == 0 {
        return AllocResult {
            assignments: vec![],
            spill_slots: 0,
            used_callee_saved: vec![],
            spill_map: HashMap::new(),
        };
    }

    let ranges = compute_live_ranges(insts, vreg_count);

    let mut assignments = vec![None; vreg_count as usize];
    let mut spill_map: HashMap<u32, u32> = HashMap::new();
    let mut spill_slot_count: u32 = 0;

    // Collect call positions from the instruction stream.
    let mut call_positions: Vec<u32> = Vec::new();
    {
        let mut clobber_buf = Vec::new();
        for (i, inst) in insts.iter().enumerate() {
            clobber_buf.clear();
            inst.clobbers(&mut clobber_buf);
            if !clobber_buf.is_empty() {
                call_positions.push(i as u32);
            }
        }
    }

    // Build callee-saved and caller-saved sets from the explicit parameter.
    let callee_saved_set: HashSet<u8> = callee_saved.iter().map(|p| p.0).collect();
    let caller_saved_set: HashSet<u8> = allocatable
        .iter()
        .map(|p| p.0)
        .filter(|p| !callee_saved_set.contains(p))
        .collect();

    // Track which PRegs are free, keyed by PReg encoding.
    let mut free: BTreeSet<u8> = allocatable.iter().map(|p| p.0).collect();
    let alloc_set: HashSet<u8> = allocatable.iter().map(|p| p.0).collect();

    // Active intervals sorted by end point: (end, vreg_index).
    let mut active: Vec<(u32, u32)> = Vec::new();

    for range in &ranges {
        let vi = range.vreg.0 as usize;

        // Expire intervals that ended before this one starts.
        expire_old(
            &mut active,
            &mut free,
            &assignments,
            range.start,
            &alloc_set,
        );

        if let Some(fixed) = constraints[vi] {
            if !alloc_set.contains(&fixed.0) {
                // Non-allocatable fixed register (e.g. RBP): assign directly.
                // These don't compete for allocatable registers and multiple
                // VRegs can share the same non-allocatable register.
                assignments[vi] = Some(fixed);
            } else {
                // Allocatable fixed constraint: must use this specific PReg.
                handle_fixed(
                    fixed,
                    range,
                    &mut active,
                    &mut free,
                    &mut assignments,
                    allocatable,
                    &ranges,
                    &call_positions,
                    &caller_saved_set,
                    constraints,
                    spill_reg,
                    &mut spill_map,
                    &mut spill_slot_count,
                );
            }
        } else {
            // Check if this range spans any call instruction.
            let spans_call = spans_any_call(range, &call_positions);

            // Build set of registers that would conflict with future fixed constraints.
            let mut future_conflict: HashSet<u8> = HashSet::new();
            for r in &ranges {
                let ri = r.vreg.0 as usize;
                if assignments[ri].is_none()
                    && ri < constraints.len()
                    && r.start < range.end
                    && r.end > range.start
                    && let Some(c) = constraints[ri]
                {
                    future_conflict.insert(c.0);
                }
            }

            // Pick a free register, avoiding future fixed-constraint conflicts:
            // - If spanning a call, prefer callee-saved (avoid clobbered).
            // - Otherwise, prefer caller-saved (pick from clobbered first).
            let safe_free: BTreeSet<u8> = free
                .iter()
                .copied()
                .filter(|r| !future_conflict.contains(r))
                .collect();

            let picked = if spans_call {
                pick_free_avoiding(&safe_free, &caller_saved_set)
                    .or_else(|| pick_free_avoiding(&free, &caller_saved_set))
                    .or_else(|| {
                        evict_callee_saved_for_call(
                            &mut active,
                            &mut free,
                            &mut assignments,
                            &ranges,
                            &call_positions,
                            &callee_saved_set,
                            &caller_saved_set,
                        )
                    })
            } else {
                pick_free_preferring(&safe_free, &caller_saved_set)
                    .or_else(|| pick_free(&safe_free))
                    .or_else(|| pick_free_preferring(&free, &caller_saved_set))
                    .or_else(|| pick_free(&free))
            };

            if let Some(preg) = picked {
                free.remove(&preg);
                assignments[vi] = Some(PReg(preg));
                active.push((range.end, range.vreg.0));
                active.sort_by_key(|&(end, _)| end);
            } else {
                // No free register — spill.
                spill_at(
                    range,
                    &mut active,
                    &mut free,
                    &mut assignments,
                    allocatable,
                    &ranges,
                    constraints,
                    spill_reg,
                    &mut spill_map,
                    &mut spill_slot_count,
                );
            }
        }
    }

    // Post-allocation fixup: detect remaining conflicts caused by cascading
    // evictions in handle_fixed and spill the longer-lived vreg in each pair.
    let alloc_set: HashSet<u8> = allocatable.iter().map(|p| p.0).collect();
    loop {
        let mut spilled_any = false;
        for i in 0..ranges.len() {
            let r1 = &ranges[i];
            if spill_map.contains_key(&r1.vreg.0) {
                continue;
            }
            let p1 = match assignments[r1.vreg.0 as usize] {
                Some(p) => p,
                None => continue,
            };
            if !alloc_set.contains(&p1.0) {
                continue;
            }
            for r2 in ranges.iter().skip(i + 1) {
                if spill_map.contains_key(&r2.vreg.0) {
                    continue;
                }
                let p2 = match assignments[r2.vreg.0 as usize] {
                    Some(p) => p,
                    None => continue,
                };
                if p1 != p2 || r1.start >= r2.end || r2.start >= r1.end {
                    continue;
                }
                // Conflict found — spill the longer-lived vreg.
                let spill_vreg = if (r1.end - r1.start) >= (r2.end - r2.start) {
                    r1.vreg.0
                } else {
                    r2.vreg.0
                };
                let slot = spill_slot_count;
                spill_slot_count += 1;
                spill_map.insert(spill_vreg, slot);
                assignments[spill_vreg as usize] = Some(spill_reg);
                spilled_any = true;
                break;
            }
            if spilled_any {
                break;
            }
        }
        if !spilled_any {
            break;
        }
    }

    // Convert Option<PReg> to PReg, assigning any unassigned VRegs
    // (unused VRegs that had no live range) a default register.
    // Spilled VRegs get the spill_reg so the backend can detect them.
    let default_reg = allocatable[0];
    let final_assignments: Vec<PReg> = assignments
        .into_iter()
        .enumerate()
        .map(|(i, opt)| {
            if spill_map.contains_key(&(i as u32)) {
                spill_reg
            } else {
                opt.unwrap_or(default_reg)
            }
        })
        .collect();

    // Determine which callee-saved registers (those in allocatable but not
    // clobbered by calls) were actually assigned to any live range.
    let mut used_callee_saved = Vec::new();
    let assigned_pregs: HashSet<u8> = final_assignments.iter().map(|p| p.0).collect();
    for &p in allocatable {
        if callee_saved_set.contains(&p.0) && assigned_pregs.contains(&p.0) {
            // Verify it's actually used by a vreg with a real live range.
            let actually_used = ranges.iter().any(|r| {
                !spill_map.contains_key(&r.vreg.0) && final_assignments[r.vreg.0 as usize].0 == p.0
            });
            if actually_used {
                used_callee_saved.push(p);
            }
        }
    }

    AllocResult {
        assignments: final_assignments,
        spill_slots: spill_slot_count,
        used_callee_saved,
        spill_map,
    }
}

/// Check whether a live range spans any call instruction position.
fn spans_any_call(range: &LiveRange, call_positions: &[u32]) -> bool {
    // A range [start, end) spans a call at position p if start <= p < end.
    call_positions
        .iter()
        .any(|&p| range.start <= p && p < range.end)
}

/// Remove intervals from `active` whose end point <= `pos`, returning their
/// registers to the free pool (only if the register is allocatable).
fn expire_old(
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &[Option<PReg>],
    pos: u32,
    alloc_set: &HashSet<u8>,
) {
    active.retain(|&(end, vi)| {
        if end <= pos {
            if let Some(preg) = assignments[vi as usize]
                && alloc_set.contains(&preg.0)
            {
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

/// Pick a free register that is NOT in the clobbered set (i.e. callee-saved).
fn pick_free_avoiding(free: &BTreeSet<u8>, avoid: &HashSet<u8>) -> Option<u8> {
    free.iter().copied().find(|r| !avoid.contains(r))
}

/// Pick a free register that IS in the preferred set (i.e. caller-saved).
/// Falls back to any free register if none in the preferred set are available.
fn pick_free_preferring(free: &BTreeSet<u8>, prefer: &HashSet<u8>) -> Option<u8> {
    free.iter().copied().find(|r| prefer.contains(r))
}

/// Check whether `candidate` PReg conflicts with any interval that overlaps
/// the range [start, end). An interval conflicts if:
/// 1. It has already been assigned `candidate` and its range overlaps, OR
/// 2. It has a fixed constraint to `candidate`, hasn't been assigned yet,
///    and its range overlaps (future fixed-constraint conflict).
fn conflicts_with(
    candidate: u8,
    start: u32,
    end: u32,
    assignments: &[Option<PReg>],
    ranges: &[LiveRange],
    constraints: &[Option<PReg>],
) -> bool {
    for r in ranges {
        let ri = r.vreg.0 as usize;
        if r.start < end && r.end > start {
            // Already assigned to candidate?
            if let Some(preg) = assignments[ri]
                && preg.0 == candidate
            {
                return true;
            }
            // Future fixed constraint to candidate?
            if assignments[ri].is_none()
                && ri < constraints.len()
                && constraints[ri] == Some(PReg(candidate))
            {
                return true;
            }
        }
    }
    false
}

/// Handle a fixed-constraint interval. If the required PReg is occupied,
/// evict the conflicting interval and reassign it to a safe register.
#[allow(clippy::too_many_arguments)]
fn handle_fixed(
    fixed: PReg,
    range: &LiveRange,
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &mut [Option<PReg>],
    allocatable: &[PReg],
    ranges: &[LiveRange],
    call_positions: &[u32],
    caller_saved_set: &HashSet<u8>,
    constraints: &[Option<PReg>],
    spill_reg: PReg,
    spill_map: &mut HashMap<u32, u32>,
    spill_slot_count: &mut u32,
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
        let evict_range = ranges
            .iter()
            .find(|r| r.vreg.0 == evict_vi)
            .expect("evicted vreg must have a range");

        let evict_spans_call = spans_any_call(evict_range, call_positions);

        // Find a conflict-free register for the evicted interval.
        let mut reassigned = false;

        // 1. Try free registers (respecting call-safety).
        let candidates: Vec<u8> = free.iter().copied().collect();
        for candidate in candidates {
            if evict_spans_call && caller_saved_set.contains(&candidate) {
                continue;
            }
            if !conflicts_with(
                candidate,
                evict_range.start,
                evict_range.end,
                assignments,
                ranges,
                constraints,
            ) {
                free.remove(&candidate);
                assignments[evict_vi as usize] = Some(PReg(candidate));
                active.push((evict_end, evict_vi));
                active.sort_by_key(|&(end, _)| end);
                reassigned = true;
                break;
            }
        }

        // 2. Try free registers without call-safety restriction.
        if !reassigned && evict_spans_call {
            let candidates: Vec<u8> = free.iter().copied().collect();
            for candidate in candidates {
                if !conflicts_with(
                    candidate,
                    evict_range.start,
                    evict_range.end,
                    assignments,
                    ranges,
                    constraints,
                ) {
                    free.remove(&candidate);
                    assignments[evict_vi as usize] = Some(PReg(candidate));
                    active.push((evict_end, evict_vi));
                    active.sort_by_key(|&(end, _)| end);
                    reassigned = true;
                    break;
                }
            }
        }

        // 3. Try ALL allocatable registers (including occupied ones).
        if !reassigned {
            for &p in allocatable {
                if p == fixed {
                    continue;
                }
                if !conflicts_with(
                    p.0,
                    evict_range.start,
                    evict_range.end,
                    assignments,
                    ranges,
                    constraints,
                ) {
                    free.remove(&p.0);
                    assignments[evict_vi as usize] = Some(p);
                    active.push((evict_end, evict_vi));
                    active.sort_by_key(|&(end, _)| end);
                    reassigned = true;
                    break;
                }
            }
        }

        if !reassigned {
            // No register available — spill the evicted vreg to a stack slot.
            let slot = *spill_slot_count;
            *spill_slot_count += 1;
            spill_map.insert(evict_vi, slot);
            assignments[evict_vi as usize] = Some(spill_reg);
            // Don't add back to active — spilled vregs live on the stack.
        }
    }

    assignments[vi] = Some(fixed);
    active.push((range.end, range.vreg.0));
    active.sort_by_key(|&(end, _)| end);
}

/// Try to free a callee-saved register for a call-spanning range by evicting
/// an active interval that does NOT span a call. The evicted interval is
/// reassigned to a free caller-saved register (safe because it doesn't cross
/// a call boundary). Returns the freed callee-saved register encoding.
#[allow(clippy::too_many_arguments)]
fn evict_callee_saved_for_call(
    active: &mut Vec<(u32, u32)>,
    free: &mut BTreeSet<u8>,
    assignments: &mut [Option<PReg>],
    ranges: &[LiveRange],
    call_positions: &[u32],
    callee_saved_set: &HashSet<u8>,
    caller_saved_set: &HashSet<u8>,
) -> Option<u8> {
    // Find a free caller-saved register to give to the evicted interval.
    let caller_reg = free
        .iter()
        .copied()
        .find(|r| caller_saved_set.contains(r))?;

    // Find an active interval on a callee-saved register that doesn't span a call.
    let mut best: Option<(usize, u8)> = None;
    for (idx, &(_, avi)) in active.iter().enumerate() {
        let preg = assignments[avi as usize]?;
        if !callee_saved_set.contains(&preg.0) {
            continue;
        }
        let evict_range = ranges.iter().find(|r| r.vreg.0 == avi)?;
        if spans_any_call(evict_range, call_positions) {
            continue;
        }
        best = Some((idx, preg.0));
        break;
    }

    let (idx, callee_reg) = best?;
    let (evict_end, evict_vi) = active.remove(idx);

    // Move the evicted interval to the caller-saved register.
    free.remove(&caller_reg);
    assignments[evict_vi as usize] = Some(PReg(caller_reg));
    active.push((evict_end, evict_vi));
    active.sort_by_key(|&(end, _)| end);

    // The callee-saved register is now available.
    Some(callee_reg)
}

/// Spill: when no free register is available, try to reuse a register
/// from a non-overlapping interval. If truly no register works, spill
/// to a stack slot.
#[allow(clippy::too_many_arguments)]
fn spill_at(
    range: &LiveRange,
    active: &mut Vec<(u32, u32)>,
    _free: &mut BTreeSet<u8>,
    assignments: &mut [Option<PReg>],
    allocatable: &[PReg],
    ranges: &[LiveRange],
    constraints: &[Option<PReg>],
    spill_reg: PReg,
    spill_map: &mut HashMap<u32, u32>,
    spill_slot_count: &mut u32,
) {
    let vi = range.vreg.0 as usize;

    // Try to find ANY allocatable register that doesn't conflict with
    // the current interval's range.
    for &p in allocatable {
        if !conflicts_with(
            p.0,
            range.start,
            range.end,
            assignments,
            ranges,
            constraints,
        ) {
            assignments[vi] = Some(p);
            active.push((range.end, range.vreg.0));
            active.sort_by_key(|&(end, _)| end);
            return;
        }
    }

    // All registers conflict — spill this vreg to a stack slot.
    // The spill_reg will be used as a temporary for loads/stores.
    let slot = *spill_slot_count;
    *spill_slot_count += 1;
    spill_map.insert(range.vreg.0, slot);
    assignments[vi] = Some(spill_reg);
    // Don't add to active — spilled vregs live on the stack, not in registers.
}
