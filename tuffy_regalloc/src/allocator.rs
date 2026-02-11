//! Linear scan register allocator.
//!
//! Currently implements a simple round-robin allocator that respects
//! fixed-register constraints. Will be replaced with a proper linear
//! scan implementation once liveness analysis is in place.

use crate::PReg;

/// Result of register allocation.
pub struct AllocResult {
    /// Maps VReg index → assigned PReg.
    pub assignments: Vec<PReg>,
    /// Number of spill slots used (currently always 0).
    pub spill_slots: u32,
}

/// Allocate physical registers for virtual registers.
///
/// `vreg_count`: total number of VRegs.
/// `constraints`: per-VReg fixed constraint (indexed by VReg.0).
/// `allocatable`: pool of physical registers the allocator may use.
pub fn allocate(
    vreg_count: u32,
    constraints: &[Option<PReg>],
    allocatable: &[PReg],
) -> AllocResult {
    let mut assignments = Vec::with_capacity(vreg_count as usize);
    let mut next = 0usize;

    for i in 0..vreg_count {
        if let Some(fixed) = constraints[i as usize] {
            assignments.push(fixed);
        } else {
            // Round-robin from the allocatable pool.
            assignments.push(allocatable[next % allocatable.len()]);
            next += 1;
        }
    }

    AllocResult {
        assignments,
        spill_slots: 0,
    }
}
