//! Conservative dead-store elimination over private stack-slot slices.

use std::collections::HashMap;

use tuffy_ir::function::Function;
use tuffy_ir::instruction::{Op, Operand};
use tuffy_ir::value::ValueRef;

use crate::cfg::collect_block_refs;
use crate::peephole::PeepholeStats;

#[derive(Clone, Copy, PartialEq, Eq)]
/// Canonical pointer expression rooted at one stack slot.
struct PtrExpr {
    /// Root stack-slot value.
    root: ValueRef,
    /// Constant byte offset from the root.
    offset: i64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
/// One private stack-slot byte range.
struct PrivateAccess {
    /// Root stack-slot value.
    root: ValueRef,
    /// First byte offset.
    offset: i64,
    /// Access width in bytes.
    size: u32,
}

#[derive(Clone, Copy)]
/// Active store candidate that may be overwritten before any observation.
struct StoreCandidate {
    /// Store instruction index.
    inst_idx: u32,
    /// Memory input feeding the store.
    mem_in: ValueRef,
    /// Canonical byte range written by the store.
    access: PrivateAccess,
}

/// Eliminate overwritten private stores within straight-line block order.
pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    let mut replacements = HashMap::<u32, ValueRef>::new();

    for block in collect_block_refs(func) {
        let mut candidates = Vec::<StoreCandidate>::new();
        let inst_indices = func
            .block_insts_with_values(block)
            .map(|(value, _)| value.index())
            .collect::<Vec<_>>();

        for idx in inst_indices {
            let Some(inst) = func.inst_pool.get(idx).map(|node| &node.inst) else {
                continue;
            };
            match &inst.op {
                Op::Store(_, ptr, size, mem) => {
                    let Some(access) = private_access(func, &ptr.clone().raw(), *size) else {
                        candidates.clear();
                        continue;
                    };
                    let mut next = Vec::with_capacity(candidates.len() + 1);
                    for candidate in candidates {
                        if candidate.access.root != access.root
                            || !ranges_overlap(candidate.access, access)
                        {
                            next.push(candidate);
                            continue;
                        }
                        if range_covers(access, candidate.access) {
                            replacements.insert(candidate.inst_idx, candidate.mem_in);
                        }
                    }
                    next.push(StoreCandidate {
                        inst_idx: idx,
                        mem_in: mem.clone().raw().value,
                        access,
                    });
                    candidates = next;
                }
                Op::Load(ptr, size, _) => invalidate_candidates(
                    &mut candidates,
                    private_access(func, &ptr.clone().raw(), *size),
                ),
                Op::MemCopy(..)
                | Op::MemMove(..)
                | Op::MemSet(..)
                | Op::LoadAtomic(..)
                | Op::StoreAtomic(..)
                | Op::AtomicRmw(..)
                | Op::AtomicCmpXchg(..)
                | Op::Fence(..)
                | Op::Call(..)
                | Op::Ret(..)
                | Op::Br(..)
                | Op::BrIf(..)
                | Op::Continue(..)
                | Op::RegionYield(..)
                | Op::Unreachable
                | Op::Trap
                | Op::LandingPad => candidates.clear(),
                _ => {}
            }
        }
    }

    if replacements.is_empty() {
        return PeepholeStats::default();
    }

    let mut stats = PeepholeStats::default();
    let mut dead_stores = replacements.keys().copied().collect::<Vec<_>>();
    dead_stores.sort_unstable();
    for idx in dead_stores {
        let replacement = resolve_replacement(&replacements, replacements[&idx]);
        func.replace_all_uses(ValueRef::inst_result(idx), replacement);
        if func.remove_inst(idx).is_some() {
            stats.record("dse_remove_dead_store");
            stats.eliminated_stores += 1;
        }
    }
    stats
}

/// Invalidate all candidates observed by one later memory access.
fn invalidate_candidates(candidates: &mut Vec<StoreCandidate>, access: Option<PrivateAccess>) {
    match access {
        Some(access) => candidates.retain(|candidate| {
            candidate.access.root != access.root || !ranges_overlap(candidate.access, access)
        }),
        None => candidates.clear(),
    }
}

/// Resolve chained dead-store replacements to the final live mem token.
fn resolve_replacement(replacements: &HashMap<u32, ValueRef>, mut value: ValueRef) -> ValueRef {
    while !value.is_block_arg() && !value.is_secondary_result() {
        let Some(&next) = replacements.get(&value.index()) else {
            break;
        };
        value = next;
    }
    value
}

/// Canonicalize one private stack-slot pointer access.
fn private_access(func: &Function, operand: &Operand, size: u32) -> Option<PrivateAccess> {
    let ptr = private_ptr_expr(func, operand.value)?;
    let slot_size = stack_slot_size(func, ptr.root)?;
    let end = ptr.offset.checked_add(i64::from(size))?;
    if ptr.offset < 0 || end > i64::from(slot_size) {
        return None;
    }
    Some(PrivateAccess {
        root: ptr.root,
        offset: ptr.offset,
        size,
    })
}

/// Canonicalize stack-slot plus constant-offset `ptradd` chains.
fn private_ptr_expr(func: &Function, value: ValueRef) -> Option<PtrExpr> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::StackSlot(_, _) => Some(PtrExpr {
            root: value,
            offset: 0,
        }),
        Op::PtrAdd(base, offset) => {
            let delta = const_i64(func, offset.clone().raw().value)?;
            let mut base_expr = private_ptr_expr(func, base.clone().raw().value)?;
            base_expr.offset += delta;
            Some(base_expr)
        }
        _ => None,
    }
}

/// Return the stack-slot size for one root value.
fn stack_slot_size(func: &Function, value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::StackSlot(bytes, _) => Some(*bytes),
        _ => None,
    }
}

/// Return the exact `i64` value for one integer constant.
fn const_i64(func: &Function, value: ValueRef) -> Option<i64> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let Op::Const(int) = &func.inst(value.index()).op else {
        return None;
    };
    int.to_string().parse().ok()
}

/// Return whether two private byte ranges overlap.
fn ranges_overlap(lhs: PrivateAccess, rhs: PrivateAccess) -> bool {
    let lhs_end = lhs.offset + i64::from(lhs.size);
    let rhs_end = rhs.offset + i64::from(rhs.size);
    lhs.offset < rhs_end && rhs.offset < lhs_end
}

/// Return whether `lhs` fully overwrites `rhs`.
fn range_covers(lhs: PrivateAccess, rhs: PrivateAccess) -> bool {
    lhs.offset <= rhs.offset && lhs.offset + i64::from(lhs.size) >= rhs.offset + i64::from(rhs.size)
}
