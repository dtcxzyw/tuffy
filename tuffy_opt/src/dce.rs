//! Dead-code elimination for unused pure instruction results.

use std::collections::VecDeque;

use tuffy_ir::function::Function;
use tuffy_ir::instruction::Op;
use tuffy_ir::value::ValueRef;

use crate::peephole::PeepholeStats;

/// Eliminate dead pure instruction chains within one function.
pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    let mut worklist = func
        .inst_pool
        .iter_insts()
        .map(|(idx, _)| idx)
        .collect::<VecDeque<_>>();
    let mut stats = PeepholeStats::default();

    while let Some(idx) = worklist.pop_front() {
        let Some((has_secondary_result, operands)) = dead_inst_operands(func, idx) else {
            continue;
        };
        if !instruction_results_unused(func, idx, has_secondary_result) {
            continue;
        }

        if func.remove_inst(idx).is_none() {
            continue;
        }
        stats.record("dce_remove_dead_inst");

        for operand in operands {
            if operand.is_block_arg() {
                continue;
            }
            worklist.push_back(operand.inst_index());
        }
    }

    stats
}

/// Return the removable dead instruction's secondary-result flag plus its operands.
fn dead_inst_operands(func: &Function, idx: u32) -> Option<(bool, Vec<ValueRef>)> {
    let node = func.inst_pool.get(idx)?;
    if !is_dead_inst_removable(&node.inst.op) {
        return None;
    }
    Some((
        node.inst.secondary_ty.is_some(),
        node.inst
            .op
            .value_refs_with_indices()
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
    ))
}

/// Return whether both results of `idx` are unused.
fn instruction_results_unused(func: &Function, idx: u32, has_secondary_result: bool) -> bool {
    if func.has_uses(ValueRef::inst_result(idx)) {
        return false;
    }
    if has_secondary_result && func.has_uses(ValueRef::inst_secondary_result(idx)) {
        return false;
    }
    true
}

/// Return whether a dead instruction can be erased without observable effects.
fn is_dead_inst_removable(op: &Op) -> bool {
    !matches!(
        op,
        Op::Param(_)
            | Op::Load(..)
            | Op::Store(..)
            | Op::StackSlot(..)
            | Op::MemCopy(..)
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
            | Op::LandingPad
    )
}
