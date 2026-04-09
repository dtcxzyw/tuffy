use std::collections::BTreeSet;

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{Instruction, Op, Operand, Origin};
use tuffy_ir::module::{Module, SymbolId};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use crate::cfg::collect_block_refs;
use crate::peephole::PeepholeStats;

#[derive(Clone, Copy, PartialEq, Eq)]
struct PtrExpr {
    root: ValueRef,
    offset: i64,
}

#[derive(Clone)]
struct MemcpyCall {
    call_idx: u32,
    mem_in: ValueRef,
    mem_out: ValueRef,
    dst: Operand,
    src: Operand,
    size: u32,
    matched: BTreeSet<u32>,
}

#[derive(Clone)]
struct MemmoveOp {
    inst_idx: u32,
    mem_in: ValueRef,
    mem_out: ValueRef,
    dst: Operand,
    src: Operand,
    size: u32,
    matched: BTreeSet<u32>,
}

#[derive(Clone)]
struct PreludeStore {
    store_idx: u32,
    mem_in: ValueRef,
    matched: BTreeSet<u32>,
}

#[derive(Clone)]
struct SwapCandidate {
    size: u32,
    left_ptr: Operand,
    right_ptr: Operand,
    initial_mem: ValueRef,
    final_mem: ValueRef,
    first_call_idx: u32,
    memmove_idx: u32,
    second_call_idx: u32,
    prelude_store_idx: Option<u32>,
    matched: BTreeSet<u32>,
}

pub(crate) fn optimize_module(
    module: &mut Module,
    changed_functions: Option<&[bool]>,
) -> PeepholeStats {
    let mut stats = PeepholeStats::default();

    for (idx, func) in module.functions.iter_mut().enumerate() {
        if changed_functions.is_some_and(|flags| !flags[idx]) {
            continue;
        }
        while let Some(candidate) = find_candidate(func, &module.symbols) {
            apply_candidate(func, candidate);
            stats.record("form_scalar_swap");
        }
    }

    stats
}

fn find_candidate(
    func: &Function,
    symbols: &tuffy_ir::module::SymbolTable,
) -> Option<SwapCandidate> {
    for block in collect_block_refs(func) {
        let insts = func
            .block_insts_with_values(block)
            .map(|(value, _)| value.index())
            .collect::<Vec<_>>();

        for &inst_idx in &insts {
            let Some(first_call) = parse_memcpy_call(func, inst_idx, symbols) else {
                continue;
            };
            let Some(temp_expr) = ptr_expr(func, &first_call.dst, &mut BTreeSet::new()) else {
                continue;
            };
            if temp_expr.offset != 0
                || stack_slot_size(func, temp_expr.root) != Some(first_call.size)
            {
                continue;
            }
            if first_call_secondary_used(func, &first_call) {
                continue;
            }

            let prelude_store =
                parse_prelude_store(func, temp_expr.root, first_call.mem_in, first_call.size);
            let base_mem = prelude_store
                .as_ref()
                .map(|store| store.mem_in)
                .unwrap_or(first_call.mem_in);

            let Some(memmove_idx) = sole_mem_user(func, first_call.mem_out) else {
                continue;
            };
            let Some(memmove) = parse_memmove_op(func, memmove_idx) else {
                continue;
            };
            if memmove.size != first_call.size || memmove.mem_in != first_call.mem_out {
                continue;
            }
            if memmove.dst.value != first_call.src.value {
                continue;
            }

            let Some(second_call_idx) = sole_mem_user(func, memmove.mem_out) else {
                continue;
            };
            let Some(second_call) = parse_memcpy_call(func, second_call_idx, symbols) else {
                continue;
            };
            if second_call.size != first_call.size || second_call.mem_in != memmove.mem_out {
                continue;
            }
            if second_call.dst.value != memmove.src.value
                || second_call.src.value != first_call.dst.value
            {
                continue;
            }
            if first_call.size != 4 && first_call.size != 8 {
                continue;
            }
            if second_call_secondary_used(func, &second_call) {
                continue;
            }
            if !temp_root_uses_are_local(
                func,
                temp_expr.root,
                prelude_store.as_ref().map(|store| store.store_idx),
                first_call.call_idx,
                second_call.call_idx,
            ) {
                continue;
            }

            let mut matched = first_call.matched.clone();
            matched.extend(memmove.matched.iter().copied());
            matched.extend(second_call.matched.iter().copied());
            if let Some(store) = &prelude_store {
                matched.extend(store.matched.iter().copied());
            }

            return Some(SwapCandidate {
                size: first_call.size,
                left_ptr: first_call.src.clone(),
                right_ptr: memmove.src.clone(),
                initial_mem: base_mem,
                final_mem: second_call.mem_out,
                first_call_idx: first_call.call_idx,
                memmove_idx: memmove.inst_idx,
                second_call_idx: second_call.call_idx,
                prelude_store_idx: prelude_store.as_ref().map(|store| store.store_idx),
                matched,
            });
        }
    }

    None
}

fn apply_candidate(func: &mut Function, candidate: SwapCandidate) {
    let origin = merged_origin(func, candidate.first_call_idx, &candidate.matched);
    let tmp_load_idx = func.insert_inst_before(
        candidate.first_call_idx,
        Instruction {
            op: Op::Load(
                candidate.left_ptr.clone().into(),
                candidate.size,
                candidate.initial_mem.into(),
            ),
            ty: Type::Int,
            secondary_ty: None,
            origin: origin.clone(),
            result_annotation: Some(int_annotation(candidate.size)),
            secondary_result_annotation: None,
        },
    );
    let right_load_idx = func.insert_inst_before(
        candidate.first_call_idx,
        Instruction {
            op: Op::Load(
                candidate.right_ptr.clone().into(),
                candidate.size,
                candidate.initial_mem.into(),
            ),
            ty: Type::Int,
            secondary_ty: None,
            origin: origin.clone(),
            result_annotation: Some(int_annotation(candidate.size)),
            secondary_result_annotation: None,
        },
    );
    let left_store_idx = func.insert_inst_before(
        candidate.first_call_idx,
        Instruction {
            op: Op::Store(
                Operand::new(ValueRef::inst_result(right_load_idx)),
                candidate.left_ptr.clone().into(),
                candidate.size,
                candidate.initial_mem.into(),
            ),
            ty: Type::Mem,
            secondary_ty: None,
            origin: origin.clone(),
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );
    let right_store_idx = func.insert_inst_before(
        candidate.first_call_idx,
        Instruction {
            op: Op::Store(
                Operand::new(ValueRef::inst_result(tmp_load_idx)),
                candidate.right_ptr.clone().into(),
                candidate.size,
                ValueRef::inst_result(left_store_idx).into(),
            ),
            ty: Type::Mem,
            secondary_ty: None,
            origin,
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );

    func.replace_all_uses(candidate.final_mem, ValueRef::inst_result(right_store_idx));

    let _ = func.remove_inst(candidate.second_call_idx);
    let _ = func.remove_inst(candidate.memmove_idx);
    let _ = func.remove_inst(candidate.first_call_idx);
    if let Some(store_idx) = candidate.prelude_store_idx {
        let _ = func.remove_inst(store_idx);
    }

    cleanup_dead_instructions(func, &candidate.matched);
    func.rebuild_use_lists();
}

fn parse_prelude_store(
    func: &Function,
    temp_root: ValueRef,
    mem_out: ValueRef,
    size: u32,
) -> Option<PreludeStore> {
    let store_idx = mem_out.index();
    let node = func.inst_pool.get(store_idx)?;
    let Op::Store(_, ptr, store_size, mem) = &node.inst.op else {
        return None;
    };
    if *store_size != size {
        return None;
    }
    let mut matched = BTreeSet::from([store_idx]);
    let ptr = ptr_expr(func, &ptr.clone().raw(), &mut matched)?;
    if ptr.root != temp_root || ptr.offset != 0 || ValueRef::inst_result(store_idx) != mem_out {
        return None;
    }
    if func.use_count(ValueRef::inst_result(store_idx)) != 1 {
        return None;
    }
    Some(PreludeStore {
        store_idx,
        mem_in: mem.clone().raw().value,
        matched,
    })
}

fn parse_memcpy_call(
    func: &Function,
    inst_idx: u32,
    symbols: &tuffy_ir::module::SymbolTable,
) -> Option<MemcpyCall> {
    let node = func.inst_pool.get(inst_idx)?;
    let Op::Call(callee, args, mem, cleanup_label) = &node.inst.op else {
        return None;
    };
    if cleanup_label.is_some() || args.len() != 3 || node.inst.secondary_ty.is_none() {
        return None;
    }
    let callee_operand = callee.clone().raw();
    let sym = direct_call_symbol(func, callee_operand.value)?;
    if symbols.resolve(sym) != "memcpy" {
        return None;
    }
    let size = const_u32(func, args[2].value)?;
    let mut matched = BTreeSet::from([inst_idx]);
    matched.insert(callee_operand.value.index());
    if !args[2].value.is_block_arg() && !args[2].value.is_secondary_result() {
        matched.insert(args[2].value.index());
    }
    let _ = ptr_expr(func, &args[0], &mut matched)?;
    let _ = ptr_expr(func, &args[1], &mut matched)?;
    Some(MemcpyCall {
        call_idx: inst_idx,
        mem_in: mem.clone().raw().value,
        mem_out: ValueRef::inst_result(inst_idx),
        dst: args[0].clone(),
        src: args[1].clone(),
        size,
        matched,
    })
}

fn parse_memmove_op(func: &Function, inst_idx: u32) -> Option<MemmoveOp> {
    let node = func.inst_pool.get(inst_idx)?;
    let Op::MemMove(dst, src, count, mem) = &node.inst.op else {
        return None;
    };
    let count_operand = count.clone().raw();
    let size = const_u32(func, count_operand.value)?;
    let mut matched = BTreeSet::from([inst_idx]);
    if !count_operand.value.is_block_arg() && !count_operand.value.is_secondary_result() {
        matched.insert(count_operand.value.index());
    }
    let _ = ptr_expr(func, &dst.clone().raw(), &mut matched)?;
    let _ = ptr_expr(func, &src.clone().raw(), &mut matched)?;
    Some(MemmoveOp {
        inst_idx,
        mem_in: mem.clone().raw().value,
        mem_out: ValueRef::inst_result(inst_idx),
        dst: dst.clone().raw(),
        src: src.clone().raw(),
        size,
        matched,
    })
}

fn ptr_expr(func: &Function, operand: &Operand, matched: &mut BTreeSet<u32>) -> Option<PtrExpr> {
    let value = operand.value;
    if value.is_secondary_result() {
        return None;
    }
    if value.is_block_arg() {
        return Some(PtrExpr {
            root: value,
            offset: 0,
        });
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::PtrAdd(base, offset) => {
            matched.insert(value.index());
            let offset_value = offset.clone().raw().value;
            if !offset_value.is_block_arg() && !offset_value.is_secondary_result() {
                matched.insert(offset_value.index());
            }
            let delta = const_i64(func, offset_value)?;
            let mut base_expr = ptr_expr(func, &base.clone().raw(), matched)?;
            base_expr.offset += delta;
            Some(base_expr)
        }
        Op::StackSlot(_, _) | Op::SymbolAddr(_) => {
            matched.insert(value.index());
            Some(PtrExpr {
                root: value,
                offset: 0,
            })
        }
        _ if matches!(func.value_type(value), Some(Type::Ptr(_))) => Some(PtrExpr {
            root: value,
            offset: 0,
        }),
        _ => None,
    }
}

fn direct_call_symbol(func: &Function, value: ValueRef) -> Option<SymbolId> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::SymbolAddr(sym) => Some(*sym),
        _ => None,
    }
}

fn stack_slot_size(func: &Function, value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::StackSlot(bytes, _) => Some(*bytes),
        _ => None,
    }
}

fn first_call_secondary_used(func: &Function, call: &MemcpyCall) -> bool {
    func.has_uses(ValueRef::inst_secondary_result(call.call_idx))
}

fn second_call_secondary_used(func: &Function, call: &MemcpyCall) -> bool {
    func.has_uses(ValueRef::inst_secondary_result(call.call_idx))
}

fn temp_root_uses_are_local(
    func: &Function,
    temp_root: ValueRef,
    prelude_store_idx: Option<u32>,
    first_call_idx: u32,
    second_call_idx: u32,
) -> bool {
    func.uses_of(temp_root).all(|use_node| {
        Some(use_node.user) == prelude_store_idx
            || use_node.user == first_call_idx
            || use_node.user == second_call_idx
    })
}

fn sole_mem_user(func: &Function, value: ValueRef) -> Option<u32> {
    let mut users = func.uses_of(value).map(|use_node| use_node.user);
    let first = users.next()?;
    users.next().is_none().then_some(first)
}

fn const_u32(func: &Function, value: ValueRef) -> Option<u32> {
    let constant = const_bigint(func, value)?;
    if constant.sign() == num_bigint::Sign::Minus {
        return None;
    }
    constant.to_string().parse().ok()
}

fn const_i64(func: &Function, value: ValueRef) -> Option<i64> {
    const_bigint(func, value)?.to_string().parse().ok()
}

fn const_bigint(func: &Function, value: ValueRef) -> Option<BigInt> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::Const(int) => Some(int.clone()),
        Op::Add(lhs, rhs) => Some(
            const_bigint(func, lhs.clone().raw().value)?
                + const_bigint(func, rhs.clone().raw().value)?,
        ),
        Op::Sub(lhs, rhs) => Some(
            const_bigint(func, lhs.clone().raw().value)?
                - const_bigint(func, rhs.clone().raw().value)?,
        ),
        Op::Mul(lhs, rhs) => Some(
            const_bigint(func, lhs.clone().raw().value)?
                * const_bigint(func, rhs.clone().raw().value)?,
        ),
        _ => None,
    }
}

fn cleanup_dead_instructions(func: &mut Function, matched_insts: &BTreeSet<u32>) {
    loop {
        let mut changed = false;
        for idx in matched_insts.iter().copied().collect::<Vec<_>>() {
            let Some(inst) = func.inst_pool.get(idx) else {
                continue;
            };
            if !matches!(
                inst.inst.op,
                Op::Const(_)
                    | Op::BConst(_)
                    | Op::PtrAdd(_, _)
                    | Op::StackSlot(_, _)
                    | Op::SymbolAddr(_)
            ) {
                continue;
            }
            if func.has_uses(ValueRef::inst_result(idx)) {
                continue;
            }
            let _ = func.remove_inst(idx);
            changed = true;
        }
        if !changed {
            break;
        }
    }
}

fn int_annotation(size: u32) -> Annotation {
    Annotation::Int(IntAnnotation {
        bit_width: size * 8,
        signedness: IntSignedness::Unsigned,
    })
}

fn merged_origin(func: &Function, root_idx: u32, matched_insts: &BTreeSet<u32>) -> Origin {
    let mut seen = BTreeSet::new();
    let mut sources = Vec::new();
    for idx in std::iter::once(root_idx).chain(matched_insts.iter().copied()) {
        if let Some(node) = func.inst_pool.get(idx) {
            for source in &node.inst.origin.sources {
                if seen.insert(*source) {
                    sources.push(*source);
                }
            }
        }
    }
    Origin { sources }
}
