use std::collections::HashMap;

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{CfgNode, Function, RegionKind};
use tuffy_ir::instruction::{Instruction, Op, Operand, Origin};
use tuffy_ir::types::Type;
use tuffy_ir::value::ValueRef;

use crate::cfg::{collect_block_refs, has_unwind_cleanup_edges};
use crate::peephole::PeepholeStats;

#[derive(Clone)]
/// Tail-recursive self-call that can be rewritten into a loop backedge.
struct TailSite {
    /// Call instruction index inside the original function.
    call_idx: u32,
    /// Dead pure instructions between the call and its branch-to-return.
    skipped_insts: Vec<u32>,
    /// Incoming memory operand passed to the self call.
    call_mem: Operand,
    /// Recursive arguments passed to the self call.
    call_args: Vec<Operand>,
}

/// Loopify direct self-tail recursion in root-only unit-returning functions.
pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    if !eligible_function(func) {
        return PeepholeStats::default();
    }
    let tail_sites = collect_tail_sites(func);
    if tail_sites.is_empty() {
        return PeepholeStats::default();
    }
    let Some(mut new_func) = rebuild_with_loop_header(func, &tail_sites) else {
        return PeepholeStats::default();
    };
    new_func.rebuild_use_lists();
    *func = new_func;

    let mut stats = PeepholeStats::default();
    for _ in 0..tail_sites.len() {
        stats.record("tailrec_loopify");
    }
    stats
}

/// Return whether the function shape is simple enough for the current transform.
fn eligible_function(func: &Function) -> bool {
    if has_unwind_cleanup_edges(func) {
        return false;
    }
    if func.regions.len() != 1 {
        return false;
    }
    if func.regions.iter().any(|region| {
        region
            .children
            .iter()
            .any(|child| matches!(child, CfgNode::Region(_)))
    }) {
        return false;
    }
    if !matches!(func.ret_ty, None | Some(Type::Unit)) {
        return false;
    }
    !func
        .inst_pool
        .iter_insts()
        .any(|(_, inst)| matches!(inst.op, Op::Continue(_) | Op::RegionYield(_)))
}

/// Collect direct self-tail-call sites that return through a mem-only continuation block.
fn collect_tail_sites(func: &Function) -> HashMap<u32, TailSite> {
    let mut sites = HashMap::new();
    for block in collect_block_refs(func) {
        let bb = func.block(block);
        let Some(br_idx) = bb.last_inst else {
            continue;
        };
        let Op::Br(target, br_args) = &func.inst(br_idx).op else {
            continue;
        };
        let mut skipped_insts = Vec::new();
        let mut cursor = func.inst_node(br_idx).prev;
        let call_idx = loop {
            let Some(inst_idx) = cursor else {
                skipped_insts.clear();
                break None;
            };
            if is_dead_tail_suffix_inst(func, inst_idx) {
                skipped_insts.push(inst_idx);
                cursor = func.inst_node(inst_idx).prev;
                continue;
            }
            break Some(inst_idx);
        };
        let Some(call_idx) = call_idx else {
            continue;
        };
        let Op::Call(callee, call_args, call_mem, cleanup) = &func.inst(call_idx).op else {
            continue;
        };
        if cleanup.is_some() || call_args.len() != func.params.len() {
            continue;
        }
        if direct_call_symbol(func, callee.clone().raw().value) != Some(func.name) {
            continue;
        }
        if br_args.len() != 1 || br_args[0].value != ValueRef::inst_result(call_idx) {
            continue;
        }
        let target_bb = func.block(*target);
        if target_bb.arg_count != 1 || target_bb.inst_count != 1 {
            continue;
        }
        let Some(ret_idx) = target_bb.last_inst else {
            continue;
        };
        let ret_mem_arg = func.block_arg_values(*target)[0];
        let Op::Ret(None, None, ret_mem) = &func.inst(ret_idx).op else {
            continue;
        };
        if ret_mem.clone().raw().value != ret_mem_arg {
            continue;
        }
        sites.insert(
            block.index(),
            TailSite {
                call_idx,
                skipped_insts,
                call_mem: call_mem.clone().into(),
                call_args: call_args.clone(),
            },
        );
    }
    sites
}

/// Rebuild the function with a preheader and loop region that carries recursive state.
fn rebuild_with_loop_header(
    func: &Function,
    tail_sites: &HashMap<u32, TailSite>,
) -> Option<Function> {
    let old_blocks = collect_block_refs(func);
    let old_entry = func.entry_block();
    let entry_args = func.block_args(old_entry);
    if entry_args.len() != 1 || entry_args[0].ty != Type::Mem {
        return None;
    }

    let mut param_origins = vec![Origin::synthetic(); func.params.len()];
    let mut seen_params = vec![false; func.params.len()];
    for (value, inst) in func.block_insts_with_values(old_entry) {
        let Op::Param(idx) = inst.op else {
            continue;
        };
        let idx = idx as usize;
        if idx >= func.params.len() {
            return None;
        }
        param_origins[idx] = func.inst(value.index()).origin.clone();
        seen_params[idx] = true;
    }
    if seen_params.iter().any(|seen| !seen) {
        return None;
    }

    let mut new_func = Function::new(
        func.name,
        func.params.clone(),
        func.param_annotations.clone(),
        func.param_names.clone(),
        func.ret_ty.clone(),
        func.ret_annotation.clone(),
    );
    new_func.byval_sizes = func.byval_sizes.clone();
    new_func.debug = func.debug.clone();

    let mut block_map = vec![None; func.blocks.len()];
    let (preheader, entry_loop_mem, entry_loop_params) = {
        let mut builder = Builder::new(&mut new_func);
        let root = builder.create_region(RegionKind::Function);
        builder.enter_region(root);
        let pre = builder.create_block();
        let _preheader_mem = builder.add_block_arg(pre, Type::Mem, None);
        let preheader = pre;

        let loop_region = builder.create_region(RegionKind::Loop);
        builder.enter_region(loop_region);
        for block in &old_blocks {
            block_map[block.index() as usize] = Some(builder.create_block());
        }
        let new_entry = block_map[old_entry.index() as usize].expect("entry block should exist");
        let entry_loop_mem =
            builder.add_block_arg(new_entry, Type::Mem, entry_args[0].annotation.clone());
        let mut entry_loop_params = Vec::new();
        for (ty, ann) in func
            .params
            .iter()
            .cloned()
            .zip(func.param_annotations.iter().cloned())
        {
            entry_loop_params.push(builder.add_block_arg(new_entry, ty, ann));
        }
        for block in &old_blocks {
            if *block == old_entry {
                continue;
            }
            for old_arg in func.block_args(*block) {
                let _ = builder.add_block_arg(
                    block_map[block.index() as usize].expect("cloned block should exist"),
                    old_arg.ty.clone(),
                    old_arg.annotation.clone(),
                );
            }
        }
        builder.exit_region();
        builder.exit_region();
        (preheader, entry_loop_mem, entry_loop_params)
    };

    let mut value_map = HashMap::<u32, ValueRef>::new();
    value_map.insert(func.block_arg_values(old_entry)[0].raw(), entry_loop_mem);
    for (param_idx, arg) in entry_loop_params.iter().enumerate() {
        for (value, inst) in func.block_insts_with_values(old_entry) {
            if let Op::Param(idx) = inst.op
                && idx as usize == param_idx
            {
                value_map.insert(value.raw(), *arg);
                break;
            }
        }
    }
    for block in &old_blocks {
        if *block == old_entry {
            continue;
        }
        for (old_arg, new_arg) in
            func.block_arg_values(*block)
                .into_iter()
                .zip(new_func.block_arg_values(
                    block_map[block.index() as usize].expect("cloned block should exist"),
                ))
        {
            value_map.insert(old_arg.raw(), new_arg);
        }
    }

    let mut init_args = vec![Operand::new(new_func.block_arg_values(preheader)[0])];
    for (idx, ((ty, ann), origin)) in func
        .params
        .iter()
        .cloned()
        .zip(func.param_annotations.iter().cloned())
        .zip(param_origins.iter().cloned())
        .enumerate()
    {
        let param_idx = new_func.append_inst(
            preheader,
            Instruction {
                op: Op::Param(idx as u32),
                ty,
                secondary_ty: None,
                origin,
                result_annotation: ann,
                secondary_result_annotation: None,
            },
        );
        init_args.push(Operand::new(ValueRef::inst_result(param_idx)));
    }
    let loop_header = block_map[old_entry.index() as usize].expect("loop header should exist");
    let _ = new_func.append_inst(
        preheader,
        Instruction {
            op: Op::Br(loop_header, init_args),
            ty: Type::Unit,
            secondary_ty: None,
            origin: Origin::synthetic(),
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );

    for old_block in &old_blocks {
        let new_block = block_map[old_block.index() as usize].expect("cloned block should exist");
        let tail_site = tail_sites.get(&old_block.index()).cloned();
        for (value, inst) in func.block_insts_with_values(*old_block) {
            let inst_idx = value.index();
            if *old_block == old_entry && matches!(inst.op, Op::Param(_)) {
                continue;
            }
            if let Some(site) = &tail_site {
                if inst_idx == site.call_idx || site.skipped_insts.contains(&inst_idx) {
                    continue;
                }
                if Some(inst_idx) == func.block(*old_block).last_inst {
                    let mut continue_args = Vec::with_capacity(site.call_args.len() + 1);
                    continue_args.push(remap_operand(&value_map, &site.call_mem));
                    continue_args.extend(
                        site.call_args
                            .iter()
                            .map(|arg| remap_operand(&value_map, arg)),
                    );
                    let new_idx = new_func.append_inst(
                        new_block,
                        Instruction {
                            op: Op::Br(loop_header, continue_args),
                            ty: Type::Unit,
                            secondary_ty: None,
                            origin: inst.origin.clone(),
                            result_annotation: None,
                            secondary_result_annotation: None,
                        },
                    );
                    value_map.insert(value.raw(), ValueRef::inst_result(new_idx));
                    continue;
                }
            }

            let mut new_inst = inst.clone();
            new_inst
                .op
                .for_each_value_ref_mut(&mut |old| *old = remap_value(&value_map, *old));
            match &mut new_inst.op {
                Op::Br(target, _) => {
                    *target = block_map[target.index() as usize]
                        .expect("cloned branch target should exist")
                }
                Op::BrIf(_, then_block, _, else_block, _) => {
                    *then_block = block_map[then_block.index() as usize]
                        .expect("cloned then target should exist");
                    *else_block = block_map[else_block.index() as usize]
                        .expect("cloned else target should exist");
                }
                Op::Call(_, _, _, cleanup) if cleanup.is_some() => return None,
                Op::Continue(_) | Op::RegionYield(_) => return None,
                _ => {}
            }
            let new_idx = new_func.append_inst(new_block, new_inst);
            value_map.insert(value.raw(), ValueRef::inst_result(new_idx));
            if inst.secondary_ty.is_some() {
                value_map.insert(
                    ValueRef::inst_secondary_result(inst_idx).raw(),
                    ValueRef::inst_secondary_result(new_idx),
                );
            }
        }
    }

    Some(new_func)
}

/// Remap one value reference through the rebuilt-function value map.
fn remap_value(value_map: &HashMap<u32, ValueRef>, value: ValueRef) -> ValueRef {
    value_map
        .get(&value.raw())
        .copied()
        .unwrap_or_else(|| panic!("missing remap for value raw={}", value.raw()))
}

/// Remap one operand through the rebuilt-function value map.
fn remap_operand(value_map: &HashMap<u32, ValueRef>, operand: &Operand) -> Operand {
    Operand {
        value: remap_value(value_map, operand.value),
        annotation: operand.annotation.clone(),
    }
}

/// Return the direct-call symbol when the callee is a `symbol_addr`.
fn direct_call_symbol(func: &Function, value: ValueRef) -> Option<tuffy_ir::module::SymbolId> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::SymbolAddr(sym) => Some(*sym),
        _ => None,
    }
}

/// Return whether an instruction is a dead pure suffix op that can be skipped
/// while recognizing a tail-recursive call/branch pattern.
fn is_dead_tail_suffix_inst(func: &Function, inst_idx: u32) -> bool {
    let inst = func.inst(inst_idx);
    if func.has_uses(ValueRef::inst_result(inst_idx)) {
        return false;
    }
    if inst.secondary_ty.is_some() && func.has_uses(ValueRef::inst_secondary_result(inst_idx)) {
        return false;
    }
    !matches!(
        inst.op,
        Op::Call(..)
            | Op::CallRet2(..)
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
