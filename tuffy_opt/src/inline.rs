use std::collections::HashMap;

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{Instruction, Op, Operand};
use tuffy_ir::module::{Module, SymbolId};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, RegionRef, ValueRef};

use crate::peephole::PeepholeStats;

const MAX_INLINE_ITERATIONS: usize = 128;
const INLINE_SCORE_THRESHOLD: u32 = 24;
const INLINE_SINGLE_CALLER_THRESHOLD: u32 = 48;
const INLINE_SINGLE_CALLER_LEAF_THRESHOLD: u32 = 64;
const INLINE_SINGLE_CALLER_SIMPLE_CFG_THRESHOLD: u32 = 128;
const INLINE_MEMORY_WRAPPER_THRESHOLD: u32 = 96;

pub(crate) struct InlineResult {
    pub(crate) stats: PeepholeStats,
    pub(crate) changed_functions: Vec<bool>,
}

#[derive(Clone)]
struct Ret2Spec {
    ty: Type,
    annotation: Option<Annotation>,
    users: Vec<u32>,
}

#[derive(Clone)]
struct InlineSite {
    caller_idx: usize,
    callee_idx: usize,
    call_idx: u32,
    call_block: BlockRef,
    ret2: Option<Ret2Spec>,
}

struct ModuleAnalysis {
    func_by_symbol: HashMap<SymbolId, usize>,
    scc_ids: Vec<usize>,
    scc_sizes: Vec<usize>,
    inline_scores: Vec<Option<u32>>,
    call_site_counts: Vec<usize>,
    local_callee_counts: Vec<usize>,
}

pub(crate) fn inline_module(module: &mut Module) -> InlineResult {
    let mut stats = PeepholeStats::default();
    let mut changed_functions = vec![false; module.functions.len()];
    let mut rounds = 0;

    while rounds < MAX_INLINE_ITERATIONS {
        let analysis = ModuleAnalysis::compute(module);
        let Some(site) = find_inline_site(module, &analysis) else {
            break;
        };
        rounds += 1;
        let new_func = build_inlined_function(
            &module.functions[site.caller_idx],
            &module.functions[site.callee_idx],
            &site,
        )
        .expect("eligible inline site should rebuild");
        module.functions[site.caller_idx] = new_func;
        changed_functions[site.caller_idx] = true;
        stats.inlined_calls += 1;
    }

    stats.inline_iterations = rounds;
    InlineResult {
        stats,
        changed_functions,
    }
}

impl ModuleAnalysis {
    fn compute(module: &Module) -> Self {
        let func_by_symbol = module
            .functions
            .iter()
            .enumerate()
            .map(|(idx, func)| (func.name, idx))
            .collect::<HashMap<_, _>>();
        let adjacency = module
            .functions
            .iter()
            .map(|func| direct_local_callees(func, &func_by_symbol))
            .collect::<Vec<_>>();
        let (scc_ids, scc_sizes) = compute_sccs(&adjacency);
        let inline_scores = module.functions.iter().map(inline_score).collect();
        let local_callee_counts = adjacency.iter().map(Vec::len).collect();
        let mut call_site_counts = vec![0; module.functions.len()];
        for func in &module.functions {
            for (_, inst) in func.inst_pool.iter_insts() {
                let Op::Call(callee, _, _, None) = &inst.op else {
                    continue;
                };
                let Some(sym) = direct_call_symbol(func, callee.clone().raw().value) else {
                    continue;
                };
                let Some(&callee_idx) = func_by_symbol.get(&sym) else {
                    continue;
                };
                call_site_counts[callee_idx] += 1;
            }
        }
        Self {
            func_by_symbol,
            scc_ids,
            scc_sizes,
            inline_scores,
            call_site_counts,
            local_callee_counts,
        }
    }

    fn is_recursive_edge(&self, caller_idx: usize, callee_idx: usize) -> bool {
        caller_idx == callee_idx
            || (self.scc_ids[caller_idx] == self.scc_ids[callee_idx]
                && self.scc_sizes[self.scc_ids[caller_idx]] > 1)
    }
}

fn find_inline_site(module: &Module, analysis: &ModuleAnalysis) -> Option<InlineSite> {
    for (caller_idx, caller) in module.functions.iter().enumerate() {
        let block_refs = collect_block_refs(caller);
        for block in block_refs {
            for (value, inst) in caller.block_insts_with_values(block) {
                let Op::Call(callee, args, _mem, cleanup_label) = &inst.op else {
                    continue;
                };
                if cleanup_label.is_some() {
                    continue;
                }
                let Some(sym) = direct_call_symbol(caller, callee.clone().raw().value) else {
                    continue;
                };
                let Some(&callee_idx) = analysis.func_by_symbol.get(&sym) else {
                    continue;
                };
                if analysis.is_recursive_edge(caller_idx, callee_idx) {
                    continue;
                }
                let Some(score) = analysis.inline_scores[callee_idx] else {
                    continue;
                };
                let callee_func = &module.functions[callee_idx];
                let call_site_count = analysis.call_site_counts[callee_idx];
                let inline_budget = if call_site_count == 1 && callee_is_leaf(callee_func) {
                    INLINE_SINGLE_CALLER_LEAF_THRESHOLD
                } else if call_site_count == 1
                    && analysis.local_callee_counts[callee_idx] <= 1
                    && callee_func.regions.len() == 1
                    && callee_is_scalar_simple_cfg(callee_func)
                {
                    INLINE_SINGLE_CALLER_SIMPLE_CFG_THRESHOLD
                } else if call_site_count <= 2
                    && analysis.local_callee_counts[callee_idx] <= 1
                    && callee_func.regions.len() == 1
                    && callee_is_memory_wrapper(callee_func)
                {
                    INLINE_MEMORY_WRAPPER_THRESHOLD
                } else if call_site_count == 1 {
                    INLINE_SINGLE_CALLER_THRESHOLD
                } else {
                    INLINE_SCORE_THRESHOLD
                };
                if score > inline_budget {
                    continue;
                }
                if !supported_entry_block(callee_func) {
                    continue;
                }
                if args.len() != callee_func.params.len() {
                    continue;
                }
                let ret2 = collect_ret2_spec(caller, value.index())?;
                if !call_signature_matches(caller, inst, callee_func, ret2.as_ref()) {
                    continue;
                }
                return Some(InlineSite {
                    caller_idx,
                    callee_idx,
                    call_idx: value.index(),
                    call_block: block,
                    ret2,
                });
            }
        }
    }
    None
}

fn callee_is_leaf(func: &Function) -> bool {
    !func
        .inst_pool
        .iter_insts()
        .any(|(_, inst)| matches!(inst.op, Op::Call(..)))
}

fn callee_is_scalar_simple_cfg(func: &Function) -> bool {
    !func.inst_pool.iter_insts().any(|(_, inst)| {
        matches!(
            inst.op,
            Op::Load(..)
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
                | Op::PtrAdd(..)
                | Op::PtrDiff(..)
                | Op::PtrToInt(..)
                | Op::PtrToAddr(..)
                | Op::IntToPtr(..)
        )
    })
}

fn callee_is_memory_wrapper(func: &Function) -> bool {
    !func.inst_pool.iter_insts().any(|(_, inst)| {
        matches!(
            inst.op,
            Op::StackSlot(..)
                | Op::MemCopy(..)
                | Op::MemMove(..)
                | Op::MemSet(..)
                | Op::LoadAtomic(..)
                | Op::StoreAtomic(..)
                | Op::AtomicRmw(..)
                | Op::AtomicCmpXchg(..)
                | Op::Fence(..)
                | Op::PtrAdd(..)
                | Op::PtrDiff(..)
                | Op::PtrToInt(..)
                | Op::PtrToAddr(..)
                | Op::IntToPtr(..)
                | Op::Continue(..)
                | Op::RegionYield(..)
        )
    })
}

fn supported_entry_block(func: &Function) -> bool {
    let entry = func.entry_block();
    let args = func.block_args(entry);
    args.len() == 1 && args[0].ty == Type::Mem
}

fn call_signature_matches(
    caller: &Function,
    call_inst: &Instruction,
    callee: &Function,
    ret2: Option<&Ret2Spec>,
) -> bool {
    let Op::Call(_, args, _, _) = &call_inst.op else {
        return false;
    };
    if args.len() != callee.params.len() {
        return false;
    }
    for (arg, expected_ty) in args.iter().zip(callee.params.iter()) {
        if caller.value_type(arg.value) != Some(expected_ty) {
            return false;
        }
    }

    if call_inst.secondary_ty != callee.ret_ty {
        return false;
    }

    for (_, inst) in callee.inst_pool.iter_insts() {
        let Op::Ret(value, ret2_value, _) = &inst.op else {
            continue;
        };
        match (&call_inst.secondary_ty, value) {
            (Some(expected_ty), Some(value)) => {
                if callee.value_type(value.value) != Some(expected_ty) {
                    return false;
                }
            }
            (Some(_), None) => return false,
            (None, Some(_)) => return false,
            (None, None) => {}
        }
        if let Some(ret2_spec) = ret2 {
            let Some(ret2_value) = ret2_value else {
                return false;
            };
            if callee.value_type(ret2_value.value) != Some(&ret2_spec.ty) {
                return false;
            }
        }
    }

    true
}

fn collect_ret2_spec(func: &Function, call_idx: u32) -> Option<Option<Ret2Spec>> {
    let call_value = ValueRef::inst_result(call_idx);
    let mut spec: Option<Ret2Spec> = None;
    for use_node in func.uses_of(call_value) {
        let inst = func.inst(use_node.user);
        if !matches!(inst.op, Op::CallRet2(_)) {
            continue;
        }
        let candidate = Ret2Spec {
            ty: inst.ty.clone(),
            annotation: inst.result_annotation.clone(),
            users: vec![use_node.user],
        };
        match &mut spec {
            Some(existing)
                if existing.ty == candidate.ty && existing.annotation == candidate.annotation =>
            {
                existing.users.push(use_node.user);
            }
            Some(_) => return None,
            None => spec = Some(candidate),
        }
    }
    if let Some(spec) = &mut spec {
        spec.users.sort_unstable();
    }
    Some(spec)
}

fn inline_score(func: &Function) -> Option<u32> {
    let mut score = 0u32;
    for (_, inst) in func.inst_pool.iter_insts() {
        score = score.saturating_add(match &inst.op {
            Op::Call(_, _, _, Some(_)) => return None,
            Op::Call(..) => 3,
            Op::Load(..)
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
            | Op::LandingPad => 2,
            _ => 1,
        });
    }
    Some(score)
}

fn direct_local_callees(func: &Function, func_by_symbol: &HashMap<SymbolId, usize>) -> Vec<usize> {
    let mut callees = Vec::new();
    for (_, inst) in func.inst_pool.iter_insts() {
        let Op::Call(callee, _, _, None) = &inst.op else {
            continue;
        };
        let Some(sym) = direct_call_symbol(func, callee.clone().raw().value) else {
            continue;
        };
        let Some(&callee_idx) = func_by_symbol.get(&sym) else {
            continue;
        };
        if !callees.contains(&callee_idx) {
            callees.push(callee_idx);
        }
    }
    callees
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

fn compute_sccs(adjacency: &[Vec<usize>]) -> (Vec<usize>, Vec<usize>) {
    struct Tarjan<'a> {
        adjacency: &'a [Vec<usize>],
        index: usize,
        indices: Vec<Option<usize>>,
        lowlinks: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        scc_ids: Vec<usize>,
        scc_sizes: Vec<usize>,
    }

    impl Tarjan<'_> {
        fn strong_connect(&mut self, node: usize) {
            self.indices[node] = Some(self.index);
            self.lowlinks[node] = self.index;
            self.index += 1;
            self.stack.push(node);
            self.on_stack[node] = true;

            for &succ in &self.adjacency[node] {
                if self.indices[succ].is_none() {
                    self.strong_connect(succ);
                    self.lowlinks[node] = self.lowlinks[node].min(self.lowlinks[succ]);
                } else if self.on_stack[succ] {
                    self.lowlinks[node] = self.lowlinks[node]
                        .min(self.indices[succ].expect("stacked node should have an index"));
                }
            }

            if self.lowlinks[node] != self.indices[node].expect("visited node should have index") {
                return;
            }

            let scc_id = self.scc_sizes.len();
            let mut size = 0;
            loop {
                let member = self
                    .stack
                    .pop()
                    .expect("current SCC should be on the stack");
                self.on_stack[member] = false;
                self.scc_ids[member] = scc_id;
                size += 1;
                if member == node {
                    break;
                }
            }
            self.scc_sizes.push(size);
        }
    }

    let mut tarjan = Tarjan {
        adjacency,
        index: 0,
        indices: vec![None; adjacency.len()],
        lowlinks: vec![0; adjacency.len()],
        stack: Vec::new(),
        on_stack: vec![false; adjacency.len()],
        scc_ids: vec![0; adjacency.len()],
        scc_sizes: Vec::new(),
    };
    for node in 0..adjacency.len() {
        if tarjan.indices[node].is_none() {
            tarjan.strong_connect(node);
        }
    }
    (tarjan.scc_ids, tarjan.scc_sizes)
}

fn collect_block_refs(func: &Function) -> Vec<BlockRef> {
    let mut refs = vec![None; func.blocks.len()];
    for region in &func.regions {
        for child in &region.children {
            if let CfgNode::Block(block) = child {
                refs[block.index() as usize] = Some(*block);
            }
        }
    }
    refs.into_iter()
        .map(|block| block.expect("every block should appear in a region"))
        .collect()
}

fn build_inlined_function(
    caller: &Function,
    callee: &Function,
    site: &InlineSite,
) -> Option<Function> {
    let call_inst = caller.inst(site.call_idx);
    let Op::Call(_, _, _, _) = &call_inst.op else {
        return None;
    };

    let mut new_func = Function::new(
        caller.name,
        caller.params.clone(),
        caller.param_annotations.clone(),
        caller.param_names.clone(),
        caller.ret_ty.clone(),
        caller.ret_annotation.clone(),
    );
    new_func.byval_sizes = caller.byval_sizes.clone();

    let mut caller_region_map = vec![None; caller.regions.len()];
    let mut caller_block_map = vec![None; caller.blocks.len()];
    let mut callee_region_map = vec![None; callee.regions.len()];
    let mut callee_block_map = vec![None; callee.blocks.len()];
    let mut continuation_slot = None;
    let mut caller_value_map = HashMap::<u32, ValueRef>::new();
    let mut callee_value_map = HashMap::<u32, ValueRef>::new();
    let (continuation_block, cont_mem, cont_ret, cont_ret2);

    {
        let mut builder = Builder::new(&mut new_func);
        clone_caller_regions_with_inline(
            caller,
            &mut builder,
            caller.root_region,
            &mut caller_region_map,
            &mut caller_block_map,
            callee,
            &mut callee_region_map,
            &mut callee_block_map,
            site.call_block,
            &mut continuation_slot,
        );
        let continuation =
            continuation_slot.expect("inline site should allocate a continuation block");

        for block in collect_block_refs(caller) {
            let new_block =
                caller_block_map[block.index() as usize].expect("caller block should be cloned");
            for old_arg in caller.block_arg_values(block) {
                let old_block_arg = &caller.block_args[old_arg.index() as usize];
                let new_arg = builder.add_block_arg(
                    new_block,
                    old_block_arg.ty.clone(),
                    old_block_arg.annotation.clone(),
                );
                caller_value_map.insert(old_arg.raw(), new_arg);
            }
        }
        for block in collect_block_refs(callee) {
            let new_block =
                callee_block_map[block.index() as usize].expect("callee block should be cloned");
            for old_arg in callee.block_arg_values(block) {
                let old_block_arg = &callee.block_args[old_arg.index() as usize];
                let new_arg = builder.add_block_arg(
                    new_block,
                    old_block_arg.ty.clone(),
                    old_block_arg.annotation.clone(),
                );
                callee_value_map.insert(old_arg.raw(), new_arg);
            }
        }

        let continuation_mem = builder.add_block_arg(continuation, Type::Mem, None);
        let continuation_ret = call_inst.secondary_ty.as_ref().map(|ty| {
            builder.add_block_arg(
                continuation,
                ty.clone(),
                call_inst.secondary_result_annotation.clone(),
            )
        });
        let continuation_ret2 = site.ret2.as_ref().map(|ret2| {
            builder.add_block_arg(continuation, ret2.ty.clone(), ret2.annotation.clone())
        });

        cont_mem = continuation_mem;
        cont_ret = continuation_ret;
        cont_ret2 = continuation_ret2;
        continuation_block = continuation;
    }

    caller_value_map.insert(ValueRef::inst_result(site.call_idx).raw(), cont_mem);
    if let Some(cont_ret) = cont_ret {
        caller_value_map.insert(
            ValueRef::inst_secondary_result(site.call_idx).raw(),
            cont_ret,
        );
    }
    if let (Some(ret2_spec), Some(cont_ret2)) = (&site.ret2, cont_ret2) {
        for &user in &ret2_spec.users {
            caller_value_map.insert(ValueRef::inst_result(user).raw(), cont_ret2);
        }
    }

    emit_caller_instructions(
        caller,
        callee,
        site,
        &caller_block_map,
        &callee_block_map,
        &mut caller_value_map,
        &mut callee_value_map,
        continuation_block,
        &mut new_func,
    )?;
    emit_callee_instructions(
        callee,
        &callee_block_map,
        &mut callee_value_map,
        continuation_block,
        cont_ret,
        cont_ret2,
        &mut new_func,
    )?;

    new_func.rebuild_use_lists();
    Some(new_func)
}

#[allow(clippy::too_many_arguments)]
fn emit_caller_instructions(
    caller: &Function,
    callee: &Function,
    site: &InlineSite,
    caller_block_map: &[Option<BlockRef>],
    callee_block_map: &[Option<BlockRef>],
    caller_value_map: &mut HashMap<u32, ValueRef>,
    callee_value_map: &mut HashMap<u32, ValueRef>,
    continuation_block: BlockRef,
    new_func: &mut Function,
) -> Option<()> {
    let callee_entry = callee_block_map[callee.entry_block().index() as usize]?;
    let entry_arg_annotation = callee
        .block_args(callee.entry_block())
        .first()
        .and_then(|arg| arg.annotation.clone());

    for block in collect_block_refs(caller) {
        let mapped_block = caller_block_map[block.index() as usize]?;
        let mut emit_block = mapped_block;
        for (value, inst) in caller.block_insts_with_values(block) {
            if site
                .ret2
                .as_ref()
                .is_some_and(|ret2| ret2.users.contains(&value.index()))
            {
                continue;
            }

            if value.index() == site.call_idx {
                let branch = Instruction {
                    op: Op::Br(
                        callee_entry,
                        vec![Operand {
                            value: match &inst.op {
                                Op::Call(_, args, mem, _) => {
                                    let mapped_args = args
                                        .iter()
                                        .map(|arg| remap_operand(caller_value_map, arg))
                                        .collect::<Option<Vec<_>>>()?;
                                    for (param_inst_idx, param_inst) in
                                        callee.inst_pool.iter_insts()
                                    {
                                        let Op::Param(param_index) = param_inst.op else {
                                            continue;
                                        };
                                        let mapped_arg =
                                            mapped_args.get(param_index as usize)?.value;
                                        callee_value_map.insert(
                                            ValueRef::inst_result(param_inst_idx).raw(),
                                            mapped_arg,
                                        );
                                    }
                                    remap_value(caller_value_map, mem.clone().raw().value)?
                                }
                                _ => return None,
                            },
                            annotation: entry_arg_annotation.clone(),
                        }],
                    ),
                    ty: Type::Unit,
                    secondary_ty: None,
                    origin: inst.origin.clone(),
                    result_annotation: None,
                    secondary_result_annotation: None,
                };
                new_func.append_inst(emit_block, branch);
                emit_block = continuation_block;
                continue;
            }

            emit_one_caller_inst(
                caller_block_map,
                caller_value_map,
                emit_block,
                value.index(),
                inst,
                new_func,
            )?;
        }
    }
    Some(())
}

fn emit_one_caller_inst(
    caller_block_map: &[Option<BlockRef>],
    caller_value_map: &mut HashMap<u32, ValueRef>,
    emit_block: BlockRef,
    inst_idx: u32,
    inst: &Instruction,
    new_func: &mut Function,
) -> Option<()> {
    let mut new_inst = inst.clone();
    new_inst.op.for_each_value_ref_mut(&mut |value| {
        *value = remap_value(caller_value_map, *value).expect("caller operands should be remapped")
    });
    match &mut new_inst.op {
        Op::Br(target, _) => *target = caller_block_map[target.index() as usize]?,
        Op::BrIf(_, then_block, _, else_block, _) => {
            *then_block = caller_block_map[then_block.index() as usize]?;
            *else_block = caller_block_map[else_block.index() as usize]?;
        }
        Op::Call(_, _, _, cleanup_label) => {
            *cleanup_label = cleanup_label
                .and_then(|old| caller_block_map.get(old as usize).copied().flatten())
                .map(|block| block.index());
        }
        _ => {}
    }
    let new_idx = new_func.append_inst(emit_block, new_inst);
    caller_value_map.insert(
        ValueRef::inst_result(inst_idx).raw(),
        ValueRef::inst_result(new_idx),
    );
    if inst.secondary_ty.is_some() {
        caller_value_map.insert(
            ValueRef::inst_secondary_result(inst_idx).raw(),
            ValueRef::inst_secondary_result(new_idx),
        );
    }
    Some(())
}

#[allow(clippy::too_many_arguments)]
fn emit_callee_instructions(
    callee: &Function,
    callee_block_map: &[Option<BlockRef>],
    callee_value_map: &mut HashMap<u32, ValueRef>,
    continuation_block: BlockRef,
    cont_ret: Option<ValueRef>,
    cont_ret2: Option<ValueRef>,
    new_func: &mut Function,
) -> Option<()> {
    for block in collect_block_refs(callee) {
        let mapped_block = callee_block_map[block.index() as usize]?;
        for (value, inst) in callee.block_insts_with_values(block) {
            if matches!(inst.op, Op::Param(_)) {
                continue;
            }
            if let Op::Ret(ret_value, ret2_value, mem) = &inst.op {
                let mut args = vec![Operand::new(remap_value(
                    callee_value_map,
                    mem.clone().raw().value,
                )?)];
                if let Some(_cont_ret) = cont_ret {
                    let ret_value = ret_value.as_ref()?;
                    let mapped = remap_operand(callee_value_map, ret_value)?;
                    args.push(mapped);
                }
                if let Some(_cont_ret2) = cont_ret2 {
                    let ret2_value = ret2_value.as_ref()?;
                    let mapped = remap_operand(callee_value_map, ret2_value)?;
                    args.push(mapped);
                }
                let branch = Instruction {
                    op: Op::Br(continuation_block, args),
                    ty: Type::Unit,
                    secondary_ty: None,
                    origin: inst.origin.clone(),
                    result_annotation: None,
                    secondary_result_annotation: None,
                };
                new_func.append_inst(mapped_block, branch);
                continue;
            }

            let mut new_inst = inst.clone();
            new_inst.op.for_each_value_ref_mut(&mut |value_ref| {
                *value_ref = remap_value(callee_value_map, *value_ref)
                    .expect("callee operands should be remapped")
            });
            match &mut new_inst.op {
                Op::Br(target, _) => *target = callee_block_map[target.index() as usize]?,
                Op::BrIf(_, then_block, _, else_block, _) => {
                    *then_block = callee_block_map[then_block.index() as usize]?;
                    *else_block = callee_block_map[else_block.index() as usize]?;
                }
                Op::Call(_, _, _, cleanup_label) => {
                    *cleanup_label = cleanup_label
                        .and_then(|old| callee_block_map.get(old as usize).copied().flatten())
                        .map(|block| block.index());
                }
                _ => {}
            }
            let new_idx = new_func.append_inst(mapped_block, new_inst);
            callee_value_map.insert(
                ValueRef::inst_result(value.index()).raw(),
                ValueRef::inst_result(new_idx),
            );
            if inst.secondary_ty.is_some() {
                callee_value_map.insert(
                    ValueRef::inst_secondary_result(value.index()).raw(),
                    ValueRef::inst_secondary_result(new_idx),
                );
            }
        }
    }
    Some(())
}

fn remap_value(value_map: &HashMap<u32, ValueRef>, value: ValueRef) -> Option<ValueRef> {
    value_map.get(&value.raw()).copied()
}

fn remap_operand(value_map: &HashMap<u32, ValueRef>, operand: &Operand) -> Option<Operand> {
    Some(Operand {
        value: remap_value(value_map, operand.value)?,
        annotation: operand.annotation.clone(),
    })
}

#[allow(clippy::too_many_arguments)]
fn clone_caller_regions_with_inline(
    caller: &Function,
    builder: &mut Builder<'_>,
    old_region: RegionRef,
    caller_region_map: &mut [Option<RegionRef>],
    caller_block_map: &mut [Option<BlockRef>],
    callee: &Function,
    callee_region_map: &mut [Option<RegionRef>],
    callee_block_map: &mut [Option<BlockRef>],
    call_block: BlockRef,
    continuation_block: &mut Option<BlockRef>,
) {
    let region = caller.region(old_region);
    let new_region = builder.create_region(region.kind);
    caller_region_map[old_region.index() as usize] = Some(new_region);
    builder.enter_region(new_region);
    for child in &region.children {
        match child {
            CfgNode::Block(block) => {
                let new_block = builder.create_block();
                caller_block_map[block.index() as usize] = Some(new_block);
                if *block == call_block {
                    clone_callee_root_children(
                        callee,
                        builder,
                        callee_region_map,
                        callee_block_map,
                    );
                    *continuation_block = Some(builder.create_block());
                }
            }
            CfgNode::Region(region) => clone_caller_regions_with_inline(
                caller,
                builder,
                *region,
                caller_region_map,
                caller_block_map,
                callee,
                callee_region_map,
                callee_block_map,
                call_block,
                continuation_block,
            ),
        }
    }
    builder.exit_region();
}

fn clone_callee_root_children(
    callee: &Function,
    builder: &mut Builder<'_>,
    callee_region_map: &mut [Option<RegionRef>],
    callee_block_map: &mut [Option<BlockRef>],
) {
    for child in &callee.region(callee.root_region).children {
        match child {
            CfgNode::Block(block) => {
                let new_block = builder.create_block();
                callee_block_map[block.index() as usize] = Some(new_block);
            }
            CfgNode::Region(region) => {
                clone_callee_region(
                    callee,
                    builder,
                    *region,
                    callee_region_map,
                    callee_block_map,
                );
            }
        }
    }
}

fn clone_callee_region(
    callee: &Function,
    builder: &mut Builder<'_>,
    old_region: RegionRef,
    callee_region_map: &mut [Option<RegionRef>],
    callee_block_map: &mut [Option<BlockRef>],
) {
    let region = callee.region(old_region);
    let new_region = builder.create_region(region.kind);
    callee_region_map[old_region.index() as usize] = Some(new_region);
    builder.enter_region(new_region);
    for child in &region.children {
        match child {
            CfgNode::Block(block) => {
                let new_block = builder.create_block();
                callee_block_map[block.index() as usize] = Some(new_block);
            }
            CfgNode::Region(region) => {
                clone_callee_region(
                    callee,
                    builder,
                    *region,
                    callee_region_map,
                    callee_block_map,
                );
            }
        }
    }
    builder.exit_region();
}
