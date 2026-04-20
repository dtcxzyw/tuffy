//! Conservative stack-slot promotion for Tuffy IR.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use num_bigint::BigInt;
use tuffy_ir::builder::Builder;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{Instruction, Op, Operand};
use tuffy_ir::pool::UseNode;
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, RegionRef, ValueRef};

use crate::cfg::{CfgInfo, collect_block_refs, has_unwind_cleanup_edges};
use crate::peephole::PeepholeStats;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Internal data structure `SliceKey`.
struct SliceKey {
    /// Byte offset from the stack-slot base.
    offset: i64,
    /// Slice width in bytes.
    size: u32,
}

#[derive(Clone, Debug)]
/// Internal enum `AccessKind`.
enum AccessKind {
    /// Variant `Load`.
    Load,
    /// Variant `Store`.
    Store,
}

#[derive(Clone, Debug)]
/// Internal data structure `AccessInfo`.
struct AccessInfo {
    /// Instruction index.
    inst_idx: u32,
    /// Block containing the access.
    block: BlockRef,
    /// Canonical slice reached by the access.
    key: SliceKey,
    /// SSA type reconstructed for the slice.
    ty: Type,
    /// Annotation.
    annotation: Option<Annotation>,
    /// Whether this access is a load or store.
    kind: AccessKind,
}

#[derive(Clone, Debug)]
/// Internal data structure `SlicePlan`.
struct SlicePlan {
    /// Canonical byte range promoted as one SSA slice.
    key: SliceKey,
    /// SSA type used when materializing the slice value.
    ty: Type,
    /// Annotation.
    annotation: Option<Annotation>,
    /// Loads and stores that belong to this slice.
    accesses: Vec<AccessInfo>,
    /// Join blocks that need SSA merge values for this slice.
    phi_blocks: HashSet<BlockRef>,
}

#[derive(Clone, Debug)]
/// Internal data structure `SlotPlan`.
struct SlotPlan {
    /// Stack slot being promoted.
    slot: ValueRef,
    /// Non-overlapping slices promoted out of the slot.
    slices: Vec<SlicePlan>,
}

#[derive(Clone, Debug)]
/// Internal data structure `FlattenedSlice`.
struct FlattenedSlice {
    /// Source stack slot.
    slot: ValueRef,
    /// Canonical byte range within the slot.
    key: SliceKey,
    /// SSA type used for the slice value.
    ty: Type,
    /// Annotation.
    annotation: Option<Annotation>,
    /// Join blocks that need SSA merge values for this slice.
    phi_blocks: HashSet<BlockRef>,
}

#[derive(Clone, Debug, Default)]
/// Internal data structure `PromotionPlan`.
struct PromotionPlan {
    /// Per-slot promotion plans.
    slots: Vec<SlotPlan>,
    /// Flattened slice view used during function rebuilding.
    slices: Vec<FlattenedSlice>,
    /// Map from load instruction to the slice it reads.
    load_to_slice: HashMap<u32, usize>,
    /// Map from store instruction to the slice it writes.
    store_to_slice: HashMap<u32, usize>,
    /// Instructions removed or rewritten as part of promotion.
    promoted_insts: HashSet<u32>,
    /// Promoted slot count or set.
    promoted_slots: HashSet<u32>,
}

/// Internal helper `value_annotation`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn value_annotation(func: &Function, value: ValueRef) -> Option<Annotation> {
    if value.is_block_arg() {
        return func
            .block_args
            .get(value.index() as usize)
            .and_then(|arg| arg.annotation.clone());
    }
    if value.is_secondary_result() {
        return func
            .inst_pool
            .get(value.inst_index())
            .and_then(|node| node.inst.secondary_result_annotation.clone());
    }
    func.inst_pool
        .get(value.index())
        .and_then(|node| node.inst.result_annotation.clone())
}

/// Internal helper `value_type`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn value_type(func: &Function, value: ValueRef) -> Option<Type> {
    func.value_type(value).cloned()
}

/// Internal helper `primary_value_ref`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn primary_value_ref(inst_idx: u32) -> ValueRef {
    ValueRef::inst_result(inst_idx)
}

/// Internal helper `const_i64`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn const_i64(func: &Function, value: ValueRef) -> Option<i64> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::Const(int) = &node.inst.op else {
        return None;
    };
    int.to_string().parse().ok()
}

/// Internal helper `const_bigint`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn const_bigint(func: &Function, value: ValueRef) -> Option<&BigInt> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::Const(int) = &node.inst.op else {
        return None;
    };
    Some(int)
}

/// Internal helper `address_root_slot`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn address_root_slot(func: &Function, value: ValueRef) -> Option<ValueRef> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::StackSlot(_, _) => Some(value),
        Op::PtrAdd(base, offset) => {
            let _ = const_i64(func, offset.clone().raw().value)?;
            address_root_slot(func, base.clone().raw().value)
        }
        _ => None,
    }
}

/// Internal helper `mark_required_address_chain`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn mark_required_address_chain(func: &Function, value: ValueRef, required: &mut HashSet<u32>) {
    let Some(root) = address_root_slot(func, value) else {
        return;
    };
    if root == value {
        required.insert(root.index());
        return;
    }
    if required.insert(value.index()) {
        let node = func
            .inst_pool
            .get(value.index())
            .expect("address value should exist");
        if let Op::PtrAdd(base, _) = &node.inst.op {
            mark_required_address_chain(func, base.clone().raw().value, required);
        }
    }
}

/// Internal helper `collect_slot_plan`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn collect_slot_plan(func: &Function, cfg: &CfgInfo, slot: ValueRef) -> Option<SlotPlan> {
    let mut work = VecDeque::from([(slot, 0i64)]);
    let mut visited = HashMap::<u32, i64>::from([(slot.raw(), 0)]);
    let mut accesses = Vec::new();

    while let Some((pointer, offset)) = work.pop_front() {
        let uses = func.uses_of(pointer).cloned().collect::<Vec<_>>();
        for use_node in uses {
            if !classify_pointer_use(
                func,
                pointer,
                offset,
                &use_node,
                &mut accesses,
                &mut work,
                &mut visited,
            ) {
                return None;
            }
        }
    }

    if accesses.is_empty() {
        return None;
    }

    let mut by_slice = BTreeMap::<SliceKey, Vec<AccessInfo>>::new();
    for access in accesses {
        by_slice.entry(access.key.clone()).or_default().push(access);
    }

    let mut previous_end = None;
    let mut slices = Vec::new();
    for (key, group) in by_slice {
        if let Some(end) = previous_end
            && key.offset < end
        {
            return None;
        }
        previous_end = Some(key.offset + i64::from(key.size));

        let canonical = group
            .iter()
            .find(|access| matches!(access.kind, AccessKind::Load))
            .unwrap_or_else(|| group.first().expect("slice group should be non-empty"));
        let canonical_ty = canonical.ty.clone();
        let canonical_ann = canonical.annotation.clone();
        let has_store = group
            .iter()
            .any(|access| matches!(access.kind, AccessKind::Store));
        if !has_store {
            return None;
        }
        if group.iter().any(|access| {
            !access_matches_slice_canonical(
                func,
                access,
                &canonical_ty,
                canonical_ann.as_ref(),
                key.size,
            )
        }) {
            return None;
        }

        let def_blocks = group
            .iter()
            .filter_map(|access| match access.kind {
                AccessKind::Store => Some(access.block),
                AccessKind::Load => None,
            })
            .collect::<HashSet<_>>();

        let phi_blocks = compute_phi_blocks(cfg, &def_blocks);
        let slice = SlicePlan {
            key,
            ty: canonical_ty,
            annotation: canonical_ann,
            accesses: group,
            phi_blocks,
        };
        if !validate_slice(func, cfg, &slice) {
            return None;
        }
        slices.push(slice);
    }

    Some(SlotPlan { slot, slices })
}

/// Return whether one slice access is compatible with the chosen canonical slice shape.
fn access_matches_slice_canonical(
    func: &Function,
    access: &AccessInfo,
    canonical_ty: &Type,
    canonical_ann: Option<&Annotation>,
    slice_size: u32,
) -> bool {
    if access.ty == *canonical_ty && access.annotation.as_ref() == canonical_ann {
        return true;
    }
    matches!(access.kind, AccessKind::Store)
        && *canonical_ty == Type::Int
        && matches!(access.ty, Type::Int)
        && store_constant_can_widen_to_slice(func, access.inst_idx, canonical_ann, slice_size)
}

/// Return whether a store writes a constant integer that can be widened to the canonical slice.
fn store_constant_can_widen_to_slice(
    func: &Function,
    inst_idx: u32,
    canonical_ann: Option<&Annotation>,
    slice_size: u32,
) -> bool {
    let Some(Annotation::Int(canonical_int)) = canonical_ann else {
        return false;
    };
    if canonical_int.bit_width != slice_size * 8 {
        return false;
    }
    let Op::Store(value, _, store_size, _) = &func.inst(inst_idx).op else {
        return false;
    };
    if *store_size != slice_size {
        return false;
    }
    const_bigint(func, value.value).is_some()
}

/// Internal helper `classify_pointer_use`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn classify_pointer_use(
    func: &Function,
    pointer: ValueRef,
    base_offset: i64,
    use_node: &UseNode,
    accesses: &mut Vec<AccessInfo>,
    work: &mut VecDeque<(ValueRef, i64)>,
    visited: &mut HashMap<u32, i64>,
) -> bool {
    let user = func.inst(use_node.user);
    match &user.op {
        Op::PtrAdd(base, delta)
            if use_node.operand_index == 0 && base.clone().raw().value == pointer =>
        {
            let Some(delta) = const_i64(func, delta.clone().raw().value) else {
                return false;
            };
            let child = primary_value_ref(use_node.user);
            let total_offset = base_offset + delta;
            if let Some(existing) = visited.get(&child.raw()) {
                return *existing == total_offset;
            }
            visited.insert(child.raw(), total_offset);
            work.push_back((child, total_offset));
            true
        }
        Op::Load(_, size, _) if use_node.operand_index == 0 => {
            accesses.push(AccessInfo {
                inst_idx: use_node.user,
                block: func.inst_node(use_node.user).parent_block,
                key: SliceKey {
                    offset: base_offset,
                    size: *size,
                },
                ty: user.ty.clone(),
                annotation: user.result_annotation.clone(),
                kind: AccessKind::Load,
            });
            true
        }
        Op::Store(value, _, size, _) if use_node.operand_index == 1 => {
            if value.annotation.is_some() {
                return false;
            }
            let Some(ty) = value_type(func, value.value) else {
                return false;
            };
            accesses.push(AccessInfo {
                inst_idx: use_node.user,
                block: func.inst_node(use_node.user).parent_block,
                key: SliceKey {
                    offset: base_offset,
                    size: *size,
                },
                ty,
                annotation: value_annotation(func, value.value),
                kind: AccessKind::Store,
            });
            true
        }
        Op::LoadAtomic(_, _, _)
        | Op::StoreAtomic(_, _, _, _)
        | Op::AtomicRmw(_, _, _, _, _)
        | Op::AtomicCmpXchg(_, _, _, _, _, _)
        | Op::MemCopy(_, _, _, _)
        | Op::MemMove(_, _, _, _)
        | Op::MemSet(_, _, _, _)
        | Op::Call(_, _, _, _)
        | Op::CallRet2(_)
        | Op::Fence(_, _) => false,
        _ => false,
    }
}

/// Internal helper `compute_phi_blocks`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn compute_phi_blocks(cfg: &CfgInfo, def_blocks: &HashSet<BlockRef>) -> HashSet<BlockRef> {
    let mut phis = HashSet::new();
    let mut work = def_blocks.iter().copied().collect::<VecDeque<_>>();
    while let Some(block) = work.pop_front() {
        for frontier in &cfg.dominance_frontier[block.index() as usize] {
            if phis.insert(*frontier) && !def_blocks.contains(frontier) {
                work.push_back(*frontier);
            }
        }
    }
    phis
}

/// Internal helper `validate_slice`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn validate_slice(func: &Function, cfg: &CfgInfo, slice: &SlicePlan) -> bool {
    if slice
        .accesses
        .iter()
        .any(|access| !cfg.reachable[access.block.index() as usize])
    {
        return false;
    }
    if slice.phi_blocks.iter().any(|block| {
        cfg.preds[block.index() as usize]
            .iter()
            .any(|pred| !cfg.reachable[pred.index() as usize])
    }) {
        return false;
    }

    /// Internal helper `visit`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn visit(
        func: &Function,
        cfg: &CfgInfo,
        slice: &SlicePlan,
        block: BlockRef,
        mut current_defined: bool,
    ) -> bool {
        if slice.phi_blocks.contains(&block) {
            current_defined = true;
        }

        for (value, inst) in func.block_insts_with_values(block) {
            let inst_idx = value.index();
            if slice.accesses.iter().any(|access| {
                access.inst_idx == inst_idx && matches!(access.kind, AccessKind::Load)
            }) {
                if !current_defined {
                    return false;
                }
                continue;
            }
            if slice.accesses.iter().any(|access| {
                access.inst_idx == inst_idx && matches!(access.kind, AccessKind::Store)
            }) {
                current_defined = true;
                continue;
            }
            if matches!(inst.op, Op::Trap | Op::Unreachable) {
                break;
            }
        }

        for succ in &cfg.succs[block.index() as usize] {
            if slice.phi_blocks.contains(succ) && !current_defined {
                return false;
            }
        }

        for child in &cfg.dom_children[block.index() as usize] {
            if !visit(func, cfg, slice, *child, current_defined) {
                return false;
            }
        }
        true
    }

    visit(func, cfg, slice, func.entry_block(), false)
}

/// Internal helper `collect_promotion_plan`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn collect_promotion_plan(func: &Function, cfg: &CfgInfo) -> PromotionPlan {
    let mut plans = Vec::new();
    for (inst_idx, inst) in func.inst_pool.iter_insts() {
        if !matches!(inst.op, Op::StackSlot(_, _)) {
            continue;
        }
        let slot = primary_value_ref(inst_idx);
        if let Some(plan) = collect_slot_plan(func, cfg, slot) {
            plans.push(plan);
        }
    }

    let mut flattened = Vec::new();
    for slot_plan in &plans {
        for slice in &slot_plan.slices {
            flattened.push(FlattenedSlice {
                slot: slot_plan.slot,
                key: slice.key.clone(),
                ty: slice.ty.clone(),
                annotation: slice.annotation.clone(),
                phi_blocks: slice.phi_blocks.clone(),
            });
        }
    }
    flattened.sort_by(|lhs, rhs| {
        lhs.slot
            .index()
            .cmp(&rhs.slot.index())
            .then(lhs.key.offset.cmp(&rhs.key.offset))
            .then(lhs.key.size.cmp(&rhs.key.size))
    });

    let mut slice_index = HashMap::<(u32, SliceKey), usize>::new();
    for (idx, slice) in flattened.iter().enumerate() {
        slice_index.insert((slice.slot.raw(), slice.key.clone()), idx);
    }

    let mut plan = PromotionPlan {
        slots: plans,
        slices: flattened,
        ..PromotionPlan::default()
    };
    for slot in &plan.slots {
        plan.promoted_slots.insert(slot.slot.index());
        for slice in &slot.slices {
            let slice_id = *slice_index
                .get(&(slot.slot.raw(), slice.key.clone()))
                .expect("flattened slice should exist");
            for access in &slice.accesses {
                plan.promoted_insts.insert(access.inst_idx);
                match access.kind {
                    AccessKind::Load => {
                        plan.load_to_slice.insert(access.inst_idx, slice_id);
                    }
                    AccessKind::Store => {
                        plan.store_to_slice.insert(access.inst_idx, slice_id);
                    }
                }
            }
        }
    }
    plan
}

/// Internal helper `clone_regions`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn clone_regions(
    old_func: &Function,
    builder: &mut Builder<'_>,
    old_region: RegionRef,
    region_map: &mut [Option<RegionRef>],
    block_map: &mut [Option<BlockRef>],
) {
    let region = old_func.region(old_region);
    let new_region = builder.create_region(region.kind);
    region_map[old_region.index() as usize] = Some(new_region);
    builder.enter_region(new_region);
    for child in &region.children {
        match child {
            tuffy_ir::function::CfgNode::Block(block) => {
                let new_block = builder.create_block();
                block_map[block.index() as usize] = Some(new_block);
            }
            tuffy_ir::function::CfgNode::Region(region) => {
                clone_regions(old_func, builder, *region, region_map, block_map);
            }
        }
    }
    builder.exit_region();
}

/// Internal helper `build_transformed_function`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn build_transformed_function(
    func: &Function,
    cfg: &CfgInfo,
    plan: &PromotionPlan,
) -> Option<Function> {
    if plan.slices.is_empty() {
        return None;
    }

    let block_refs = collect_block_refs(func);
    let mut phi_slices_by_block = vec![Vec::<usize>::new(); func.blocks.len()];
    for (slice_id, slice) in plan.slices.iter().enumerate() {
        for block in &slice.phi_blocks {
            phi_slices_by_block[block.index() as usize].push(slice_id);
        }
    }
    for slices in &mut phi_slices_by_block {
        slices.sort_unstable();
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

    let mut block_map = vec![None; func.blocks.len()];
    let mut region_map = vec![None; func.regions.len()];
    let mut existing_block_arg_map = HashMap::<u32, ValueRef>::new();
    let mut phi_arg_map = vec![HashMap::<usize, ValueRef>::new(); func.blocks.len()];

    {
        let mut builder = Builder::new(&mut new_func);
        clone_regions(
            func,
            &mut builder,
            func.root_region,
            &mut region_map,
            &mut block_map,
        );

        for old_block_idx in 0..func.blocks.len() {
            let old_block = block_refs[old_block_idx];
            let new_block = block_map[old_block_idx].expect("block should be cloned");
            let old_args = func.block_arg_values(old_block);
            for old_arg in old_args {
                let block_arg = &func.block_args[old_arg.index() as usize];
                let new_arg = builder.add_block_arg(
                    new_block,
                    block_arg.ty.clone(),
                    block_arg.annotation.clone(),
                );
                existing_block_arg_map.insert(old_arg.raw(), new_arg);
            }
            for &slice_id in &phi_slices_by_block[old_block_idx] {
                let slice = &plan.slices[slice_id];
                let new_arg =
                    builder.add_block_arg(new_block, slice.ty.clone(), slice.annotation.clone());
                phi_arg_map[old_block_idx].insert(slice_id, new_arg);
            }
        }
    }

    let mut required_addr_insts = HashSet::new();
    for (inst_idx, inst) in func.inst_pool.iter_insts() {
        if plan.promoted_insts.contains(&inst_idx) {
            continue;
        }
        if matches!(inst.op, Op::StackSlot(_, _) | Op::PtrAdd(_, _)) {
            continue;
        }
        for value in inst.op.value_refs() {
            mark_required_address_chain(func, value, &mut required_addr_insts);
        }
    }

    let new_blocks = block_map
        .iter()
        .map(|block| block.expect("block should be cloned"))
        .collect::<Vec<_>>();

    let mut value_map = existing_block_arg_map;
    let mut emitted = HashSet::<u32>::new();
    let mut current_slice_values = vec![None::<ValueRef>; plan.slices.len()];

    /// Internal helper `remap_value`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn remap_value(value_map: &HashMap<u32, ValueRef>, value: ValueRef) -> ValueRef {
        value_map
            .get(&value.raw())
            .copied()
            .unwrap_or_else(|| panic!("missing remap for value raw={}", value.raw()))
    }

    /// Internal helper `remap_operand`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn remap_operand(value_map: &HashMap<u32, ValueRef>, operand: &Operand) -> Operand {
        Operand {
            value: remap_value(value_map, operand.value),
            annotation: operand.annotation.clone(),
        }
    }

    /// Internal helper `append_phi_args`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn append_phi_args(
        args: &mut Vec<Operand>,
        current_slice_values: &[Option<ValueRef>],
        phi_slices_by_block: &[Vec<usize>],
        target: BlockRef,
    ) -> Option<()> {
        for &slice_id in &phi_slices_by_block[target.index() as usize] {
            let value = current_slice_values[slice_id]?;
            args.push(Operand::new(value));
        }
        Some(())
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "Required by the current implementation shape."
    )]
    /// Internal helper `transform_and_append_instruction`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn transform_and_append_instruction(
        func: &Function,
        cfg: &CfgInfo,
        plan: &PromotionPlan,
        promoted_slot_roots: &HashSet<u32>,
        phi_slices_by_block: &[Vec<usize>],
        required_addr_insts: &HashSet<u32>,
        block_map: &[BlockRef],
        value_map: &mut HashMap<u32, ValueRef>,
        current_slice_values: &mut [Option<ValueRef>],
        new_func: &mut Function,
        inst_idx: u32,
    ) -> Option<()> {
        if plan.promoted_insts.contains(&inst_idx) {
            let inst = func.inst(inst_idx);
            if let Some(&slice_id) = plan.load_to_slice.get(&inst_idx) {
                let replacement = current_slice_values[slice_id]?;
                value_map.insert(primary_value_ref(inst_idx).raw(), replacement);
                return Some(());
            }
            if let Some(&slice_id) = plan.store_to_slice.get(&inst_idx) {
                let Op::Store(_, _, _, mem) = &inst.op else {
                    return None;
                };
                let replacement_mem = remap_value(value_map, mem.clone().raw().value);
                value_map.insert(primary_value_ref(inst_idx).raw(), replacement_mem);
                let stored_value = remap_promoted_store_value(
                    func,
                    inst,
                    &plan.slices[slice_id],
                    value_map,
                    block_map,
                    new_func,
                    inst_idx,
                )?;
                current_slice_values[slice_id] = Some(stored_value);
                return Some(());
            }
        }

        if matches!(
            func.inst(inst_idx).op,
            Op::StackSlot(_, _) | Op::PtrAdd(_, _)
        ) {
            let root = address_root_slot(func, primary_value_ref(inst_idx));
            if let Some(root) = root
                && promoted_slot_roots.contains(&root.index())
                && !required_addr_insts.contains(&inst_idx)
            {
                return Some(());
            }
        }

        let old_inst = func.inst(inst_idx);
        let mut new_inst = old_inst.clone();
        match &old_inst.op {
            Op::Br(target, args) => {
                let mut new_args = args
                    .iter()
                    .map(|arg| remap_operand(value_map, arg))
                    .collect::<Vec<_>>();
                append_phi_args(
                    &mut new_args,
                    current_slice_values,
                    phi_slices_by_block,
                    *target,
                )?;
                new_inst.op = Op::Br(block_map[target.index() as usize], new_args);
            }
            Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
                let new_cond = remap_value(value_map, cond.clone().raw().value);
                let mut new_then_args = then_args
                    .iter()
                    .map(|arg| remap_operand(value_map, arg))
                    .collect::<Vec<_>>();
                let mut new_else_args = else_args
                    .iter()
                    .map(|arg| remap_operand(value_map, arg))
                    .collect::<Vec<_>>();
                append_phi_args(
                    &mut new_then_args,
                    current_slice_values,
                    phi_slices_by_block,
                    *then_block,
                )?;
                append_phi_args(
                    &mut new_else_args,
                    current_slice_values,
                    phi_slices_by_block,
                    *else_block,
                )?;
                new_inst.op = Op::BrIf(
                    tuffy_ir::typed::BoolOperand::from(new_cond),
                    block_map[then_block.index() as usize],
                    new_then_args,
                    block_map[else_block.index() as usize],
                    new_else_args,
                );
            }
            Op::Continue(args) => {
                let mut new_args = args
                    .iter()
                    .map(|arg| remap_operand(value_map, arg))
                    .collect::<Vec<_>>();
                let header =
                    cfg.loop_header[func.inst_node(inst_idx).parent_block.index() as usize]?;
                append_phi_args(
                    &mut new_args,
                    current_slice_values,
                    phi_slices_by_block,
                    header,
                )?;
                new_inst.op = Op::Continue(new_args);
            }
            _ => {
                new_inst.op.for_each_value_ref_mut(&mut |value| {
                    *value = remap_value(value_map, *value);
                });
                match &mut new_inst.op {
                    Op::Br(target, args) => {
                        *target = block_map[target.index() as usize];
                        for arg in args {
                            arg.value = remap_value(value_map, arg.value);
                        }
                    }
                    Op::Call(_, _, _, cleanup_label) => {
                        *cleanup_label = cleanup_label.map(|old| block_map[old as usize].index());
                    }
                    _ => {}
                }
            }
        }

        let block = func.inst_node(inst_idx).parent_block;
        let new_idx = new_func.append_inst(block_map[block.index() as usize], new_inst);
        value_map.insert(
            primary_value_ref(inst_idx).raw(),
            primary_value_ref(new_idx),
        );
        if func.inst(inst_idx).secondary_ty.is_some() {
            value_map.insert(
                ValueRef::inst_secondary_result(inst_idx).raw(),
                ValueRef::inst_secondary_result(new_idx),
            );
        }
        Some(())
    }

    /// Internal helper `remap_promoted_store_value`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn remap_promoted_store_value(
        func: &Function,
        inst: &tuffy_ir::instruction::Instruction,
        slice: &FlattenedSlice,
        value_map: &HashMap<u32, ValueRef>,
        block_map: &[BlockRef],
        new_func: &mut Function,
        inst_idx: u32,
    ) -> Option<ValueRef> {
        let Op::Store(value, _, store_size, _) = &inst.op else {
            return None;
        };
        let remapped = remap_value(value_map, value.value);
        if matches!(slice.ty, Type::Int)
            && store_constant_can_widen_to_slice(
                func,
                inst_idx,
                slice.annotation.as_ref(),
                *store_size,
            )
            && let Some(constant) = const_bigint(func, value.value)
        {
            let block = func.inst_node(inst_idx).parent_block;
            let widened_idx = new_func.append_inst(
                block_map[block.index() as usize],
                Instruction {
                    op: Op::Const(constant.clone()),
                    ty: slice.ty.clone(),
                    secondary_ty: None,
                    origin: inst.origin.clone(),
                    result_annotation: slice.annotation.clone(),
                    secondary_result_annotation: None,
                },
            );
            return Some(ValueRef::inst_result(widened_idx));
        }
        Some(remapped)
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "Required by the current implementation shape."
    )]
    /// Internal helper `emit_reachable_subtree`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn emit_reachable_subtree(
        func: &Function,
        cfg: &CfgInfo,
        plan: &PromotionPlan,
        promoted_slot_roots: &HashSet<u32>,
        phi_slices_by_block: &[Vec<usize>],
        required_addr_insts: &HashSet<u32>,
        block_map: &[BlockRef],
        phi_arg_map: &[HashMap<usize, ValueRef>],
        value_map: &mut HashMap<u32, ValueRef>,
        current_slice_values: &mut [Option<ValueRef>],
        emitted: &mut HashSet<u32>,
        new_func: &mut Function,
        block: BlockRef,
    ) -> Option<()> {
        let mut undo = Vec::<(usize, Option<ValueRef>)>::new();
        for (&slice_id, &phi_value) in &phi_arg_map[block.index() as usize] {
            undo.push((slice_id, current_slice_values[slice_id]));
            current_slice_values[slice_id] = Some(phi_value);
        }

        for (value, _) in func.block_insts_with_values(block) {
            let inst_idx = value.index();
            emitted.insert(inst_idx);
            if let Some(&slice_id) = plan.store_to_slice.get(&inst_idx) {
                let inst = func.inst(inst_idx);
                if let Op::Store(value, _, _, mem) = &inst.op {
                    let replacement_mem = remap_value(value_map, mem.clone().raw().value);
                    value_map.insert(primary_value_ref(inst_idx).raw(), replacement_mem);
                    let stored_value = remap_value(value_map, value.value);
                    undo.push((slice_id, current_slice_values[slice_id]));
                    current_slice_values[slice_id] = Some(stored_value);
                    continue;
                }
            }
            if let Some(&slice_id) = plan.load_to_slice.get(&inst_idx) {
                let replacement = current_slice_values[slice_id]?;
                value_map.insert(primary_value_ref(inst_idx).raw(), replacement);
                continue;
            }
            transform_and_append_instruction(
                func,
                cfg,
                plan,
                promoted_slot_roots,
                phi_slices_by_block,
                required_addr_insts,
                block_map,
                value_map,
                current_slice_values,
                new_func,
                inst_idx,
            )?;
        }

        for child in &cfg.dom_children[block.index() as usize] {
            emit_reachable_subtree(
                func,
                cfg,
                plan,
                promoted_slot_roots,
                phi_slices_by_block,
                required_addr_insts,
                block_map,
                phi_arg_map,
                value_map,
                current_slice_values,
                emitted,
                new_func,
                *child,
            )?;
        }

        while let Some((slice_id, old_value)) = undo.pop() {
            current_slice_values[slice_id] = old_value;
        }
        Some(())
    }

    emit_reachable_subtree(
        func,
        cfg,
        plan,
        &plan.promoted_slots,
        &phi_slices_by_block,
        &required_addr_insts,
        &new_blocks,
        &phi_arg_map,
        &mut value_map,
        &mut current_slice_values,
        &mut emitted,
        &mut new_func,
        func.entry_block(),
    )?;

    for &block in &block_refs {
        if cfg.reachable[block.index() as usize] {
            continue;
        }
        for (value, _) in func.block_insts_with_values(block) {
            let inst_idx = value.index();
            if emitted.contains(&inst_idx) {
                continue;
            }
            transform_and_append_instruction(
                func,
                cfg,
                plan,
                &plan.promoted_slots,
                &phi_slices_by_block,
                &required_addr_insts,
                &new_blocks,
                &mut value_map,
                &mut current_slice_values,
                &mut new_func,
                inst_idx,
            )?;
        }
    }

    Some(new_func)
}

/// Internal helper `promote_function`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub(crate) fn promote_function(func: &mut Function) -> PeepholeStats {
    if has_unwind_cleanup_edges(func) {
        return PeepholeStats::default();
    }
    let cfg = CfgInfo::compute(func);
    let plan = collect_promotion_plan(func, &cfg);
    if plan.slices.is_empty() {
        return PeepholeStats::default();
    }

    let mut phi_slices_by_block = vec![Vec::<usize>::new(); func.blocks.len()];
    for (slice_id, slice) in plan.slices.iter().enumerate() {
        for block in &slice.phi_blocks {
            phi_slices_by_block[block.index() as usize].push(slice_id);
        }
    }
    if phi_slices_by_block
        .iter()
        .enumerate()
        .any(|(block_idx, slices)| {
            !slices.is_empty()
                && cfg.preds[block_idx]
                    .iter()
                    .any(|pred| !cfg.reachable[pred.index() as usize])
        })
    {
        return PeepholeStats::default();
    }

    let Some(mut new_func) = build_transformed_function(func, &cfg, &plan) else {
        return PeepholeStats::default();
    };
    let stats = PeepholeStats {
        promoted_slots: plan.slots.len(),
        promoted_slices: plan.slices.len(),
        promoted_loads: plan.load_to_slice.len(),
        eliminated_stores: plan.store_to_slice.len(),
        ..PeepholeStats::default()
    };
    new_func.rebuild_use_lists();
    *func = new_func;
    stats
}
