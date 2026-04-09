use std::collections::{BTreeSet, HashMap};

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{Instruction, Op, Operand, Origin};
use tuffy_ir::module::{Module, SymbolId};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use crate::peephole::PeepholeStats;

const MIN_BULK_MEMORY_BYTES: usize = 32;

#[derive(Clone)]
struct StaticInfo {
    data: Vec<u8>,
    relocations: Vec<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RootKind {
    StackSlot,
    Symbol(SymbolId),
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct PtrExpr {
    root: ValueRef,
    offset: i64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SourcePattern {
    FillZero,
    CopyFrom(PtrExpr),
}

#[derive(Clone)]
struct StorePattern {
    store_idx: u32,
    mem_in: ValueRef,
    mem_out: ValueRef,
    size: u32,
    dst: PtrExpr,
    src: SourcePattern,
    matched: BTreeSet<u32>,
}

#[derive(Clone)]
enum BulkOpKind {
    MemCopy { src_root: ValueRef },
    MemSetZero,
}

#[derive(Clone)]
struct BulkCandidate {
    block: BlockRef,
    first_store: u32,
    last_store: u32,
    mem_in: ValueRef,
    mem_out: ValueRef,
    dst_root: ValueRef,
    total_bytes: usize,
    op_kind: BulkOpKind,
    matched: BTreeSet<u32>,
    load_indices: Vec<u32>,
    store_indices: Vec<u32>,
}

pub(crate) fn optimize_module(
    module: &mut Module,
    changed_functions: Option<&[bool]>,
) -> PeepholeStats {
    let mut stats = PeepholeStats::default();
    let static_data = build_static_map(module);

    for (idx, func) in module.functions.iter_mut().enumerate() {
        if changed_functions.is_some_and(|flags| !flags[idx]) {
            continue;
        }
        while let Some(candidate) = find_candidate(func, &static_data) {
            let rule_name = if matches!(candidate.op_kind, BulkOpKind::MemSetZero) {
                "form_bulk_memset_zero"
            } else {
                "form_bulk_memcopy"
            };
            apply_candidate(func, candidate);
            stats.record(rule_name);
        }
    }

    stats
}

fn build_static_map(module: &Module) -> HashMap<SymbolId, StaticInfo> {
    module
        .static_data
        .iter()
        .map(|data| {
            (
                data.name,
                StaticInfo {
                    data: data.data.clone(),
                    relocations: data.relocations.iter().map(|reloc| reloc.offset).collect(),
                },
            )
        })
        .collect()
}

fn find_candidate(
    func: &Function,
    static_data: &HashMap<SymbolId, StaticInfo>,
) -> Option<BulkCandidate> {
    for block in collect_block_refs(func) {
        let insts = func
            .block_insts_with_values(block)
            .map(|(value, _)| value.index())
            .collect::<Vec<_>>();

        for &inst_idx in &insts {
            let Some(pattern) = parse_store_pattern(func, inst_idx) else {
                continue;
            };
            let Some(mut candidate) = start_candidate(func, pattern) else {
                continue;
            };
            candidate.block = block;

            let mut previous = candidate.last_store;
            let mut next_expected_dst = candidate.total_bytes as i64;
            let mut next_expected_src = match candidate.op_kind {
                BulkOpKind::MemCopy { .. } => Some(candidate.total_bytes as i64),
                BulkOpKind::MemSetZero => None,
            };

            let mut cursor = insts
                .iter()
                .position(|&idx| idx == previous)
                .expect("candidate store should be in block");
            while let Some(&next_idx) = insts.get(cursor + 1) {
                cursor += 1;
                let Some(pattern) = parse_store_pattern(func, next_idx) else {
                    continue;
                };
                if pattern.mem_in != previous_value(previous) {
                    continue;
                }

                if pattern.dst.root != candidate.dst_root || pattern.dst.offset != next_expected_dst
                {
                    break;
                }

                match (&candidate.op_kind, pattern.src) {
                    (BulkOpKind::MemSetZero, SourcePattern::FillZero) => {}
                    (BulkOpKind::MemCopy { src_root }, SourcePattern::CopyFrom(src))
                        if src.root == *src_root && Some(src.offset) == next_expected_src => {}
                    _ => break,
                }

                if has_external_mem_uses(func, previous, next_idx) {
                    break;
                }

                candidate.last_store = next_idx;
                candidate.mem_out = pattern.mem_out;
                candidate.total_bytes += pattern.size as usize;
                candidate.matched.extend(pattern.matched);
                candidate.store_indices.push(pattern.store_idx);
                if let Some(load_idx) = load_index_for_store(func, pattern.store_idx) {
                    candidate.load_indices.push(load_idx);
                }

                previous = next_idx;
                next_expected_dst += i64::from(pattern.size);
                if let Some(expected_src) = &mut next_expected_src {
                    *expected_src += i64::from(pattern.size);
                }
            }

            if candidate.total_bytes < MIN_BULK_MEMORY_BYTES {
                continue;
            }
            if let BulkOpKind::MemCopy { src_root } = candidate.op_kind
                && let RootKind::Symbol(sym) = root_kind(func, src_root)
                && static_range_is_zero(static_data.get(&sym), 0, candidate.total_bytes)
            {
                candidate.op_kind = BulkOpKind::MemSetZero;
            }
            return Some(candidate);
        }
    }
    None
}

fn previous_value(store_idx: u32) -> ValueRef {
    ValueRef::inst_result(store_idx)
}

fn has_external_mem_uses(func: &Function, store_idx: u32, next_store_idx: u32) -> bool {
    let produced = ValueRef::inst_result(store_idx);
    for use_node in func.uses_of(produced) {
        if use_node.user == next_store_idx {
            continue;
        }
        let user = func.inst(use_node.user);
        let is_load_use = matches!(user.op, Op::Load(_, _, _)) && use_node.operand_index == 1;
        if !is_load_use {
            return true;
        }
    }
    false
}

fn start_candidate(func: &Function, pattern: StorePattern) -> Option<BulkCandidate> {
    if pattern.dst.offset != 0 {
        return None;
    }
    if root_kind(func, pattern.dst.root) != RootKind::StackSlot {
        return None;
    }

    let op_kind = match pattern.src {
        SourcePattern::FillZero => BulkOpKind::MemSetZero,
        SourcePattern::CopyFrom(src) => {
            if src.offset != 0 {
                return None;
            }
            match root_kind(func, src.root) {
                RootKind::StackSlot if src.root != pattern.dst.root => {
                    BulkOpKind::MemCopy { src_root: src.root }
                }
                RootKind::Symbol(_sym) => BulkOpKind::MemCopy { src_root: src.root },
                _ => return None,
            }
        }
    };

    let load_indices = load_index_for_store(func, pattern.store_idx)
        .into_iter()
        .collect();

    Some(BulkCandidate {
        block: func.inst_node(pattern.store_idx).parent_block,
        first_store: pattern.store_idx,
        last_store: pattern.store_idx,
        mem_in: pattern.mem_in,
        mem_out: pattern.mem_out,
        dst_root: pattern.dst.root,
        total_bytes: pattern.size as usize,
        op_kind,
        matched: pattern.matched,
        load_indices,
        store_indices: vec![pattern.store_idx],
    })
}

fn static_range_is_zero(info: Option<&StaticInfo>, start: usize, len: usize) -> bool {
    let Some(info) = info else {
        return false;
    };
    let end = start.saturating_add(len);
    if end > info.data.len() {
        return false;
    }
    if info
        .relocations
        .iter()
        .any(|&offset| (start..end).contains(&offset))
    {
        return false;
    }
    info.data[start..end].iter().all(|&byte| byte == 0)
}

fn load_index_for_store(func: &Function, store_idx: u32) -> Option<u32> {
    let Op::Store(value, _, _, _) = &func.inst(store_idx).op else {
        return None;
    };
    if value.value.is_block_arg() || value.value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.value.index())?;
    matches!(node.inst.op, Op::Load(_, _, _)).then_some(value.value.index())
}

fn parse_store_pattern(func: &Function, store_idx: u32) -> Option<StorePattern> {
    let inst = func.inst_pool.get(store_idx)?;
    let Op::Store(value, ptr, size, mem) = &inst.inst.op else {
        return None;
    };
    if *size == 0 {
        return None;
    }

    let mut matched = BTreeSet::new();
    matched.insert(store_idx);
    let dst = ptr_expr(func, ptr.clone().raw().value, &mut matched)?;
    let src = parse_store_source(func, value, *size, &mut matched)?;

    Some(StorePattern {
        store_idx,
        mem_in: mem.clone().raw().value,
        mem_out: ValueRef::inst_result(store_idx),
        size: *size,
        dst,
        src,
        matched,
    })
}

fn collect_block_refs(func: &Function) -> Vec<BlockRef> {
    let mut refs = vec![None; func.blocks.len()];
    for region in &func.regions {
        for child in &region.children {
            if let tuffy_ir::function::CfgNode::Block(block) = child {
                refs[block.index() as usize] = Some(*block);
            }
        }
    }
    refs.into_iter()
        .map(|block| block.expect("every block should appear in a region"))
        .collect()
}

fn parse_store_source(
    func: &Function,
    value: &Operand,
    store_size: u32,
    matched: &mut BTreeSet<u32>,
) -> Option<SourcePattern> {
    if let Some(constant) = const_bigint(func, value.value) {
        if *constant == BigInt::from(0u8) {
            if !value.value.is_block_arg() && !value.value.is_secondary_result() {
                matched.insert(value.value.index());
            }
            return Some(SourcePattern::FillZero);
        }
        return None;
    }

    if value.value.is_block_arg() || value.value.is_secondary_result() {
        return None;
    }
    let load_idx = value.value.index();
    let load_inst = func.inst_pool.get(load_idx)?;
    let Op::Load(ptr, size, _mem) = &load_inst.inst.op else {
        return None;
    };
    if *size != store_size || func.use_count(value.value) != 1 {
        return None;
    }
    matched.insert(load_idx);
    let src = ptr_expr(func, ptr.clone().raw().value, matched)?;
    Some(SourcePattern::CopyFrom(src))
}

fn ptr_expr(func: &Function, value: ValueRef, matched: &mut BTreeSet<u32>) -> Option<PtrExpr> {
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
            let mut base_expr = ptr_expr(func, base.clone().raw().value, matched)?;
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

fn root_kind(func: &Function, value: ValueRef) -> RootKind {
    if value.is_block_arg() || value.is_secondary_result() {
        return RootKind::Other;
    }
    match &func.inst(value.index()).op {
        Op::StackSlot(_, _) => RootKind::StackSlot,
        Op::SymbolAddr(sym) => RootKind::Symbol(*sym),
        _ => RootKind::Other,
    }
}

fn const_i64(func: &Function, value: ValueRef) -> Option<i64> {
    const_bigint(func, value)?.to_string().parse().ok()
}

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

fn apply_candidate(func: &mut Function, candidate: BulkCandidate) {
    let mut matched = candidate.matched.clone();
    let count_idx = func.insert_inst_before(
        candidate.first_store,
        Instruction {
            op: Op::Const(BigInt::from(candidate.total_bytes)),
            ty: Type::Int,
            secondary_ty: None,
            origin: merged_origin(func, candidate.first_store, &matched),
            result_annotation: Some(Annotation::Int(IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Unsigned,
            })),
            secondary_result_annotation: None,
        },
    );
    let count_value = ValueRef::inst_result(count_idx);

    let mem_op = match candidate.op_kind {
        BulkOpKind::MemCopy { src_root } => Op::MemCopy(
            candidate.dst_root.into(),
            src_root.into(),
            count_value.into(),
            candidate.mem_in.into(),
        ),
        BulkOpKind::MemSetZero => {
            let zero_idx = func.insert_inst_before(
                candidate.first_store,
                Instruction {
                    op: Op::Const(BigInt::from(0u8)),
                    ty: Type::Int,
                    secondary_ty: None,
                    origin: merged_origin(func, candidate.first_store, &matched),
                    result_annotation: Some(Annotation::Int(IntAnnotation {
                        bit_width: 8,
                        signedness: IntSignedness::Unsigned,
                    })),
                    secondary_result_annotation: None,
                },
            );
            Op::MemSet(
                candidate.dst_root.into(),
                Operand::new(ValueRef::inst_result(zero_idx)),
                count_value.into(),
                candidate.mem_in.into(),
            )
        }
    };

    let mem_idx = func.insert_inst_before(
        candidate.first_store,
        Instruction {
            op: mem_op,
            ty: Type::Mem,
            secondary_ty: None,
            origin: merged_origin(func, candidate.first_store, &matched),
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );
    let replacement_mem = ValueRef::inst_result(mem_idx);
    func.replace_all_uses(candidate.mem_out, replacement_mem);

    let mut removal_order = candidate
        .store_indices
        .iter()
        .chain(candidate.load_indices.iter())
        .copied()
        .collect::<Vec<_>>();
    removal_order.sort_unstable_by(|lhs, rhs| rhs.cmp(lhs));
    for idx in removal_order {
        let _ = func.remove_inst(idx);
    }

    matched.retain(|idx| {
        !candidate.store_indices.contains(idx)
            && !candidate.load_indices.contains(idx)
            && *idx != mem_idx
            && *idx != count_idx
    });
    cleanup_dead_instructions(func, &matched);
    func.rebuild_use_lists();
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
            func.remove_inst(idx);
            changed = true;
        }
        if !changed {
            break;
        }
    }
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
