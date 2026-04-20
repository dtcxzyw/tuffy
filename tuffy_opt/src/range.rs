//! Legacy range-analysis-based compare and branch folding for Tuffy IR.

use std::collections::{HashMap, VecDeque};

use num_bigint::BigInt;
use tuffy_ir::function::{BlockArg, Function};
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Operand, Origin};
use tuffy_ir::types::{Annotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use crate::cfg::{CfgInfo, collect_block_refs};
use crate::peephole::PeepholeStats;

/// Maximum fixpoint rounds when repeatedly simplifying one function.
const MAX_SIMPLIFY_ITERATIONS: usize = 16;
/// Maximum times a block entry fact set may widen before falling back to annotations.
const MAX_BLOCK_ENV_UPDATES: usize = 256;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Integer range facts tracked in both signed and unsigned domains.
struct IntRange {
    /// Whether this lattice element is known to be impossible.
    is_bottom: bool,
    /// Proven signed lower bound, when available.
    signed_min: Option<BigInt>,
    /// Proven signed upper bound, when available.
    signed_max: Option<BigInt>,
    /// Proven unsigned lower bound, when available.
    unsigned_min: Option<BigInt>,
    /// Proven unsigned upper bound, when available.
    unsigned_max: Option<BigInt>,
}

/// Per-value range facts keyed by raw SSA value index.
type FactMap = HashMap<u32, IntRange>;

#[derive(Clone)]
/// Forward dataflow result storing block-entry range environments.
struct RangeAnalysis {
    /// Entry facts for each block after merging predecessor flows.
    entry: Vec<Option<FactMap>>,
}

/// Run the legacy range pass until no compare or branch folding opportunity remains.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    let mut stats = PeepholeStats::default();

    for _ in 0..MAX_SIMPLIFY_ITERATIONS {
        let analysis = RangeAnalysis::compute(func);
        let mut changed = false;
        for block in collect_block_refs(func) {
            let Some(mut current_env) = analysis.entry_env(block).cloned() else {
                continue;
            };
            seed_block_args(func, block, &mut current_env);
            for (value, inst) in func.block_insts_with_values(block) {
                match &inst.op {
                    Op::ICmp(op, lhs, rhs) => {
                        let lhs = lhs.clone().raw();
                        let rhs = rhs.clone().raw();
                        if let Some(result) = evaluate_icmp(func, &current_env, *op, &lhs, &rhs) {
                            rewrite_icmp_to_const(func, value.index(), result);
                            func.rebuild_use_lists();
                            stats.record("range_fold_icmp");
                            changed = true;
                            break;
                        }
                    }
                    Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
                        let cond_value = cond.clone().raw().value;
                        if let Some(result) = evaluate_bool(func, &current_env, cond_value) {
                            rewrite_brif_to_br(
                                func,
                                value.index(),
                                if result { *then_block } else { *else_block },
                                if result {
                                    then_args.clone()
                                } else {
                                    else_args.clone()
                                },
                                inst.origin.clone(),
                            );
                            func.rebuild_use_lists();
                            cleanup_dead_value(func, cond_value);
                            func.rebuild_use_lists();
                            stats.record("range_fold_brif");
                            changed = true;
                            break;
                        }
                    }
                    _ => {}
                }
                if let Some(range) = transfer_inst(func, &current_env, inst) {
                    if !range.is_unknown() {
                        current_env.insert(value.raw(), range);
                    } else {
                        current_env.remove(&value.raw());
                    }
                }
            }
            if changed {
                break;
            }
        }
        if !changed {
            break;
        }
    }

    stats
}

impl RangeAnalysis {
    /// Compute block-entry range environments with forward propagation over the CFG.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn compute(func: &Function) -> Self {
        let cfg = CfgInfo::compute(func);
        let mut entry = vec![None; func.blocks.len()];
        let mut update_counts = vec![0usize; func.blocks.len()];
        let mut worklist = VecDeque::new();
        let entry_block = func.entry_block();
        entry[entry_block.index() as usize] = Some(FactMap::new());
        worklist.push_back(entry_block);

        while let Some(block) = worklist.pop_front() {
            let Some(mut env) = entry[block.index() as usize].clone() else {
                continue;
            };
            seed_block_args(func, block, &mut env);
            let mut current_env = env;
            for (value, inst) in func.block_insts_with_values(block) {
                if let Some(range) = transfer_inst(func, &current_env, inst) {
                    if !range.is_unknown() {
                        current_env.insert(value.raw(), range);
                    } else {
                        current_env.remove(&value.raw());
                    }
                }
            }

            let Some(last_idx) = func.block(block).last_inst else {
                continue;
            };
            let term = func.inst(last_idx);
            for (target, succ_env) in successor_envs(func, &cfg, block, &current_env, term) {
                let target_idx = target.index() as usize;
                let changed = match &mut entry[target_idx] {
                    slot @ None => {
                        *slot = Some(succ_env);
                        true
                    }
                    Some(existing) => merge_env(existing, &succ_env),
                };
                if changed {
                    update_counts[target_idx] = update_counts[target_idx].saturating_add(1);
                    if update_counts[target_idx] > MAX_BLOCK_ENV_UPDATES {
                        // If the edge facts keep widening, fall back to annotation-derived facts
                        // so the pass stays terminating and conservative.
                        entry[target_idx] = Some(annotation_only_env(func, target));
                    }
                    worklist.push_back(target);
                }
            }
        }

        Self { entry }
    }

    /// Return the propagated entry environment for `block`, if the block is reachable.
    fn entry_env(&self, block: BlockRef) -> Option<&FactMap> {
        self.entry[block.index() as usize].as_ref()
    }
}

/// Seed a block environment from block-argument annotations when propagation has not
/// already produced a tighter fact.
fn seed_block_args(func: &Function, block: BlockRef, env: &mut FactMap) {
    for (arg_ref, block_arg) in func
        .block_arg_values(block)
        .into_iter()
        .zip(func.block_args(block).iter())
    {
        if !matches!(block_arg.ty, Type::Int) {
            continue;
        }
        if env.contains_key(&arg_ref.raw()) {
            continue;
        }
        if let Some(range) = range_from_block_arg(block_arg)
            && !range.is_unknown()
        {
            env.insert(arg_ref.raw(), range);
        }
    }
}

/// Compute successor-specific environments for the current terminator.
fn successor_envs(
    func: &Function,
    cfg: &CfgInfo,
    block: BlockRef,
    env: &FactMap,
    term: &Instruction,
) -> Vec<(BlockRef, FactMap)> {
    match &term.op {
        Op::Br(target, args) => vec![(*target, successor_env(func, env, *target, args, None))],
        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            let cond_value = cond.clone().raw().value;
            let then_refine = branch_refinement(func, cond_value, true);
            let else_refine = branch_refinement(func, cond_value, false);
            vec![
                (
                    *then_block,
                    successor_env(func, env, *then_block, then_args, then_refine),
                ),
                (
                    *else_block,
                    successor_env(func, env, *else_block, else_args, else_refine),
                ),
            ]
        }
        Op::Continue(args) => {
            let Some(header) = cfg.loop_header[block.index() as usize] else {
                return Vec::new();
            };
            vec![(header, successor_env(func, env, header, args, None))]
        }
        _ => Vec::new(),
    }
}

/// Apply edge refinements and branch arguments to the environment entering `target`.
fn successor_env(
    func: &Function,
    env: &FactMap,
    target: BlockRef,
    args: &[Operand],
    refinement: Option<(ValueRef, IntRange)>,
) -> FactMap {
    let mut next = env.clone();
    if let Some((value, range)) = refinement {
        if range.is_bottom {
            return HashMap::new();
        }
        if range.is_unknown() {
            next.remove(&value.raw());
        } else {
            next.insert(value.raw(), range);
        }
    }

    for (arg_ref, operand) in func.block_arg_values(target).into_iter().zip(args.iter()) {
        if !matches!(func.value_type(arg_ref), Some(Type::Int)) {
            continue;
        }
        if let Some(range) = operand_range(func, &next, operand) {
            if !range.is_unknown() {
                next.insert(arg_ref.raw(), range);
            } else {
                next.remove(&arg_ref.raw());
            }
        } else {
            next.remove(&arg_ref.raw());
        }
    }
    next
}

/// Join incoming predecessor facts into an existing block-entry environment.
fn merge_env(existing: &mut FactMap, incoming: &FactMap) -> bool {
    let original = existing.clone();
    if original.is_empty() {
        *existing = incoming.clone();
        return *existing != original;
    }

    let keys = original
        .keys()
        .chain(incoming.keys())
        .copied()
        .collect::<std::collections::HashSet<_>>();
    let mut merged = FactMap::new();
    for key in keys {
        let Some(lhs) = original.get(&key) else {
            continue;
        };
        let Some(rhs) = incoming.get(&key) else {
            continue;
        };
        let joined = lhs.join(rhs);
        if !joined.is_unknown() {
            merged.insert(key, joined);
        }
    }
    let changed = merged != original;
    *existing = merged;
    changed
}

/// Compute the range fact defined by `inst` when the instruction is transparent to this pass.
fn transfer_inst(func: &Function, env: &FactMap, inst: &Instruction) -> Option<IntRange> {
    if !matches!(inst.ty, Type::Int) {
        return None;
    }
    let _ = env;
    let mut range = match &inst.op {
        Op::Const(value) => IntRange::exact(value.clone()),
        Op::Param(index) => func
            .param_annotations
            .get(*index as usize)
            .and_then(|ann| ann.as_ref())
            .and_then(range_from_annotation)
            .unwrap_or_default(),
        _ => return None,
    };

    if let Some(annotation) = &inst.result_annotation {
        range = range.intersect(&range_from_annotation(annotation)?);
    }
    Some(range)
}

#[allow(dead_code)]
/// Approximate multiplication when at least one operand is a known integer constant.
fn mul_range(func: &Function, env: &FactMap, lhs: &Operand, rhs: &Operand) -> Option<IntRange> {
    let lhs_const = bound_int_constant(func, lhs.value);
    let rhs_const = bound_int_constant(func, rhs.value);
    match (lhs_const, rhs_const) {
        (Some(constant), None) => {
            operand_range(func, env, rhs).map(|range| range.mul_const(constant))
        }
        (None, Some(constant)) => {
            operand_range(func, env, lhs).map(|range| range.mul_const(constant))
        }
        (Some(lhs), Some(rhs)) => Some(IntRange::exact(lhs * rhs)),
        (None, None) => None,
    }
}

#[allow(dead_code)]
/// Approximate bitwise-and against a non-negative mask.
fn and_range(func: &Function, _env: &FactMap, lhs: &Operand, rhs: &Operand) -> Option<IntRange> {
    let lhs_const = bound_int_constant(func, lhs.value);
    let rhs_const = bound_int_constant(func, rhs.value);
    let mask = lhs_const.or(rhs_const)?;
    if mask.sign() == num_bigint::Sign::Minus {
        return None;
    }
    let max = mask.clone();
    Some(IntRange {
        is_bottom: false,
        signed_min: Some(BigInt::from(0u8)),
        signed_max: Some(max.clone()),
        unsigned_min: Some(BigInt::from(0u8)),
        unsigned_max: Some(max),
    })
}

/// Refine one compared operand along a specific branch edge when the other side is constant.
fn branch_refinement(
    func: &Function,
    cond_value: ValueRef,
    when_true: bool,
) -> Option<(ValueRef, IntRange)> {
    let (cmp_op, lhs, rhs, invert) = decode_condition(func, cond_value)?;
    let truth = if invert { !when_true } else { when_true };
    let lhs_operand = lhs.clone().raw();
    let rhs_operand = rhs.clone().raw();
    let lhs_range = range_from_operand_annotation_or_def(func, &lhs_operand)?;
    let rhs_range = range_from_operand_annotation_or_def(func, &rhs_operand)?;

    if let Some(constant) = bound_int_constant(func, rhs_operand.value) {
        let refined = refine_compare(lhs_range, cmp_op, constant.clone(), truth)?;
        return Some((lhs_operand.value, refined));
    }
    if let Some(constant) = bound_int_constant(func, lhs_operand.value) {
        let flipped = flip_cmp(cmp_op);
        let refined = refine_compare(rhs_range, flipped, constant.clone(), truth)?;
        return Some((rhs_operand.value, refined));
    }
    None
}

/// Normalize a boolean condition into an integer comparison plus an optional inversion.
fn decode_condition(
    func: &Function,
    value: ValueRef,
) -> Option<(
    ICmpOp,
    tuffy_ir::typed::IntOperand,
    tuffy_ir::typed::IntOperand,
    bool,
)> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let inst = func.inst(value.index());
    match &inst.op {
        Op::ICmp(op, lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            // Fold integer encodings of booleans back to the underlying comparison so edge
            // refinement reasons about the original domain instead of the `{0, 1}` wrapper.
            if let Some(constant) = bound_int_constant(func, rhs_value)
                && let Some(decoded) = decode_intified_bool_compare(func, *op, lhs_value, constant)
            {
                Some(decoded)
            } else if let Some(constant) = bound_int_constant(func, lhs_value)
                && let Some(decoded) =
                    decode_intified_bool_compare(func, flip_cmp(*op), rhs_value, constant)
            {
                Some(decoded)
            } else {
                Some((*op, lhs.clone(), rhs.clone(), false))
            }
        }
        Op::BXor(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if bound_bool_constant(func, lhs_value) == Some(true) {
                let (op, l, r, invert) = decode_condition(func, rhs_value)?;
                Some((op, l, r, !invert))
            } else if bound_bool_constant(func, rhs_value) == Some(true) {
                let (op, l, r, invert) = decode_condition(func, lhs_value)?;
                Some((op, l, r, !invert))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recover the source comparison from `icmp` against `0` or `1` on an intified boolean.
fn decode_intified_bool_compare(
    func: &Function,
    pred: ICmpOp,
    intified_value: ValueRef,
    compare_const: &BigInt,
) -> Option<(
    ICmpOp,
    tuffy_ir::typed::IntOperand,
    tuffy_ir::typed::IntOperand,
    bool,
)> {
    let compare_zero = *compare_const == BigInt::from(0u8);
    let compare_one = *compare_const == BigInt::from(1u8);
    if !compare_zero && !compare_one {
        return None;
    }
    let (source_value, mut invert) = decode_intified_bool(func, intified_value)?;
    invert ^= match pred {
        ICmpOp::Eq if compare_zero => true,
        ICmpOp::Eq if compare_one => false,
        ICmpOp::Ne if compare_zero => false,
        ICmpOp::Ne if compare_one => true,
        _ => return None,
    };
    let (cmp_op, lhs, rhs, source_invert) = decode_condition(func, source_value)?;
    Some((cmp_op, lhs, rhs, invert ^ source_invert))
}

/// Peel common integer encodings of booleans back to the source condition.
fn decode_intified_bool(func: &Function, value: ValueRef) -> Option<(ValueRef, bool)> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::Select(cond, true_value, false_value) => {
            let true_const = bound_int_constant(func, true_value.value)?;
            let false_const = bound_int_constant(func, false_value.value)?;
            if *true_const == BigInt::from(1u8) && *false_const == BigInt::from(0u8) {
                Some((cond.clone().raw().value, false))
            } else if *true_const == BigInt::from(0u8) && *false_const == BigInt::from(1u8) {
                Some((cond.clone().raw().value, true))
            } else {
                None
            }
        }
        Op::And(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if bound_int_constant(func, lhs_value).is_some_and(is_non_negative_odd_int) {
                decode_intified_bool(func, rhs_value)
            } else if bound_int_constant(func, rhs_value).is_some_and(is_non_negative_odd_int) {
                decode_intified_bool(func, lhs_value)
            } else {
                None
            }
        }
        Op::Xor(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if bound_int_constant(func, lhs_value) == Some(&BigInt::from(1u8)) {
                let (cond, invert) = decode_intified_bool(func, rhs_value)?;
                Some((cond, !invert))
            } else if bound_int_constant(func, rhs_value) == Some(&BigInt::from(1u8)) {
                let (cond, invert) = decode_intified_bool(func, lhs_value)?;
                Some((cond, !invert))
            } else {
                None
            }
        }
        _ if matches!(func.value_type(value), Some(Type::Bool)) => Some((value, false)),
        _ => None,
    }
}

/// Evaluate a boolean value when current facts make it constant.
fn evaluate_bool(func: &Function, env: &FactMap, value: ValueRef) -> Option<bool> {
    if let Some(value) = bound_bool_constant(func, value) {
        return Some(value);
    }
    let (cmp_op, lhs, rhs, invert) = decode_condition(func, value)?;
    let result = evaluate_icmp(func, env, cmp_op, &lhs.raw(), &rhs.raw())?;
    Some(if invert { !result } else { result })
}

/// Evaluate an integer comparison from current operand ranges.
fn evaluate_icmp(
    func: &Function,
    env: &FactMap,
    op: ICmpOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<bool> {
    let lhs_range = operand_range(func, env, lhs)?;
    let rhs_range = operand_range(func, env, rhs)?;
    let lhs_min = lhs_range.math_min()?;
    let lhs_max = lhs_range.math_max()?;
    let rhs_min = rhs_range.math_min()?;
    let rhs_max = rhs_range.math_max()?;

    match op {
        ICmpOp::Eq => {
            if lhs_min == lhs_max && rhs_min == rhs_max {
                Some(lhs_min == rhs_min)
            } else if lhs_max < rhs_min || rhs_max < lhs_min {
                Some(false)
            } else {
                None
            }
        }
        ICmpOp::Ne => {
            if lhs_min == lhs_max && rhs_min == rhs_max {
                Some(lhs_min != rhs_min)
            } else if lhs_max < rhs_min || rhs_max < lhs_min {
                Some(true)
            } else {
                None
            }
        }
        ICmpOp::Lt => {
            if lhs_max < rhs_min {
                Some(true)
            } else if lhs_min >= rhs_max {
                Some(false)
            } else {
                None
            }
        }
        ICmpOp::Le => {
            if lhs_max <= rhs_min {
                Some(true)
            } else if lhs_min > rhs_max {
                Some(false)
            } else {
                None
            }
        }
        ICmpOp::Gt => {
            if lhs_min > rhs_max {
                Some(true)
            } else if lhs_max <= rhs_min {
                Some(false)
            } else {
                None
            }
        }
        ICmpOp::Ge => {
            if lhs_min >= rhs_max {
                Some(true)
            } else if lhs_max < rhs_min {
                Some(false)
            } else {
                None
            }
        }
    }
}

/// Intersect `current` with the constraint implied by a comparison's truth value.
fn refine_compare(
    mut current: IntRange,
    op: ICmpOp,
    constant: BigInt,
    truth: bool,
) -> Option<IntRange> {
    let one = BigInt::from(1u8);
    match (op, truth) {
        (ICmpOp::Eq, true) => current = current.intersect(&IntRange::exact(constant)),
        (ICmpOp::Eq, false) => {
            if current.is_exact(&constant) {
                current = IntRange::bottom();
            }
        }
        (ICmpOp::Ne, true) => {
            if current.is_exact(&constant) {
                current = IntRange::bottom();
            }
        }
        (ICmpOp::Ne, false) => current = current.intersect(&IntRange::exact(constant)),
        (ICmpOp::Lt, true) => current.refine_math_upper(constant - &one),
        (ICmpOp::Lt, false) => current.refine_math_lower(constant),
        (ICmpOp::Le, true) => current.refine_math_upper(constant),
        (ICmpOp::Le, false) => current.refine_math_lower(constant + &one),
        (ICmpOp::Gt, true) => current.refine_math_lower(constant + &one),
        (ICmpOp::Gt, false) => current.refine_math_upper(constant),
        (ICmpOp::Ge, true) => current.refine_math_lower(constant),
        (ICmpOp::Ge, false) => current.refine_math_upper(constant - &one),
    }
    (!current.is_bottom).then_some(current)
}

/// Flip a comparison when moving the constant operand from left to right.
fn flip_cmp(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Eq => ICmpOp::Eq,
        ICmpOp::Ne => ICmpOp::Ne,
        ICmpOp::Lt => ICmpOp::Gt,
        ICmpOp::Le => ICmpOp::Ge,
        ICmpOp::Gt => ICmpOp::Lt,
        ICmpOp::Ge => ICmpOp::Le,
    }
}

/// Resolve the best known range for an operand from propagated facts, constants, or annotations.
fn operand_range(func: &Function, env: &FactMap, operand: &Operand) -> Option<IntRange> {
    if let Some(range) = env.get(&operand.value.raw()) {
        let mut range = range.clone();
        if let Some(annotation) = &operand.annotation {
            range = range.intersect(&range_from_annotation(annotation)?);
        }
        return Some(range);
    }

    if let Some(constant) = bound_int_constant(func, operand.value) {
        let mut range = IntRange::exact(constant.clone());
        if let Some(annotation) = &operand.annotation {
            range = range.intersect(&range_from_annotation(annotation)?);
        }
        return Some(range);
    }

    range_from_operand_annotation_or_def(func, operand)
}

/// Read the range implied by an operand annotation or its defining value annotation.
fn range_from_operand_annotation_or_def(func: &Function, operand: &Operand) -> Option<IntRange> {
    if let Some(annotation) = &operand.annotation {
        return range_from_annotation(annotation);
    }
    if operand.value.is_block_arg() {
        let block_arg = func.block_args.get(operand.value.index() as usize)?;
        return block_arg
            .annotation
            .as_ref()
            .and_then(range_from_annotation);
    }
    if operand.value.is_secondary_result() {
        let node = func.inst_pool.get(operand.value.inst_index())?;
        return node
            .inst
            .secondary_result_annotation
            .as_ref()
            .and_then(range_from_annotation);
    }
    let node = func.inst_pool.get(operand.value.index())?;
    node.inst
        .result_annotation
        .as_ref()
        .and_then(range_from_annotation)
}

/// Convert a block-argument annotation into an `IntRange`.
fn range_from_block_arg(block_arg: &BlockArg) -> Option<IntRange> {
    block_arg
        .annotation
        .as_ref()
        .and_then(range_from_annotation)
}

/// Convert an integer annotation into the corresponding signed and unsigned bounds.
fn range_from_annotation(annotation: &Annotation) -> Option<IntRange> {
    let Annotation::Int(ann) = annotation else {
        return None;
    };
    let mut range = IntRange::default();
    match ann.signedness {
        IntSignedness::Unsigned | IntSignedness::DontCare => {
            range.unsigned_min = Some(BigInt::from(0u8));
            range.unsigned_max = Some((BigInt::from(1u8) << ann.bit_width) - BigInt::from(1u8));
            range.signed_min = Some(BigInt::from(0u8));
            range.signed_max = range.unsigned_max.clone();
        }
        IntSignedness::Signed => {
            let bound = BigInt::from(1u8) << (ann.bit_width.saturating_sub(1));
            range.signed_min = Some(-bound.clone());
            range.signed_max = Some(bound - BigInt::from(1u8));
        }
    }
    Some(range)
}

/// Return the payload of an integer constant result.
fn bound_int_constant(func: &Function, value: ValueRef) -> Option<&BigInt> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::Const(int) = &node.inst.op else {
        return None;
    };
    Some(int)
}

/// Return the payload of a boolean constant result.
fn bound_bool_constant(func: &Function, value: ValueRef) -> Option<bool> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::BConst(value) = &node.inst.op else {
        return None;
    };
    Some(*value)
}

/// Report whether `value` is a non-negative odd integer mask.
fn is_non_negative_odd_int(value: &BigInt) -> bool {
    value.sign() != num_bigint::Sign::Minus && (value & BigInt::from(1u8)) == BigInt::from(1u8)
}

/// Replace an `icmp` instruction with a boolean constant result.
fn rewrite_icmp_to_const(func: &mut Function, root_idx: u32, value: bool) {
    let origin = func.inst(root_idx).origin.clone();
    let new_idx = func.insert_inst_before(
        root_idx,
        Instruction {
            op: Op::BConst(value),
            ty: Type::Bool,
            secondary_ty: None,
            origin,
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );
    func.replace_all_uses(
        ValueRef::inst_result(root_idx),
        ValueRef::inst_result(new_idx),
    );
    let _ = func.remove_inst(root_idx);
}

/// Rewrite a conditional branch to an unconditional branch to the chosen successor.
fn rewrite_brif_to_br(
    func: &mut Function,
    root_idx: u32,
    target: BlockRef,
    args: Vec<Operand>,
    origin: Origin,
) {
    let _ = func.insert_inst_before(
        root_idx,
        Instruction {
            op: Op::Br(target, args),
            ty: Type::Unit,
            secondary_ty: None,
            origin,
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );
    let _ = func.remove_inst(root_idx);
}

/// Recursively remove dead pure producers exposed by a rewrite.
fn cleanup_dead_value(func: &mut Function, value: ValueRef) {
    if value.is_block_arg() || value.is_secondary_result() || func.has_uses(value) {
        return;
    }
    let Some(node) = func.inst_pool.get(value.index()) else {
        return;
    };
    if !is_cleanup_pure_op(&node.inst.op) {
        return;
    }
    let deps = node.inst.op.value_refs();
    func.remove_inst(value.index());
    for dep in deps {
        cleanup_dead_value(func, dep);
    }
}

/// Rebuild the conservative environment for `block` from annotations only.
fn annotation_only_env(func: &Function, block: BlockRef) -> FactMap {
    let mut env = FactMap::new();
    seed_block_args(func, block, &mut env);
    env
}

/// Return whether a dead producer can be erased without observable side effects.
fn is_cleanup_pure_op(op: &Op) -> bool {
    matches!(
        op,
        Op::Const(_)
            | Op::BConst(_)
            | Op::And(_, _)
            | Op::Or(_, _)
            | Op::Xor(_, _)
            | Op::BAnd(_, _)
            | Op::BOr(_, _)
            | Op::BXor(_, _)
            | Op::Select(_, _, _)
            | Op::ICmp(_, _, _)
    )
}

impl IntRange {
    /// Return the empty lattice element.
    fn bottom() -> Self {
        Self {
            is_bottom: true,
            ..Self::default()
        }
    }

    /// Return the singleton range containing `value`.
    fn exact(value: BigInt) -> Self {
        Self {
            is_bottom: false,
            signed_min: Some(value.clone()),
            signed_max: Some(value.clone()),
            unsigned_min: (value >= BigInt::from(0u8)).then_some(value.clone()),
            unsigned_max: (value >= BigInt::from(0u8)).then_some(value),
        }
    }

    /// Return whether no useful bounds are currently known.
    fn is_unknown(&self) -> bool {
        !self.is_bottom
            && self.signed_min.is_none()
            && self.signed_max.is_none()
            && self.unsigned_min.is_none()
            && self.unsigned_max.is_none()
    }

    /// Return whether the range is exactly `value`.
    fn is_exact(&self, value: &BigInt) -> bool {
        self.signed_min.as_ref() == Some(value) && self.signed_max.as_ref() == Some(value)
    }

    /// Join two predecessor facts by widening each known bound.
    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }
        Self {
            is_bottom: false,
            signed_min: match (&self.signed_min, &other.signed_min) {
                (Some(lhs), Some(rhs)) => Some(lhs.min(rhs).clone()),
                _ => None,
            },
            signed_max: match (&self.signed_max, &other.signed_max) {
                (Some(lhs), Some(rhs)) => Some(lhs.max(rhs).clone()),
                _ => None,
            },
            unsigned_min: match (&self.unsigned_min, &other.unsigned_min) {
                (Some(lhs), Some(rhs)) => Some(lhs.min(rhs).clone()),
                _ => None,
            },
            unsigned_max: match (&self.unsigned_max, &other.unsigned_max) {
                (Some(lhs), Some(rhs)) => Some(lhs.max(rhs).clone()),
                _ => None,
            },
        }
    }

    /// Intersect two range facts and detect contradictory bounds.
    fn intersect(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        let mut result = Self {
            is_bottom: false,
            signed_min: max_bound(&self.signed_min, &other.signed_min),
            signed_max: min_bound(&self.signed_max, &other.signed_max),
            unsigned_min: max_bound(&self.unsigned_min, &other.unsigned_min),
            unsigned_max: min_bound(&self.unsigned_max, &other.unsigned_max),
        };
        // Each domain is intersected independently; any contradiction in either domain means the
        // value set is empty.
        if result
            .signed_min
            .as_ref()
            .zip(result.signed_max.as_ref())
            .is_some_and(|(lo, hi)| lo > hi)
            || result
                .unsigned_min
                .as_ref()
                .zip(result.unsigned_max.as_ref())
                .is_some_and(|(lo, hi)| lo > hi)
        {
            result.is_bottom = true;
        }
        result
    }

    #[allow(dead_code)]
    /// Add two ranges conservatively using endpoint arithmetic.
    fn add(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        Self {
            is_bottom: false,
            signed_min: add_opt(&self.signed_min, &other.signed_min),
            signed_max: add_opt(&self.signed_max, &other.signed_max),
            unsigned_min: add_opt(&self.unsigned_min, &other.unsigned_min),
            unsigned_max: add_opt(&self.unsigned_max, &other.unsigned_max),
        }
    }

    #[allow(dead_code)]
    /// Subtract two ranges conservatively using endpoint arithmetic.
    fn sub(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        Self {
            is_bottom: false,
            signed_min: sub_opt(&self.signed_min, &other.signed_max),
            signed_max: sub_opt(&self.signed_max, &other.signed_min),
            unsigned_min: sub_opt(&self.unsigned_min, &other.unsigned_max),
            unsigned_max: sub_opt(&self.unsigned_max, &other.unsigned_min),
        }
    }

    #[allow(dead_code)]
    /// Multiply the range by a known constant.
    fn mul_const(&self, constant: &BigInt) -> Self {
        if self.is_bottom {
            return Self::bottom();
        }
        if constant == &BigInt::from(0u8) {
            return Self::exact(BigInt::from(0u8));
        }
        let signed_candidates =
            self.signed_min
                .as_ref()
                .zip(self.signed_max.as_ref())
                .map(|(lo, hi)| {
                    let a = lo * constant;
                    let b = hi * constant;
                    if a <= b { (a, b) } else { (b, a) }
                });
        let unsigned_candidates = if constant >= &BigInt::from(0u8) {
            self.unsigned_min
                .as_ref()
                .zip(self.unsigned_max.as_ref())
                .map(|(lo, hi)| (lo * constant, hi * constant))
        } else {
            None
        };
        Self {
            is_bottom: false,
            signed_min: signed_candidates.as_ref().map(|(lo, _)| lo.clone()),
            signed_max: signed_candidates.as_ref().map(|(_, hi)| hi.clone()),
            unsigned_min: unsigned_candidates.as_ref().map(|(lo, _)| lo.clone()),
            unsigned_max: unsigned_candidates.as_ref().map(|(_, hi)| hi.clone()),
        }
    }

    /// Return the best available arithmetic lower bound regardless of signedness.
    fn math_min(&self) -> Option<&BigInt> {
        self.signed_min.as_ref().or(self.unsigned_min.as_ref())
    }

    /// Return the best available arithmetic upper bound regardless of signedness.
    fn math_max(&self) -> Option<&BigInt> {
        self.signed_max.as_ref().or(self.unsigned_max.as_ref())
    }

    /// Tighten the arithmetic lower bound and the unsigned domain when that remains valid.
    fn refine_math_lower(&mut self, lower: BigInt) {
        self.signed_min = max_bound(&self.signed_min, &Some(lower.clone()));
        if lower >= BigInt::from(0u8) {
            self.unsigned_min = max_bound(&self.unsigned_min, &Some(lower));
        }
        if self
            .math_min()
            .zip(self.math_max())
            .is_some_and(|(lo, hi)| lo > hi)
        {
            *self = Self::bottom();
        }
    }

    /// Tighten the arithmetic upper bound and drop unsigned facts when the bound goes negative.
    fn refine_math_upper(&mut self, upper: BigInt) {
        self.signed_max = min_bound(&self.signed_max, &Some(upper.clone()));
        if upper >= BigInt::from(0u8) {
            self.unsigned_max = min_bound(&self.unsigned_max, &Some(upper));
        } else {
            if self.unsigned_min.is_some() {
                // Unsigned facts cannot survive a negative upper bound.
                *self = Self::bottom();
            }
        }
        if self
            .math_min()
            .zip(self.math_max())
            .is_some_and(|(lo, hi)| lo > hi)
        {
            *self = Self::bottom();
        }
    }
}

/// Return the larger of two optional lower bounds.
fn max_bound(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.max(rhs).clone()),
        (Some(lhs), None) => Some(lhs.clone()),
        (None, Some(rhs)) => Some(rhs.clone()),
        (None, None) => None,
    }
}

/// Return the smaller of two optional upper bounds.
fn min_bound(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs).clone()),
        (Some(lhs), None) => Some(lhs.clone()),
        (None, Some(rhs)) => Some(rhs.clone()),
        (None, None) => None,
    }
}

#[allow(dead_code)]
/// Add two optional bounds when both are known.
fn add_opt(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    Some(lhs.as_ref()? + rhs.as_ref()?)
}

#[allow(dead_code)]
/// Subtract two optional bounds when both are known.
fn sub_opt(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    Some(lhs.as_ref()? - rhs.as_ref()?)
}
