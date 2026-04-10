use std::collections::{HashMap, VecDeque};

use num_bigint::{BigInt, BigUint, Sign};
use tuffy_ir::function::{BlockArg, Function};
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Operand, Origin};
use tuffy_ir::typed::{BoolOperand, IntOperand, MemOperand};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, KnownBits, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use crate::cfg::{CfgInfo, collect_block_refs};
use crate::peephole::PeepholeStats;

const MAX_SIMPLIFY_ITERATIONS: usize = 16;
const MAX_BLOCK_ENV_UPDATES: usize = 256;

type FactMap = HashMap<u32, AtUseFacts>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AtUseTransformKind {
    FoldIcmp,
    FoldBrIf,
    StrengthenOperand,
    StrengthenResult,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct AtUseTransformDescriptor {
    name: &'static str,
    kind: AtUseTransformKind,
    proof_ref: &'static str,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AtUseFacts {
    is_bottom: bool,
    known_zero: BigUint,
    known_one: BigUint,
    demanded: BigUint,
    signed_min: Option<BigInt>,
    signed_max: Option<BigInt>,
    unsigned_min: Option<BigInt>,
    unsigned_max: Option<BigInt>,
    dontcare_width_upper_bound: Option<u32>,
}

#[derive(Clone)]
struct AtUseAnalysis {
    entry: Vec<Option<FactMap>>,
}

pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    if function_is_pointer_sensitive(func) {
        return PeepholeStats::default();
    }
    optimize_with_generated_transforms(func, GENERATED_AT_USE_TRANSFORMS)
}

fn function_is_pointer_sensitive(func: &Function) -> bool {
    func.params.iter().any(|ty| matches!(ty, Type::Ptr(_)))
        || func
            .block_args
            .iter()
            .any(|arg| matches!(arg.ty, Type::Ptr(_)))
        || func.inst_pool.iter_insts().any(|(_, inst)| {
            matches!(inst.ty, Type::Ptr(_))
                || inst
                    .secondary_ty
                    .as_ref()
                    .is_some_and(|ty| matches!(ty, Type::Ptr(_)))
                || matches!(
                    inst.op,
                    Op::Call(..)
                        | Op::CallRet2(..)
                        | Op::StackSlot(..)
                        | Op::Load(..)
                        | Op::Store(..)
                        | Op::MemCopy(..)
                        | Op::MemMove(..)
                        | Op::MemSet(..)
                        | Op::LoadAtomic(..)
                        | Op::StoreAtomic(..)
                        | Op::AtomicRmw(..)
                        | Op::AtomicCmpXchg(..)
                        | Op::Fence(..)
                        | Op::SymbolAddr(..)
                        | Op::PtrAdd(..)
                        | Op::PtrDiff(..)
                        | Op::PtrToInt(..)
                        | Op::PtrToAddr(..)
                        | Op::IntToPtr(..)
                        | Op::LandingPad
                )
        })
}

fn optimize_with_generated_transforms(
    func: &mut Function,
    transforms: &[AtUseTransformDescriptor],
) -> PeepholeStats {
    let mut stats = PeepholeStats::default();

    for _ in 0..MAX_SIMPLIFY_ITERATIONS {
        let analysis = AtUseAnalysis::compute(func);
        let mut changed = false;

        'blocks: for block in collect_block_refs(func) {
            let Some(mut current_env) = analysis.entry_env(block).cloned() else {
                continue;
            };
            seed_block_args(func, block, &mut current_env);

            let block_insts: Vec<_> = func
                .block_insts_with_values(block)
                .map(|(value, inst)| (value, inst.clone()))
                .collect();
            for (value, inst) in block_insts {
                for transform in transforms {
                    let _ = transform.proof_ref;
                    let applied = match transform.kind {
                        AtUseTransformKind::FoldIcmp => {
                            try_fold_icmp(func, &current_env, value, &inst, &mut stats, transform)
                        }
                        AtUseTransformKind::FoldBrIf => {
                            try_fold_brif(func, &current_env, value, &inst, &mut stats, transform)
                        }
                        AtUseTransformKind::StrengthenOperand => try_strengthen_operands(
                            func,
                            &current_env,
                            value,
                            &inst,
                            &mut stats,
                            transform,
                        ),
                        AtUseTransformKind::StrengthenResult => try_strengthen_result(
                            func,
                            &current_env,
                            value,
                            &inst,
                            &mut stats,
                            transform,
                        ),
                    };
                    if applied {
                        changed = true;
                        break 'blocks;
                    }
                }

                if let Some(facts) = transfer_inst(func, &current_env, value, &inst) {
                    if !facts.is_unknown() {
                        current_env.insert(value.raw(), facts);
                    } else {
                        current_env.remove(&value.raw());
                    }
                }
            }
        }

        if !changed {
            break;
        }
    }

    stats
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use super::{function_is_pointer_sensitive, optimize_function};
    use tuffy_ir::parser::parse_module;

    fn parse_single_function(input: &str) -> tuffy_ir::function::Function {
        let module = parse_module(input).unwrap_or_else(|err| panic!("parse error: {err}"));
        module
            .functions
            .into_iter()
            .next()
            .expect("module should contain one function")
    }

    #[test]
    fn detects_pointer_sensitive_functions() {
        let func = parse_single_function(
            r#"
func @ptr_sensitive(ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int = ptrtoaddr v1
    v3: int = iconst 0
    v4: bool = icmp.eq v2, v3
    brif v4, bb1(v0), bb2(v0)
  bb1(v5: mem):
    ret v5
  bb2(v6: mem):
    ret v6
}
"#,
        );
        assert!(function_is_pointer_sensitive(&func));
    }

    #[test]
    fn skips_pointer_sensitive_at_use_optimization() {
        let mut func = parse_single_function(
            r#"
func @ptr_sensitive(ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int = ptrtoaddr v1
    v3: int = iconst 0
    v4: bool = icmp.eq v2, v3
    brif v4, bb1(v0), bb2(v0)
  bb1(v5: mem):
    ret v5
  bb2(v6: mem):
    ret v6
}
"#,
        );
        let stats = optimize_function(&mut func);
        assert_eq!(stats.rewrites, 0);
    }
}

impl AtUseAnalysis {
    fn compute(func: &Function) -> Self {
        let cfg = CfgInfo::compute(func);
        let mut entry = vec![None; func.blocks.len()];
        let mut update_counts = vec![0usize; func.blocks.len()];
        let mut worklist = VecDeque::new();
        let entry_block = func.entry_block();
        entry[entry_block.index() as usize] = Some(FactMap::new());
        worklist.push_back(entry_block);

        while let Some(block) = worklist.pop_front() {
            let Some(mut current_env) = entry[block.index() as usize].clone() else {
                continue;
            };
            seed_block_args(func, block, &mut current_env);
            for (value, inst) in func.block_insts_with_values(block) {
                if let Some(facts) = transfer_inst(func, &current_env, value, inst) {
                    if !facts.is_unknown() {
                        current_env.insert(value.raw(), facts);
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
                        entry[target_idx] = Some(annotation_only_env(func, target));
                    }
                    worklist.push_back(target);
                }
            }
        }

        Self { entry }
    }

    fn entry_env(&self, block: BlockRef) -> Option<&FactMap> {
        self.entry[block.index() as usize].as_ref()
    }
}

fn seed_block_args(func: &Function, block: BlockRef, env: &mut FactMap) {
    for (arg_ref, block_arg) in func
        .block_arg_values(block)
        .into_iter()
        .zip(func.block_args(block).iter())
    {
        if !matches!(block_arg.ty, Type::Int) || env.contains_key(&arg_ref.raw()) {
            continue;
        }
        if let Some(facts) = facts_from_block_arg(block_arg)
            && !facts.is_unknown()
        {
            env.insert(arg_ref.raw(), facts);
        }
    }
}

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

fn successor_env(
    func: &Function,
    env: &FactMap,
    target: BlockRef,
    args: &[Operand],
    refinement: Option<(ValueRef, AtUseFacts)>,
) -> FactMap {
    let mut next = env.clone();
    if let Some((value, facts)) = refinement {
        if facts.is_bottom {
            return HashMap::new();
        }
        if facts.is_unknown() {
            next.remove(&value.raw());
        } else {
            next.insert(value.raw(), facts);
        }
    }

    for (arg_ref, operand) in func.block_arg_values(target).into_iter().zip(args.iter()) {
        if !matches!(func.value_type(arg_ref), Some(Type::Int)) {
            continue;
        }
        if let Some(facts) = operand_facts(func, &next, operand) {
            if !facts.is_unknown() {
                next.insert(arg_ref.raw(), facts);
            } else {
                next.remove(&arg_ref.raw());
            }
        } else {
            next.remove(&arg_ref.raw());
        }
    }
    next
}

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

fn try_fold_icmp(
    func: &mut Function,
    env: &FactMap,
    value: ValueRef,
    inst: &Instruction,
    stats: &mut PeepholeStats,
    transform: &AtUseTransformDescriptor,
) -> bool {
    let Op::ICmp(op, lhs, rhs) = &inst.op else {
        return false;
    };
    let lhs = lhs.clone().raw();
    let rhs = rhs.clone().raw();
    let Some(result) = evaluate_icmp(func, env, *op, &lhs, &rhs) else {
        return false;
    };
    rewrite_icmp_to_const(func, value.index(), result);
    func.rebuild_use_lists();
    stats.record(transform.name);
    true
}

fn try_fold_brif(
    func: &mut Function,
    env: &FactMap,
    value: ValueRef,
    inst: &Instruction,
    stats: &mut PeepholeStats,
    transform: &AtUseTransformDescriptor,
) -> bool {
    let Op::BrIf(cond, then_block, then_args, else_block, else_args) = &inst.op else {
        return false;
    };
    let cond_value = cond.clone().raw().value;
    let Some(result) = evaluate_bool(func, env, cond_value) else {
        return false;
    };
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
    stats.record(transform.name);
    true
}

fn try_strengthen_result(
    func: &mut Function,
    env: &FactMap,
    value: ValueRef,
    inst: &Instruction,
    stats: &mut PeepholeStats,
    transform: &AtUseTransformDescriptor,
) -> bool {
    if !matches!(inst.ty, Type::Int) {
        return false;
    }
    let Some(facts) = transfer_inst(func, env, value, inst) else {
        return false;
    };
    let Some(candidate) = materialize_result_annotation(inst.result_annotation.as_ref(), &facts)
    else {
        return false;
    };
    let slot = &mut func.inst_pool.inst_mut(value.index()).result_annotation;
    if slot.as_ref() == Some(&candidate) {
        return false;
    }
    *slot = Some(candidate);
    stats.record(transform.name);
    true
}

fn try_strengthen_operands(
    func: &mut Function,
    env: &FactMap,
    value: ValueRef,
    inst: &Instruction,
    stats: &mut PeepholeStats,
    transform: &AtUseTransformDescriptor,
) -> bool {
    let mut changed = false;
    let mut new_op = inst.op.clone();
    match &inst.op {
        Op::ICmp(pred, lhs, rhs) => {
            let old_lhs = lhs.clone().raw();
            let old_rhs = rhs.clone().raw();
            let new_lhs = strengthen_operand_from_env(func, env, &old_lhs);
            let new_rhs = strengthen_operand_from_env(func, env, &old_rhs);
            changed |= new_lhs.annotation != old_lhs.annotation;
            changed |= new_rhs.annotation != old_rhs.annotation;
            if changed {
                new_op = Op::ICmp(*pred, IntOperand::from(new_lhs), IntOperand::from(new_rhs));
            }
        }
        Op::Select(cond, tv, fv) => {
            let new_tv = strengthen_operand_from_env(func, env, tv);
            let new_fv = strengthen_operand_from_env(func, env, fv);
            changed |= new_tv.annotation != tv.annotation;
            changed |= new_fv.annotation != fv.annotation;
            if changed {
                new_op = Op::Select(cond.clone(), new_tv, new_fv);
            }
        }
        Op::Ret(val, ret2, mem) => {
            let new_val = val
                .as_ref()
                .map(|operand| strengthen_operand_from_env(func, env, operand));
            let new_ret2 = ret2
                .as_ref()
                .map(|operand| strengthen_operand_from_env(func, env, operand));
            changed |= new_val
                .as_ref()
                .zip(val.as_ref())
                .is_some_and(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            changed |= new_ret2
                .as_ref()
                .zip(ret2.as_ref())
                .is_some_and(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            if changed {
                new_op = Op::Ret(new_val, new_ret2, MemOperand::from(mem.clone().raw()));
            }
        }
        Op::Br(target, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|operand| strengthen_operand_from_env(func, env, operand))
                .collect();
            changed |= new_args
                .iter()
                .zip(args.iter())
                .any(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            if changed {
                new_op = Op::Br(*target, new_args);
            }
        }
        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            let cond_value = cond.clone().raw().value;
            let then_env = branch_refined_env(func, env, cond_value, true);
            let else_env = branch_refined_env(func, env, cond_value, false);
            let new_then_args: Vec<_> = then_args
                .iter()
                .map(|operand| strengthen_operand_from_env(func, &then_env, operand))
                .collect();
            let new_else_args: Vec<_> = else_args
                .iter()
                .map(|operand| strengthen_operand_from_env(func, &else_env, operand))
                .collect();
            changed |= new_then_args
                .iter()
                .zip(then_args.iter())
                .any(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            changed |= new_else_args
                .iter()
                .zip(else_args.iter())
                .any(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            if changed {
                new_op = Op::BrIf(
                    BoolOperand::from(cond.clone().raw()),
                    *then_block,
                    new_then_args,
                    *else_block,
                    new_else_args,
                );
            }
        }
        Op::Continue(args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|operand| strengthen_operand_from_env(func, env, operand))
                .collect();
            changed |= new_args
                .iter()
                .zip(args.iter())
                .any(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            if changed {
                new_op = Op::Continue(new_args);
            }
        }
        Op::RegionYield(args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|operand| strengthen_operand_from_env(func, env, operand))
                .collect();
            changed |= new_args
                .iter()
                .zip(args.iter())
                .any(|(lhs, rhs)| lhs.annotation != rhs.annotation);
            if changed {
                new_op = Op::RegionYield(new_args);
            }
        }
        _ => {}
    }

    if !changed {
        return false;
    }

    func.inst_pool.inst_mut(value.index()).op = new_op;
    stats.record(transform.name);
    true
}

fn branch_refined_env(
    func: &Function,
    env: &FactMap,
    cond_value: ValueRef,
    when_true: bool,
) -> FactMap {
    let mut next = env.clone();
    if let Some((value, facts)) = branch_refinement(func, cond_value, when_true) {
        if facts.is_bottom {
            return HashMap::new();
        }
        if facts.is_unknown() {
            next.remove(&value.raw());
        } else {
            next.insert(value.raw(), facts);
        }
    }
    next
}

fn strengthen_operand_from_env(func: &Function, env: &FactMap, operand: &Operand) -> Operand {
    let Some(facts) = operand_facts(func, env, operand) else {
        return operand.clone();
    };
    let Some(candidate) = materialize_operand_annotation(operand.annotation.as_ref(), &facts)
    else {
        return operand.clone();
    };
    if operand.annotation.as_ref() == Some(&candidate) {
        return operand.clone();
    }
    Operand {
        value: operand.value,
        annotation: Some(candidate),
    }
}

fn materialize_result_annotation(
    current: Option<&Annotation>,
    facts: &AtUseFacts,
) -> Option<Annotation> {
    match current {
        Some(Annotation::Int(int_ann)) => {
            let candidate = facts.best_int_annotation()?;
            (annotation_rank(candidate) < annotation_rank(*int_ann))
                .then_some(Annotation::Int(candidate))
        }
        Some(Annotation::KnownBits(known)) => {
            let candidate = facts.materialize_known_bits()?;
            known_bits_stricter(&candidate, known).then_some(Annotation::KnownBits(candidate))
        }
        _ => None,
    }
}

fn materialize_operand_annotation(
    current: Option<&Annotation>,
    facts: &AtUseFacts,
) -> Option<Annotation> {
    if let Some(Annotation::KnownBits(current_known)) = current
        && let Some(candidate) = facts.materialize_known_bits()
        && known_bits_stricter(&candidate, current_known)
    {
        return Some(Annotation::KnownBits(candidate));
    }

    if let Some(Annotation::Int(current_int)) = current {
        if let Some(candidate) = facts.best_int_annotation()
            && annotation_rank(candidate) < annotation_rank(*current_int)
        {
            return Some(Annotation::Int(candidate));
        }
        return None;
    }

    if let Some(candidate) = facts.best_int_annotation() {
        return Some(Annotation::Int(candidate));
    }
    facts.materialize_known_bits().map(Annotation::KnownBits)
}

fn known_bits_stricter(candidate: &KnownBits, current: &KnownBits) -> bool {
    let current_known = &current.ones | &current.zeros;
    let candidate_known = &candidate.ones | &candidate.zeros;
    candidate.demanded != current.demanded
        || ((&candidate_known & &current_known) == current_known
            && candidate_known != current_known)
}

fn annotation_rank(annotation: IntAnnotation) -> (u32, u8) {
    let signedness_rank = match annotation.signedness {
        IntSignedness::Unsigned => 0,
        IntSignedness::Signed => 1,
        IntSignedness::DontCare => 2,
    };
    (annotation.bit_width, signedness_rank)
}

fn transfer_inst(
    func: &Function,
    env: &FactMap,
    value: ValueRef,
    inst: &Instruction,
) -> Option<AtUseFacts> {
    if !matches!(inst.ty, Type::Int) {
        return None;
    }

    let mut facts = match &inst.op {
        Op::Param(index) => func
            .param_annotations
            .get(*index as usize)
            .and_then(|ann| ann.as_ref())
            .map(AtUseFacts::from_annotation)
            .unwrap_or_else(AtUseFacts::unknown),
        _ => generated_forward_at_use_facts(func, value, env).unwrap_or_else(AtUseFacts::unknown),
    };

    if let Op::Const(value) = &inst.op {
        facts = AtUseFacts::exact(value.clone());
    }
    if let Some(annotation) = &inst.result_annotation {
        let _ = facts.meet_with(&AtUseFacts::from_annotation(annotation));
    }
    Some(facts)
}

fn operand_facts(func: &Function, env: &FactMap, operand: &Operand) -> Option<AtUseFacts> {
    if !matches!(func.value_type(operand.value), Some(Type::Int)) {
        return None;
    }

    let mut facts = env
        .get(&operand.value.raw())
        .cloned()
        .or_else(|| facts_from_operand_annotation_or_def(func, operand))
        .unwrap_or_else(AtUseFacts::unknown);

    if let Some(annotation) = &operand.annotation {
        let _ = facts.meet_with(&AtUseFacts::from_annotation(annotation));
    }
    Some(facts)
}

fn facts_from_operand_annotation_or_def(func: &Function, operand: &Operand) -> Option<AtUseFacts> {
    if let Some(annotation) = &operand.annotation {
        return Some(AtUseFacts::from_annotation(annotation));
    }
    if let Some(constant) = bound_int_constant(func, operand.value) {
        return Some(AtUseFacts::exact(constant.clone()));
    }
    if operand.value.is_block_arg() {
        let block_arg = func.block_args.get(operand.value.index() as usize)?;
        return facts_from_block_arg(block_arg);
    }
    if operand.value.is_secondary_result() {
        let node = func.inst_pool.get(operand.value.inst_index())?;
        return node
            .inst
            .secondary_result_annotation
            .as_ref()
            .map(AtUseFacts::from_annotation);
    }
    let node = func.inst_pool.get(operand.value.index())?;
    if let Op::Param(index) = &node.inst.op {
        return func
            .param_annotations
            .get(*index as usize)
            .and_then(|ann| ann.as_ref())
            .map(AtUseFacts::from_annotation)
            .or_else(|| {
                node.inst
                    .result_annotation
                    .as_ref()
                    .map(AtUseFacts::from_annotation)
            });
    }
    node.inst
        .result_annotation
        .as_ref()
        .map(AtUseFacts::from_annotation)
}

fn facts_from_block_arg(block_arg: &BlockArg) -> Option<AtUseFacts> {
    block_arg
        .annotation
        .as_ref()
        .map(AtUseFacts::from_annotation)
}

fn forward_unknown() -> AtUseFacts {
    AtUseFacts::unknown()
}

fn forward_const(value: &BigInt) -> AtUseFacts {
    AtUseFacts::exact(value.clone())
}

fn forward_select(
    func: &Function,
    current: &FactMap,
    true_value: &Operand,
    false_value: &Operand,
) -> AtUseFacts {
    let lhs = operand_facts(func, current, true_value).unwrap_or_else(AtUseFacts::unknown);
    let rhs = operand_facts(func, current, false_value).unwrap_or_else(AtUseFacts::unknown);
    lhs.join(&rhs)
}

fn forward_bitand(func: &Function, current: &FactMap, lhs: &Operand, rhs: &Operand) -> AtUseFacts {
    let lhs_facts = operand_facts(func, current, lhs).unwrap_or_else(AtUseFacts::unknown);
    let rhs_facts = operand_facts(func, current, rhs).unwrap_or_else(AtUseFacts::unknown);
    let mut facts = AtUseFacts::unknown();
    facts.known_zero = &lhs_facts.known_zero | &rhs_facts.known_zero;
    facts.known_one = &lhs_facts.known_one & &rhs_facts.known_one;
    facts.normalize();

    if let Some(range) = and_facts(func, current, lhs, rhs) {
        let _ = facts.meet_with(&range);
    }
    facts
}

fn forward_bitor(func: &Function, current: &FactMap, lhs: &Operand, rhs: &Operand) -> AtUseFacts {
    let lhs_facts = operand_facts(func, current, lhs).unwrap_or_else(AtUseFacts::unknown);
    let rhs_facts = operand_facts(func, current, rhs).unwrap_or_else(AtUseFacts::unknown);
    let mut facts = AtUseFacts::unknown();
    facts.known_zero = &lhs_facts.known_zero & &rhs_facts.known_zero;
    facts.known_one = &lhs_facts.known_one | &rhs_facts.known_one;
    facts.normalize();

    if let (Some(lhs), Some(rhs)) = (lhs_facts.exact_value(), rhs_facts.exact_value()) {
        let _ = facts.meet_with(&AtUseFacts::exact(lhs | rhs));
    }
    facts
}

fn forward_bitxor(func: &Function, current: &FactMap, lhs: &Operand, rhs: &Operand) -> AtUseFacts {
    let lhs_facts = operand_facts(func, current, lhs).unwrap_or_else(AtUseFacts::unknown);
    let rhs_facts = operand_facts(func, current, rhs).unwrap_or_else(AtUseFacts::unknown);
    let mut facts = AtUseFacts::unknown();

    let zero_zero = &lhs_facts.known_zero & &rhs_facts.known_zero;
    let one_one = &lhs_facts.known_one & &rhs_facts.known_one;
    let zero_one = &lhs_facts.known_zero & &rhs_facts.known_one;
    let one_zero = &lhs_facts.known_one & &rhs_facts.known_zero;

    facts.known_zero = &zero_zero | &one_one;
    facts.known_one = &zero_one | &one_zero;
    facts.normalize();

    if let (Some(lhs), Some(rhs)) = (lhs_facts.exact_value(), rhs_facts.exact_value()) {
        let _ = facts.meet_with(&AtUseFacts::exact(lhs ^ rhs));
    }
    facts
}

fn and_facts(func: &Function, env: &FactMap, lhs: &Operand, rhs: &Operand) -> Option<AtUseFacts> {
    let lhs_const = bound_int_constant(func, lhs.value);
    let rhs_const = bound_int_constant(func, rhs.value);
    let mask = lhs_const.or(rhs_const)?;
    if mask.sign() == Sign::Minus {
        return None;
    }
    let operand = if lhs_const.is_some() { rhs } else { lhs };
    let mut facts = operand_facts(func, env, operand).unwrap_or_else(AtUseFacts::unknown);
    facts.signed_min = Some(BigInt::from(0u8));
    facts.unsigned_min = Some(BigInt::from(0u8));
    facts.signed_max = Some(mask.clone());
    facts.unsigned_max = Some(mask.clone());
    Some(facts)
}

fn branch_refinement(
    func: &Function,
    cond_value: ValueRef,
    when_true: bool,
) -> Option<(ValueRef, AtUseFacts)> {
    let (cmp_op, lhs, rhs, invert) = decode_condition(func, cond_value)?;
    let truth = if invert { !when_true } else { when_true };
    let lhs_operand = lhs.clone().raw();
    let rhs_operand = rhs.clone().raw();
    let lhs_facts = facts_from_operand_annotation_or_def(func, &lhs_operand)?;
    let rhs_facts = facts_from_operand_annotation_or_def(func, &rhs_operand)?;

    if let Some(constant) = bound_int_constant(func, rhs_operand.value) {
        let refined = refine_compare(lhs_facts, cmp_op, constant.clone(), truth)?;
        return Some((lhs_operand.value, refined));
    }
    if let Some(constant) = bound_int_constant(func, lhs_operand.value) {
        let flipped = flip_cmp(cmp_op);
        let refined = refine_compare(rhs_facts, flipped, constant.clone(), truth)?;
        return Some((rhs_operand.value, refined));
    }
    None
}

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

fn evaluate_bool(func: &Function, env: &FactMap, value: ValueRef) -> Option<bool> {
    if let Some(value) = bound_bool_constant(func, value) {
        return Some(value);
    }
    let (cmp_op, lhs, rhs, invert) = decode_condition(func, value)?;
    let result = evaluate_icmp(func, env, cmp_op, &lhs.raw(), &rhs.raw())?;
    Some(if invert { !result } else { result })
}

fn evaluate_icmp(
    func: &Function,
    env: &FactMap,
    op: ICmpOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<bool> {
    let lhs_facts = operand_facts(func, env, lhs)?;
    let rhs_facts = operand_facts(func, env, rhs)?;
    let lhs_min = lhs_facts.math_min()?;
    let lhs_max = lhs_facts.math_max()?;
    let rhs_min = rhs_facts.math_min()?;
    let rhs_max = rhs_facts.math_max()?;

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

fn refine_compare(
    mut current: AtUseFacts,
    op: ICmpOp,
    constant: BigInt,
    truth: bool,
) -> Option<AtUseFacts> {
    let one = BigInt::from(1u8);
    match (op, truth) {
        (ICmpOp::Eq, true) => current = current.intersect(&AtUseFacts::exact(constant)),
        (ICmpOp::Eq, false) => {
            if current.is_exact(&constant) {
                current = AtUseFacts::bottom();
            }
        }
        (ICmpOp::Ne, true) => {
            if current.is_exact(&constant) {
                current = AtUseFacts::bottom();
            }
        }
        (ICmpOp::Ne, false) => current = current.intersect(&AtUseFacts::exact(constant)),
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

fn is_non_negative_odd_int(value: &BigInt) -> bool {
    value.sign() != Sign::Minus && (value & BigInt::from(1u8)) == BigInt::from(1u8)
}

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

fn annotation_only_env(func: &Function, block: BlockRef) -> FactMap {
    let mut env = FactMap::new();
    seed_block_args(func, block, &mut env);
    env
}

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

impl AtUseFacts {
    fn unknown() -> Self {
        Self::default()
    }

    fn bottom() -> Self {
        Self {
            is_bottom: true,
            ..Self::default()
        }
    }

    fn exact(value: BigInt) -> Self {
        let mut facts = Self {
            is_bottom: false,
            known_zero: BigUint::default(),
            known_one: BigUint::default(),
            demanded: BigUint::default(),
            signed_min: Some(value.clone()),
            signed_max: Some(value.clone()),
            unsigned_min: (value >= BigInt::from(0u8)).then_some(value.clone()),
            unsigned_max: (value >= BigInt::from(0u8)).then_some(value.clone()),
            dontcare_width_upper_bound: None,
        };
        let width = exact_unsigned_width(&value)
            .or_else(|| Some(exact_signed_width(&value)))
            .unwrap_or(1) as usize;
        for bit in 0..width.max(1) {
            let mask = bit_mask(bit);
            if exact_bit_is_one(&value, bit as u32) {
                facts.known_one |= &mask;
            } else {
                facts.known_zero |= &mask;
            }
            facts.demanded |= mask;
        }
        facts.normalize();
        facts
    }

    fn from_annotation(annotation: &Annotation) -> Self {
        match annotation {
            Annotation::Int(int_ann) => {
                let mut facts = Self::unknown();
                match int_ann.signedness {
                    IntSignedness::Unsigned => {
                        facts.signed_min = Some(BigInt::from(0u8));
                        facts.signed_max =
                            Some((BigInt::from(1u8) << int_ann.bit_width) - BigInt::from(1u8));
                        facts.unsigned_min = Some(BigInt::from(0u8));
                        facts.unsigned_max = facts.signed_max.clone();
                    }
                    IntSignedness::Signed => {
                        let bound = BigInt::from(1u8) << int_ann.bit_width.saturating_sub(1);
                        facts.signed_min = Some(-bound.clone());
                        facts.signed_max = Some(bound - BigInt::from(1u8));
                    }
                    IntSignedness::DontCare => {
                        facts.dontcare_width_upper_bound = Some(int_ann.bit_width);
                    }
                }
                facts.normalize();
                facts
            }
            Annotation::KnownBits(known) => {
                let mut facts = Self {
                    is_bottom: false,
                    known_zero: known.zeros.clone(),
                    known_one: known.ones.clone(),
                    demanded: known.demanded.clone(),
                    signed_min: None,
                    signed_max: None,
                    unsigned_min: None,
                    unsigned_max: None,
                    dontcare_width_upper_bound: None,
                };
                facts.normalize();
                facts
            }
            _ => Self::unknown(),
        }
    }

    fn normalize(&mut self) {
        self.demanded |= &self.known_zero | &self.known_one;
        self.known_zero &= &self.demanded;
        self.known_one &= &self.demanded;
        if (&self.known_zero & &self.known_one) != BigUint::default() {
            *self = Self::bottom();
            return;
        }
        if self
            .signed_min
            .as_ref()
            .zip(self.signed_max.as_ref())
            .is_some_and(|(lo, hi)| lo > hi)
            || self
                .unsigned_min
                .as_ref()
                .zip(self.unsigned_max.as_ref())
                .is_some_and(|(lo, hi)| lo > hi)
        {
            *self = Self::bottom();
        }
    }

    fn meet_with(&mut self, other: &Self) -> bool {
        let original = self.clone();
        if self.is_bottom || other.is_bottom {
            *self = Self::bottom();
            return *self != original;
        }

        self.known_zero |= &other.known_zero;
        self.known_one |= &other.known_one;
        self.demanded |= &other.demanded;
        self.signed_min = max_bound(&self.signed_min, &other.signed_min);
        self.signed_max = min_bound(&self.signed_max, &other.signed_max);
        self.unsigned_min = max_bound(&self.unsigned_min, &other.unsigned_min);
        self.unsigned_max = min_bound(&self.unsigned_max, &other.unsigned_max);
        self.dontcare_width_upper_bound = min_bound_u32(
            self.dontcare_width_upper_bound,
            other.dontcare_width_upper_bound,
        );
        self.normalize();
        *self != original
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }

        let mut facts = Self {
            is_bottom: false,
            known_zero: &self.known_zero & &other.known_zero,
            known_one: &self.known_one & &other.known_one,
            demanded: &self.demanded & &other.demanded,
            signed_min: min_bound(&self.signed_min, &other.signed_min),
            signed_max: max_bound(&self.signed_max, &other.signed_max),
            unsigned_min: min_bound(&self.unsigned_min, &other.unsigned_min),
            unsigned_max: max_bound(&self.unsigned_max, &other.unsigned_max),
            dontcare_width_upper_bound: max_bound_u32(
                self.dontcare_width_upper_bound,
                other.dontcare_width_upper_bound,
            ),
        };
        facts.normalize();
        facts
    }

    fn intersect(&self, other: &Self) -> Self {
        let mut result = self.clone();
        let _ = result.meet_with(other);
        result
    }

    fn is_unknown(&self) -> bool {
        !self.is_bottom
            && self.known_zero == BigUint::default()
            && self.known_one == BigUint::default()
            && self.demanded == BigUint::default()
            && self.signed_min.is_none()
            && self.signed_max.is_none()
            && self.unsigned_min.is_none()
            && self.unsigned_max.is_none()
            && self.dontcare_width_upper_bound.is_none()
    }

    fn is_exact(&self, value: &BigInt) -> bool {
        self.signed_min.as_ref() == Some(value) && self.signed_max.as_ref() == Some(value)
    }

    fn exact_value(&self) -> Option<BigInt> {
        self.signed_min
            .as_ref()
            .zip(self.signed_max.as_ref())
            .filter(|(lo, hi)| lo == hi)
            .map(|(lo, _)| lo.clone())
    }

    fn unsigned_width_upper_bound(&self) -> Option<u32> {
        self.unsigned_max
            .as_ref()
            .map(|max| exact_unsigned_width(max).unwrap_or(1))
    }

    fn signed_width_upper_bound(&self) -> Option<u32> {
        let min = self.signed_min.as_ref()?;
        let max = self.signed_max.as_ref()?;
        Some(bits_for_signed_range(min, max))
    }

    fn best_int_annotation(&self) -> Option<IntAnnotation> {
        if self.is_bottom {
            return None;
        }
        let mut best = self
            .unsigned_width_upper_bound()
            .map(|bit_width| IntAnnotation {
                bit_width,
                signedness: IntSignedness::Unsigned,
            });
        if let Some(bit_width) = self.signed_width_upper_bound() {
            let candidate = IntAnnotation {
                bit_width,
                signedness: IntSignedness::Signed,
            };
            if best.is_none_or(|current| annotation_rank(candidate) < annotation_rank(current)) {
                best = Some(candidate);
            }
        }
        best
    }

    fn materialized_demanded(&self) -> BigUint {
        let mut demanded = self.demanded.clone();
        if let Some(bits) = self.dontcare_width_upper_bound {
            demanded |= low_mask(bits as usize);
        }
        demanded |= &self.known_zero | &self.known_one;
        demanded
    }

    fn materialize_known_bits(&self) -> Option<KnownBits> {
        if self.is_bottom {
            return None;
        }
        let demanded = self.materialized_demanded();
        if demanded == BigUint::default()
            && self.known_zero == BigUint::default()
            && self.known_one == BigUint::default()
        {
            return None;
        }
        Some(KnownBits {
            ones: &self.known_one & &demanded,
            zeros: &self.known_zero & &demanded,
            demanded,
        })
    }

    fn math_min(&self) -> Option<&BigInt> {
        self.signed_min.as_ref().or(self.unsigned_min.as_ref())
    }

    fn math_max(&self) -> Option<&BigInt> {
        self.signed_max.as_ref().or(self.unsigned_max.as_ref())
    }

    fn refine_math_lower(&mut self, lower: BigInt) {
        self.signed_min = max_bound(&self.signed_min, &Some(lower.clone()));
        if lower >= BigInt::from(0u8) {
            self.unsigned_min = max_bound(&self.unsigned_min, &Some(lower));
        }
        self.normalize();
    }

    fn refine_math_upper(&mut self, upper: BigInt) {
        self.signed_max = min_bound(&self.signed_max, &Some(upper.clone()));
        if upper >= BigInt::from(0u8) {
            self.unsigned_max = min_bound(&self.unsigned_max, &Some(upper));
        } else if self.unsigned_min.is_some() {
            *self = Self::bottom();
        }
        self.normalize();
    }
}

fn max_bound(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.max(rhs).clone()),
        (Some(lhs), None) => Some(lhs.clone()),
        (None, Some(rhs)) => Some(rhs.clone()),
        (None, None) => None,
    }
}

fn min_bound(lhs: &Option<BigInt>, rhs: &Option<BigInt>) -> Option<BigInt> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs).clone()),
        (Some(lhs), None) => Some(lhs.clone()),
        (None, Some(rhs)) => Some(rhs.clone()),
        (None, None) => None,
    }
}

fn min_bound_u32(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (None, None) => None,
    }
}

fn max_bound_u32(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.max(rhs)),
        _ => None,
    }
}

fn bit_mask(bit: usize) -> BigUint {
    BigUint::from(1u8) << bit
}

fn low_mask(bits: usize) -> BigUint {
    if bits == 0 {
        BigUint::default()
    } else {
        (BigUint::from(1u8) << bits) - BigUint::from(1u8)
    }
}

fn exact_bit_is_one(value: &BigInt, bit: u32) -> bool {
    let modulus = BigInt::from(1u8) << (bit as usize + 1);
    let truncated = ((value % &modulus) + &modulus) % &modulus;
    let shifted = truncated >> bit as usize;
    (&shifted % BigInt::from(2u8)) != BigInt::from(0u8)
}

fn exact_unsigned_width(value: &BigInt) -> Option<u32> {
    if value.sign() == Sign::Minus {
        None
    } else {
        Some((value.bits() as u32).max(1))
    }
}

fn exact_signed_width(value: &BigInt) -> u32 {
    if value.sign() == Sign::Minus {
        (((-value) - BigInt::from(1u8)).bits() as u32) + 1
    } else {
        (value.bits() as u32).saturating_add(1).max(1)
    }
}

fn bits_for_signed_range(min: &BigInt, max: &BigInt) -> u32 {
    let mut bits = 1u32;
    loop {
        let bound = BigInt::from(1u8) << bits.saturating_sub(1);
        let range_min = -bound.clone();
        let range_max = bound - BigInt::from(1u8);
        if min >= &range_min && max <= &range_max {
            return bits;
        }
        bits = bits.saturating_add(1);
    }
}

include!(concat!(env!("OUT_DIR"), "/at_use_gen.rs"));
