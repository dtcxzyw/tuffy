use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Operand, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::BlockRef;
use tuffy_ir::value::ValueRef;
use tuffy_ir_interp::exec::{
    ExecResult, apply_annotation, apply_result_annotation, execute_instruction,
};
use tuffy_ir_interp::memory::Memory;
use tuffy_ir_interp::value::{AllocId, Value};

const MAX_ITERATIONS: usize = 32;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PeepholeStats {
    pub iterations: usize,
    pub rewrites: usize,
    pub per_rule: BTreeMap<String, usize>,
}

impl PeepholeStats {
    fn record(&mut self, rule_name: &str) {
        self.rewrites += 1;
        *self.per_rule.entry(rule_name.to_string()).or_default() += 1;
    }

    fn merge(&mut self, other: PeepholeStats) {
        self.iterations += other.iterations;
        self.rewrites += other.rewrites;
        for (name, count) in other.per_rule {
            *self.per_rule.entry(name).or_default() += count;
        }
    }
}

pub fn generated_rule_count() -> usize {
    GENERATED_RULE_COUNT
}

pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(optimize_function(func));
    }
    total
}

pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    let mut stats = PeepholeStats::default();
    let mut iterations = 0;

    while iterations < MAX_ITERATIONS {
        iterations += 1;
        let mut changed = false;
        let mut candidates: Vec<u32> = func.inst_pool.iter_insts().map(|(idx, _)| idx).collect();
        candidates.reverse();

        'candidate: for idx in candidates {
            if func.inst_pool.get(idx).is_none() {
                continue;
            }
            if try_apply_generated_rule(func, idx, &mut stats) {
                changed = true;
                break 'candidate;
            }
        }

        if !changed {
            break;
        }
    }

    stats.iterations = iterations;
    stats
}

fn bind_value_slot(slot: &mut Option<ValueRef>, value: ValueRef) -> bool {
    match slot {
        Some(existing) => *existing == value,
        None => {
            *slot = Some(value);
            true
        }
    }
}

fn primary_inst_index(value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        None
    } else {
        Some(value.index())
    }
}

fn bound_int_constant(func: &Function, value: ValueRef) -> Option<&BigInt> {
    let idx = primary_inst_index(value)?;
    let node = func.inst_pool.get(idx)?;
    match &node.inst.op {
        Op::Const(value) => Some(value),
        _ => None,
    }
}

fn bigint_is_odd(value: &BigInt) -> bool {
    let modulus = BigInt::from(2u8);
    (value % &modulus) != BigInt::from(0u8)
}

#[allow(dead_code)]
fn parse_decimal_bigint(value: &str) -> BigInt {
    value
        .parse()
        .unwrap_or_else(|_| panic!("invalid generated bigint literal: {value}"))
}

#[derive(Clone, Copy)]
enum TerminatorOpcode {
    BrIf,
}

struct ReplacementTerminator {
    opcode: TerminatorOpcode,
    operands: Vec<ValueRef>,
    successors: Vec<usize>,
}

#[derive(Clone)]
struct MatchedSuccessor {
    block: BlockRef,
    args: Vec<Operand>,
}

enum ValueRewrite {
    Existing(ValueRef),
    ConstInt(BigInt),
    ConstBool(bool),
}

#[derive(Clone, Copy)]
enum ConstFoldKind {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    BAnd,
    BOr,
    BXor,
    Shl,
    Shr,
    Min,
    Max,
    CountOnes,
    CountLeadingZeros,
    CountTrailingZeros,
    Bswap,
    BitReverse,
    RotateLeft,
    RotateRight,
    Select,
    ICmp(ICmpOp),
}

struct ConstantFoldMatch {
    replacement: ValueRewrite,
    matched_insts: BTreeSet<u32>,
}

fn apply_value_root_rewrite(
    func: &mut Function,
    root_idx: u32,
    replacement: ValueRewrite,
    matched_insts: &BTreeSet<u32>,
) {
    let root_value = ValueRef::inst_result(root_idx);
    let replacement = match replacement {
        ValueRewrite::Existing(value) => {
            if value == root_value {
                return;
            }
            value
        }
        ValueRewrite::ConstInt(value) => {
            let new_inst = build_const_rewrite_instruction(
                func,
                root_idx,
                matched_insts,
                Op::Const(value),
                Type::Int,
            );
            let new_idx = func.insert_inst_before(root_idx, new_inst);
            ValueRef::inst_result(new_idx)
        }
        ValueRewrite::ConstBool(value) => {
            let new_inst = build_const_rewrite_instruction(
                func,
                root_idx,
                matched_insts,
                Op::BConst(value),
                Type::Bool,
            );
            let new_idx = func.insert_inst_before(root_idx, new_inst);
            ValueRef::inst_result(new_idx)
        }
    };
    func.replace_all_uses(root_value, replacement);
    func.remove_inst(root_idx);
    cleanup_dead_instructions(func, matched_insts);
}

fn build_const_rewrite_instruction(
    func: &Function,
    root_idx: u32,
    matched_insts: &BTreeSet<u32>,
    op: Op,
    ty: Type,
) -> Instruction {
    let root_inst = func.inst(root_idx).clone();
    Instruction {
        op,
        ty,
        secondary_ty: None,
        origin: merged_origin(func, root_idx, matched_insts),
        result_annotation: root_inst.result_annotation,
        secondary_result_annotation: None,
    }
}

fn try_fold_constant_root(
    func: &Function,
    root_idx: u32,
    kind: ConstFoldKind,
) -> Option<ConstantFoldMatch> {
    let node = func.inst_pool.get(root_idx)?;
    if !root_matches_const_fold_kind(&node.inst.op, kind) {
        return None;
    }

    let matched_insts = RefCell::new(BTreeSet::new());
    let resolve_value = |value: ValueRef| {
        constant_value_for_fold(func, value, &matched_insts).unwrap_or(Value::Poison)
    };
    let resolve_operand_value = |operand: &Operand| {
        apply_operand_annotation_for_fold(resolve_value(operand.value), &operand.annotation)
    };
    let resolve_symbol = |_symbol| Value::Poison;
    let def_annotation = |value: ValueRef| definition_annotation(func, value);
    let mut memory = Memory::new();
    let mut alloc_stack_slot = |_bytes: usize| AllocId(0);

    let result = execute_instruction(
        &node.inst.op,
        &node.inst.ty,
        &node.inst.result_annotation,
        &node.inst.secondary_ty,
        &node.inst.secondary_result_annotation,
        &resolve_value,
        &resolve_operand_value,
        &mut memory,
        &mut alloc_stack_slot,
        &resolve_symbol,
        &def_annotation,
    )
    .ok()?;

    let replacement = match result {
        ExecResult::Value(Value::Int(value)) => ValueRewrite::ConstInt(value),
        ExecResult::Value(Value::Bool(value)) => ValueRewrite::ConstBool(value),
        _ => return None,
    };

    Some(ConstantFoldMatch {
        replacement,
        matched_insts: matched_insts.into_inner(),
    })
}

fn root_matches_const_fold_kind(op: &Op, kind: ConstFoldKind) -> bool {
    match (kind, op) {
        (ConstFoldKind::Add, Op::Add(_, _))
        | (ConstFoldKind::Sub, Op::Sub(_, _))
        | (ConstFoldKind::Mul, Op::Mul(_, _))
        | (ConstFoldKind::Div, Op::Div(_, _))
        | (ConstFoldKind::Rem, Op::Rem(_, _))
        | (ConstFoldKind::And, Op::And(_, _))
        | (ConstFoldKind::Or, Op::Or(_, _))
        | (ConstFoldKind::Xor, Op::Xor(_, _))
        | (ConstFoldKind::BAnd, Op::BAnd(_, _))
        | (ConstFoldKind::BOr, Op::BOr(_, _))
        | (ConstFoldKind::BXor, Op::BXor(_, _))
        | (ConstFoldKind::Shl, Op::Shl(_, _))
        | (ConstFoldKind::Shr, Op::Shr(_, _))
        | (ConstFoldKind::Min, Op::Min(_, _))
        | (ConstFoldKind::Max, Op::Max(_, _))
        | (ConstFoldKind::CountOnes, Op::CountOnes(_))
        | (ConstFoldKind::CountLeadingZeros, Op::CountLeadingZeros(_, _))
        | (ConstFoldKind::CountTrailingZeros, Op::CountTrailingZeros(_))
        | (ConstFoldKind::Bswap, Op::Bswap(_, _))
        | (ConstFoldKind::BitReverse, Op::BitReverse(_, _))
        | (ConstFoldKind::RotateLeft, Op::RotateLeft(_, _, _))
        | (ConstFoldKind::RotateRight, Op::RotateRight(_, _, _))
        | (ConstFoldKind::Select, Op::Select(_, _, _)) => true,
        (ConstFoldKind::ICmp(expected), Op::ICmp(actual, _, _)) => *actual == expected,
        _ => false,
    }
}

fn constant_value_for_fold(
    func: &Function,
    value: ValueRef,
    matched_insts: &RefCell<BTreeSet<u32>>,
) -> Option<Value> {
    let idx = primary_inst_index(value)?;
    let node = func.inst_pool.get(idx)?;
    let resolved = match &node.inst.op {
        Op::Const(value) => {
            apply_result_annotation(Value::Int(value.clone()), &node.inst.result_annotation)
        }
        Op::BConst(value) => Value::Bool(*value),
        _ => return None,
    };
    matched_insts.borrow_mut().insert(idx);
    Some(resolved)
}

fn apply_operand_annotation_for_fold(value: Value, annotation: &Option<Annotation>) -> Value {
    match (value, annotation) {
        (Value::Poison, _) => Value::Poison,
        (Value::Int(value), Some(Annotation::Int(int_ann))) => apply_annotation(&value, int_ann),
        (value, _) => value,
    }
}

fn definition_annotation(func: &Function, value: ValueRef) -> Option<Annotation> {
    if value.is_block_arg() {
        func.block_args
            .get(value.index() as usize)
            .and_then(|arg| arg.annotation)
    } else if value.is_secondary_result() {
        func.inst_pool
            .get(value.inst_index())
            .and_then(|node| node.inst.secondary_result_annotation)
    } else {
        func.inst_pool
            .get(value.index())
            .and_then(|node| node.inst.result_annotation)
    }
}

fn apply_terminator_root_rewrite(
    func: &mut Function,
    root_idx: u32,
    replacement: ReplacementTerminator,
    matched_insts: &BTreeSet<u32>,
) {
    let old_inst = func.inst(root_idx).clone();
    let mut new_inst = old_inst.clone();
    new_inst.origin = merged_origin(func, root_idx, matched_insts);
    new_inst.op = build_terminator_op(func, &old_inst.op, replacement);
    func.insert_inst_before(root_idx, new_inst);
    func.remove_inst(root_idx);
    cleanup_dead_instructions(func, matched_insts);
}

fn build_terminator_op(func: &Function, root_op: &Op, replacement: ReplacementTerminator) -> Op {
    let matched_successors = extract_matched_successors(root_op);

    match replacement.opcode {
        TerminatorOpcode::BrIf => {
            assert_eq!(
                replacement.operands.len(),
                1,
                "brif replacement expects one condition operand"
            );
            assert_eq!(
                replacement.successors.len(),
                2,
                "brif replacement expects two successor mappings"
            );

            let cond = BoolOperand::from_value(BoolValue::new(replacement.operands[0], func));
            let then_succ = &matched_successors[replacement.successors[0]];
            let else_succ = &matched_successors[replacement.successors[1]];
            Op::BrIf(
                cond,
                then_succ.block,
                then_succ.args.clone(),
                else_succ.block,
                else_succ.args.clone(),
            )
        }
    }
}

fn extract_matched_successors(root_op: &Op) -> Vec<MatchedSuccessor> {
    match root_op {
        Op::BrIf(_, then_block, then_args, else_block, else_args) => vec![
            MatchedSuccessor {
                block: *then_block,
                args: then_args.clone(),
            },
            MatchedSuccessor {
                block: *else_block,
                args: else_args.clone(),
            },
        ],
        other => panic!("unsupported matched terminator root: {other:?}"),
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

fn cleanup_dead_instructions(func: &mut Function, matched_insts: &BTreeSet<u32>) {
    loop {
        let mut changed = false;
        for idx in matched_insts.iter().copied().collect::<Vec<_>>() {
            let Some(inst) = func.inst_pool.get(idx) else {
                continue;
            };
            if !instruction_results_unused(func, idx, inst.inst.secondary_ty.is_some()) {
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

fn instruction_results_unused(func: &Function, idx: u32, has_secondary_result: bool) -> bool {
    if func.has_uses(ValueRef::inst_result(idx)) {
        return false;
    }
    if has_secondary_result && func.has_uses(ValueRef::inst_secondary_result(idx)) {
        return false;
    }
    true
}

include!(concat!(env!("OUT_DIR"), "/peephole_gen.rs"));
