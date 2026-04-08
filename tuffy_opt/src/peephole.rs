use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, Sign};
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Operand, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
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
        let mut fact_cache = IntFactCache::default();
        let mut candidates: Vec<u32> = func.inst_pool.iter_insts().map(|(idx, _)| idx).collect();
        candidates.reverse();

        'candidate: for idx in candidates {
            if func.inst_pool.get(idx).is_none() {
                continue;
            }
            if try_apply_generated_rule(func, idx, &mut stats, &mut fact_cache) {
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

#[allow(dead_code)]
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

#[derive(Clone, Debug, Default)]
struct IntFacts {
    exact_const: Option<BigInt>,
    known_zero: u64,
    known_one: u64,
    unsigned_width_upper_bound: Option<u32>,
    signed_width_upper_bound: Option<u32>,
}

impl IntFacts {
    fn unknown() -> Self {
        Self::default()
    }

    fn from_exact_const(value: &BigInt) -> Self {
        Self {
            exact_const: Some(value.clone()),
            known_zero: !low_bits_u64(value),
            known_one: low_bits_u64(value),
            unsigned_width_upper_bound: exact_unsigned_width(value),
            signed_width_upper_bound: Some(exact_signed_width(value)),
        }
    }

    fn refine_with_annotation(mut self, annotation: &IntAnnotation) -> Self {
        if let Some(value) = &self.exact_const {
            self = match apply_annotation(value, annotation) {
                Value::Int(value) => Self::from_exact_const(&value),
                Value::Poison => Self::unknown(),
                _ => unreachable!("integer annotation should not produce non-int values"),
            };
            return self;
        }

        match annotation.signedness {
            IntSignedness::Signed => {
                self.signed_width_upper_bound =
                    min_bound(self.signed_width_upper_bound, Some(annotation.bit_width));
            }
            IntSignedness::Unsigned | IntSignedness::DontCare => {
                self.unsigned_width_upper_bound =
                    min_bound(self.unsigned_width_upper_bound, Some(annotation.bit_width));
                self.signed_width_upper_bound = min_bound(
                    self.signed_width_upper_bound,
                    Some(annotation.bit_width.saturating_add(1)),
                );
                self.add_known_zero_above(annotation.bit_width);
            }
        }

        self
    }

    fn tighten_from_unsigned(&mut self) {
        if let Some(bits) = self.unsigned_width_upper_bound {
            self.signed_width_upper_bound =
                min_bound(self.signed_width_upper_bound, Some(bits.saturating_add(1)));
            self.add_known_zero_above(bits);
        }
    }

    fn add_known_zero_above(&mut self, bits: u32) {
        if bits >= 64 {
            return;
        }
        let upper_zero_mask = !((1u64 << bits) - 1);
        self.known_zero |= upper_zero_mask;
    }

    fn best_annotation(&self) -> Option<IntAnnotation> {
        let mut best: Option<IntAnnotation> = None;

        if let Some(bit_width) = self.unsigned_width_upper_bound {
            best = Some(IntAnnotation {
                bit_width,
                signedness: IntSignedness::Unsigned,
            });
        }

        if let Some(bit_width) = self.signed_width_upper_bound {
            let candidate = IntAnnotation {
                bit_width,
                signedness: IntSignedness::Signed,
            };
            let should_replace = match best {
                Some(current) => annotation_rank(candidate) < annotation_rank(current),
                None => true,
            };
            if should_replace {
                best = Some(candidate);
            }
        }

        best
    }
}

#[derive(Default)]
pub(super) struct IntFactCache {
    entries: BTreeMap<u32, Option<IntFacts>>,
}

fn annotation_rank(annotation: IntAnnotation) -> (u32, u8) {
    let signedness_rank = match annotation.signedness {
        IntSignedness::Unsigned => 0,
        IntSignedness::Signed => 1,
        IntSignedness::DontCare => 2,
    };
    (annotation.bit_width, signedness_rank)
}

fn min_bound(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (None, None) => None,
    }
}

fn max_bound(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.max(rhs)),
        _ => None,
    }
}

fn low_bits_u64(value: &BigInt) -> u64 {
    let modulus = BigInt::from(1u8) << 64;
    let truncated: BigInt = ((value % &modulus) + &modulus) % &modulus;
    let (_, digits) = truncated.to_u64_digits();
    digits.first().copied().unwrap_or(0)
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

#[derive(Clone, Copy)]
#[allow(dead_code)]
enum TerminatorOpcode {
    BrIf,
}

#[allow(dead_code)]
struct ReplacementTerminator {
    opcode: TerminatorOpcode,
    operands: Vec<ValueRef>,
    successors: Vec<usize>,
}

#[derive(Clone)]
#[allow(dead_code)]
struct MatchedSuccessor {
    block: BlockRef,
    args: Vec<Operand>,
}

enum ValueRewrite {
    Existing(ValueRef),
    ConstInt(BigInt),
    ConstBool(bool),
    Expr(ReplacementExpr),
}

enum ReplacementExpr {
    Value(ValueRef),
    ConstBool(bool),
    BoolNot(Box<ReplacementExpr>),
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

fn best_int_annotation_matches(
    func: &Function,
    fact_cache: &mut IntFactCache,
    value: ValueRef,
    expected: &IntAnnotation,
) -> bool {
    int_facts(func, fact_cache, value)
        .and_then(|facts| facts.best_annotation())
        .is_some_and(|annotation| annotation == *expected)
}

fn known_one(func: &Function, fact_cache: &mut IntFactCache, value: ValueRef, bit: u32) -> bool {
    if bit >= 64 {
        return int_facts(func, fact_cache, value)
            .and_then(|facts| facts.exact_const)
            .is_some_and(|value| exact_bit_is_one(&value, bit));
    }

    int_facts(func, fact_cache, value).is_some_and(|facts| (facts.known_one & (1u64 << bit)) != 0)
}

fn exact_bit_is_one(value: &BigInt, bit: u32) -> bool {
    if bit < 64 {
        return (low_bits_u64(value) & (1u64 << bit)) != 0;
    }

    let modulus = BigInt::from(1u8) << (bit as usize + 1);
    let truncated = ((value % &modulus) + &modulus) % &modulus;
    let shifted = truncated >> bit as usize;
    (&shifted % BigInt::from(2u8)) != BigInt::from(0u8)
}

fn int_facts(func: &Function, fact_cache: &mut IntFactCache, value: ValueRef) -> Option<IntFacts> {
    if let Some(cached) = fact_cache.entries.get(&value.raw()) {
        return cached.clone();
    }

    let computed = compute_int_facts(func, fact_cache, value);
    fact_cache.entries.insert(value.raw(), computed.clone());
    computed
}

fn compute_int_facts(
    func: &Function,
    fact_cache: &mut IntFactCache,
    value: ValueRef,
) -> Option<IntFacts> {
    if !matches!(func.value_type(value), Some(Type::Int)) {
        return None;
    }

    let mut facts = if value.is_block_arg() || value.is_secondary_result() {
        IntFacts::unknown()
    } else {
        let idx = value.index();
        let node = func.inst_pool.get(idx)?;
        match &node.inst.op {
            Op::Const(value) => IntFacts::from_exact_const(value),
            Op::Select(_, true_value, false_value) => {
                let true_facts = int_facts(func, fact_cache, true_value.value);
                let false_facts = int_facts(func, fact_cache, false_value.value);
                merge_select_facts(true_facts, false_facts)
            }
            Op::And(lhs, rhs) => {
                let lhs = int_facts(func, fact_cache, lhs.clone().raw().value);
                let rhs = int_facts(func, fact_cache, rhs.clone().raw().value);
                merge_and_facts(lhs, rhs)
            }
            Op::Xor(lhs, rhs) => {
                let lhs = int_facts(func, fact_cache, lhs.clone().raw().value);
                let rhs = int_facts(func, fact_cache, rhs.clone().raw().value);
                merge_xor_facts(lhs, rhs)
            }
            _ => IntFacts::unknown(),
        }
    };

    if let Some(Annotation::Int(annotation)) = definition_annotation(func, value) {
        facts = facts.refine_with_annotation(&annotation);
    }

    facts.tighten_from_unsigned();
    Some(facts)
}

fn merge_select_facts(lhs: Option<IntFacts>, rhs: Option<IntFacts>) -> IntFacts {
    let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
        return IntFacts::unknown();
    };

    let exact_const = match (&lhs.exact_const, &rhs.exact_const) {
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(lhs.clone()),
        _ => None,
    };

    if let Some(value) = exact_const {
        return IntFacts::from_exact_const(&value);
    }

    let mut facts = IntFacts {
        exact_const: None,
        known_zero: lhs.known_zero & rhs.known_zero,
        known_one: lhs.known_one & rhs.known_one,
        unsigned_width_upper_bound: max_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: max_bound(
            lhs.signed_width_upper_bound,
            rhs.signed_width_upper_bound,
        ),
    };
    facts.tighten_from_unsigned();
    facts
}

fn merge_and_facts(lhs: Option<IntFacts>, rhs: Option<IntFacts>) -> IntFacts {
    let lhs = lhs.unwrap_or_else(IntFacts::unknown);
    let rhs = rhs.unwrap_or_else(IntFacts::unknown);

    if let (Some(lhs), Some(rhs)) = (&lhs.exact_const, &rhs.exact_const) {
        return IntFacts::from_exact_const(&(lhs & rhs));
    }

    let mut facts = IntFacts {
        exact_const: None,
        known_zero: lhs.known_zero | rhs.known_zero,
        known_one: lhs.known_one & rhs.known_one,
        unsigned_width_upper_bound: min_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: None,
    };
    facts.tighten_from_unsigned();
    facts
}

fn merge_xor_facts(lhs: Option<IntFacts>, rhs: Option<IntFacts>) -> IntFacts {
    let lhs = lhs.unwrap_or_else(IntFacts::unknown);
    let rhs = rhs.unwrap_or_else(IntFacts::unknown);

    if let (Some(lhs), Some(rhs)) = (&lhs.exact_const, &rhs.exact_const) {
        return IntFacts::from_exact_const(&(lhs ^ rhs));
    }

    let mut facts = IntFacts {
        exact_const: None,
        known_zero: (lhs.known_zero & rhs.known_zero) | (lhs.known_one & rhs.known_one),
        known_one: (lhs.known_zero & rhs.known_one) | (lhs.known_one & rhs.known_zero),
        unsigned_width_upper_bound: max_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: None,
    };
    facts.tighten_from_unsigned();
    facts
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
        ValueRewrite::Expr(expr) => build_replacement_expr(func, root_idx, matched_insts, &expr),
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

fn build_replacement_expr(
    func: &mut Function,
    root_idx: u32,
    matched_insts: &BTreeSet<u32>,
    expr: &ReplacementExpr,
) -> ValueRef {
    match expr {
        ReplacementExpr::Value(value) => *value,
        ReplacementExpr::ConstBool(value) => {
            let new_inst = build_const_rewrite_instruction(
                func,
                root_idx,
                matched_insts,
                Op::BConst(*value),
                Type::Bool,
            );
            let new_idx = func.insert_inst_before(root_idx, new_inst);
            ValueRef::inst_result(new_idx)
        }
        ReplacementExpr::BoolNot(value) => {
            let operand = build_replacement_expr(func, root_idx, matched_insts, value);
            let true_value = build_replacement_expr(
                func,
                root_idx,
                matched_insts,
                &ReplacementExpr::ConstBool(true),
            );
            let new_inst = Instruction {
                op: Op::BXor(
                    BoolOperand::from_value(BoolValue::new(operand, func)),
                    BoolOperand::from_value(BoolValue::new(true_value, func)),
                ),
                ty: Type::Bool,
                secondary_ty: None,
                origin: merged_origin(func, root_idx, matched_insts),
                result_annotation: None,
                secondary_result_annotation: None,
            };
            let new_idx = func.insert_inst_before(root_idx, new_inst);
            ValueRef::inst_result(new_idx)
        }
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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
