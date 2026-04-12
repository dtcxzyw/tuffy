use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint, Sign};
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Operand, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, KnownBits, Type};
use tuffy_ir::value::BlockRef;
use tuffy_ir::value::ValueRef;
use tuffy_ir_interp::exec::{
    ExecResult, apply_annotation, apply_result_annotation, execute_instruction,
};
use tuffy_ir_interp::memory::Memory;
use tuffy_ir_interp::value::{AllocId, Value};

/// Internal constant `MAX_ITERATIONS`.
const MAX_ITERATIONS: usize = 32;
/// Internal constant `MAX_FACT_ITERATIONS`.
const MAX_FACT_ITERATIONS: usize = 64;
/// Internal constant `MAX_PEEPHOLE_FUNCTION_INSTS`.
const MAX_PEEPHOLE_FUNCTION_INSTS: usize = 1024;

#[path = "at_use.rs"]
/// Optimization module `cfg_sensitive`.
mod cfg_sensitive;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// Internal data structure `PeepholeStats`.
pub struct PeepholeStats {
    /// Iteration count.
    pub iterations: usize,
    /// Rewrite count.
    pub rewrites: usize,
    /// Per-rule counters.
    pub per_rule: BTreeMap<String, usize>,
    /// Promoted slot count or set.
    pub promoted_slots: usize,
    /// Promoted slice count.
    pub promoted_slices: usize,
    /// Promoted load count.
    pub promoted_loads: usize,
    /// Eliminated store count.
    pub eliminated_stores: usize,
    /// Inlining iteration count.
    pub inline_iterations: usize,
    /// Inlined call count.
    pub inlined_calls: usize,
}

impl PeepholeStats {
    /// Internal helper `record`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    pub(crate) fn record(&mut self, rule_name: &str) {
        self.rewrites += 1;
        *self.per_rule.entry(rule_name.to_string()).or_default() += 1;
    }

    /// Internal helper `merge`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    pub(crate) fn merge(&mut self, other: PeepholeStats) {
        self.iterations += other.iterations;
        self.rewrites += other.rewrites;
        self.promoted_slots += other.promoted_slots;
        self.promoted_slices += other.promoted_slices;
        self.promoted_loads += other.promoted_loads;
        self.eliminated_stores += other.eliminated_stores;
        self.inline_iterations += other.inline_iterations;
        self.inlined_calls += other.inlined_calls;
        for (name, count) in other.per_rule {
            *self.per_rule.entry(name).or_default() += count;
        }
    }
}

/// Generated rule count.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn generated_rule_count() -> usize {
    GENERATED_RULE_COUNT
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Optimize module.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(optimize_function(func));
    }
    total
}

/// Optimize function.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    if func.inst_pool.iter_insts().count() > MAX_PEEPHOLE_FUNCTION_INSTS {
        return PeepholeStats::default();
    }
    let mut total = PeepholeStats::default();
    for _ in 0..MAX_ITERATIONS {
        let local = optimize_local_roots(func);
        let cfg = cfg_sensitive::optimize_function(func);
        let changed = local.rewrites > 0 || cfg.rewrites > 0;
        total.merge(local);
        total.merge(cfg);
        if !changed {
            break;
        }
    }
    total
}

/// Internal helper `optimize_local_roots`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn optimize_local_roots(func: &mut Function) -> PeepholeStats {
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

#[derive(Clone, Copy)]
#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal enum `CanonicalBrIfMode`.
enum CanonicalBrIfMode {
    /// Variant `BoolXorConst`.
    BoolXorConst,
    /// Variant `IntifiedBoolCompare`.
    IntifiedBoolCompare,
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal data structure `CanonicalBrIfMatch`.
struct CanonicalBrIfMatch {
    /// Cond.
    cond: ValueRef,
    /// Invert.
    invert: bool,
    /// Matched insts.
    matched_insts: BTreeSet<u32>,
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `try_match_canonical_brif`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn try_match_canonical_brif(
    func: &Function,
    root_idx: u32,
    mode: CanonicalBrIfMode,
) -> Option<CanonicalBrIfMatch> {
    let root = func.inst_pool.get(root_idx)?;
    let Op::BrIf(cond, _, _, _, _) = &root.inst.op else {
        return None;
    };

    let mut matched_insts = BTreeSet::new();
    let (cond, invert) = match mode {
        CanonicalBrIfMode::BoolXorConst => {
            decode_bool_not(func, cond.clone().raw().value, &mut matched_insts)?
        }
        CanonicalBrIfMode::IntifiedBoolCompare => {
            decode_intified_bool_compare(func, cond.clone().raw().value, &mut matched_insts)?
        }
    };
    Some(CanonicalBrIfMatch {
        cond,
        invert,
        matched_insts,
    })
}

/// Internal helper `decode_bool_not`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn decode_bool_not(
    func: &Function,
    value: ValueRef,
    matched: &mut BTreeSet<u32>,
) -> Option<(ValueRef, bool)> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::BXor(lhs, rhs) = &node.inst.op else {
        return None;
    };

    let lhs_value = lhs.clone().raw().value;
    let rhs_value = rhs.clone().raw().value;
    if bound_bool_constant(func, lhs_value) == Some(true)
        && matches!(func.value_type(rhs_value), Some(Type::Bool))
    {
        matched.insert(value.index());
        if !lhs_value.is_block_arg() && !lhs_value.is_secondary_result() {
            matched.insert(lhs_value.index());
        }
        return Some((rhs_value, true));
    }
    if bound_bool_constant(func, rhs_value) == Some(true)
        && matches!(func.value_type(lhs_value), Some(Type::Bool))
    {
        matched.insert(value.index());
        if !rhs_value.is_block_arg() && !rhs_value.is_secondary_result() {
            matched.insert(rhs_value.index());
        }
        return Some((lhs_value, true));
    }
    if bound_bool_constant(func, lhs_value) == Some(false)
        && matches!(func.value_type(rhs_value), Some(Type::Bool))
    {
        matched.insert(value.index());
        if !lhs_value.is_block_arg() && !lhs_value.is_secondary_result() {
            matched.insert(lhs_value.index());
        }
        return Some((rhs_value, false));
    }
    if bound_bool_constant(func, rhs_value) == Some(false)
        && matches!(func.value_type(lhs_value), Some(Type::Bool))
    {
        matched.insert(value.index());
        if !rhs_value.is_block_arg() && !rhs_value.is_secondary_result() {
            matched.insert(rhs_value.index());
        }
        return Some((lhs_value, false));
    }
    None
}

/// Internal helper `decode_intified_bool_compare`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn decode_intified_bool_compare(
    func: &Function,
    value: ValueRef,
    matched: &mut BTreeSet<u32>,
) -> Option<(ValueRef, bool)> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::ICmp(pred, lhs, rhs) = &node.inst.op else {
        return None;
    };

    let (bool_source, compare_const, source_is_lhs) =
        if let Some(constant) = bound_int_constant(func, rhs.clone().raw().value) {
            let rhs_value = rhs.clone().raw().value;
            if !rhs_value.is_block_arg() && !rhs_value.is_secondary_result() {
                matched.insert(rhs_value.index());
            }
            let source = decode_intified_bool(func, lhs.clone().raw().value, matched)?;
            (source, constant, true)
        } else if let Some(constant) = bound_int_constant(func, lhs.clone().raw().value) {
            let lhs_value = lhs.clone().raw().value;
            if !lhs_value.is_block_arg() && !lhs_value.is_secondary_result() {
                matched.insert(lhs_value.index());
            }
            let source = decode_intified_bool(func, rhs.clone().raw().value, matched)?;
            (source, constant, false)
        } else {
            return None;
        };

    let compare_zero = *compare_const == BigInt::from(0u8);
    let compare_one = *compare_const == BigInt::from(1u8);
    if !compare_zero && !compare_one {
        return None;
    }

    let (cond, mut invert) = bool_source;
    invert ^= match pred {
        ICmpOp::Eq if compare_zero => true,
        ICmpOp::Eq if compare_one => false,
        ICmpOp::Ne if compare_zero => false,
        ICmpOp::Ne if compare_one => true,
        _ => return None,
    };

    // Keep commuted constant compares eligible but do not accept non-Eq/Ne roots.
    let _ = source_is_lhs;
    matched.insert(value.index());
    Some((cond, invert))
}

/// Internal helper `decode_intified_bool`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn decode_intified_bool(
    func: &Function,
    value: ValueRef,
    matched: &mut BTreeSet<u32>,
) -> Option<(ValueRef, bool)> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::Select(cond, true_value, false_value) => {
            let true_const = bound_int_constant(func, true_value.value)?;
            let false_const = bound_int_constant(func, false_value.value)?;
            if *true_const == BigInt::from(1u8) && *false_const == BigInt::from(0u8) {
                matched.insert(value.index());
                if !true_value.value.is_block_arg() && !true_value.value.is_secondary_result() {
                    matched.insert(true_value.value.index());
                }
                if !false_value.value.is_block_arg() && !false_value.value.is_secondary_result() {
                    matched.insert(false_value.value.index());
                }
                Some((cond.clone().raw().value, false))
            } else if *true_const == BigInt::from(0u8) && *false_const == BigInt::from(1u8) {
                matched.insert(value.index());
                if !true_value.value.is_block_arg() && !true_value.value.is_secondary_result() {
                    matched.insert(true_value.value.index());
                }
                if !false_value.value.is_block_arg() && !false_value.value.is_secondary_result() {
                    matched.insert(false_value.value.index());
                }
                Some((cond.clone().raw().value, true))
            } else {
                None
            }
        }
        Op::And(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            let lhs_const = bound_int_constant(func, lhs_value);
            let rhs_const = bound_int_constant(func, rhs_value);
            if lhs_const.is_some_and(is_non_negative_odd_int) {
                if !lhs_value.is_block_arg() && !lhs_value.is_secondary_result() {
                    matched.insert(lhs_value.index());
                }
                let (cond, invert) = decode_intified_bool(func, rhs_value, matched)?;
                matched.insert(value.index());
                Some((cond, invert))
            } else if rhs_const.is_some_and(is_non_negative_odd_int) {
                if !rhs_value.is_block_arg() && !rhs_value.is_secondary_result() {
                    matched.insert(rhs_value.index());
                }
                let (cond, invert) = decode_intified_bool(func, lhs_value, matched)?;
                matched.insert(value.index());
                Some((cond, invert))
            } else {
                None
            }
        }
        Op::Xor(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if bound_int_constant(func, lhs_value) == Some(&BigInt::from(1u8)) {
                if !lhs_value.is_block_arg() && !lhs_value.is_secondary_result() {
                    matched.insert(lhs_value.index());
                }
                let (cond, invert) = decode_intified_bool(func, rhs_value, matched)?;
                matched.insert(value.index());
                Some((cond, !invert))
            } else if bound_int_constant(func, rhs_value) == Some(&BigInt::from(1u8)) {
                if !rhs_value.is_block_arg() && !rhs_value.is_secondary_result() {
                    matched.insert(rhs_value.index());
                }
                let (cond, invert) = decode_intified_bool(func, lhs_value, matched)?;
                matched.insert(value.index());
                Some((cond, !invert))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Internal helper `is_non_negative_odd_int`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn is_non_negative_odd_int(value: &BigInt) -> bool {
    value.sign() != Sign::Minus && bigint_is_odd(value)
}

/// Internal helper `bind_value_slot`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bind_value_slot(slot: &mut Option<ValueRef>, value: ValueRef) -> bool {
    match slot {
        Some(existing) => *existing == value,
        None => {
            *slot = Some(value);
            true
        }
    }
}

/// Internal helper `primary_inst_index`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn primary_inst_index(value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        None
    } else {
        Some(value.index())
    }
}

/// Internal helper `bound_int_constant`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bound_int_constant(func: &Function, value: ValueRef) -> Option<&BigInt> {
    let idx = primary_inst_index(value)?;
    let node = func.inst_pool.get(idx)?;
    match &node.inst.op {
        Op::Const(value) => Some(value),
        _ => None,
    }
}

/// Internal helper `bound_bool_constant`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bound_bool_constant(func: &Function, value: ValueRef) -> Option<bool> {
    let idx = primary_inst_index(value)?;
    let node = func.inst_pool.get(idx)?;
    match &node.inst.op {
        Op::BConst(value) => Some(*value),
        _ => None,
    }
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `bigint_is_odd`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bigint_is_odd(value: &BigInt) -> bool {
    let modulus = BigInt::from(2u8);
    (value % &modulus) != BigInt::from(0u8)
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `parse_decimal_bigint`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn parse_decimal_bigint(value: &str) -> BigInt {
    value
        .parse()
        .unwrap_or_else(|_| panic!("invalid generated bigint literal: {value}"))
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Internal data structure `IntFacts`.
struct IntFacts {
    /// Is bottom.
    is_bottom: bool,
    /// Known zero.
    known_zero: BigUint,
    /// Known one.
    known_one: BigUint,
    /// Unsigned width upper bound.
    unsigned_width_upper_bound: Option<u32>,
    /// Signed width upper bound.
    signed_width_upper_bound: Option<u32>,
}

impl IntFacts {
    /// Internal helper `unknown`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn unknown() -> Self {
        Self::default()
    }

    /// Internal helper `bottom`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn bottom() -> Self {
        Self {
            is_bottom: true,
            ..Self::default()
        }
    }

    /// Internal helper `from_exact_const`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn from_exact_const(value: &BigInt) -> Self {
        let mut facts = Self {
            is_bottom: false,
            known_zero: BigUint::default(),
            known_one: BigUint::default(),
            unsigned_width_upper_bound: exact_unsigned_width(value),
            signed_width_upper_bound: Some(exact_signed_width(value)),
        };
        let width = facts
            .unsigned_width_upper_bound
            .or(facts.signed_width_upper_bound)
            .unwrap_or(1) as usize;
        for bit in 0..width.max(1) {
            if exact_bit_is_one(value, bit as u32) {
                facts.set_known_one(bit);
            } else {
                facts.set_known_zero(bit);
            }
        }
        facts.tighten_from_unsigned();
        facts
    }

    /// Internal helper `from_int_annotation`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn from_int_annotation(annotation: &IntAnnotation) -> Self {
        let mut facts = Self::unknown();
        match annotation.signedness {
            IntSignedness::Signed => {
                facts.signed_width_upper_bound = Some(annotation.bit_width);
            }
            IntSignedness::Unsigned | IntSignedness::DontCare => {
                facts.unsigned_width_upper_bound = Some(annotation.bit_width);
            }
        }
        facts.tighten_from_unsigned();
        facts
    }

    /// Internal helper `from_known_bits`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn from_known_bits(known: &KnownBits) -> Self {
        let mut facts = Self {
            is_bottom: false,
            known_zero: known.zeros.clone(),
            known_one: known.ones.clone(),
            unsigned_width_upper_bound: None,
            signed_width_upper_bound: None,
        };
        facts.normalize();
        facts
    }

    /// Internal helper `meet_with`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn meet_with(&mut self, other: &Self) -> bool {
        let original = self.clone();
        if self.is_bottom || other.is_bottom {
            self.is_bottom = true;
            self.known_zero = BigUint::default();
            self.known_one = BigUint::default();
            self.unsigned_width_upper_bound = None;
            self.signed_width_upper_bound = None;
            return *self != original;
        }

        self.known_zero |= &other.known_zero;
        self.known_one |= &other.known_one;
        self.unsigned_width_upper_bound = min_bound(
            self.unsigned_width_upper_bound,
            other.unsigned_width_upper_bound,
        );
        self.signed_width_upper_bound = min_bound(
            self.signed_width_upper_bound,
            other.signed_width_upper_bound,
        );
        self.tighten_from_unsigned();
        self.normalize();
        *self != original
    }

    /// Internal helper `normalize`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn normalize(&mut self) {
        if (&self.known_zero & &self.known_one) != BigUint::default() {
            *self = Self::bottom();
        }
    }

    /// Internal helper `refine_with_annotation`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn refine_with_annotation(&mut self, annotation: &Annotation) {
        let update = match annotation {
            Annotation::Int(annotation) => Self::from_int_annotation(annotation),
            Annotation::KnownBits(known) => Self::from_known_bits(known),
            _ => return,
        };
        let _ = self.meet_with(&update);
    }

    /// Internal helper `tighten_from_unsigned`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn tighten_from_unsigned(&mut self) {
        if let Some(bits) = self.unsigned_width_upper_bound {
            self.signed_width_upper_bound =
                min_bound(self.signed_width_upper_bound, Some(bits.saturating_add(1)));
        }
    }

    /// Internal helper `set_known_zero`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn set_known_zero(&mut self, bit: usize) {
        self.known_zero |= bit_mask(bit);
        self.normalize();
    }

    /// Internal helper `set_known_one`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn set_known_one(&mut self, bit: usize) {
        self.known_one |= bit_mask(bit);
        self.normalize();
    }

    /// Internal helper `bit_known_zero`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn bit_known_zero(&self, bit: usize) -> bool {
        if self.is_bottom {
            return false;
        }
        mask_has_bit(&self.known_zero, bit)
            || self
                .unsigned_width_upper_bound
                .is_some_and(|width| bit >= width as usize)
    }

    /// Internal helper `bit_known_one`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn bit_known_one(&self, bit: usize) -> bool {
        !self.is_bottom && mask_has_bit(&self.known_one, bit)
    }

    /// Internal helper `relevant_bit_width`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn relevant_bit_width(&self) -> usize {
        let mask_bits = highest_mask_bit(&(&self.known_zero | &self.known_one)).map(|bit| bit + 1);
        let width_bits = self
            .unsigned_width_upper_bound
            .map(|bits| bits as usize)
            .into_iter()
            .chain(self.signed_width_upper_bound.map(|bits| bits as usize))
            .max();
        mask_bits.into_iter().chain(width_bits).max().unwrap_or(1)
    }

    /// Internal helper `best_annotation`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn best_annotation(&self) -> Option<IntAnnotation> {
        if self.is_bottom {
            return None;
        }

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
/// Cached integer facts for the current peephole iteration.
pub(super) struct IntFactCache {
    /// Cached facts keyed by SSA value index.
    entries: BTreeMap<u32, IntFacts>,
    /// Whether the cache has been populated for the current snapshot.
    computed: bool,
}

/// Internal helper `annotation_rank`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn annotation_rank(annotation: IntAnnotation) -> (u32, u8) {
    let signedness_rank = match annotation.signedness {
        IntSignedness::Unsigned => 0,
        IntSignedness::Signed => 1,
        IntSignedness::DontCare => 2,
    };
    (annotation.bit_width, signedness_rank)
}

/// Internal helper `min_bound`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn min_bound(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (None, None) => None,
    }
}

/// Internal helper `max_bound`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn max_bound(lhs: Option<u32>, rhs: Option<u32>) -> Option<u32> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.max(rhs)),
        _ => None,
    }
}

/// Internal helper `bit_mask`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bit_mask(bit: usize) -> BigUint {
    BigUint::from(1u8) << bit
}

/// Internal helper `mask_has_bit`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn mask_has_bit(mask: &BigUint, bit: usize) -> bool {
    (mask & bit_mask(bit)) != BigUint::default()
}

/// Internal helper `highest_mask_bit`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn highest_mask_bit(mask: &BigUint) -> Option<usize> {
    let bits = mask.bits();
    if bits == 0 {
        None
    } else {
        Some(bits as usize - 1)
    }
}

/// Internal helper `exact_unsigned_width`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn exact_unsigned_width(value: &BigInt) -> Option<u32> {
    if value.sign() == Sign::Minus {
        None
    } else {
        Some((value.bits() as u32).max(1))
    }
}

/// Internal helper `exact_signed_width`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn exact_signed_width(value: &BigInt) -> u32 {
    if value.sign() == Sign::Minus {
        (((-value) - BigInt::from(1u8)).bits() as u32) + 1
    } else {
        (value.bits() as u32).saturating_add(1).max(1)
    }
}

#[derive(Clone, Copy)]
#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal enum `TerminatorOpcode`.
enum TerminatorOpcode {
    /// Variant `BrIf`.
    BrIf,
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal data structure `ReplacementTerminator`.
struct ReplacementTerminator {
    /// Opcode.
    opcode: TerminatorOpcode,
    /// Operands.
    operands: Vec<ValueRef>,
    /// Successors.
    successors: Vec<usize>,
}

#[derive(Clone)]
#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal data structure `MatchedSuccessor`.
struct MatchedSuccessor {
    /// Block.
    block: BlockRef,
    /// Args.
    args: Vec<Operand>,
}

/// Internal enum `ValueRewrite`.
enum ValueRewrite {
    /// Variant `Existing`.
    Existing(ValueRef),
    /// Variant `ConstInt`.
    ConstInt(BigInt),
    /// Variant `ConstBool`.
    ConstBool(bool),
    /// Variant `Expr`.
    Expr(ReplacementExpr),
}

/// Internal enum `ReplacementExpr`.
enum ReplacementExpr {
    /// Variant `Value`.
    Value(ValueRef),
    /// Variant `ConstBool`.
    ConstBool(bool),
    /// Variant `BoolNot`.
    BoolNot(Box<ReplacementExpr>),
}

#[derive(Clone, Copy)]
/// Internal enum `ConstFoldKind`.
enum ConstFoldKind {
    /// Variant `Add`.
    Add,
    /// Variant `Sub`.
    Sub,
    /// Variant `Mul`.
    Mul,
    /// Variant `Div`.
    Div,
    /// Variant `Rem`.
    Rem,
    /// Variant `And`.
    And,
    /// Variant `Or`.
    Or,
    /// Variant `Xor`.
    Xor,
    /// Variant `BAnd`.
    BAnd,
    /// Variant `BOr`.
    BOr,
    /// Variant `BXor`.
    BXor,
    /// Variant `Shl`.
    Shl,
    /// Variant `Shr`.
    Shr,
    /// Variant `Min`.
    Min,
    /// Variant `Max`.
    Max,
    /// Variant `CountOnes`.
    CountOnes,
    /// Variant `CountLeadingZeros`.
    CountLeadingZeros,
    /// Variant `CountTrailingZeros`.
    CountTrailingZeros,
    /// Variant `Bswap`.
    Bswap,
    /// Variant `BitReverse`.
    BitReverse,
    /// Variant `RotateLeft`.
    RotateLeft,
    /// Variant `RotateRight`.
    RotateRight,
    /// Variant `Select`.
    Select,
    /// Variant `ICmp`.
    ICmp(ICmpOp),
}

/// Internal data structure `ConstantFoldMatch`.
struct ConstantFoldMatch {
    /// Replacement.
    replacement: ValueRewrite,
    /// Matched insts.
    matched_insts: BTreeSet<u32>,
}

/// Internal helper `best_int_annotation_matches`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `known_one`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn known_one(func: &Function, fact_cache: &mut IntFactCache, value: ValueRef, bit: u32) -> bool {
    int_facts(func, fact_cache, value).is_some_and(|facts| facts.bit_known_one(bit as usize))
}

/// Internal helper `exact_bit_is_one`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn exact_bit_is_one(value: &BigInt, bit: u32) -> bool {
    let modulus = BigInt::from(1u8) << (bit as usize + 1);
    let truncated = ((value % &modulus) + &modulus) % &modulus;
    let shifted = truncated >> bit as usize;
    (&shifted % BigInt::from(2u8)) != BigInt::from(0u8)
}

/// Internal helper `int_facts`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn int_facts(func: &Function, fact_cache: &mut IntFactCache, value: ValueRef) -> Option<IntFacts> {
    if !matches!(func.value_type(value), Some(Type::Int)) {
        return None;
    }

    ensure_int_facts(func, fact_cache);
    Some(
        fact_cache
            .entries
            .get(&value.raw())
            .cloned()
            .unwrap_or_else(IntFacts::unknown),
    )
}

/// Internal helper `ensure_int_facts`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn ensure_int_facts(func: &Function, fact_cache: &mut IntFactCache) {
    if fact_cache.computed {
        return;
    }

    let int_values = collect_int_values(func);
    fact_cache.entries.clear();
    for value in &int_values {
        fact_cache
            .entries
            .insert(value.raw(), seed_int_facts_for_value(func, *value));
    }

    for _ in 0..MAX_FACT_ITERATIONS {
        let mut changed = false;
        let snapshot = fact_cache.entries.clone();

        for value in &int_values {
            if value.is_block_arg() {
                continue;
            }
            let mut forward = generated_forward_int_facts(func, *value, &snapshot)
                .unwrap_or_else(IntFacts::unknown);
            let seed = seed_int_facts_for_value(func, *value);
            let _ = forward.meet_with(&seed);
            changed |= update_fact_entry(&mut fact_cache.entries, *value, &forward);
        }

        let snapshot = fact_cache.entries.clone();
        for (idx, inst) in func.inst_pool.iter_insts() {
            let primary_value = ValueRef::inst_result(idx);
            let secondary_value = ValueRef::inst_secondary_result(idx);
            let primary_is_int = matches!(inst.ty, Type::Int);
            let secondary_is_int = matches!(inst.secondary_ty, Some(Type::Int));
            if !primary_is_int && !secondary_is_int {
                continue;
            }

            let primary_facts = snapshot
                .get(&primary_value.raw())
                .cloned()
                .unwrap_or_else(IntFacts::unknown);
            let secondary_facts = if secondary_is_int {
                Some(
                    snapshot
                        .get(&secondary_value.raw())
                        .cloned()
                        .unwrap_or_else(IntFacts::unknown),
                )
            } else {
                None
            };

            for update in generated_backward_int_facts(
                func,
                idx,
                &primary_facts,
                secondary_facts.as_ref(),
                &snapshot,
            ) {
                if !matches!(func.value_type(update.value), Some(Type::Int)) {
                    continue;
                }
                changed |= update_fact_entry(&mut fact_cache.entries, update.value, &update.facts);
            }
        }

        if !changed {
            break;
        }
    }

    fact_cache.computed = true;
}

/// Internal helper `collect_int_values`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn collect_int_values(func: &Function) -> Vec<ValueRef> {
    let mut values = Vec::new();
    for (idx, arg) in func.block_args.iter().enumerate() {
        if matches!(arg.ty, Type::Int) {
            values.push(ValueRef::block_arg(idx as u32));
        }
    }
    for (idx, inst) in func.inst_pool.iter_insts() {
        if matches!(inst.ty, Type::Int) {
            values.push(ValueRef::inst_result(idx));
        }
        if matches!(inst.secondary_ty, Some(Type::Int)) {
            values.push(ValueRef::inst_secondary_result(idx));
        }
    }
    values
}

/// Internal helper `update_fact_entry`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn update_fact_entry(
    entries: &mut BTreeMap<u32, IntFacts>,
    value: ValueRef,
    update: &IntFacts,
) -> bool {
    let entry = entries.entry(value.raw()).or_insert_with(IntFacts::unknown);
    entry.meet_with(update)
}

/// Internal helper `seed_int_facts_for_value`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn seed_int_facts_for_value(func: &Function, value: ValueRef) -> IntFacts {
    let mut facts = IntFacts::unknown();
    if !value.is_block_arg()
        && !value.is_secondary_result()
        && let Some(node) = func.inst_pool.get(value.index())
        && let Op::Const(value) = &node.inst.op
    {
        let const_facts = IntFacts::from_exact_const(value);
        let _ = facts.meet_with(&const_facts);
    }
    if let Some(annotation) = definition_annotation(func, value) {
        facts.refine_with_annotation(&annotation);
    }
    facts
}

/// Internal helper `value_facts_from_snapshot`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn value_facts_from_snapshot(current: &BTreeMap<u32, IntFacts>, value: ValueRef) -> IntFacts {
    current
        .get(&value.raw())
        .cloned()
        .unwrap_or_else(IntFacts::unknown)
}

/// Internal helper `operand_input_facts`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn operand_input_facts(
    _func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    operand: &Operand,
) -> IntFacts {
    let mut facts = value_facts_from_snapshot(current, operand.value);
    if let Some(annotation) = &operand.annotation {
        facts.refine_with_annotation(annotation);
    }
    facts
}

/// Internal helper `forward_unknown`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_unknown() -> IntFacts {
    IntFacts::unknown()
}

/// Internal helper `forward_const`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_const(value: &BigInt) -> IntFacts {
    IntFacts::from_exact_const(value)
}

/// Internal helper `forward_select`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_select(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    true_value: &Operand,
    false_value: &Operand,
) -> IntFacts {
    let true_facts = operand_input_facts(func, current, true_value);
    let false_facts = operand_input_facts(func, current, false_value);
    let mut facts = IntFacts {
        is_bottom: false,
        known_zero: BigUint::default(),
        known_one: BigUint::default(),
        unsigned_width_upper_bound: max_bound(
            true_facts.unsigned_width_upper_bound,
            false_facts.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: max_bound(
            true_facts.signed_width_upper_bound,
            false_facts.signed_width_upper_bound,
        ),
    };
    let width = true_facts
        .relevant_bit_width()
        .max(false_facts.relevant_bit_width());
    for bit in 0..width {
        if true_facts.bit_known_zero(bit) && false_facts.bit_known_zero(bit) {
            facts.set_known_zero(bit);
        }
        if true_facts.bit_known_one(bit) && false_facts.bit_known_one(bit) {
            facts.set_known_one(bit);
        }
    }
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_bitand`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_bitand(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
) -> IntFacts {
    let lhs = operand_input_facts(func, current, lhs);
    let rhs = operand_input_facts(func, current, rhs);
    let mut facts = IntFacts {
        is_bottom: false,
        known_zero: BigUint::default(),
        known_one: BigUint::default(),
        unsigned_width_upper_bound: min_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: None,
    };
    let width = lhs.relevant_bit_width().max(rhs.relevant_bit_width());
    for bit in 0..width {
        if lhs.bit_known_zero(bit) || rhs.bit_known_zero(bit) {
            facts.set_known_zero(bit);
        }
        if lhs.bit_known_one(bit) && rhs.bit_known_one(bit) {
            facts.set_known_one(bit);
        }
    }
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_bitor`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_bitor(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
) -> IntFacts {
    let lhs = operand_input_facts(func, current, lhs);
    let rhs = operand_input_facts(func, current, rhs);
    let mut facts = IntFacts {
        is_bottom: false,
        known_zero: BigUint::default(),
        known_one: BigUint::default(),
        unsigned_width_upper_bound: max_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: None,
    };
    let width = lhs.relevant_bit_width().max(rhs.relevant_bit_width());
    for bit in 0..width {
        if lhs.bit_known_zero(bit) && rhs.bit_known_zero(bit) {
            facts.set_known_zero(bit);
        }
        if lhs.bit_known_one(bit) || rhs.bit_known_one(bit) {
            facts.set_known_one(bit);
        }
    }
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_bitxor`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_bitxor(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
) -> IntFacts {
    let lhs = operand_input_facts(func, current, lhs);
    let rhs = operand_input_facts(func, current, rhs);
    let mut facts = IntFacts {
        is_bottom: false,
        known_zero: BigUint::default(),
        known_one: BigUint::default(),
        unsigned_width_upper_bound: max_bound(
            lhs.unsigned_width_upper_bound,
            rhs.unsigned_width_upper_bound,
        ),
        signed_width_upper_bound: None,
    };
    let width = lhs.relevant_bit_width().max(rhs.relevant_bit_width());
    for bit in 0..width {
        if (lhs.bit_known_zero(bit) && rhs.bit_known_zero(bit))
            || (lhs.bit_known_one(bit) && rhs.bit_known_one(bit))
        {
            facts.set_known_zero(bit);
        }
        if (lhs.bit_known_zero(bit) && rhs.bit_known_one(bit))
            || (lhs.bit_known_one(bit) && rhs.bit_known_zero(bit))
        {
            facts.set_known_one(bit);
        }
    }
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_shl`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_shl(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
) -> IntFacts {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let Some(shift) = bound_int_constant(func, rhs.value).and_then(bigint_to_nonnegative_u32)
    else {
        return IntFacts::unknown();
    };

    let mut facts = IntFacts::unknown();
    let width = lhs_facts.relevant_bit_width() + shift as usize;
    for bit in 0..width {
        if bit < shift as usize {
            facts.set_known_zero(bit);
            continue;
        }
        let src_bit = bit - shift as usize;
        if lhs_facts.bit_known_zero(src_bit) {
            facts.set_known_zero(bit);
        }
        if lhs_facts.bit_known_one(src_bit) {
            facts.set_known_one(bit);
        }
    }
    facts.unsigned_width_upper_bound = lhs_facts
        .unsigned_width_upper_bound
        .map(|bits| bits.saturating_add(shift));
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_shr`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_shr(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
) -> IntFacts {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let Some(shift) = bound_int_constant(func, rhs.value).and_then(bigint_to_nonnegative_u32)
    else {
        return IntFacts::unknown();
    };

    let mut facts = IntFacts::unknown();
    let width = lhs_facts
        .relevant_bit_width()
        .saturating_sub(shift as usize)
        .max(1);
    for bit in 0..width {
        let src_bit = bit + shift as usize;
        if lhs_facts.bit_known_zero(src_bit) {
            facts.set_known_zero(bit);
        }
        if lhs_facts.bit_known_one(src_bit) {
            facts.set_known_one(bit);
        }
    }
    facts.unsigned_width_upper_bound = lhs_facts
        .unsigned_width_upper_bound
        .map(|bits| if shift >= bits { 1 } else { bits - shift });
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_merge`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_merge(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> IntFacts {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let rhs_facts = operand_input_facts(func, current, rhs);
    let mut facts = IntFacts::unknown();
    let total_width = lhs_facts.relevant_bit_width().max(
        rhs_facts
            .relevant_bit_width()
            .saturating_add(width as usize),
    );
    for bit in 0..total_width {
        if bit < width as usize {
            if rhs_facts.bit_known_zero(bit) {
                facts.set_known_zero(bit);
            }
            if rhs_facts.bit_known_one(bit) {
                facts.set_known_one(bit);
            }
        } else {
            if lhs_facts.bit_known_zero(bit) {
                facts.set_known_zero(bit);
            }
            if lhs_facts.bit_known_one(bit) {
                facts.set_known_one(bit);
            }
        }
    }
    facts
}

/// Internal helper `forward_split_hi`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_split_hi(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    src: &Operand,
    width: u32,
) -> IntFacts {
    let src_facts = operand_input_facts(func, current, src);
    let mut facts = IntFacts::unknown();
    let out_width = src_facts
        .relevant_bit_width()
        .saturating_sub(width as usize)
        .max(1);
    for bit in 0..out_width {
        let src_bit = bit + width as usize;
        if src_facts.bit_known_zero(src_bit) {
            facts.set_known_zero(bit);
        }
        if src_facts.bit_known_one(src_bit) {
            facts.set_known_one(bit);
        }
    }
    facts.unsigned_width_upper_bound = src_facts
        .unsigned_width_upper_bound
        .map(|bits| if width >= bits { 1 } else { bits - width });
    facts.tighten_from_unsigned();
    facts
}

/// Internal helper `forward_split_lo`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn forward_split_lo(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    src: &Operand,
    width: u32,
) -> IntFacts {
    let src_facts = operand_input_facts(func, current, src);
    let mut facts = IntFacts::unknown();
    for bit in 0..width as usize {
        if src_facts.bit_known_zero(bit) {
            facts.set_known_zero(bit);
        }
        if src_facts.bit_known_one(bit) {
            facts.set_known_one(bit);
        }
    }
    facts.unsigned_width_upper_bound = Some(width.max(1));
    facts.tighten_from_unsigned();
    facts
}

#[derive(Clone)]
/// Internal data structure `BackwardFactUpdate`.
struct BackwardFactUpdate {
    /// Value.
    value: ValueRef,
    /// Facts.
    facts: IntFacts,
}

/// Internal helper `backward_select`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_select(
    func: &Function,
    cond: &tuffy_ir::typed::BoolOperand,
    true_value: &Operand,
    false_value: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    match bound_bool_constant(func, cond.clone().raw().value) {
        Some(true) => vec![BackwardFactUpdate {
            value: true_value.value,
            facts: result.clone(),
        }],
        Some(false) => vec![BackwardFactUpdate {
            value: false_value.value,
            facts: result.clone(),
        }],
        None if true_value.value == false_value.value => vec![BackwardFactUpdate {
            value: true_value.value,
            facts: result.clone(),
        }],
        None => Vec::new(),
    }
}

/// Internal helper `backward_bitand`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_bitand(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let rhs_facts = operand_input_facts(func, current, rhs);
    let width = lhs_facts
        .relevant_bit_width()
        .max(rhs_facts.relevant_bit_width())
        .max(result.relevant_bit_width());
    let mut lhs_update = IntFacts::unknown();
    let mut rhs_update = IntFacts::unknown();
    for bit in 0..width {
        if result.bit_known_one(bit) {
            lhs_update.set_known_one(bit);
            rhs_update.set_known_one(bit);
        }
        if result.bit_known_zero(bit) && rhs_facts.bit_known_one(bit) {
            lhs_update.set_known_zero(bit);
        }
        if result.bit_known_zero(bit) && lhs_facts.bit_known_one(bit) {
            rhs_update.set_known_zero(bit);
        }
    }
    vec![
        BackwardFactUpdate {
            value: lhs.value,
            facts: lhs_update,
        },
        BackwardFactUpdate {
            value: rhs.value,
            facts: rhs_update,
        },
    ]
}

/// Internal helper `backward_bitor`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_bitor(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let rhs_facts = operand_input_facts(func, current, rhs);
    let width = lhs_facts
        .relevant_bit_width()
        .max(rhs_facts.relevant_bit_width())
        .max(result.relevant_bit_width());
    let mut lhs_update = IntFacts::unknown();
    let mut rhs_update = IntFacts::unknown();
    for bit in 0..width {
        if result.bit_known_zero(bit) {
            lhs_update.set_known_zero(bit);
            rhs_update.set_known_zero(bit);
        }
        if result.bit_known_one(bit) && rhs_facts.bit_known_zero(bit) {
            lhs_update.set_known_one(bit);
        }
        if result.bit_known_one(bit) && lhs_facts.bit_known_zero(bit) {
            rhs_update.set_known_one(bit);
        }
    }
    vec![
        BackwardFactUpdate {
            value: lhs.value,
            facts: lhs_update,
        },
        BackwardFactUpdate {
            value: rhs.value,
            facts: rhs_update,
        },
    ]
}

/// Internal helper `backward_bitxor`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_bitxor(
    func: &Function,
    current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let lhs_facts = operand_input_facts(func, current, lhs);
    let rhs_facts = operand_input_facts(func, current, rhs);
    let width = lhs_facts
        .relevant_bit_width()
        .max(rhs_facts.relevant_bit_width())
        .max(result.relevant_bit_width());
    let mut lhs_update = IntFacts::unknown();
    let mut rhs_update = IntFacts::unknown();
    for bit in 0..width {
        if result.bit_known_zero(bit) {
            if rhs_facts.bit_known_zero(bit) {
                lhs_update.set_known_zero(bit);
            }
            if rhs_facts.bit_known_one(bit) {
                lhs_update.set_known_one(bit);
            }
            if lhs_facts.bit_known_zero(bit) {
                rhs_update.set_known_zero(bit);
            }
            if lhs_facts.bit_known_one(bit) {
                rhs_update.set_known_one(bit);
            }
        }
        if result.bit_known_one(bit) {
            if rhs_facts.bit_known_zero(bit) {
                lhs_update.set_known_one(bit);
            }
            if rhs_facts.bit_known_one(bit) {
                lhs_update.set_known_zero(bit);
            }
            if lhs_facts.bit_known_zero(bit) {
                rhs_update.set_known_one(bit);
            }
            if lhs_facts.bit_known_one(bit) {
                rhs_update.set_known_zero(bit);
            }
        }
    }
    vec![
        BackwardFactUpdate {
            value: lhs.value,
            facts: lhs_update,
        },
        BackwardFactUpdate {
            value: rhs.value,
            facts: rhs_update,
        },
    ]
}

/// Internal helper `backward_shl`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_shl(
    func: &Function,
    _current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let Some(shift) = bound_int_constant(func, rhs.value).and_then(bigint_to_nonnegative_u32)
    else {
        return Vec::new();
    };
    let mut lhs_update = IntFacts::unknown();
    for bit in shift as usize..result.relevant_bit_width() {
        let dst_bit = bit - shift as usize;
        if result.bit_known_zero(bit) {
            lhs_update.set_known_zero(dst_bit);
        }
        if result.bit_known_one(bit) {
            lhs_update.set_known_one(dst_bit);
        }
    }
    vec![BackwardFactUpdate {
        value: lhs.value,
        facts: lhs_update,
    }]
}

/// Internal helper `backward_shr`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_shr(
    func: &Function,
    _current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let Some(shift) = bound_int_constant(func, rhs.value).and_then(bigint_to_nonnegative_u32)
    else {
        return Vec::new();
    };
    let mut lhs_update = IntFacts::unknown();
    for bit in 0..result.relevant_bit_width() {
        let dst_bit = bit + shift as usize;
        if result.bit_known_zero(bit) {
            lhs_update.set_known_zero(dst_bit);
        }
        if result.bit_known_one(bit) {
            lhs_update.set_known_one(dst_bit);
        }
    }
    vec![BackwardFactUpdate {
        value: lhs.value,
        facts: lhs_update,
    }]
}

/// Internal helper `backward_merge`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_merge(
    func: &Function,
    _current: &BTreeMap<u32, IntFacts>,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let _ = func;
    let mut lhs_update = IntFacts::unknown();
    let mut rhs_update = IntFacts::unknown();
    for bit in 0..result.relevant_bit_width() {
        if bit < width as usize {
            if result.bit_known_zero(bit) {
                rhs_update.set_known_zero(bit);
            }
            if result.bit_known_one(bit) {
                rhs_update.set_known_one(bit);
            }
        } else {
            if result.bit_known_zero(bit) {
                lhs_update.set_known_zero(bit);
            }
            if result.bit_known_one(bit) {
                lhs_update.set_known_one(bit);
            }
        }
    }
    vec![
        BackwardFactUpdate {
            value: lhs.value,
            facts: lhs_update,
        },
        BackwardFactUpdate {
            value: rhs.value,
            facts: rhs_update,
        },
    ]
}

/// Internal helper `backward_split`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn backward_split(
    _func: &Function,
    _current: &BTreeMap<u32, IntFacts>,
    src: &Operand,
    width: u32,
    primary_result: &IntFacts,
    secondary_result: &IntFacts,
) -> Vec<BackwardFactUpdate> {
    let mut src_update = IntFacts::unknown();
    for bit in 0..primary_result.relevant_bit_width() {
        let src_bit = bit + width as usize;
        if primary_result.bit_known_zero(bit) {
            src_update.set_known_zero(src_bit);
        }
        if primary_result.bit_known_one(bit) {
            src_update.set_known_one(src_bit);
        }
    }
    for bit in 0..width as usize {
        if secondary_result.bit_known_zero(bit) {
            src_update.set_known_zero(bit);
        }
        if secondary_result.bit_known_one(bit) {
            src_update.set_known_one(bit);
        }
    }
    vec![BackwardFactUpdate {
        value: src.value,
        facts: src_update,
    }]
}

/// Internal helper `bigint_to_nonnegative_u32`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn bigint_to_nonnegative_u32(value: &BigInt) -> Option<u32> {
    if value.sign() == Sign::Minus {
        None
    } else {
        value.try_into().ok()
    }
}

/// Internal helper `apply_value_root_rewrite`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `build_const_rewrite_instruction`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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
        result_annotation: root_inst.result_annotation.clone(),
        secondary_result_annotation: None,
    }
}

/// Internal helper `build_replacement_expr`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `try_fold_constant_root`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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
    let def_type = |value: ValueRef| definition_type(func, value);
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
        &def_type,
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

/// Internal helper `root_matches_const_fold_kind`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `constant_value_for_fold`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `apply_operand_annotation_for_fold`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn apply_operand_annotation_for_fold(value: Value, annotation: &Option<Annotation>) -> Value {
    match (value, annotation) {
        (Value::Poison, _) => Value::Poison,
        (Value::Int(value), Some(Annotation::Int(int_ann))) => apply_annotation(&value, int_ann),
        (Value::Int(value), Some(Annotation::KnownBits(known))) => apply_result_annotation(
            Value::Int(value),
            &Some(Annotation::KnownBits(known.clone())),
        ),
        (value, _) => value,
    }
}

/// Internal helper `definition_annotation`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn definition_annotation(func: &Function, value: ValueRef) -> Option<Annotation> {
    if value.is_block_arg() {
        func.block_args
            .get(value.index() as usize)
            .and_then(|arg| arg.annotation.clone())
    } else if value.is_secondary_result() {
        func.inst_pool
            .get(value.inst_index())
            .and_then(|node| node.inst.secondary_result_annotation.clone())
    } else {
        func.inst_pool
            .get(value.index())
            .and_then(|node| node.inst.result_annotation.clone())
    }
}

/// Internal helper `definition_type`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn definition_type(func: &Function, value: ValueRef) -> Option<Type> {
    func.value_type(value).cloned()
}

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `apply_terminator_root_rewrite`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `build_terminator_op`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

#[allow(dead_code, reason = "Required by the current implementation shape.")]
/// Internal helper `extract_matched_successors`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `merged_origin`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `cleanup_dead_instructions`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
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

/// Internal helper `instruction_results_unused`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn instruction_results_unused(func: &Function, idx: u32, has_secondary_result: bool) -> bool {
    if func.has_uses(ValueRef::inst_result(idx)) {
        return false;
    }
    if has_secondary_result && func.has_uses(ValueRef::inst_secondary_result(idx)) {
        return false;
    }
    true
}

include!(concat!(env!("OUT_DIR"), "/peephole_facts_gen.rs"));
include!(concat!(env!("OUT_DIR"), "/peephole_gen.rs"));

#[cfg(test)]
mod fact_tests {
    use super::*;
    use tuffy_ir::parser::parse_module;

    /// Internal helper `single_function`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn single_function(input: &str) -> Function {
        let module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));
        module
            .functions
            .into_iter()
            .next()
            .expect("module should contain one function")
    }

    /// Internal helper `select_operands`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn select_operands(
        func: &Function,
        inst_idx: u32,
    ) -> (&tuffy_ir::typed::BoolOperand, &Operand, &Operand) {
        match &func.inst(inst_idx).op {
            Op::Select(cond, true_value, false_value) => (cond, true_value, false_value),
            other => panic!("expected select, got {other:?}"),
        }
    }

    #[test]
    /// Internal helper `best_annotation_prefers_unsigned_when_widths_tie`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn best_annotation_prefers_unsigned_when_widths_tie() {
        let mut facts = IntFacts::unknown();
        facts.unsigned_width_upper_bound = Some(8);
        facts.signed_width_upper_bound = Some(8);
        assert_eq!(
            facts.best_annotation(),
            Some(IntAnnotation {
                bit_width: 8,
                signedness: IntSignedness::Unsigned,
            })
        );
    }

    #[test]
    /// Internal helper `best_annotation_prefers_narrower_signed_width`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn best_annotation_prefers_narrower_signed_width() {
        let mut facts = IntFacts::unknown();
        facts.unsigned_width_upper_bound = Some(8);
        facts.signed_width_upper_bound = Some(4);
        assert_eq!(
            facts.best_annotation(),
            Some(IntAnnotation {
                bit_width: 4,
                signedness: IntSignedness::Signed,
            })
        );
    }

    #[test]
    /// Internal helper `backward_select_only_updates_taken_const_branch`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn backward_select_only_updates_taken_const_branch() {
        let func = single_function(
            r#"
func @const_true_select() {
  bb0:
    v0: bool = bconst true
    v1: int:u8 = iconst 1
    v2: int:u8 = iconst 2
    v3: int:u8 = select v0, v1, v2
    unreachable
}
"#,
        );
        let (cond, true_value, false_value) = select_operands(&func, 3);
        let mut result = IntFacts::unknown();
        result.set_known_one(0);
        let updates = backward_select(&func, cond, true_value, false_value, &result);
        assert_eq!(updates.len(), 1);
        assert_eq!(updates[0].value, true_value.value);
    }

    #[test]
    /// Internal helper `backward_select_skips_unknown_distinct_branches`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn backward_select_skips_unknown_distinct_branches() {
        let func = single_function(
            r#"
func @unknown_select(bool, int:u8, int:u8) {
  bb0:
    v0: bool = param 0
    v1: int:u8 = param 1
    v2: int:u8 = param 2
    v3: int:u8 = select v0, v1, v2
    unreachable
}
"#,
        );
        let (cond, true_value, false_value) = select_operands(&func, 3);
        let result = IntFacts::from_int_annotation(&IntAnnotation {
            bit_width: 8,
            signedness: IntSignedness::Unsigned,
        });
        let updates = backward_select(&func, cond, true_value, false_value, &result);
        assert!(updates.is_empty());
    }

    #[test]
    /// Internal helper `backward_select_updates_unknown_shared_value`.
    ///
    /// # Panics
    ///
    /// May panic if internal IR invariants are violated.
    fn backward_select_updates_unknown_shared_value() {
        let func = single_function(
            r#"
func @unknown_shared(bool, int:u8) {
  bb0:
    v0: bool = param 0
    v1: int:u8 = param 1
    v2: int:u8 = select v0, v1, v1
    unreachable
}
"#,
        );
        let (cond, true_value, false_value) = select_operands(&func, 2);
        let mut result = IntFacts::unknown();
        result.set_known_zero(0);
        let updates = backward_select(&func, cond, true_value, false_value, &result);
        assert_eq!(updates.len(), 1);
        assert_eq!(updates[0].value, true_value.value);
        assert!(updates[0].facts.bit_known_zero(0));
    }
}
