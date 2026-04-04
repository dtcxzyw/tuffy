//! Instruction executor: evaluate each Op variant.
//!
//! Follows the Lean operational semantics in `lean/TuffyLean/IR/Semantics.lean`.
//! All integer arithmetic uses infinite precision via BigInt.
//! Poison propagates through computations; UB is detected at observation points.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rustc_apfloat::ieee::{Double, Half, Quad, Single};
use rustc_apfloat::{Float, FloatConvert, StatusAnd};
use tuffy_ir::instruction::{FCmpOp, FloatConst, ICmpOp, Op, Operand};
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use crate::memory::Memory;
use crate::value::{
    AbstractByte, AllocId, Pointer, Value, float_to_le_bytes, int_to_le_bytes, le_bytes_to_int,
    ptr_to_le_bytes,
};

/// Base multiplier for synthetic addresses in `PtrToAddr`/`IntToPtr`.
/// Pointer addresses are synthesized as `alloc_id * SYNTH_ADDR_BASE + offset`.
/// Must be large enough that no allocation offset exceeds this value.
pub const SYNTH_ADDR_BASE: i64 = 1 << 32;

/// Reverse the synthetic address scheme: recover `(alloc_id, offset)` from an
/// address produced by `ptrtoaddr`.
fn addr_to_pointer(addr: i64) -> Pointer {
    if addr == 0 {
        Pointer {
            alloc_id: AllocId(0),
            offset: 0,
        }
    } else {
        let alloc_id = addr / SYNTH_ADDR_BASE;
        let offset = addr - alloc_id * SYNTH_ADDR_BASE;
        if alloc_id > 0 {
            Pointer {
                alloc_id: AllocId(alloc_id as u64),
                offset,
            }
        } else {
            // Can't recover provenance; use alloc_id 0 as sentinel.
            Pointer {
                alloc_id: AllocId(0),
                offset: addr,
            }
        }
    }
}

/// Result of executing a single instruction.
#[derive(Debug)]
pub enum ExecResult {
    /// Produced a value (possibly poison).
    Value(Value),
    /// Produced two values (multi-result instructions like Split, *WithOverflow).
    MultiValue(Value, Value),
    /// A terminator was reached.
    Terminator(TerminatorAction),
}

/// Action to take after a terminator instruction.
#[derive(Debug)]
pub enum TerminatorAction {
    /// Return from function with optional value.
    Return(Option<Value>),
    /// Branch to a block with arguments.
    Branch(tuffy_ir::value::BlockRef, Vec<Value>),
    /// Conditional branch.
    BranchIf {
        cond: Value,
        then_block: tuffy_ir::value::BlockRef,
        then_args: Vec<Value>,
        else_block: tuffy_ir::value::BlockRef,
        else_args: Vec<Value>,
    },
    /// Loop backedge with values.
    Continue(Vec<Value>),
    /// Region exit with values.
    RegionYield(Vec<Value>),
    /// Unreachable reached — immediate UB.
    Unreachable,
    /// Trap — abort execution.
    Trap,
}

/// UB violation detected during execution.
#[derive(Debug, Clone)]
pub struct UbViolation {
    pub kind: UbKind,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UbKind {
    /// Annotation violation producing poison was observed.
    PoisonObserved,
    /// Division by zero.
    DivisionByZero,
    /// Read of uninitialized memory.
    UninitRead,
    /// Memory error (OOB, use-after-free, etc.).
    MemoryViolation,
    /// Unreachable code reached.
    UnreachableReached,
    /// Trap instruction executed.
    TrapExecuted,
    /// Invalid operand for operation.
    InvalidOperand,
}

impl std::fmt::Display for UbViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "UB: {:?}: {}", self.kind, self.message)
    }
}

/// Apply an annotation to an integer value. Returns poison if violated.
pub fn apply_annotation(val: &BigInt, ann: &IntAnnotation) -> Value {
    let n = ann.bit_width as usize;
    if n == 0 {
        return Value::Poison;
    }
    // Truncate to n bits first (wrapping semantics).
    let modulus = BigInt::one() << n;
    let truncated = ((val % &modulus) + &modulus) % &modulus;
    match ann.signedness {
        IntSignedness::Signed => {
            // Interpret as signed: if high bit set, subtract modulus.
            let sign_bit = BigInt::one() << (n - 1);
            if truncated >= sign_bit {
                Value::Int(truncated - modulus)
            } else {
                Value::Int(truncated)
            }
        }
        IntSignedness::Unsigned | IntSignedness::DontCare => Value::Int(truncated),
    }
}

/// Apply a result annotation to a value. Returns the (possibly poisoned) value.
pub fn apply_result_annotation(val: Value, ann: &Option<Annotation>) -> Value {
    match (&val, ann) {
        (Value::Poison, _) => Value::Poison,
        (Value::Int(n), Some(Annotation::Int(int_ann))) => apply_annotation(n, int_ann),
        _ => val,
    }
}

/// Resolve an operand: apply use-side annotation if present.
fn resolve_operand(val: &Value, ann: &Option<Annotation>) -> Value {
    match (val, ann) {
        (Value::Poison, _) => Value::Poison,
        (Value::Int(n), Some(Annotation::Int(int_ann))) => apply_annotation(n, int_ann),
        _ => val.clone(),
    }
}

/// Helper to get two integer operands. Returns None (=poison) if either is not int.
fn get_int_binop(a: &Value, b: &Value) -> Option<(BigInt, BigInt)> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Some((x.clone(), y.clone())),
        _ => None,
    }
}

/// Truncate to low n bits (positive result in [0, 2^n)).
fn truncate_to_bits(val: &BigInt, n: usize) -> BigInt {
    if n == 0 {
        return BigInt::zero();
    }
    let modulus = BigInt::one() << n;
    ((val % &modulus) + &modulus) % &modulus
}

/// Infer the minimum unsigned bit width needed for a value.
/// Rounds up to the nearest standard width (8, 16, 32, 64, 128).
fn infer_unsigned_width(val: &BigInt) -> usize {
    let needed = if val.sign() == num_bigint::Sign::Minus {
        // Two's complement: -(val) - 1 gives the positive magnitude,
        // then add 1 for the sign bit.
        let mag = (-val) - BigInt::one();
        mag.bits() as usize + 1
    } else {
        std::cmp::max(val.bits() as usize, 1)
    };
    if needed <= 8 {
        8
    } else if needed <= 16 {
        16
    } else if needed <= 32 {
        32
    } else if needed <= 64 {
        64
    } else {
        128
    }
}

/// Sign-extend from n bits to infinite precision.
fn sign_extend(val: &BigInt, n: usize) -> BigInt {
    if n == 0 {
        return BigInt::zero();
    }
    let truncated = truncate_to_bits(val, n);
    let sign_bit = BigInt::one() << (n - 1);
    if truncated >= sign_bit {
        let modulus = BigInt::one() << n;
        truncated - modulus
    } else {
        truncated
    }
}

/// Wrap a signed result to n bits (two's complement).
fn wrap_signed(val: &BigInt, n: usize) -> BigInt {
    sign_extend(&truncate_to_bits(val, n), n)
}

/// Wrap an unsigned result to n bits.
fn wrap_unsigned(val: &BigInt, n: usize) -> BigInt {
    truncate_to_bits(val, n)
}

// ── Floating-point helpers ──

/// Execute a binary float operation using rustc_apfloat.
fn exec_float_arith(fa: &FloatConst, fb: &FloatConst, op_name: &str) -> Value {
    let ft = fa.float_type();
    match ft {
        FloatType::F32 => {
            let a = Single::from_bits(fa.to_bits());
            let b = Single::from_bits(fb.to_bits());
            let result = match op_name {
                "add" => (a + b).value,
                "sub" => (a - b).value,
                "mul" => (a * b).value,
                "div" => (a / b).value,
                _ => return Value::Poison,
            };
            Value::Float(FloatConst::from_bits(ft, result.to_bits()))
        }
        FloatType::F64 => {
            let a = Double::from_bits(fa.to_bits());
            let b = Double::from_bits(fb.to_bits());
            let result = match op_name {
                "add" => (a + b).value,
                "sub" => (a - b).value,
                "mul" => (a * b).value,
                "div" => (a / b).value,
                _ => return Value::Poison,
            };
            Value::Float(FloatConst::from_bits(ft, result.to_bits()))
        }
        FloatType::F16 => {
            let a = Half::from_bits(fa.to_bits());
            let b = Half::from_bits(fb.to_bits());
            let result = match op_name {
                "add" => (a + b).value,
                "sub" => (a - b).value,
                "mul" => (a * b).value,
                "div" => (a / b).value,
                _ => return Value::Poison,
            };
            Value::Float(FloatConst::from_bits(ft, result.to_bits()))
        }
        FloatType::F128 => {
            let a = Quad::from_bits(fa.to_bits());
            let b = Quad::from_bits(fb.to_bits());
            let result = match op_name {
                "add" => (a + b).value,
                "sub" => (a - b).value,
                "mul" => (a * b).value,
                "div" => (a / b).value,
                _ => return Value::Poison,
            };
            Value::Float(FloatConst::from_bits(ft, result.to_bits()))
        }
        FloatType::BF16 => {
            // BFloat: convert via f32
            let a_f32 = f32::from_bits((fa.to_bits() as u32) << 16);
            let b_f32 = f32::from_bits((fb.to_bits() as u32) << 16);
            let result = match op_name {
                "add" => a_f32 + b_f32,
                "sub" => a_f32 - b_f32,
                "mul" => a_f32 * b_f32,
                "div" => a_f32 / b_f32,
                _ => return Value::Poison,
            };
            let result_bits = (result.to_bits() >> 16) as u128;
            Value::Float(FloatConst::from_bits(ft, result_bits))
        }
    }
}

/// Check if a float is NaN.
fn float_is_nan(fc: &FloatConst) -> bool {
    match fc.float_type() {
        FloatType::F32 => Single::from_bits(fc.to_bits()).is_nan(),
        FloatType::F64 => Double::from_bits(fc.to_bits()).is_nan(),
        FloatType::F16 => Half::from_bits(fc.to_bits()).is_nan(),
        FloatType::F128 => Quad::from_bits(fc.to_bits()).is_nan(),
        FloatType::BF16 => {
            let bits = fc.to_bits() as u16;
            f32::from_bits((bits as u32) << 16).is_nan()
        }
    }
}

/// Compare two floats. Returns (is_less, is_equal, is_greater, is_unordered).
fn float_compare(a: &FloatConst, b: &FloatConst) -> (bool, bool, bool, bool) {
    let a_nan = float_is_nan(a);
    let b_nan = float_is_nan(b);
    if a_nan || b_nan {
        return (false, false, false, true);
    }
    // Use f64 for comparison (sufficient precision for all types except f128).
    let a_f64 = float_to_f64(a);
    let b_f64 = float_to_f64(b);
    (a_f64 < b_f64, a_f64 == b_f64, a_f64 > b_f64, false)
}

pub fn float_to_f64(fc: &FloatConst) -> f64 {
    match fc.float_type() {
        FloatType::F64 => f64::from_bits(fc.to_bits() as u64),
        FloatType::F32 => f32::from_bits(fc.to_bits() as u32) as f64,
        FloatType::F16 => {
            let h = Half::from_bits(fc.to_bits());
            let StatusAnd { value: d, .. } = h.convert(&mut false);
            let d: Double = d;
            f64::from_bits(d.to_bits() as u64)
        }
        FloatType::BF16 => {
            let bits = fc.to_bits() as u16;
            f32::from_bits((bits as u32) << 16) as f64
        }
        FloatType::F128 => {
            // Lossy conversion for comparison purposes
            let q = Quad::from_bits(fc.to_bits());
            let StatusAnd { value: d, .. } = q.convert(&mut false);
            let d: Double = d;
            f64::from_bits(d.to_bits() as u64)
        }
    }
}

/// Execute a single instruction.
///
/// `resolve_value` is a closure that looks up a ValueRef in the current environment.
#[allow(clippy::too_many_arguments)]
pub fn execute_instruction(
    op: &Op,
    ty: &Type,
    result_annotation: &Option<Annotation>,
    _secondary_ty: &Option<Type>,
    secondary_result_annotation: &Option<Annotation>,
    resolve_value: &dyn Fn(ValueRef) -> Value,
    resolve_operand_value: &dyn Fn(&Operand) -> Value,
    memory: &mut Memory,
    alloc_stack_slot: &mut dyn FnMut(usize) -> AllocId,
    resolve_symbol: &dyn Fn(tuffy_ir::module::SymbolId) -> Value,
    def_annotation: &dyn Fn(ValueRef) -> Option<Annotation>,
) -> Result<ExecResult, UbViolation> {
    /// Helper: resolve an operand with its annotation applied.
    fn res_op(resolve_value: &dyn Fn(ValueRef) -> Value, op: &Operand) -> Value {
        let base = resolve_value(op.value);
        resolve_operand(&base, &op.annotation)
    }

    /// Get the source bit width from an operand: prefer use-site annotation,
    /// fall back to definition-site annotation.
    fn operand_bit_width(
        op: &Operand,
        def_annotation: &dyn Fn(ValueRef) -> Option<Annotation>,
    ) -> Option<usize> {
        op.annotation
            .as_ref()
            .and_then(|ann| match ann {
                Annotation::Int(ia) => Some(ia.bit_width as usize),
                _ => None,
            })
            .or_else(|| {
                def_annotation(op.value).and_then(|ann| match ann {
                    Annotation::Int(ia) => Some(ia.bit_width as usize),
                    _ => None,
                })
            })
    }

    match op {
        // ── Constants ──
        Op::Const(n) => {
            let v = Value::Int(n.clone());
            Ok(ExecResult::Value(apply_result_annotation(
                v,
                result_annotation,
            )))
        }
        Op::BConst(b) => Ok(ExecResult::Value(Value::Bool(*b))),
        Op::FConst(fc) => Ok(ExecResult::Value(Value::Float(*fc))),
        Op::Param(_) => {
            // Param values are pre-populated by the caller.
            // This instruction just references the already-set value.
            // The caller handles this specially before calling execute_instruction.
            unreachable!("Param should be handled before execute_instruction")
        }

        // ── Integer Arithmetic ──
        Op::Add(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x + y),
                None if va.is_poison() || vb.is_poison() => Value::Poison,
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Sub(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x - y),
                None if va.is_poison() || vb.is_poison() => Value::Poison,
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Mul(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x * y),
                None if va.is_poison() || vb.is_poison() => Value::Poison,
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Div(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((_, ref y)) if y.is_zero() => Value::Poison,
                Some((x, y)) => Value::Int(x / y),
                None if va.is_poison() || vb.is_poison() => Value::Poison,
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Rem(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((_, ref y)) if y.is_zero() => Value::Poison,
                Some((x, y)) => Value::Int(x % y),
                None if va.is_poison() || vb.is_poison() => Value::Poison,
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Bitwise ──
        Op::And(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x & y),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Or(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x | y),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Xor(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x ^ y),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Boolean ──
        Op::BAnd(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_bool(), vb.as_bool()) {
                (Some(x), Some(y)) => Ok(ExecResult::Value(Value::Bool(x && y))),
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::BOr(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_bool(), vb.as_bool()) {
                (Some(x), Some(y)) => Ok(ExecResult::Value(Value::Bool(x || y))),
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::BXor(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_bool(), vb.as_bool()) {
                (Some(x), Some(y)) => Ok(ExecResult::Value(Value::Bool(x ^ y))),
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Shifts ──
        Op::Shl(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((_, ref y)) if y.is_negative() => Value::Poison,
                Some((x, y)) => {
                    if let Some(shift) = y.to_u64() {
                        Value::Int(x << shift)
                    } else {
                        // Shift amount too large; result is implementation-defined.
                        // For infinite precision, shifting by huge amount is valid.
                        Value::Int(BigInt::zero())
                    }
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Shr(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((_, ref y)) if y.is_negative() => Value::Poison,
                Some((x, y)) => {
                    if let Some(shift) = y.to_u64() {
                        Value::Int(x >> shift)
                    } else {
                        if x.is_negative() {
                            Value::Int(BigInt::from(-1))
                        } else {
                            Value::Int(BigInt::zero())
                        }
                    }
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Min/Max ──
        Op::Min(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            // Apply result annotation before comparison so signed values
            // are properly interpreted (e.g. DontCare u64 -32768 → s64 -32768).
            let va = apply_result_annotation(va, result_annotation);
            let vb = apply_result_annotation(vb, result_annotation);
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x.min(y)),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }
        Op::Max(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let va = apply_result_annotation(va, result_annotation);
            let vb = apply_result_annotation(vb, result_annotation);
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => Value::Int(x.max(y)),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }

        // ── Bit manipulation ──
        Op::CountOnes(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match &va {
                Value::Int(n) if n.is_negative() => Value::Poison,
                Value::Int(n) => {
                    let count = n
                        .to_bytes_le()
                        .1
                        .iter()
                        .map(|b| b.count_ones() as u64)
                        .sum::<u64>();
                    Value::Int(BigInt::from(count))
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::CountLeadingZeros(a, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let n = *n as usize;
            let result = if n == 0 {
                Value::Poison
            } else {
                match &va {
                    Value::Int(v) => {
                        let truncated = truncate_to_bits(v, n);
                        if truncated.is_zero() {
                            Value::Int(BigInt::from(n))
                        } else {
                            let bits = truncated.bits() as usize;
                            Value::Int(BigInt::from(n - bits))
                        }
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::CountTrailingZeros(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match &va {
                Value::Int(n) if n.is_negative() || n.is_zero() => Value::Poison,
                Value::Int(n) => {
                    let mut count = 0u64;
                    let mut v = n.clone();
                    while (&v & BigInt::one()).is_zero() {
                        count += 1;
                        v >>= 1;
                    }
                    Value::Int(BigInt::from(count))
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Bswap(a, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let n = *n as usize;
            let result = if n == 0 {
                Value::Poison
            } else {
                match &va {
                    Value::Int(v) => {
                        let truncated = truncate_to_bits(v, n * 8);
                        let bytes: Vec<u8> = (0..n)
                            .map(|i| {
                                ((&truncated >> (i * 8)) & BigInt::from(0xffu8))
                                    .to_u8()
                                    .unwrap_or(0)
                            })
                            .collect();
                        let reversed: Vec<u8> = bytes.into_iter().rev().collect();
                        Value::Int(BigInt::from_bytes_le(num_bigint::Sign::Plus, &reversed))
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::BitReverse(a, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let n = *n as usize;
            let result = if n == 0 {
                Value::Poison
            } else {
                match &va {
                    Value::Int(v) => {
                        let truncated = truncate_to_bits(v, n);
                        let mut reversed = BigInt::zero();
                        for i in 0..n {
                            if (&truncated >> i) & BigInt::one() == BigInt::one() {
                                reversed |= BigInt::one() << (n - 1 - i);
                            }
                        }
                        Value::Int(reversed)
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Merge/Split ──
        Op::Merge(a, b, width) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let w = *width as usize;
            let result = if w == 0 {
                Value::Poison
            } else {
                match get_int_binop(&va, &vb) {
                    Some((x, y)) => {
                        let mask = (BigInt::one() << w) - 1;
                        let hi = &x >> w << w;
                        Value::Int(hi | (&y & &mask))
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Split(a, width) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let w = *width as usize;
            if w == 0 {
                Ok(ExecResult::MultiValue(Value::Poison, Value::Poison))
            } else {
                match &va {
                    Value::Int(v) => {
                        let lo = truncate_to_bits(v, w);
                        let hi = v >> w;
                        let hi = apply_result_annotation(Value::Int(hi), result_annotation);
                        let lo =
                            apply_result_annotation(Value::Int(lo), secondary_result_annotation);
                        Ok(ExecResult::MultiValue(hi, lo))
                    }
                    _ => Ok(ExecResult::MultiValue(Value::Poison, Value::Poison)),
                }
            }
        }

        // ── Carry-less multiply ──
        Op::Clmul(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((ref x, _)) if x.is_negative() => Value::Poison,
                Some((_, ref y)) if y.is_negative() => Value::Poison,
                Some((x, y)) => {
                    let mut result = BigInt::zero();
                    let bits_b = y.bits();
                    for i in 0..bits_b {
                        if (&y >> i) & BigInt::one() == BigInt::one() {
                            result ^= &x << i;
                        }
                    }
                    Value::Int(result)
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Rotations ──
        Op::RotateLeft(a, b, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let n = *n as usize;
            let result = if n == 0 {
                Value::Poison
            } else {
                match get_int_binop(&va, &vb) {
                    Some((x, y)) => {
                        let amt = (((y % BigInt::from(n)) + BigInt::from(n)) % BigInt::from(n))
                            .to_usize()
                            .unwrap_or(0);
                        let trunc = truncate_to_bits(&x, n);
                        let rotated = (&trunc << amt) | (&trunc >> (n - amt));
                        Value::Int(truncate_to_bits(&rotated, n))
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::RotateRight(a, b, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let n = *n as usize;
            let result = if n == 0 {
                Value::Poison
            } else {
                match get_int_binop(&va, &vb) {
                    Some((x, y)) => {
                        let amt = (((y % BigInt::from(n)) + BigInt::from(n)) % BigInt::from(n))
                            .to_usize()
                            .unwrap_or(0);
                        let trunc = truncate_to_bits(&x, n);
                        let rotated = (&trunc >> amt) | (&trunc << (n - amt));
                        Value::Int(truncate_to_bits(&rotated, n))
                    }
                    _ => Value::Poison,
                }
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }

        // ── Saturating arithmetic ──
        Op::SaturatingAdd(a, b, n) => {
            exec_saturating(a, b, *n, true, false, result_annotation, resolve_value)
        }
        Op::SaturatingSub(a, b, n) => {
            exec_saturating(a, b, *n, false, false, result_annotation, resolve_value)
        }
        Op::SignedSaturatingAdd(a, b, n) => {
            exec_saturating(a, b, *n, true, true, result_annotation, resolve_value)
        }
        Op::SignedSaturatingSub(a, b, n) => {
            exec_saturating(a, b, *n, false, true, result_annotation, resolve_value)
        }

        // ── Overflow-detecting arithmetic ──
        Op::SAddWithOverflow(a, b, n) => exec_overflow(
            a,
            b,
            *n,
            true,
            true,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),
        Op::UAddWithOverflow(a, b, n) => exec_overflow(
            a,
            b,
            *n,
            true,
            false,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),
        Op::SSubWithOverflow(a, b, n) => exec_overflow(
            a,
            b,
            *n,
            false,
            true,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),
        Op::USubWithOverflow(a, b, n) => exec_overflow(
            a,
            b,
            *n,
            false,
            false,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),
        Op::SMulWithOverflow(a, b, n) => exec_mul_overflow(
            a,
            b,
            *n,
            true,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),
        Op::UMulWithOverflow(a, b, n) => exec_mul_overflow(
            a,
            b,
            *n,
            false,
            result_annotation,
            secondary_result_annotation,
            resolve_value,
        ),

        // ── Comparison ──
        Op::ICmp(cmp_op, a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            let result = match get_int_binop(&va, &vb) {
                Some((x, y)) => {
                    let b = match cmp_op {
                        // For equality, compare unsigned bit patterns to handle
                        // mixed signed/unsigned representations of the same value.
                        // Use operand annotations to determine the comparison width
                        // rather than inferring from value magnitude, which can
                        // incorrectly equate values like -128_i64 and 128_i64
                        // (both fit in 8 bits but differ at 64-bit width).
                        ICmpOp::Eq | ICmpOp::Ne => {
                            let wa = operand_bit_width(&a.clone().raw(), def_annotation);
                            let wb = operand_bit_width(&b.clone().raw(), def_annotation);
                            let w = match (wa, wb) {
                                (Some(a), Some(b)) => std::cmp::max(a, b),
                                (Some(a), None) => a,
                                (None, Some(b)) => b,
                                (None, None) => std::cmp::max(
                                    infer_unsigned_width(&x),
                                    infer_unsigned_width(&y),
                                ),
                            };
                            let mask = (BigInt::one() << w) - 1;
                            let xu = &x & &mask;
                            let yu = &y & &mask;
                            match cmp_op {
                                ICmpOp::Eq => xu == yu,
                                _ => xu != yu,
                            }
                        }
                        ICmpOp::Lt => x < y,
                        ICmpOp::Le => x <= y,
                        ICmpOp::Gt => x > y,
                        ICmpOp::Ge => x >= y,
                    };
                    Value::Bool(b)
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }
        Op::FCmp(cmp_op, a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_float(), vb.as_float()) {
                (Some(fa), Some(fb)) => {
                    let (lt, eq, gt, uno) = float_compare(fa, fb);
                    let result = match cmp_op {
                        FCmpOp::False => false,
                        FCmpOp::OEq => eq,
                        FCmpOp::OGt => gt,
                        FCmpOp::OGe => gt || eq,
                        FCmpOp::OLt => lt,
                        FCmpOp::OLe => lt || eq,
                        FCmpOp::ONe => lt || gt,
                        FCmpOp::Ord => !uno,
                        FCmpOp::Uno => uno,
                        FCmpOp::UEq => uno || eq,
                        FCmpOp::UGt => uno || gt,
                        FCmpOp::UGe => uno || gt || eq,
                        FCmpOp::ULt => uno || lt,
                        FCmpOp::ULe => uno || lt || eq,
                        FCmpOp::UNe => uno || lt || gt,
                        FCmpOp::True => true,
                    };
                    Ok(ExecResult::Value(Value::Bool(result)))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Select ──
        Op::Select(cond, true_val, false_val) => {
            let vc = res_op(resolve_value, &cond.clone().raw());
            match vc.as_bool() {
                Some(true) => {
                    let v = resolve_operand_value(true_val);
                    Ok(ExecResult::Value(v))
                }
                Some(false) => {
                    let v = resolve_operand_value(false_val);
                    Ok(ExecResult::Value(v))
                }
                None => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Memory ──
        Op::StackSlot(bytes, _align) => {
            let id = alloc_stack_slot(*bytes as usize);
            Ok(ExecResult::Value(Value::Ptr(Pointer {
                alloc_id: id,
                offset: 0,
            })))
        }
        Op::Load(ptr_op, byte_count, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = *byte_count as usize;
                    match memory.read(ptr, n) {
                        Ok(bytes) => {
                            let val = bytes_to_value(&bytes, ty, n);
                            Ok(ExecResult::Value(apply_result_annotation(
                                val,
                                result_annotation,
                            )))
                        }
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                None if vp.is_poison() => Ok(ExecResult::Value(Value::Poison)),
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "load from non-pointer value".into(),
                }),
            }
        }
        Op::Store(val_op, ptr_op, byte_count, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            let vv = resolve_operand_value(val_op);
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = *byte_count as usize;
                    let bytes = value_to_bytes(&vv, n);
                    match memory.write(ptr, &bytes) {
                        Ok(()) => Ok(ExecResult::Value(Value::Mem)),
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                None if vp.is_poison() => Err(UbViolation {
                    kind: UbKind::MemoryViolation,
                    message: "store through poison pointer".into(),
                }),
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "store to non-pointer value".into(),
                }),
            }
        }
        Op::MemCopy(dst, src, count, _mem) => {
            let vd = res_op(resolve_value, &dst.clone().raw());
            let vs = res_op(resolve_value, &src.clone().raw());
            let vc = res_op(resolve_value, &count.clone().raw());
            match (vd.as_ptr(), vs.as_ptr(), vc.as_int()) {
                (Some(d), Some(s), Some(n)) => {
                    let n = n.to_usize().unwrap_or(0);
                    match memory.memcpy(d, s, n) {
                        Ok(()) => Ok(ExecResult::Value(Value::Mem)),
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "invalid memcpy operands".into(),
                }),
            }
        }
        Op::MemMove(dst, src, count, _mem) => {
            let vd = res_op(resolve_value, &dst.clone().raw());
            let vs = res_op(resolve_value, &src.clone().raw());
            let vc = res_op(resolve_value, &count.clone().raw());
            match (vd.as_ptr(), vs.as_ptr(), vc.as_int()) {
                (Some(d), Some(s), Some(n)) => {
                    let n = n.to_usize().unwrap_or(0);
                    match memory.memmove(d, s, n) {
                        Ok(()) => Ok(ExecResult::Value(Value::Mem)),
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "invalid memmove operands".into(),
                }),
            }
        }
        Op::MemSet(dst, val, count, _mem) => {
            let vd = res_op(resolve_value, &dst.clone().raw());
            let vv = resolve_operand_value(val);
            let vc = res_op(resolve_value, &count.clone().raw());
            match (vd.as_ptr(), &vv, vc.as_int()) {
                (Some(d), Value::Int(byte_val), Some(n)) => {
                    let n = n.to_usize().unwrap_or(0);
                    let b = byte_val.to_u8().unwrap_or(0);
                    match memory.memset(d, b, n) {
                        Ok(()) => Ok(ExecResult::Value(Value::Mem)),
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "invalid memset operands".into(),
                }),
            }
        }

        // ── Atomic memory (sequential semantics) ──
        Op::LoadAtomic(ptr_op, _ordering, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = type_byte_size(ty);
                    match memory.read(ptr, n) {
                        Ok(bytes) => {
                            let val = bytes_to_value(&bytes, ty, n);
                            let annotated =
                                apply_result_annotation(val, secondary_result_annotation);
                            Ok(ExecResult::MultiValue(Value::Mem, annotated))
                        }
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                None => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "atomic load from non-pointer".into(),
                }),
            }
        }
        Op::StoreAtomic(val_op, ptr_op, _ordering, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            let vv = resolve_operand_value(val_op);
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = type_byte_size(ty);
                    let bytes = value_to_bytes(&vv, n);
                    match memory.write(ptr, &bytes) {
                        Ok(()) => Ok(ExecResult::Value(Value::Mem)),
                        Err(e) => Err(UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        }),
                    }
                }
                None => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "atomic store to non-pointer".into(),
                }),
            }
        }
        Op::Fence(_ordering, _mem) => Ok(ExecResult::Value(Value::Mem)),
        Op::AtomicRmw(rmw_op, ptr_op, val_op, _ordering, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            let vv = resolve_operand_value(val_op);
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = type_byte_size(ty);
                    let old_bytes = memory.read(ptr, n).map_err(|e| UbViolation {
                        kind: UbKind::MemoryViolation,
                        message: e.to_string(),
                    })?;
                    let old_val = bytes_to_value(&old_bytes, ty, n);
                    let new_val = match (old_val.as_int(), vv.as_int()) {
                        (Some(old), Some(new)) => {
                            use tuffy_ir::instruction::AtomicRmwOp;
                            let result = match rmw_op {
                                AtomicRmwOp::Xchg => new.clone(),
                                AtomicRmwOp::Add => old + new,
                                AtomicRmwOp::Sub => old - new,
                                AtomicRmwOp::And => old & new,
                                AtomicRmwOp::Or => old | new,
                                AtomicRmwOp::Xor => old ^ new,
                            };
                            Value::Int(result)
                        }
                        _ => Value::Poison,
                    };
                    let new_bytes = value_to_bytes(&new_val, n);
                    memory.write(ptr, &new_bytes).map_err(|e| UbViolation {
                        kind: UbKind::MemoryViolation,
                        message: e.to_string(),
                    })?;
                    let annotated = apply_result_annotation(old_val, secondary_result_annotation);
                    Ok(ExecResult::MultiValue(Value::Mem, annotated))
                }
                None => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "atomic rmw on non-pointer".into(),
                }),
            }
        }
        Op::AtomicCmpXchg(ptr_op, expected, desired, _succ_ord, _fail_ord, _mem) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            let ve = resolve_operand_value(expected);
            let vd = resolve_operand_value(desired);
            match vp.as_ptr() {
                Some(ptr) => {
                    let n = type_byte_size(ty);
                    let old_bytes = memory.read(ptr, n).map_err(|e| UbViolation {
                        kind: UbKind::MemoryViolation,
                        message: e.to_string(),
                    })?;
                    let old_val = bytes_to_value(&old_bytes, ty, n);
                    // Compare old with expected
                    let matches = match (old_val.as_int(), ve.as_int()) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    };
                    if matches {
                        let new_bytes = value_to_bytes(&vd, n);
                        memory.write(ptr, &new_bytes).map_err(|e| UbViolation {
                            kind: UbKind::MemoryViolation,
                            message: e.to_string(),
                        })?;
                    }
                    let annotated = apply_result_annotation(old_val, secondary_result_annotation);
                    Ok(ExecResult::MultiValue(Value::Mem, annotated))
                }
                None => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "cmpxchg on non-pointer".into(),
                }),
            }
        }

        // ── Symbol address ──
        Op::SymbolAddr(sym_id) => {
            let v = resolve_symbol(*sym_id);
            Ok(ExecResult::Value(v))
        }

        Op::TlsSymbolAddr(sym_id) => {
            let v = resolve_symbol(*sym_id);
            Ok(ExecResult::Value(v))
        }

        // ── Call ──
        Op::Call(_, _, _) => {
            // Calls are handled specially by the interpreter (interp.rs).
            unreachable!("Call should be handled by the interpreter, not the executor")
        }

        // ── Type conversions ──
        Op::Bitcast(op) => {
            let v = resolve_operand_value(op);
            let result = match (&v, ty) {
                // Float → Int: extract bit pattern.
                (Value::Float(fc), Type::Int) => Value::Int(BigInt::from(fc.to_bits())),
                // Int → Float: interpret bits as float.
                (Value::Int(n), Type::Float(ft)) => {
                    let bits = n.to_u128().unwrap_or(0);
                    Value::Float(FloatConst::from_bits(*ft, bits))
                }
                _ => v,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Sext(a, n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let _n = *n as usize;
            let result = match &va {
                Value::Int(v) => {
                    let src_bits = operand_bit_width(&a.clone().raw(), def_annotation);
                    match src_bits {
                        Some(src) => Value::Int(sign_extend(&truncate_to_bits(v, src), src)),
                        None => Value::Int(v.clone()),
                    }
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::Zext(a, _n) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match &va {
                Value::Int(v) => {
                    let src_bits = operand_bit_width(&a.clone().raw(), def_annotation);
                    match src_bits {
                        Some(src) => Value::Int(truncate_to_bits(v, src)),
                        None => Value::Int(v.clone()),
                    }
                }
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::FpToSi(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match va.as_float() {
                Some(fc) => {
                    let f = float_to_f64(fc);
                    // Check result annotation to determine conversion width.
                    let result_bw = match result_annotation {
                        Some(Annotation::Int(ia)) => ia.bit_width as usize,
                        _ => 64,
                    };
                    if result_bw > 64 {
                        // Use i128 saturating semantics for wide results.
                        Value::Int(BigInt::from(f as i128))
                    } else {
                        Value::Int(BigInt::from(f as i64))
                    }
                }
                None => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::FpToUi(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match va.as_float() {
                Some(fc) => {
                    let f = float_to_f64(fc);
                    let result_bw = match result_annotation {
                        Some(Annotation::Int(ia)) => ia.bit_width as usize,
                        _ => 64,
                    };
                    if result_bw > 64 {
                        Value::Int(BigInt::from(f as u128))
                    } else {
                        Value::Int(BigInt::from(f as u64))
                    }
                }
                None => Value::Poison,
            };
            Ok(ExecResult::Value(apply_result_annotation(
                result,
                result_annotation,
            )))
        }
        Op::SiToFp(a, ft) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match va.as_int() {
                Some(n) => {
                    let f = n.to_f64().unwrap_or(0.0);
                    let bits = match ft {
                        FloatType::F32 => (f as f32).to_bits() as u128,
                        FloatType::F64 => f.to_bits() as u128,
                        FloatType::F16 => {
                            let s = Single::from_bits((f as f32).to_bits() as u128);
                            let StatusAnd { value: h, .. } = s.convert(&mut false);
                            let h: Half = h;
                            h.to_bits()
                        }
                        FloatType::BF16 => ((f as f32).to_bits() >> 16) as u128,
                        FloatType::F128 => {
                            let d = Double::from_bits(f.to_bits() as u128);
                            let StatusAnd { value: q, .. } = d.convert(&mut false);
                            let q: Quad = q;
                            q.to_bits()
                        }
                    };
                    Value::Float(FloatConst::from_bits(*ft, bits))
                }
                None => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }
        Op::UiToFp(a, ft) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let result = match va.as_int() {
                Some(n) => {
                    // Ensure unsigned: if still negative, mask to inferred width.
                    let n = if n.sign() == num_bigint::Sign::Minus {
                        let w = infer_unsigned_width(n);
                        let mask = (BigInt::from(1u128) << w) - 1;
                        n & &mask
                    } else {
                        n.clone()
                    };
                    let f = n.to_f64().unwrap_or(0.0);
                    let bits = match ft {
                        FloatType::F32 => (f as f32).to_bits() as u128,
                        FloatType::F64 => f.to_bits() as u128,
                        FloatType::F16 => {
                            let s = Single::from_bits((f as f32).to_bits() as u128);
                            let StatusAnd { value: h, .. } = s.convert(&mut false);
                            let h: Half = h;
                            h.to_bits()
                        }
                        FloatType::BF16 => ((f as f32).to_bits() >> 16) as u128,
                        FloatType::F128 => {
                            let d = Double::from_bits(f.to_bits() as u128);
                            let StatusAnd { value: q, .. } = d.convert(&mut false);
                            let q: Quad = q;
                            q.to_bits()
                        }
                    };
                    Value::Float(FloatConst::from_bits(*ft, bits))
                }
                None => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }
        Op::FpConvert(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            match (va.as_float(), ty) {
                (Some(fc), Type::Float(target_ft)) => {
                    let f = float_to_f64(fc);
                    let bits = match target_ft {
                        FloatType::F32 => (f as f32).to_bits() as u128,
                        FloatType::F64 => f.to_bits() as u128,
                        FloatType::F16 => {
                            let s = Single::from_bits((f as f32).to_bits() as u128);
                            let StatusAnd { value: h, .. } = s.convert(&mut false);
                            let h: Half = h;
                            h.to_bits()
                        }
                        FloatType::BF16 => ((f as f32).to_bits() >> 16) as u128,
                        FloatType::F128 => {
                            let d = Double::from_bits(f.to_bits() as u128);
                            let StatusAnd { value: q, .. } = d.convert(&mut false);
                            let q: Quad = q;
                            q.to_bits()
                        }
                    };
                    Ok(ExecResult::Value(Value::Float(FloatConst::from_bits(
                        *target_ft, bits,
                    ))))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Floating-point arithmetic ──
        Op::FAdd(a, b, _flags) => exec_float_binop(a, b, "add", resolve_value),
        Op::FSub(a, b, _flags) => exec_float_binop(a, b, "sub", resolve_value),
        Op::FMul(a, b, _flags) => exec_float_binop(a, b, "mul", resolve_value),
        Op::FDiv(a, b, _flags) => exec_float_binop(a, b, "div", resolve_value),
        Op::FRem(a, b, _flags) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_float(), vb.as_float()) {
                (Some(fa), Some(fb)) => {
                    let a_f64 = float_to_f64(fa);
                    let b_f64 = float_to_f64(fb);
                    let result = a_f64 % b_f64;
                    let ft = fa.float_type();
                    let bits = match ft {
                        FloatType::F32 => (result as f32).to_bits() as u128,
                        FloatType::F64 => result.to_bits() as u128,
                        _ => (result as f32).to_bits() as u128,
                    };
                    Ok(ExecResult::Value(Value::Float(FloatConst::from_bits(
                        ft, bits,
                    ))))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::FMinNum(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            #[allow(clippy::if_same_then_else)]
            // NaN handling branches intentionally differ in semantics
            match (va.as_float(), vb.as_float()) {
                (Some(fa), Some(fb)) => {
                    let result = if float_is_nan(fa) {
                        *fb
                    } else if float_is_nan(fb) {
                        *fa
                    } else if float_to_f64(fa) < float_to_f64(fb) {
                        *fa
                    } else {
                        *fb
                    };
                    Ok(ExecResult::Value(Value::Float(result)))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::FMaxNum(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            #[allow(clippy::if_same_then_else)]
            match (va.as_float(), vb.as_float()) {
                (Some(fa), Some(fb)) => {
                    let result = if float_is_nan(fa) {
                        *fb
                    } else if float_is_nan(fb) {
                        *fa
                    } else if float_to_f64(fa) > float_to_f64(fb) {
                        *fa
                    } else {
                        *fb
                    };
                    Ok(ExecResult::Value(Value::Float(result)))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::FNeg(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            match va.as_float() {
                Some(fc) => {
                    let ft = fc.float_type();
                    // Flip sign bit
                    let sign_bit: u128 = match ft {
                        FloatType::BF16 | FloatType::F16 => 1 << 15,
                        FloatType::F32 => 1 << 31,
                        FloatType::F64 => 1 << 63,
                        FloatType::F128 => 1 << 127,
                    };
                    Ok(ExecResult::Value(Value::Float(FloatConst::from_bits(
                        ft,
                        fc.to_bits() ^ sign_bit,
                    ))))
                }
                None => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::FAbs(a) => {
            let va = res_op(resolve_value, &a.clone().raw());
            match va.as_float() {
                Some(fc) => {
                    let ft = fc.float_type();
                    let sign_mask: u128 = match ft {
                        FloatType::BF16 | FloatType::F16 => !(1u128 << 15),
                        FloatType::F32 => !(1u128 << 31),
                        FloatType::F64 => !(1u128 << 63),
                        FloatType::F128 => !(1u128 << 127),
                    };
                    Ok(ExecResult::Value(Value::Float(FloatConst::from_bits(
                        ft,
                        fc.to_bits() & sign_mask,
                    ))))
                }
                None => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::CopySign(mag, sign) => {
            let vm = res_op(resolve_value, &mag.clone().raw());
            let vs = res_op(resolve_value, &sign.clone().raw());
            match (vm.as_float(), vs.as_float()) {
                (Some(fm), Some(fs)) => {
                    let ft = fm.float_type();
                    let sign_bit: u128 = match ft {
                        FloatType::BF16 | FloatType::F16 => 1 << 15,
                        FloatType::F32 => 1 << 31,
                        FloatType::F64 => 1 << 63,
                        FloatType::F128 => 1 << 127,
                    };
                    let mag_bits = fm.to_bits() & !sign_bit;
                    let sign_bits = fs.to_bits() & sign_bit;
                    Ok(ExecResult::Value(Value::Float(FloatConst::from_bits(
                        ft,
                        mag_bits | sign_bits,
                    ))))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Pointer operations ──
        Op::PtrAdd(ptr_op, offset_op) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            let vo = res_op(resolve_value, &offset_op.clone().raw());
            match (vp.as_ptr(), vo.as_int()) {
                (Some(ptr), Some(offset)) => {
                    let new_offset = ptr.offset + offset.to_i64().unwrap_or(0);
                    Ok(ExecResult::Value(Value::Ptr(Pointer {
                        alloc_id: ptr.alloc_id,
                        offset: new_offset,
                    })))
                }
                _ if vp.is_poison() || vo.is_poison() => Ok(ExecResult::Value(Value::Poison)),
                _ => Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "ptradd with invalid operands".into(),
                }),
            }
        }
        Op::PtrDiff(a, b) => {
            let va = res_op(resolve_value, &a.clone().raw());
            let vb = res_op(resolve_value, &b.clone().raw());
            match (va.as_ptr(), vb.as_ptr()) {
                (Some(pa), Some(pb)) => {
                    if pa.alloc_id == pb.alloc_id {
                        Ok(ExecResult::Value(apply_result_annotation(
                            Value::Int(BigInt::from(pa.offset - pb.offset)),
                            result_annotation,
                        )))
                    } else {
                        Ok(ExecResult::Value(Value::Poison))
                    }
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::PtrToInt(ptr_op) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            match vp.as_ptr() {
                Some(ptr) => Ok(ExecResult::Value(apply_result_annotation(
                    Value::Int(BigInt::from(ptr.offset)),
                    result_annotation,
                ))),
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::PtrToAddr(ptr_op) => {
            let vp = res_op(resolve_value, &ptr_op.clone().raw());
            match vp.as_ptr() {
                Some(ptr) => {
                    let addr = (ptr.alloc_id.0 as i64) * SYNTH_ADDR_BASE + ptr.offset;
                    Ok(ExecResult::Value(apply_result_annotation(
                        Value::Int(BigInt::from(addr)),
                        result_annotation,
                    )))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }
        Op::IntToPtr(int_op) => {
            let vi = res_op(resolve_value, &int_op.clone().raw());
            match vi.as_int() {
                Some(n) => {
                    let addr = n.to_i64().unwrap_or(0);
                    Ok(ExecResult::Value(Value::Ptr(addr_to_pointer(addr))))
                }
                _ => Ok(ExecResult::Value(Value::Poison)),
            }
        }

        // ── Aggregate operations ──
        Op::ExtractValue(agg_op, indices) => {
            let v = resolve_operand_value(agg_op);
            let result = extract_value(&v, indices);
            Ok(ExecResult::Value(result))
        }
        Op::InsertValue(agg_op, val_op, indices) => {
            let agg = resolve_operand_value(agg_op);
            let val = resolve_operand_value(val_op);
            let result = insert_value(agg, &val, indices);
            Ok(ExecResult::Value(result))
        }

        // ── Terminators ──
        Op::Ret(val, _mem) => {
            let ret_val = val.as_ref().map(resolve_operand_value);
            Ok(ExecResult::Terminator(TerminatorAction::Return(ret_val)))
        }
        Op::Br(target, args) => {
            let arg_vals: Vec<Value> = args.iter().map(resolve_operand_value).collect();
            Ok(ExecResult::Terminator(TerminatorAction::Branch(
                *target, arg_vals,
            )))
        }
        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            let vc = res_op(resolve_value, &cond.clone().raw());
            let then_vals: Vec<Value> = then_args.iter().map(resolve_operand_value).collect();
            let else_vals: Vec<Value> = else_args.iter().map(resolve_operand_value).collect();
            Ok(ExecResult::Terminator(TerminatorAction::BranchIf {
                cond: vc,
                then_block: *then_block,
                then_args: then_vals,
                else_block: *else_block,
                else_args: else_vals,
            }))
        }
        Op::Continue(args) => {
            let arg_vals: Vec<Value> = args.iter().map(resolve_operand_value).collect();
            Ok(ExecResult::Terminator(TerminatorAction::Continue(arg_vals)))
        }
        Op::RegionYield(args) => {
            let arg_vals: Vec<Value> = args.iter().map(resolve_operand_value).collect();
            Ok(ExecResult::Terminator(TerminatorAction::RegionYield(
                arg_vals,
            )))
        }
        Op::Unreachable => Ok(ExecResult::Terminator(TerminatorAction::Unreachable)),
        Op::Trap => Ok(ExecResult::Terminator(TerminatorAction::Trap)),
        Op::LandingPad => {
            // The interpreter doesn't model exception handling. Treat as unreachable.
            Ok(ExecResult::Terminator(TerminatorAction::Unreachable))
        }
    }
}

// ── Helper functions ──

fn exec_float_binop(
    a: &tuffy_ir::typed::FloatOperand,
    b: &tuffy_ir::typed::FloatOperand,
    op_name: &str,
    resolve_value: &dyn Fn(ValueRef) -> Value,
) -> Result<ExecResult, UbViolation> {
    fn res_op(resolve_value: &dyn Fn(ValueRef) -> Value, op: &Operand) -> Value {
        let base = resolve_value(op.value);
        resolve_operand(&base, &op.annotation)
    }
    let va = res_op(resolve_value, &a.clone().raw());
    let vb = res_op(resolve_value, &b.clone().raw());
    match (va.as_float(), vb.as_float()) {
        (Some(fa), Some(fb)) => {
            let result = match op_name {
                "add" => exec_float_arith(fa, fb, "add"),
                "sub" => exec_float_arith(fa, fb, "sub"),
                "mul" => exec_float_arith(fa, fb, "mul"),
                "div" => exec_float_arith(fa, fb, "div"),
                _ => Value::Poison,
            };
            Ok(ExecResult::Value(result))
        }
        _ => Ok(ExecResult::Value(Value::Poison)),
    }
}

fn exec_saturating(
    a: &tuffy_ir::typed::IntOperand,
    b: &tuffy_ir::typed::IntOperand,
    n: u32,
    is_add: bool,
    is_signed: bool,
    result_annotation: &Option<Annotation>,
    resolve_value: &dyn Fn(ValueRef) -> Value,
) -> Result<ExecResult, UbViolation> {
    fn res_op(resolve_value: &dyn Fn(ValueRef) -> Value, op: &Operand) -> Value {
        let base = resolve_value(op.value);
        resolve_operand(&base, &op.annotation)
    }
    let va = res_op(resolve_value, &a.clone().raw());
    let vb = res_op(resolve_value, &b.clone().raw());
    let n = n as usize;
    if n == 0 {
        return Ok(ExecResult::Value(Value::Poison));
    }
    let result = match get_int_binop(&va, &vb) {
        Some((x, y)) => {
            let raw = if is_add { &x + &y } else { &x - &y };
            if is_signed {
                let min = -(BigInt::one() << (n - 1));
                let max = (BigInt::one() << (n - 1)) - 1;
                Value::Int(raw.max(min).min(max))
            } else {
                let max = (BigInt::one() << n) - 1;
                Value::Int(raw.max(BigInt::zero()).min(max))
            }
        }
        _ => Value::Poison,
    };
    Ok(ExecResult::Value(apply_result_annotation(
        result,
        result_annotation,
    )))
}

#[allow(clippy::too_many_arguments)]
fn exec_overflow(
    a: &tuffy_ir::typed::IntOperand,
    b: &tuffy_ir::typed::IntOperand,
    n: u32,
    is_add: bool,
    is_signed: bool,
    result_annotation: &Option<Annotation>,
    _secondary_result_annotation: &Option<Annotation>,
    resolve_value: &dyn Fn(ValueRef) -> Value,
) -> Result<ExecResult, UbViolation> {
    fn res_op(resolve_value: &dyn Fn(ValueRef) -> Value, op: &Operand) -> Value {
        let base = resolve_value(op.value);
        resolve_operand(&base, &op.annotation)
    }
    let va = res_op(resolve_value, &a.clone().raw());
    let vb = res_op(resolve_value, &b.clone().raw());
    let n = n as usize;
    if n == 0 {
        return Ok(ExecResult::MultiValue(Value::Poison, Value::Poison));
    }
    match get_int_binop(&va, &vb) {
        Some((x, y)) => {
            let raw = if is_add { &x + &y } else { &x - &y };
            let (wrapped, overflowed) = if is_signed {
                let min = -(BigInt::one() << (n - 1));
                let max = (BigInt::one() << (n - 1)) - 1;
                let of = raw > max || raw < min;
                (wrap_signed(&raw, n), of)
            } else {
                let max = (BigInt::one() << n) - 1;
                let of = raw > max || raw < BigInt::zero();
                (wrap_unsigned(&raw, n), of)
            };
            let v1 = apply_result_annotation(Value::Int(wrapped), result_annotation);
            let v2 = Value::Bool(overflowed);
            Ok(ExecResult::MultiValue(v1, v2))
        }
        _ => Ok(ExecResult::MultiValue(Value::Poison, Value::Poison)),
    }
}

fn exec_mul_overflow(
    a: &tuffy_ir::typed::IntOperand,
    b: &tuffy_ir::typed::IntOperand,
    n: u32,
    is_signed: bool,
    result_annotation: &Option<Annotation>,
    _secondary_result_annotation: &Option<Annotation>,
    resolve_value: &dyn Fn(ValueRef) -> Value,
) -> Result<ExecResult, UbViolation> {
    fn res_op(resolve_value: &dyn Fn(ValueRef) -> Value, op: &Operand) -> Value {
        let base = resolve_value(op.value);
        resolve_operand(&base, &op.annotation)
    }
    let va = res_op(resolve_value, &a.clone().raw());
    let vb = res_op(resolve_value, &b.clone().raw());
    let n = n as usize;
    if n == 0 {
        return Ok(ExecResult::MultiValue(Value::Poison, Value::Poison));
    }
    match get_int_binop(&va, &vb) {
        Some((x, y)) => {
            let raw = &x * &y;
            let (wrapped, overflowed) = if is_signed {
                let min = -(BigInt::one() << (n - 1));
                let max = (BigInt::one() << (n - 1)) - 1;
                let of = raw > max || raw < min;
                (wrap_signed(&raw, n), of)
            } else {
                let max = (BigInt::one() << n) - 1;
                let of = raw > max || raw < BigInt::zero();
                (wrap_unsigned(&raw, n), of)
            };
            let v1 = apply_result_annotation(Value::Int(wrapped), result_annotation);
            let v2 = Value::Bool(overflowed);
            Ok(ExecResult::MultiValue(v1, v2))
        }
        _ => Ok(ExecResult::MultiValue(Value::Poison, Value::Poison)),
    }
}

/// Get the byte size of a type (for memory operations).
pub fn type_byte_size(ty: &Type) -> usize {
    match ty {
        Type::Bool => 1,
        Type::Int => 8, // Default: 8 bytes for memory operations
        Type::Unit => 0,
        Type::Byte(n) => *n as usize,
        Type::Ptr(_) => 8,
        Type::Float(ft) => match ft {
            FloatType::BF16 | FloatType::F16 => 2,
            FloatType::F32 => 4,
            FloatType::F64 => 8,
            FloatType::F128 => 16,
        },
        Type::Mem => 0,
        Type::Vec(vt) => (vt.base_width() / 8) as usize,
        Type::Struct(fields) => fields.iter().map(type_byte_size).sum(),
        Type::Array(elem, count) => type_byte_size(elem) * (*count as usize),
    }
}

/// Convert memory bytes to a Value based on the target type.
fn bytes_to_value(bytes: &[AbstractByte], ty: &Type, n: usize) -> Value {
    // Treat Uninit as 0 — codegen may emit wide loads that span padding bytes.
    // Real hardware reads arbitrary junk; we pick 0 for determinism.
    // Check for pointer fragments
    let has_ptr_fragments = bytes
        .iter()
        .any(|b| matches!(b, AbstractByte::PtrFragment(_, _, _)));
    if has_ptr_fragments && n == 8 {
        // Try to reconstruct a pointer
        if let Some((alloc_id, offset)) = bytes.iter().find_map(|b| match b {
            AbstractByte::PtrFragment(id, off, _) => Some((*id, *off)),
            _ => None,
        }) {
            // Verify all bytes are fragments of the same pointer
            let all_same = bytes.iter().enumerate().all(|(i, b)| {
                matches!(b, AbstractByte::PtrFragment(id, off, idx) if *id == alloc_id && *off == offset && *idx == i)
            });
            if all_same {
                return Value::Ptr(Pointer { alloc_id, offset });
            }
        }
    }
    match ty {
        Type::Int => le_bytes_to_int(bytes, false)
            .map(Value::Int)
            .unwrap_or(Value::Poison),
        Type::Bool => match bytes.first() {
            Some(AbstractByte::Bits(0)) => Value::Bool(false),
            Some(AbstractByte::Bits(1)) => Value::Bool(true),
            _ => Value::Poison,
        },
        Type::Ptr(_) => {
            // If not reconstructed as pointer fragments above, try as integer address.
            // Reverse the synthetic address scheme from PtrToAddr.
            le_bytes_to_int(bytes, false)
                .map(|n| Value::Ptr(addr_to_pointer(n.to_i64().unwrap_or(0))))
                .unwrap_or(Value::Poison)
        }
        Type::Float(ft) => {
            let mut bits: u128 = 0;
            for (i, b) in bytes.iter().enumerate() {
                match b {
                    AbstractByte::Bits(v) => bits |= (*v as u128) << (i * 8),
                    // Treat Uninit/Poison as 0 for padding tolerance.
                    AbstractByte::Uninit | AbstractByte::Poison => {}
                    _ => return Value::Poison,
                }
            }
            Value::Float(FloatConst::from_bits(*ft, bits))
        }
        _ => {
            // For other types, return as Bytes
            Value::Bytes(bytes.to_vec())
        }
    }
}

/// Convert a Value to memory bytes.
fn value_to_bytes(val: &Value, n: usize) -> Vec<AbstractByte> {
    match val {
        Value::Int(i) => int_to_le_bytes(i, n),
        Value::Bool(b) => {
            let mut bytes = vec![AbstractByte::Bits(if *b { 1 } else { 0 })];
            bytes.resize(n, AbstractByte::Bits(0));
            bytes
        }
        Value::Float(fc) => float_to_le_bytes(fc),
        Value::Ptr(ptr) => ptr_to_le_bytes(ptr),
        Value::Bytes(bs) => {
            let mut result = bs.clone();
            result.resize(n, AbstractByte::Uninit);
            result
        }
        Value::Poison => vec![AbstractByte::Poison; n],
        Value::Unit => vec![],
        Value::Aggregate(_) => vec![AbstractByte::Uninit; n],
        Value::Mem => vec![],
    }
}

/// Extract a value from a nested aggregate using an index path.
fn extract_value(val: &Value, indices: &[u32]) -> Value {
    if indices.is_empty() {
        return val.clone();
    }
    match val {
        Value::Aggregate(fields) => {
            let idx = indices[0] as usize;
            if idx < fields.len() {
                extract_value(&fields[idx], &indices[1..])
            } else {
                Value::Poison
            }
        }
        Value::Poison => Value::Poison,
        _ => Value::Poison,
    }
}

/// Insert a value into a nested aggregate at an index path.
fn insert_value(agg: Value, val: &Value, indices: &[u32]) -> Value {
    if indices.is_empty() {
        return val.clone();
    }
    match agg {
        Value::Aggregate(mut fields) => {
            let idx = indices[0] as usize;
            if idx < fields.len() {
                fields[idx] = insert_value(fields[idx].clone(), val, &indices[1..]);
                Value::Aggregate(fields)
            } else {
                Value::Poison
            }
        }
        _ => Value::Poison,
    }
}
