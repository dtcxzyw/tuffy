//! Instruction definitions for tuffy IR.

use core::fmt;

use num_bigint::BigInt;
use rustc_apfloat::Float;
use rustc_apfloat::ieee::{BFloat, Double, Half, Quad, Single};

use crate::module::SymbolId;
use crate::typed::{BoolOperand, FloatOperand, IntOperand, MemOperand, PtrOperand};
use crate::types::{Annotation, FloatType, FpRewriteFlags, MemoryOrdering, Type};
use crate::value::{BlockRef, ValueRef};

/// An operand: a value reference with an optional use-side annotation.
#[derive(Debug, Clone)]
pub struct Operand {
    pub value: ValueRef,
    pub annotation: Option<Annotation>,
}

impl Operand {
    /// Create an operand with no annotation.
    pub fn new(value: ValueRef) -> Self {
        Self {
            value,
            annotation: None,
        }
    }

    /// Create an operand with an annotation.
    pub fn annotated(value: ValueRef, annotation: Annotation) -> Self {
        Self {
            value,
            annotation: Some(annotation),
        }
    }
}

impl From<ValueRef> for Operand {
    fn from(value: ValueRef) -> Self {
        Self::new(value)
    }
}

/// Origin tracks where an instruction came from (for debug info / profiling).
#[derive(Debug, Clone)]
pub struct Origin {
    /// Source instruction(s) this was derived from.
    pub sources: Vec<u32>,
}

impl Origin {
    /// Create a synthetic origin (no source).
    pub fn synthetic() -> Self {
        Self { sources: vec![] }
    }

    /// Create an origin from a single source.
    pub fn from_source(id: u32) -> Self {
        Self { sources: vec![id] }
    }
}

/// An instruction in the tuffy IR.
#[derive(Debug, Clone)]
pub struct Instruction {
    pub op: Op,
    pub ty: Type,
    /// Secondary result type for multi-result instructions (e.g., load.atomic produces mem + data).
    pub secondary_ty: Option<Type>,
    pub origin: Origin,
    /// Result-side annotation. Violation causes this instruction to produce poison.
    pub result_annotation: Option<Annotation>,
    /// Secondary result annotation (for instructions with secondary_ty).
    pub secondary_result_annotation: Option<Annotation>,
}

impl Instruction {
    /// Number of results this instruction produces (1 or 2).
    pub fn result_count(&self) -> u8 {
        if self.secondary_ty.is_some() { 2 } else { 1 }
    }
}

#[derive(Clone, Copy)]
enum FloatConstRepr {
    BF16(BFloat),
    F16(Half),
    F32(Single),
    F64(Double),
    F128(Quad),
}

/// A floating-point constant backed by `rustc_apfloat`.
#[derive(Clone, Copy)]
pub struct FloatConst(FloatConstRepr);

impl FloatConst {
    /// Construct a float constant from the raw IEEE 754 bit pattern for `ft`.
    pub fn from_bits(ft: FloatType, bits: u128) -> Self {
        Self(match ft {
            FloatType::BF16 => FloatConstRepr::BF16(BFloat::from_bits(bits)),
            FloatType::F16 => FloatConstRepr::F16(Half::from_bits(bits)),
            FloatType::F32 => FloatConstRepr::F32(Single::from_bits(bits)),
            FloatType::F64 => FloatConstRepr::F64(Double::from_bits(bits)),
            FloatType::F128 => FloatConstRepr::F128(Quad::from_bits(bits)),
        })
    }

    /// The float width carried by this constant.
    pub fn float_type(self) -> FloatType {
        match self.0 {
            FloatConstRepr::BF16(_) => FloatType::BF16,
            FloatConstRepr::F16(_) => FloatType::F16,
            FloatConstRepr::F32(_) => FloatType::F32,
            FloatConstRepr::F64(_) => FloatType::F64,
            FloatConstRepr::F128(_) => FloatType::F128,
        }
    }

    /// The exact IEEE 754 bit pattern of this constant.
    pub fn to_bits(self) -> u128 {
        match self.0 {
            FloatConstRepr::BF16(v) => v.to_bits(),
            FloatConstRepr::F16(v) => v.to_bits(),
            FloatConstRepr::F32(v) => v.to_bits(),
            FloatConstRepr::F64(v) => v.to_bits(),
            FloatConstRepr::F128(v) => v.to_bits(),
        }
    }
}

impl PartialEq for FloatConst {
    fn eq(&self, other: &Self) -> bool {
        self.float_type() == other.float_type() && self.to_bits() == other.to_bits()
    }
}

impl Eq for FloatConst {}

impl fmt::Debug for FloatConst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self.float_type() {
            FloatType::BF16 => "bf16",
            FloatType::F16 => "f16",
            FloatType::F32 => "f32",
            FloatType::F64 => "f64",
            FloatType::F128 => "f128",
        };
        write!(f, "FloatConst({name} {:#x})", self.to_bits())
    }
}

/// Integer comparison predicates.
/// Signedness is a property of operand annotations, not the predicate.
/// In infinite precision, comparison is purely mathematical.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ICmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Floating point comparison predicates (LLVM-style 4-bit encoding).
///
/// Each predicate is a 4-bit bitmask:
///   bit 0 = equal, bit 1 = greater-than, bit 2 = less-than, bit 3 = unordered.
/// Ordered predicates return false if either operand is NaN.
/// Unordered predicates return true if either operand is NaN.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FCmpOp {
    /// Always false (0b0000).
    False = 0,
    /// Ordered equal (0b0001).
    OEq = 1,
    /// Ordered greater-than (0b0010).
    OGt = 2,
    /// Ordered greater-or-equal (0b0011).
    OGe = 3,
    /// Ordered less-than (0b0100).
    OLt = 4,
    /// Ordered less-or-equal (0b0101).
    OLe = 5,
    /// Ordered not-equal (0b0110).
    ONe = 6,
    /// Ordered: true iff neither operand is NaN (0b0111).
    Ord = 7,
    /// Unordered: true iff either operand is NaN (0b1000).
    Uno = 8,
    /// Unordered or equal (0b1001).
    UEq = 9,
    /// Unordered or greater-than (0b1010).
    UGt = 10,
    /// Unordered or greater-or-equal (0b1011).
    UGe = 11,
    /// Unordered or less-than (0b1100).
    ULt = 12,
    /// Unordered or less-or-equal (0b1101).
    ULe = 13,
    /// Unordered or not-equal (0b1110).
    UNe = 14,
    /// Always true (0b1111).
    True = 15,
}

/// Atomic read-modify-write operation kinds.
///
/// Mirrors `TuffyLean.IR.AtomicRmwOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AtomicRmwOp {
    /// Exchange (swap).
    Xchg,
    /// Integer addition.
    Add,
    /// Integer subtraction.
    Sub,
    /// Bitwise AND.
    And,
    /// Bitwise OR.
    Or,
    /// Bitwise XOR.
    Xor,
}

/// Instruction opcodes.
///
/// Data operands use `Operand` (value + optional use-side annotation).
/// Block targets use `BlockRef` directly.
#[derive(Debug, Clone)]
pub enum Op {
    /// Function parameter. Index into the parameter list.
    Param(u32),
    /// Integer addition: add %a, %b
    Add(IntOperand, IntOperand),
    /// Integer subtraction: sub %a, %b
    Sub(IntOperand, IntOperand),
    /// Integer multiplication: mul %a, %b
    Mul(IntOperand, IntOperand),
    /// Integer division: div %a, %b (poison on div-by-zero)
    Div(IntOperand, IntOperand),
    /// Integer remainder: rem %a, %b (poison on div-by-zero)
    Rem(IntOperand, IntOperand),
    /// Bitwise AND: and %a, %b
    And(IntOperand, IntOperand),
    /// Bitwise OR: or %a, %b
    Or(IntOperand, IntOperand),
    /// Bitwise XOR: xor %a, %b
    Xor(IntOperand, IntOperand),
    /// Boolean AND: band %a, %b
    BAnd(BoolOperand, BoolOperand),
    /// Boolean OR: bor %a, %b
    BOr(BoolOperand, BoolOperand),
    /// Boolean XOR: bxor %a, %b
    BXor(BoolOperand, BoolOperand),
    /// Left shift: shl %a, %b (poison if shift amount < 0)
    Shl(IntOperand, IntOperand),
    /// Right shift: shr %a, %b (poison if shift amount < 0).
    /// Signedness is a property of operand annotations, not the operation.
    Shr(IntOperand, IntOperand),
    /// Integer minimum: min %a, %b
    Min(IntOperand, IntOperand),
    /// Integer maximum: max %a, %b
    Max(IntOperand, IntOperand),
    /// Population count: count the number of set bits.
    CountOnes(IntOperand),
    /// Count leading zeros: truncate to n bits (mod 2^n), then count leading zero bits.
    /// n = 0 produces poison. Second field is the bit width.
    CountLeadingZeros(IntOperand, u32),
    /// Count trailing zeros: number of zero bits after the least significant set bit.
    /// Defined for non-negative integers; negative values and zero produce poison.
    CountTrailingZeros(IntOperand),
    /// Byte-swap: reverse byte order of the low n bytes. n = 0 produces poison.
    Bswap(IntOperand, u32),
    /// Bit-reverse: reverse bit order of the low n bits. n = 0 produces poison.
    BitReverse(IntOperand, u32),
    /// Merge: replace the low `width` bits of `a` with the low `width` bits of `b`.
    /// width = 0 produces poison.
    Merge(IntOperand, IntOperand, u32),
    /// Split: decompose `a` at bit position `width`.
    /// Produces two results: hi = a >> width, lo = a mod 2^width.
    /// width = 0 produces poison. Multi-result instruction.
    Split(IntOperand, u32),
    /// Carry-less multiplication (polynomial multiplication over GF(2)).
    /// Uses XOR instead of addition for partial product accumulation.
    /// Negative inputs produce poison.
    Clmul(IntOperand, IntOperand),
    /// Rotate left: rotate value left by amount in an n-bit field. n = 0 produces poison.
    RotateLeft(IntOperand, IntOperand, u32),
    /// Rotate right: rotate value right by amount in an n-bit field. n = 0 produces poison.
    RotateRight(IntOperand, IntOperand, u32),
    /// Unsigned saturating addition in n bits. n = 0 produces poison.
    SaturatingAdd(IntOperand, IntOperand, u32),
    /// Unsigned saturating subtraction in n bits. n = 0 produces poison.
    SaturatingSub(IntOperand, IntOperand, u32),
    /// Signed saturating addition in n bits. n = 0 produces poison.
    /// Result is clamped to [-(2^(n-1)), 2^(n-1)-1].
    SignedSaturatingAdd(IntOperand, IntOperand, u32),
    /// Signed saturating subtraction in n bits. n = 0 produces poison.
    /// Result is clamped to [-(2^(n-1)), 2^(n-1)-1].
    SignedSaturatingSub(IntOperand, IntOperand, u32),
    /// Signed addition with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping sum (Int), secondary = overflow flag (Bool).
    SAddWithOverflow(IntOperand, IntOperand, u32),
    /// Unsigned addition with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping sum (Int), secondary = overflow flag (Bool).
    UAddWithOverflow(IntOperand, IntOperand, u32),
    /// Signed subtraction with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping difference (Int), secondary = overflow flag (Bool).
    SSubWithOverflow(IntOperand, IntOperand, u32),
    /// Unsigned subtraction with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping difference (Int), secondary = overflow flag (Bool).
    USubWithOverflow(IntOperand, IntOperand, u32),
    /// Signed multiplication with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping product (Int), secondary = overflow flag (Bool).
    SMulWithOverflow(IntOperand, IntOperand, u32),
    /// Unsigned multiplication with overflow detection in n bits. n = 0 produces poison.
    /// Multi-result: primary = wrapping product (Int), secondary = overflow flag (Bool).
    UMulWithOverflow(IntOperand, IntOperand, u32),
    /// Integer constant (arbitrary precision, matching Lean `Int`).
    Const(BigInt),
    /// Boolean constant: true or false.
    BConst(bool),
    /// Float constant stored as a `rustc_apfloat` value.
    FConst(FloatConst),

    // -- Comparison --
    /// Integer comparison. Returns Bool.
    ICmp(ICmpOp, IntOperand, IntOperand),
    /// Float comparison. Returns Bool.
    FCmp(FCmpOp, FloatOperand, FloatOperand),

    // -- Select --
    /// Conditional select: select cond, true_val, false_val. Cond must be Bool.
    Select(BoolOperand, Operand, Operand),

    // -- Memory --
    /// Load from pointer. Second field is byte count. Third is mem token input.
    Load(PtrOperand, u32, MemOperand),
    /// Store value to pointer: store val, ptr. Third field is byte count. Fourth is mem token input.
    Store(Operand, PtrOperand, u32, MemOperand),
    /// Allocate n bytes on stack, returns pointer.
    StackSlot(u32),
    /// Memory copy (non-overlapping): memcpy semantics.
    /// Args: (dst_ptr, src_ptr, byte_count, mem_token)
    MemCopy(PtrOperand, PtrOperand, IntOperand, MemOperand),
    /// Memory move (may overlap): memmove semantics.
    /// Args: (dst_ptr, src_ptr, byte_count, mem_token)
    MemMove(PtrOperand, PtrOperand, IntOperand, MemOperand),
    /// Memory set: memset semantics.
    /// Args: (dst_ptr, value, byte_count, mem_token)
    MemSet(PtrOperand, Operand, IntOperand, MemOperand),

    // -- Atomic memory operations --
    /// Atomic load from pointer with memory ordering. Third is mem token input.
    LoadAtomic(PtrOperand, MemoryOrdering, MemOperand),
    /// Atomic store value to pointer: store.atomic val, ptr, ordering. Fourth is mem token input.
    StoreAtomic(Operand, PtrOperand, MemoryOrdering, MemOperand),
    /// Atomic read-modify-write: rmw op, ptr, val, ordering. Fifth is mem token input.
    AtomicRmw(AtomicRmwOp, PtrOperand, Operand, MemoryOrdering, MemOperand),
    /// Atomic compare-and-exchange: cmpxchg ptr, expected, desired, success_ord, failure_ord.
    /// Returns the old value; caller uses icmp to check success. Sixth is mem token input.
    AtomicCmpXchg(
        PtrOperand,
        Operand,
        Operand,
        MemoryOrdering,
        MemoryOrdering,
        MemOperand,
    ),
    /// Memory fence with ordering. Second is mem token input.
    Fence(MemoryOrdering, MemOperand),

    // -- Symbol --
    /// Load the address of a symbol (function or static data).
    /// The SymbolId indexes into the module's symbol table.
    SymbolAddr(SymbolId),

    // -- Call --
    /// Call function with arguments. Third is mem token input.
    Call(PtrOperand, Vec<Operand>, MemOperand),

    // -- Type conversion --
    /// Bitcast (reinterpret bits).
    Bitcast(Operand),
    /// Sign-extend to n bits (for lowering).
    Sext(IntOperand, u32),
    /// Zero-extend to n bits (for lowering).
    Zext(IntOperand, u32),
    /// Float to signed integer (truncation toward zero).
    FpToSi(FloatOperand),
    /// Float to unsigned integer (truncation toward zero).
    FpToUi(FloatOperand),
    /// Signed integer to float.
    SiToFp(IntOperand, FloatType),
    /// Unsigned integer to float.
    UiToFp(IntOperand, FloatType),
    /// Float-to-float conversion (widen or narrow).
    FpConvert(FloatOperand),

    // -- Floating point arithmetic --
    /// Floating point addition: fadd %a, %b
    FAdd(FloatOperand, FloatOperand, FpRewriteFlags),
    /// Floating point subtraction: fsub %a, %b
    FSub(FloatOperand, FloatOperand, FpRewriteFlags),
    /// Floating point multiplication: fmul %a, %b
    FMul(FloatOperand, FloatOperand, FpRewriteFlags),
    /// Floating point division: fdiv %a, %b
    FDiv(FloatOperand, FloatOperand, FpRewriteFlags),
    /// Floating point remainder: frem %a, %b
    FRem(FloatOperand, FloatOperand, FpRewriteFlags),
    /// IEEE 754-2008 minNum: fminnum %a, %b
    FMinNum(FloatOperand, FloatOperand),
    /// IEEE 754-2008 maxNum: fmaxnum %a, %b
    FMaxNum(FloatOperand, FloatOperand),
    /// Floating point negation: fneg %a
    FNeg(FloatOperand),
    /// Floating point absolute value: fabs %a
    FAbs(FloatOperand),
    /// Copy sign: copysign %mag, %sign
    CopySign(FloatOperand, FloatOperand),

    // -- Pointer operations --
    /// Pointer addition: ptradd ptr, offset → ptr (preserves provenance).
    PtrAdd(PtrOperand, IntOperand),
    /// Pointer difference: ptrdiff ptr_a, ptr_b → int (same allocation).
    PtrDiff(PtrOperand, PtrOperand),
    /// Pointer to integer with provenance capture.
    PtrToInt(PtrOperand),
    /// Pointer to address (discard provenance).
    PtrToAddr(PtrOperand),
    /// Integer to pointer (no valid provenance).
    IntToPtr(IntOperand),

    // -- Aggregate operations --
    /// Extract value from struct/array at indices path.
    /// ExtractValue(agg, indices) -> element_type
    ExtractValue(Operand, Vec<u32>),
    /// Insert value into struct/array at indices path.
    /// InsertValue(agg, val, indices) -> struct/array_type
    InsertValue(Operand, Operand, Vec<u32>),

    // -- Terminators (by convention, placed last in a basic block) --
    /// Return value from function. Second is mem token output.
    Ret(Option<Operand>, MemOperand),
    /// Unconditional branch with block arguments.
    Br(BlockRef, Vec<Operand>),
    /// Conditional branch: brif cond, then_block(args...), else_block(args...).
    BrIf(BoolOperand, BlockRef, Vec<Operand>, BlockRef, Vec<Operand>),
    /// Loop backedge: continue with values fed back to loop header.
    Continue(Vec<Operand>),
    /// Exit region with values.
    RegionYield(Vec<Operand>),
    /// Unreachable: indicates control flow should never reach this point.
    Unreachable,
    /// Trap: unconditionally abort execution (e.g., failed assertion).
    Trap,
}
