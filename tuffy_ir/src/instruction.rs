//! Instruction definitions for tuffy IR.

use num_bigint::BigInt;

use crate::module::SymbolId;
use crate::types::{Annotation, FpRewriteFlags, MemoryOrdering, Type};
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
}

impl Instruction {
    /// Number of results this instruction produces (1 or 2).
    pub fn result_count(&self) -> u8 {
        if self.secondary_ty.is_some() { 2 } else { 1 }
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
    Add(Operand, Operand),
    /// Integer subtraction: sub %a, %b
    Sub(Operand, Operand),
    /// Integer multiplication: mul %a, %b
    Mul(Operand, Operand),
    /// Integer division: div %a, %b (poison on div-by-zero)
    Div(Operand, Operand),
    /// Integer remainder: rem %a, %b (poison on div-by-zero)
    Rem(Operand, Operand),
    /// Bitwise AND: and %a, %b
    And(Operand, Operand),
    /// Bitwise OR: or %a, %b
    Or(Operand, Operand),
    /// Bitwise XOR: xor %a, %b
    Xor(Operand, Operand),
    /// Left shift: shl %a, %b (poison if shift amount < 0)
    Shl(Operand, Operand),
    /// Right shift: shr %a, %b (poison if shift amount < 0).
    /// Signedness is a property of operand annotations, not the operation.
    Shr(Operand, Operand),
    /// Integer minimum: min %a, %b
    Min(Operand, Operand),
    /// Integer maximum: max %a, %b
    Max(Operand, Operand),
    /// Population count: count the number of set bits.
    CountOnes(Operand),
    /// Integer constant (arbitrary precision, matching Lean `Int`).
    Const(BigInt),

    // -- Comparison --
    /// Integer comparison. Returns Bool.
    ICmp(ICmpOp, Operand, Operand),

    // -- Select --
    /// Conditional select: select cond, true_val, false_val. Cond must be Bool.
    Select(Operand, Operand, Operand),
    /// Convert Bool to Int: true → 1, false → 0.
    BoolToInt(Operand),

    // -- Memory --
    /// Load from pointer. Second field is byte count. Third is mem token input.
    Load(Operand, u32, Operand),
    /// Store value to pointer: store val, ptr. Third field is byte count. Fourth is mem token input.
    Store(Operand, Operand, u32, Operand),
    /// Allocate n bytes on stack, returns pointer.
    StackSlot(u32),

    // -- Atomic memory operations --
    /// Atomic load from pointer with memory ordering. Third is mem token input.
    LoadAtomic(Operand, MemoryOrdering, Operand),
    /// Atomic store value to pointer: store.atomic val, ptr, ordering. Fourth is mem token input.
    StoreAtomic(Operand, Operand, MemoryOrdering, Operand),
    /// Atomic read-modify-write: rmw op, ptr, val, ordering. Fifth is mem token input.
    AtomicRmw(AtomicRmwOp, Operand, Operand, MemoryOrdering, Operand),
    /// Atomic compare-and-exchange: cmpxchg ptr, expected, desired, success_ord, failure_ord.
    /// Returns the old value; caller uses icmp to check success. Sixth is mem token input.
    AtomicCmpXchg(
        Operand,
        Operand,
        Operand,
        MemoryOrdering,
        MemoryOrdering,
        Operand,
    ),
    /// Memory fence with ordering. Second is mem token input.
    Fence(MemoryOrdering, Operand),

    // -- Symbol --
    /// Load the address of a symbol (function or static data).
    /// The SymbolId indexes into the module's symbol table.
    SymbolAddr(SymbolId),

    // -- Call --
    /// Call function with arguments. Third is mem token input.
    Call(Operand, Vec<Operand>, Operand),

    // -- Type conversion --
    /// Bitcast (reinterpret bits).
    Bitcast(Operand),
    /// Sign-extend to n bits (for lowering).
    Sext(Operand, u32),
    /// Zero-extend to n bits (for lowering).
    Zext(Operand, u32),

    // -- Floating point arithmetic --
    /// Floating point addition: fadd %a, %b
    FAdd(Operand, Operand, FpRewriteFlags),
    /// Floating point subtraction: fsub %a, %b
    FSub(Operand, Operand, FpRewriteFlags),
    /// Floating point multiplication: fmul %a, %b
    FMul(Operand, Operand, FpRewriteFlags),
    /// Floating point division: fdiv %a, %b
    FDiv(Operand, Operand, FpRewriteFlags),
    /// Floating point negation: fneg %a
    FNeg(Operand),
    /// Floating point absolute value: fabs %a
    FAbs(Operand),
    /// Copy sign: copysign %mag, %sign
    CopySign(Operand, Operand),

    // -- Pointer operations --
    /// Pointer addition: ptradd ptr, offset → ptr (preserves provenance).
    PtrAdd(Operand, Operand),
    /// Pointer difference: ptrdiff ptr_a, ptr_b → int (same allocation).
    PtrDiff(Operand, Operand),
    /// Pointer to integer with provenance capture.
    PtrToInt(Operand),
    /// Pointer to address (discard provenance).
    PtrToAddr(Operand),
    /// Integer to pointer (no valid provenance).
    IntToPtr(Operand),

    // -- Terminators (by convention, placed last in a basic block) --
    /// Return value from function. Second is mem token output.
    Ret(Option<Operand>, Operand),
    /// Unconditional branch with block arguments.
    Br(BlockRef, Vec<Operand>),
    /// Conditional branch: brif cond, then_block(args...), else_block(args...).
    BrIf(Operand, BlockRef, Vec<Operand>, BlockRef, Vec<Operand>),
    /// Loop backedge: continue with values fed back to loop header.
    Continue(Vec<Operand>),
    /// Exit region with values.
    RegionYield(Vec<Operand>),
    /// Unreachable: indicates control flow should never reach this point.
    Unreachable,
    /// Trap: unconditionally abort execution (e.g., failed assertion).
    Trap,
}
