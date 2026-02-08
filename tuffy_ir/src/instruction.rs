//! Instruction definitions for tuffy IR.

use crate::types::Type;
use crate::value::{BlockRef, ValueRef};

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
    pub origin: Origin,
}

/// Integer comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ICmpOp {
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
    Ult,
    Ule,
    Ugt,
    Uge,
}

/// Instruction opcodes.
#[derive(Debug, Clone)]
pub enum Op {
    /// Function parameter. Index into the parameter list.
    Param(u32),
    /// Integer addition: add %a, %b
    Add(ValueRef, ValueRef),
    /// Integer subtraction: sub %a, %b
    Sub(ValueRef, ValueRef),
    /// Integer multiplication: mul %a, %b
    Mul(ValueRef, ValueRef),
    /// Assert signed extension: produces poison if value doesn't fit in n-bit signed range.
    AssertSext(ValueRef, u32),
    /// Assert zero extension: produces poison if value doesn't fit in n-bit unsigned range.
    AssertZext(ValueRef, u32),
    /// Integer constant.
    Const(i64),

    // -- Comparison --
    /// Integer comparison.
    ICmp(ICmpOp, ValueRef, ValueRef),

    // -- Memory --
    /// Load from pointer.
    Load(ValueRef),
    /// Store value to pointer: store val, ptr.
    Store(ValueRef, ValueRef),
    /// Allocate n bytes on stack, returns pointer.
    StackSlot(u32),

    // -- Call --
    /// Call function with arguments.
    Call(ValueRef, Vec<ValueRef>),

    // -- Type conversion --
    /// Bitcast (reinterpret bits).
    Bitcast(ValueRef),
    /// Sign-extend to n bits (for lowering).
    Sext(ValueRef, u32),
    /// Zero-extend to n bits (for lowering).
    Zext(ValueRef, u32),

    // -- Terminators (by convention, placed last in a basic block) --
    /// Return value from function.
    Ret(Option<ValueRef>),
    /// Unconditional branch with block arguments.
    Br(BlockRef, Vec<ValueRef>),
    /// Conditional branch: brif cond, then_block(args...), else_block(args...).
    BrIf(ValueRef, BlockRef, Vec<ValueRef>, BlockRef, Vec<ValueRef>),
    /// Loop backedge: continue with values fed back to loop header.
    Continue(Vec<ValueRef>),
    /// Exit region with values.
    RegionYield(Vec<ValueRef>),
}
