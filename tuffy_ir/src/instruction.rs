//! Instruction definitions for tuffy IR.

use crate::types::Type;
use crate::value::ValueRef;

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

/// Instruction opcodes (minimal subset for first e2e test).
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
    /// Return value from function.
    Ret(Option<ValueRef>),
}
