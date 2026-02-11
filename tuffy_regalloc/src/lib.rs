//! Target-agnostic register allocator.
//!
//! Provides a linear scan register allocator that operates on virtual registers
//! and rewrites them to physical registers. Backends implement the [`RegAllocInst`]
//! and [`RegAllocTarget`] traits to integrate with the allocator.

pub mod allocator;
pub mod liveness;

use std::fmt;

/// Operand kind: whether a register is read, written, or both.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpKind {
    /// Register is read by this instruction.
    Use,
    /// Register is written by this instruction.
    Def,
    /// Register is both read and written (e.g., `add dst, src`).
    UseDef,
}

/// A register operand declaration for the allocator.
#[derive(Debug, Clone, Copy)]
pub struct RegOp {
    pub vreg: VReg,
    pub kind: OpKind,
}

/// Trait that instructions implement to declare register operands and
/// control flow properties for liveness analysis and register allocation.
pub trait RegAllocInst {
    /// Append all register operands of this instruction to `ops`.
    fn reg_operands(&self, ops: &mut Vec<RegOp>);

    /// If this instruction is a label pseudo-instruction, return its ID.
    fn label_id(&self) -> Option<u32>;

    /// Append branch target label IDs to `targets`.
    /// For unconditional jumps: one target.
    /// For conditional branches: one target (fallthrough is implicit).
    fn branch_targets(&self, targets: &mut Vec<u32>);

    /// Append physical registers clobbered by this instruction to `clobbers`.
    /// Used for call instructions that destroy caller-saved registers.
    fn clobbers(&self, clobbers: &mut Vec<PReg>);

    /// Whether this instruction is a terminator (ret, jmp, etc.).
    fn is_terminator(&self) -> bool;
}

/// A virtual register produced by instruction selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A physical register, target-agnostic representation.
/// The `hw` field holds the hardware encoding (e.g. 0..15 for x86-64 GPRs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PReg(pub u8);

impl fmt::Display for PReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "p{}", self.0)
    }
}
