//! x86-64 machine instruction definitions.

use crate::reg::Gpr;

/// Operand size for x86 instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpSize {
    S32,
    S64,
}

/// A machine-level x86-64 instruction.
#[derive(Debug, Clone)]
pub enum MInst {
    /// mov reg, reg
    MovRR { size: OpSize, dst: Gpr, src: Gpr },
    /// mov reg, imm32
    MovRI { size: OpSize, dst: Gpr, imm: i64 },
    /// add dst, src (dst += src)
    AddRR { size: OpSize, dst: Gpr, src: Gpr },
    /// sub dst, src (dst -= src)
    SubRR { size: OpSize, dst: Gpr, src: Gpr },
    /// imul dst, src (dst *= src)
    ImulRR { size: OpSize, dst: Gpr, src: Gpr },
    /// ret
    Ret,
}
