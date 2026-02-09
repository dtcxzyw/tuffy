//! x86-64 machine instruction definitions.

use crate::reg::Gpr;

/// Operand size for x86 instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpSize {
    S8,
    S16,
    S32,
    S64,
}

/// x86 condition codes for Jcc/SETcc/CMOVcc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CondCode {
    /// Equal (ZF=1)
    E,
    /// Not equal (ZF=0)
    Ne,
    /// Signed less than (SF!=OF)
    L,
    /// Signed less or equal (ZF=1 or SF!=OF)
    Le,
    /// Signed greater (ZF=0 and SF=OF)
    G,
    /// Signed greater or equal (SF=OF)
    Ge,
    /// Unsigned below (CF=1)
    B,
    /// Unsigned below or equal (CF=1 or ZF=1)
    Be,
    /// Unsigned above (CF=0 and ZF=0)
    A,
    /// Unsigned above or equal (CF=0)
    Ae,
}

impl CondCode {
    /// 4-bit condition code for Jcc encoding (0x0F 0x80+cc).
    pub fn encoding(self) -> u8 {
        match self {
            CondCode::E => 0x4,
            CondCode::Ne => 0x5,
            CondCode::L => 0xC,
            CondCode::Le => 0xE,
            CondCode::G => 0xF,
            CondCode::Ge => 0xD,
            CondCode::B => 0x2,
            CondCode::Be => 0x6,
            CondCode::A => 0x7,
            CondCode::Ae => 0x3,
        }
    }
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
    /// Label (pseudo-instruction, not emitted as code).
    Label { id: u32 },
    /// jmp rel32 (unconditional jump to label)
    Jmp { target: u32 },
    /// jcc rel32 (conditional jump to label)
    Jcc { cc: CondCode, target: u32 },
    /// cmp r/m, r (compare two registers, sets flags)
    CmpRR { size: OpSize, src1: Gpr, src2: Gpr },
    /// cmp r/m, imm32 (compare register with immediate)
    CmpRI { size: OpSize, src: Gpr, imm: i32 },
    /// test r/m, r (AND without storing, sets flags)
    TestRR { size: OpSize, src1: Gpr, src2: Gpr },
    /// call to named symbol (uses relocation)
    CallSym { name: String },
    /// push reg onto stack
    Push { reg: Gpr },
    /// pop reg from stack
    Pop { reg: Gpr },
    /// sub rsp, imm32 (allocate stack space)
    SubSPI { imm: i32 },
    /// add rsp, imm32 (deallocate stack space)
    AddSPI { imm: i32 },
    /// mov reg, [base+offset] (load from memory)
    MovRM {
        size: OpSize,
        dst: Gpr,
        base: Gpr,
        offset: i32,
    },
    /// mov [base+offset], reg (store to memory)
    MovMR {
        size: OpSize,
        base: Gpr,
        offset: i32,
        src: Gpr,
    },
    /// lea reg, [base+offset] (load effective address)
    Lea { dst: Gpr, base: Gpr, offset: i32 },
    /// mov reg, imm64 (64-bit immediate, REX.W + B8+rd io)
    MovRI64 { dst: Gpr, imm: i64 },
    /// mov [base+offset], imm32 (store immediate to memory)
    MovMI {
        size: OpSize,
        base: Gpr,
        offset: i32,
        imm: i32,
    },
    /// lea reg, [rip+symbol] (RIP-relative address of named symbol)
    LeaSymbol { dst: Gpr, symbol: String },
    /// or dst, src (dst |= src)
    OrRR { size: OpSize, dst: Gpr, src: Gpr },
    /// and dst, src (dst &= src)
    AndRR { size: OpSize, dst: Gpr, src: Gpr },
    /// xor dst, src (dst ^= src)
    XorRR { size: OpSize, dst: Gpr, src: Gpr },
    /// shl dst, cl (dst <<= cl)
    ShlRCL { size: OpSize, dst: Gpr },
    /// shr dst, cl (logical right shift by cl)
    ShrRCL { size: OpSize, dst: Gpr },
    /// sar dst, cl (arithmetic right shift by cl)
    SarRCL { size: OpSize, dst: Gpr },
    /// cmovcc dst, src (conditional move based on condition code)
    CMOVcc { size: OpSize, cc: CondCode, dst: Gpr, src: Gpr },
    /// setcc dst (set byte based on condition code)
    SetCC { cc: CondCode, dst: Gpr },
    /// movzx r64, r8 (zero-extend byte to qword)
    MovzxB { dst: Gpr, src: Gpr },
    /// ud2 (undefined instruction trap)
    Ud2,
}
