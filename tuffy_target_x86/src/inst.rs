//! x86-64 machine instruction definitions.

use std::fmt;
use std::hash::Hash;

use crate::reg::Gpr;
use tuffy_regalloc::VReg;

/// Trait bound for register types used in MInst.
pub trait RegType: Copy + Clone + PartialEq + Eq + Hash + fmt::Debug {}

impl RegType for Gpr {}
impl RegType for VReg {}

/// Type alias for virtual-register instructions (pre-regalloc).
pub type VInst = MInst<VReg>;

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

/// Type alias for physical-register instructions (post-regalloc).
pub type PInst = MInst<Gpr>;

/// A machine-level x86-64 instruction, generic over register type `R`.
///
/// Isel emits `MInst<VReg>`, regalloc rewrites to `MInst<Gpr>` (`PInst`),
/// and the encoder consumes `PInst`.
#[derive(Debug, Clone)]
pub enum MInst<R: RegType> {
    /// mov reg, reg
    MovRR { size: OpSize, dst: R, src: R },
    /// mov reg, imm32
    MovRI { size: OpSize, dst: R, imm: i64 },
    /// add dst, src (dst += src)
    AddRR { size: OpSize, dst: R, src: R },
    /// sub dst, src (dst -= src)
    SubRR { size: OpSize, dst: R, src: R },
    /// imul dst, src (dst *= src)
    ImulRR { size: OpSize, dst: R, src: R },
    /// ret
    Ret,
    /// Label (pseudo-instruction, not emitted as code).
    Label { id: u32 },
    /// jmp rel32 (unconditional jump to label)
    Jmp { target: u32 },
    /// jcc rel32 (conditional jump to label)
    Jcc { cc: CondCode, target: u32 },
    /// cmp r/m, r (compare two registers, sets flags)
    CmpRR { size: OpSize, src1: R, src2: R },
    /// cmp r/m, imm32 (compare register with immediate)
    CmpRI { size: OpSize, src: R, imm: i32 },
    /// test r/m, r (AND without storing, sets flags)
    TestRR { size: OpSize, src1: R, src2: R },
    /// call to named symbol (uses relocation)
    CallSym {
        name: String,
        ret: Option<R>,
        ret2: Option<R>,
    },
    /// indirect call through register (call *%reg)
    CallReg {
        callee: R,
        ret: Option<R>,
        ret2: Option<R>,
    },
    /// push reg onto stack
    Push { reg: R },
    /// pop reg from stack
    Pop { reg: R },
    /// sub rsp, imm32 (allocate stack space)
    SubSPI { imm: i32 },
    /// add rsp, imm32 (deallocate stack space)
    AddSPI { imm: i32 },
    /// mov reg, [base+offset] (load from memory)
    MovRM {
        size: OpSize,
        dst: R,
        base: R,
        offset: i32,
    },
    /// mov [base+offset], reg (store to memory)
    MovMR {
        size: OpSize,
        base: R,
        offset: i32,
        src: R,
    },
    /// lea reg, [base+offset] (load effective address)
    Lea { dst: R, base: R, offset: i32 },
    /// mov reg, imm64 (64-bit immediate, REX.W + B8+rd io)
    MovRI64 { dst: R, imm: i64 },
    /// mov [base+offset], imm32 (store immediate to memory)
    MovMI {
        size: OpSize,
        base: R,
        offset: i32,
        imm: i32,
    },
    /// lea reg, [rip+symbol] (RIP-relative address of named symbol)
    LeaSymbol { dst: R, symbol: String },
    /// or dst, src (dst |= src)
    OrRR { size: OpSize, dst: R, src: R },
    /// and dst, src (dst &= src)
    AndRR { size: OpSize, dst: R, src: R },
    /// xor dst, src (dst ^= src)
    XorRR { size: OpSize, dst: R, src: R },
    /// shl dst, cl (dst <<= cl)
    ShlRCL { size: OpSize, dst: R },
    /// shr dst, cl (logical right shift by cl)
    ShrRCL { size: OpSize, dst: R },
    /// sar dst, cl (arithmetic right shift by cl)
    SarRCL { size: OpSize, dst: R },
    /// shl dst, imm8 (dst <<= imm8)
    ShlImm { size: OpSize, dst: R, imm: u8 },
    /// sar dst, imm8 (arithmetic right shift by immediate)
    SarImm { size: OpSize, dst: R, imm: u8 },
    /// and dst, imm32 (dst &= imm32)
    AndRI { size: OpSize, dst: R, imm: i64 },
    /// cmovcc dst, src (conditional move based on condition code)
    CMOVcc {
        size: OpSize,
        cc: CondCode,
        dst: R,
        src: R,
    },
    /// setcc dst (set byte based on condition code)
    SetCC { cc: CondCode, dst: R },
    /// movzx r64, r8 (zero-extend byte to qword)
    MovzxB { dst: R, src: R },
    /// movzx r64, r16 (zero-extend word to qword)
    MovzxW { dst: R, src: R },
    /// movsx r64, r8 (sign-extend byte to qword)
    MovsxB { dst: R, src: R },
    /// movsx r64, r16 (sign-extend word to qword)
    MovsxW { dst: R, src: R },
    /// movsxd r64, r32 (sign-extend dword to qword)
    MovsxD { dst: R, src: R },
    /// cqo (sign-extend RAX into RDX:RAX)
    Cqo,
    /// Pseudo-instruction: 64-bit division/remainder.
    ///
    /// Expanded by the encoder into: mov rcx,rhs; mov rax,lhs; xor edx,edx
    /// (or cqo for signed); div/idiv rcx; mov dst,rax (or rdx for rem).
    ///
    /// This avoids exposing the implicit RAX/RCX/RDX usage to the register
    /// allocator, which cannot reliably handle multiple fixed-register
    /// constraints in the same function.
    DivRem {
        dst: R,
        lhs: R,
        rhs: R,
        signed: bool,
        rem: bool,
    },
    /// popcnt r64, r64 (population count)
    Popcnt { dst: R, src: R },
    /// lzcnt r64, r64 (count leading zeros)
    Lzcnt { dst: R, src: R },
    /// tzcnt r64, r64 (count trailing zeros)
    Tzcnt { dst: R, src: R },
    /// ud2 (undefined instruction trap)
    Ud2,
}
