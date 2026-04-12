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
    /// 8-bit operand.
    S8,
    /// 16-bit operand.
    S16,
    /// 32-bit operand.
    S32,
    /// 64-bit operand.
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
    /// Overflow (OF=1)
    O,
    /// Not overflow (OF=0)
    No,
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
            CondCode::O => 0x0,
            CondCode::No => 0x1,
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
    MovRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// mov reg, imm32
    MovRI {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: i64,
    },
    /// add dst, src (dst += src)
    AddRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// sub dst, src (dst -= src)
    SubRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// adc dst, src — add with carry (dst += src + CF)
    AdcRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// sbb dst, src — subtract with borrow (dst -= src + CF)
    SbbRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// imul dst, src (dst *= src)
    ImulRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// ret
    Ret,
    /// Label (pseudo-instruction, not emitted as code).
    Label {
        /// Label identifier.
        id: u32,
    },
    /// jmp rel32 (unconditional jump to label)
    Jmp {
        /// Target label id.
        target: u32,
    },
    /// jcc rel32 (conditional jump to label)
    Jcc {
        /// Condition code.
        cc: CondCode,
        /// Target label id.
        target: u32,
    },
    /// cmp r/m, r (compare two registers, sets flags)
    CmpRR {
        /// Operand size.
        size: OpSize,
        /// First source register.
        src1: R,
        /// Second source register.
        src2: R,
    },
    /// cmp r/m, imm32 (compare register with immediate)
    CmpRI {
        /// Operand size.
        size: OpSize,
        /// Source register.
        src: R,
        /// Immediate value.
        imm: i32,
    },
    /// test r/m, r (AND without storing, sets flags)
    TestRR {
        /// Operand size.
        size: OpSize,
        /// First source register.
        src1: R,
        /// Second source register.
        src2: R,
    },
    /// call to named symbol (uses relocation)
    CallSym {
        /// Referenced symbol name.
        name: String,
        /// Primary return register, if any.
        ret: Option<R>,
        /// Secondary return register, if any.
        ret2: Option<R>,
        /// If present, this call has a cleanup landing pad at the given
        /// label (used for LSDA generation).
        cleanup_label: Option<u32>,
    },
    /// indirect call through register (call *%reg)
    CallReg {
        /// Callee.
        callee: R,
        /// Primary return register, if any.
        ret: Option<R>,
        /// Secondary return register, if any.
        ret2: Option<R>,
        /// If present, this call has a cleanup landing pad at the given
        /// label (used for LSDA generation).
        cleanup_label: Option<u32>,
    },
    /// push reg onto stack
    Push {
        /// Register operand.
        reg: R,
    },
    /// pop reg from stack
    Pop {
        /// Register operand.
        reg: R,
    },
    /// sub rsp, imm32 (allocate stack space)
    SubSPI {
        /// Immediate value.
        imm: i32,
    },
    /// add rsp, imm32 (deallocate stack space)
    AddSPI {
        /// Immediate value.
        imm: i32,
    },
    /// mov reg, [base+offset] (load from memory)
    MovRM {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Base register.
        base: R,
        /// Displacement from the base register.
        offset: i32,
    },
    /// mov [base+offset], reg (store to memory)
    MovMR {
        /// Operand size.
        size: OpSize,
        /// Base register.
        base: R,
        /// Displacement from the base register.
        offset: i32,
        /// Source register.
        src: R,
    },
    /// lea reg, [base+offset] (load effective address)
    Lea {
        /// Destination register.
        dst: R,
        /// Base register.
        base: R,
        /// Displacement from the base register.
        offset: i32,
    },
    /// mov reg, imm64 (64-bit immediate, REX.W + B8+rd io)
    MovRI64 {
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: i64,
    },
    /// mov [base+offset], imm32 (store immediate to memory)
    MovMI {
        /// Operand size.
        size: OpSize,
        /// Base register.
        base: R,
        /// Displacement from the base register.
        offset: i32,
        /// Immediate value.
        imm: i32,
    },
    /// lea reg, [rip+symbol] (RIP-relative address of named symbol)
    LeaSymbol {
        /// Destination register.
        dst: R,
        /// Referenced symbol name.
        symbol: String,
    },
    /// Load the address of a thread-local symbol using Initial Exec TLS model.
    /// Emits: mov %fs:0, dst ; add symbol@GOTTPOFF(%rip), dst
    TlsLeaSymbol {
        /// Destination register.
        dst: R,
        /// Referenced symbol name.
        symbol: String,
    },
    /// or dst, src (dst |= src)
    OrRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// and dst, src (dst &= src)
    AndRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// xor dst, src (dst ^= src)
    XorRR {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// shl dst, cl (dst <<= cl)
    ShlRCL {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// shr dst, cl (logical right shift by cl)
    ShrRCL {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// sar dst, cl (arithmetic right shift by cl)
    SarRCL {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// shl dst, imm8 (dst <<= imm8)
    ShlImm {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: u8,
    },
    /// shr dst, imm8 (logical right shift by immediate)
    ShrImm {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: u8,
    },
    /// sar dst, imm8 (arithmetic right shift by immediate)
    SarImm {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: u8,
    },
    /// and dst, imm32 (dst &= imm32)
    AndRI {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Immediate value.
        imm: i64,
    },
    /// cmovcc dst, src (conditional move based on condition code)
    CMOVcc {
        /// Operand size.
        size: OpSize,
        /// Condition code.
        cc: CondCode,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// setcc dst (set byte based on condition code)
    SetCC {
        /// Condition code.
        cc: CondCode,
        /// Destination register.
        dst: R,
    },
    /// movzx r64, r8 (zero-extend byte to qword)
    MovzxB {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// movzx r64, r16 (zero-extend word to qword)
    MovzxW {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// movsx r64, r8 (sign-extend byte to qword)
    MovsxB {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// movsx r64, r16 (sign-extend word to qword)
    MovsxW {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// movsxd r64, r32 (sign-extend dword to qword)
    MovsxD {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
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
        /// Destination register.
        dst: R,
        /// Left-hand input register.
        lhs: R,
        /// Right-hand input register.
        rhs: R,
        /// Whether the operation uses signed arithmetic.
        signed: bool,
        /// Whether the operation returns the remainder instead of the quotient.
        rem: bool,
    },
    /// Pseudo-instruction: 64-bit unsigned multiply with overflow detection.
    ///
    /// Expanded by the encoder into: mov rax,lhs; mul rhs → RDX:RAX;
    /// test rdx,rdx; setne overflow_dst; movzx overflow_dst; mov dst,rax.
    ///
    /// Uses the one-operand MUL which produces a 128-bit result in RDX:RAX.
    /// Overflow is detected when RDX != 0.
    UMulOverflow {
        /// Destination register.
        dst: R,
        /// Register receiving the overflow flag/result.
        overflow: R,
        /// Left-hand input register.
        lhs: R,
        /// Right-hand input register.
        rhs: R,
    },
    /// popcnt r32/r64, r32/r64 (population count)
    Popcnt {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// lzcnt r32/r64, r32/r64 (count leading zeros)
    Lzcnt {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// tzcnt r32/r64, r32/r64 (count trailing zeros)
    Tzcnt {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
    },
    /// bswap r32/r64 (byte-swap in place)
    Bswap {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// rol dst, cl (rotate left by cl)
    RolRCL {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// ror dst, cl (rotate right by cl)
    RorRCL {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
    },
    /// ud2 (undefined instruction trap)
    Ud2,
    /// Pseudo-instruction: parallel copy of two register pairs.
    ///
    /// Used after calls returning i128/u128 in RAX:RDX to copy both return
    /// registers to unconstrained vregs without cross-clobbering. The encoder
    /// emits two `mov` instructions in the correct order (or uses `xchg` if
    /// the destinations cross).
    MovRR2 {
        /// First destination register.
        dst1: R,
        /// First source register.
        src1: R,
        /// Second destination register.
        dst2: R,
        /// Second source register.
        src2: R,
    },
    /// Pseudo-instruction: SSE2 f64 binary operation.
    ///
    /// Performs direct XMM register operations (dst = lhs op rhs).
    FpBinOp {
        /// Operation kind.
        op: FpBinOpKind,
        /// Destination register.
        dst: R,
        /// Left-hand input register.
        lhs: R,
        /// Right-hand input register.
        rhs: R,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: convert float (in XMM) to signed integer (in GPR).
    ///
    /// Uses cvttsd2si (double=true) or cvttss2si (double=false).
    CvtFpToInt {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: convert signed integer (in GPR) to float (in XMM).
    ///
    /// Uses cvtsi2sd (double=true) or cvtsi2ss (double=false).
    CvtIntToFp {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: move XMM to GPR (for external float-returning calls).
    MoveXmmToGpr {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: GPR → XMM bit-reinterpretation (movd for f32, movq for f64).
    GprToXmm {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: convert between float formats (f32↔f64).
    ///
    /// Uses cvtss2sd (src_double=false) or cvtsd2ss (src_double=true).
    CvtFpToFp {
        /// Destination register.
        dst: R,
        /// Source register.
        src: R,
        /// true if source is f64 (narrowing to f32), false if source is f32 (widening to f64).
        src_double: bool,
    },
    /// Pseudo-instruction: SSE2 float comparison.
    ///
    /// Performs direct XMM comparison and produces a bool result in dst GPR.
    FpCmp {
        /// Destination register.
        dst: R,
        /// Left-hand input register.
        lhs: R,
        /// Right-hand input register.
        rhs: R,
        /// Scratch GPR for two-setcc patterns (OEq, OLt, OLe).
        tmp: R,
        /// FCmpOp discriminant (see tuffy_ir::instruction::FCmpOp).
        kind: u8,
        /// Whether the operation uses the f64 encoding instead of f32.
        double: bool,
    },
    /// Pseudo-instruction: atomic read-modify-write.
    ///
    /// Atomically reads [base], applies `op` with `val`, writes the result back.
    /// Returns the **old** value in `dst`.
    ///
    /// Expanded by the encoder into:
    /// - Xchg: `xchg [base], val` (implicit lock)
    /// - Add:  `lock xadd [base], val`
    /// - Sub:  `neg val; lock xadd [base], val`
    /// - And/Or/Xor: cmpxchg loop
    AtomicRmw {
        /// Operation kind.
        op: AtomicRmwOpKind,
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Base register.
        base: R,
        /// Value register.
        val: R,
    },
    /// Pseudo-instruction: atomic compare-and-exchange.
    ///
    /// Atomically compares [base] with `expected`; if equal, stores `desired`.
    /// Returns the **old** value in `dst`.
    ///
    /// Expanded by the encoder into:
    /// `mov rax, expected; lock cmpxchg [base], desired; mov dst, rax`
    AtomicCmpXchg {
        /// Operand size.
        size: OpSize,
        /// Destination register.
        dst: R,
        /// Base register.
        base: R,
        /// Register holding the expected value.
        expected: R,
        /// Register holding the replacement value.
        desired: R,
    },
    /// Pseudo-instruction: landing pad entry.
    ///
    /// Marks the definition of `dst` which receives the exception pointer
    /// from %rax (deposited by the unwinder).  Emits no machine code —
    /// the physical register is already correct.
    LandingPadCapture {
        /// Destination register.
        dst: R,
    },
}

/// SSE2 floating-point binary operation kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpBinOpKind {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Division.
    Div,
    /// Minimum.
    Min,
    /// Maximum.
    Max,
}

/// Atomic read-modify-write operation kind (x86 encoding).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicRmwOpKind {
    /// Exchange.
    Xchg,
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise xor.
    Xor,
}
