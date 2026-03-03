//! x86-64 machine code encoding using iced-x86.

use std::collections::HashMap;

use iced_x86::{Code, Encoder, Instruction, MemoryOperand, Register};

use crate::inst::{CondCode, FpBinOpKind, MInst, OpSize, PInst};
use crate::reg::Gpr;
use tuffy_target::reloc::{EncodeResult, RelocKind, Relocation};

/// A fixup for a jump instruction whose target offset is not yet known.
struct JumpFixup {
    /// Byte offset in the buffer where the rel32 displacement starts.
    patch_offset: usize,
    /// The label ID this jump targets.
    target_label: u32,
}

// ---------------------------------------------------------------------------
// Register mapping
// ---------------------------------------------------------------------------

/// Map a Gpr + OpSize to the corresponding iced-x86 Register.
fn gpr_to_iced(gpr: Gpr, size: OpSize) -> Register {
    const R64: [Register; 16] = [
        Register::RAX,
        Register::RCX,
        Register::RDX,
        Register::RBX,
        Register::RSP,
        Register::RBP,
        Register::RSI,
        Register::RDI,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::R12,
        Register::R13,
        Register::R14,
        Register::R15,
    ];
    const R32: [Register; 16] = [
        Register::EAX,
        Register::ECX,
        Register::EDX,
        Register::EBX,
        Register::ESP,
        Register::EBP,
        Register::ESI,
        Register::EDI,
        Register::R8D,
        Register::R9D,
        Register::R10D,
        Register::R11D,
        Register::R12D,
        Register::R13D,
        Register::R14D,
        Register::R15D,
    ];
    const R16: [Register; 16] = [
        Register::AX,
        Register::CX,
        Register::DX,
        Register::BX,
        Register::SP,
        Register::BP,
        Register::SI,
        Register::DI,
        Register::R8W,
        Register::R9W,
        Register::R10W,
        Register::R11W,
        Register::R12W,
        Register::R13W,
        Register::R14W,
        Register::R15W,
    ];
    const R8: [Register; 16] = [
        Register::AL,
        Register::CL,
        Register::DL,
        Register::BL,
        Register::SPL,
        Register::BPL,
        Register::SIL,
        Register::DIL,
        Register::R8L,
        Register::R9L,
        Register::R10L,
        Register::R11L,
        Register::R12L,
        Register::R13L,
        Register::R14L,
        Register::R15L,
    ];
    let idx = gpr as usize;
    match size {
        OpSize::S64 => R64[idx],
        OpSize::S32 => R32[idx],
        OpSize::S16 => R16[idx],
        OpSize::S8 => R8[idx],
    }
}

/// Shorthand: map Gpr to 64-bit iced register.
fn gpr64(gpr: Gpr) -> Register {
    gpr_to_iced(gpr, OpSize::S64)
}

/// Map Gpr to XMM register (for XMM instructions after register allocation).
fn xmm_to_iced(gpr: Gpr) -> Register {
    const XMM: [Register; 16] = [
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
        Register::XMM8,
        Register::XMM9,
        Register::XMM10,
        Register::XMM11,
        Register::XMM12,
        Register::XMM13,
        Register::XMM14,
        Register::XMM15,
    ];
    XMM[gpr as usize]
}

/// Build a [base+disp] memory operand.
fn mem(base: Gpr, offset: i32) -> MemoryOperand {
    MemoryOperand::with_base_displ(gpr64(base), offset as i64)
}

// ---------------------------------------------------------------------------
// Code selection helpers
// ---------------------------------------------------------------------------

/// Select the sized ADD r/m, r code.
fn add_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Add_rm64_r64,
        OpSize::S32 => Code::Add_rm32_r32,
        OpSize::S16 => Code::Add_rm16_r16,
        OpSize::S8 => Code::Add_rm8_r8,
    }
}

fn sub_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sub_rm64_r64,
        OpSize::S32 => Code::Sub_rm32_r32,
        OpSize::S16 => Code::Sub_rm16_r16,
        OpSize::S8 => Code::Sub_rm8_r8,
    }
}

fn or_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Or_rm64_r64,
        OpSize::S32 => Code::Or_rm32_r32,
        OpSize::S16 => Code::Or_rm16_r16,
        OpSize::S8 => Code::Or_rm8_r8,
    }
}

fn and_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::And_rm64_r64,
        OpSize::S32 => Code::And_rm32_r32,
        OpSize::S16 => Code::And_rm16_r16,
        OpSize::S8 => Code::And_rm8_r8,
    }
}

fn xor_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Xor_rm64_r64,
        OpSize::S32 => Code::Xor_rm32_r32,
        OpSize::S16 => Code::Xor_rm16_r16,
        OpSize::S8 => Code::Xor_rm8_r8,
    }
}

fn cmp_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Cmp_rm64_r64,
        OpSize::S32 => Code::Cmp_rm32_r32,
        OpSize::S16 => Code::Cmp_rm16_r16,
        OpSize::S8 => Code::Cmp_rm8_r8,
    }
}

fn test_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Test_rm64_r64,
        OpSize::S32 => Code::Test_rm32_r32,
        OpSize::S16 => Code::Test_rm16_r16,
        OpSize::S8 => Code::Test_rm8_r8,
    }
}

fn mov_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_r64,
        OpSize::S32 => Code::Mov_rm32_r32,
        OpSize::S16 => Code::Mov_rm16_r16,
        OpSize::S8 => Code::Mov_rm8_r8,
    }
}

fn imul_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Imul_r64_rm64,
        OpSize::S32 => Code::Imul_r32_rm32,
        OpSize::S16 => Code::Imul_r16_rm16,
        OpSize::S8 => unreachable!("imul not supported for 8-bit"),
    }
}

fn cmp_ri_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Cmp_rm64_imm32,
        OpSize::S32 => Code::Cmp_rm32_imm32,
        OpSize::S16 => Code::Cmp_rm16_imm16,
        OpSize::S8 => Code::Cmp_rm8_imm8,
    }
}

fn and_ri_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::And_rm64_imm32,
        OpSize::S32 => Code::And_rm32_imm32,
        OpSize::S16 => Code::And_rm16_imm16,
        OpSize::S8 => Code::And_rm8_imm8,
    }
}

// --- Shift codes ---

fn shl_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shl_rm64_CL,
        OpSize::S32 => Code::Shl_rm32_CL,
        OpSize::S16 => Code::Shl_rm16_CL,
        OpSize::S8 => Code::Shl_rm8_CL,
    }
}

fn shr_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shr_rm64_CL,
        OpSize::S32 => Code::Shr_rm32_CL,
        OpSize::S16 => Code::Shr_rm16_CL,
        OpSize::S8 => Code::Shr_rm8_CL,
    }
}

fn sar_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sar_rm64_CL,
        OpSize::S32 => Code::Sar_rm32_CL,
        OpSize::S16 => Code::Sar_rm16_CL,
        OpSize::S8 => Code::Sar_rm8_CL,
    }
}

fn rol_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Rol_rm64_CL,
        OpSize::S32 => Code::Rol_rm32_CL,
        OpSize::S16 => Code::Rol_rm16_CL,
        OpSize::S8 => Code::Rol_rm8_CL,
    }
}

fn ror_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Ror_rm64_CL,
        OpSize::S32 => Code::Ror_rm32_CL,
        OpSize::S16 => Code::Ror_rm16_CL,
        OpSize::S8 => Code::Ror_rm8_CL,
    }
}

fn shl_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shl_rm64_imm8,
        OpSize::S32 => Code::Shl_rm32_imm8,
        OpSize::S16 => Code::Shl_rm16_imm8,
        OpSize::S8 => Code::Shl_rm8_imm8,
    }
}

fn sar_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sar_rm64_imm8,
        OpSize::S32 => Code::Sar_rm32_imm8,
        OpSize::S16 => Code::Sar_rm16_imm8,
        OpSize::S8 => Code::Sar_rm8_imm8,
    }
}

fn shr_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shr_rm64_imm8,
        OpSize::S32 => Code::Shr_rm32_imm8,
        OpSize::S16 => Code::Shr_rm16_imm8,
        OpSize::S8 => Code::Shr_rm8_imm8,
    }
}

// --- Branch / conditional codes ---

fn jcc_code(cc: CondCode) -> Code {
    match cc {
        CondCode::E => Code::Je_rel32_64,
        CondCode::Ne => Code::Jne_rel32_64,
        CondCode::L => Code::Jl_rel32_64,
        CondCode::Le => Code::Jle_rel32_64,
        CondCode::G => Code::Jg_rel32_64,
        CondCode::Ge => Code::Jge_rel32_64,
        CondCode::B => Code::Jb_rel32_64,
        CondCode::Be => Code::Jbe_rel32_64,
        CondCode::A => Code::Ja_rel32_64,
        CondCode::Ae => Code::Jae_rel32_64,
    }
}

fn cmovcc_code(cc: CondCode, size: OpSize) -> Code {
    match (cc, size) {
        (CondCode::E, OpSize::S64) => Code::Cmove_r64_rm64,
        (CondCode::E, OpSize::S32) => Code::Cmove_r32_rm32,
        (CondCode::E, OpSize::S16) => Code::Cmove_r16_rm16,
        (CondCode::Ne, OpSize::S64) => Code::Cmovne_r64_rm64,
        (CondCode::Ne, OpSize::S32) => Code::Cmovne_r32_rm32,
        (CondCode::Ne, OpSize::S16) => Code::Cmovne_r16_rm16,
        (CondCode::L, OpSize::S64) => Code::Cmovl_r64_rm64,
        (CondCode::L, OpSize::S32) => Code::Cmovl_r32_rm32,
        (CondCode::L, OpSize::S16) => Code::Cmovl_r16_rm16,
        (CondCode::Le, OpSize::S64) => Code::Cmovle_r64_rm64,
        (CondCode::Le, OpSize::S32) => Code::Cmovle_r32_rm32,
        (CondCode::Le, OpSize::S16) => Code::Cmovle_r16_rm16,
        (CondCode::G, OpSize::S64) => Code::Cmovg_r64_rm64,
        (CondCode::G, OpSize::S32) => Code::Cmovg_r32_rm32,
        (CondCode::G, OpSize::S16) => Code::Cmovg_r16_rm16,
        (CondCode::Ge, OpSize::S64) => Code::Cmovge_r64_rm64,
        (CondCode::Ge, OpSize::S32) => Code::Cmovge_r32_rm32,
        (CondCode::Ge, OpSize::S16) => Code::Cmovge_r16_rm16,
        (CondCode::B, OpSize::S64) => Code::Cmovb_r64_rm64,
        (CondCode::B, OpSize::S32) => Code::Cmovb_r32_rm32,
        (CondCode::B, OpSize::S16) => Code::Cmovb_r16_rm16,
        (CondCode::Be, OpSize::S64) => Code::Cmovbe_r64_rm64,
        (CondCode::Be, OpSize::S32) => Code::Cmovbe_r32_rm32,
        (CondCode::Be, OpSize::S16) => Code::Cmovbe_r16_rm16,
        (CondCode::A, OpSize::S64) => Code::Cmova_r64_rm64,
        (CondCode::A, OpSize::S32) => Code::Cmova_r32_rm32,
        (CondCode::A, OpSize::S16) => Code::Cmova_r16_rm16,
        (CondCode::Ae, OpSize::S64) => Code::Cmovae_r64_rm64,
        (CondCode::Ae, OpSize::S32) => Code::Cmovae_r32_rm32,
        (CondCode::Ae, OpSize::S16) => Code::Cmovae_r16_rm16,
        (_, OpSize::S8) => unreachable!("cmovcc not supported for 8-bit"),
    }
}

fn setcc_code(cc: CondCode) -> Code {
    match cc {
        CondCode::E => Code::Sete_rm8,
        CondCode::Ne => Code::Setne_rm8,
        CondCode::L => Code::Setl_rm8,
        CondCode::Le => Code::Setle_rm8,
        CondCode::G => Code::Setg_rm8,
        CondCode::Ge => Code::Setge_rm8,
        CondCode::B => Code::Setb_rm8,
        CondCode::Be => Code::Setbe_rm8,
        CondCode::A => Code::Seta_rm8,
        CondCode::Ae => Code::Setae_rm8,
    }
}

// --- Memory load/store codes ---

fn mov_load_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_r64_rm64,
        OpSize::S32 => Code::Mov_r32_rm32,
        OpSize::S16 => Code::Mov_r16_rm16,
        OpSize::S8 => Code::Mov_r8_rm8,
    }
}

fn mov_store_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_r64,
        OpSize::S32 => Code::Mov_rm32_r32,
        OpSize::S16 => Code::Mov_rm16_r16,
        OpSize::S8 => Code::Mov_rm8_r8,
    }
}

fn mov_store_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_imm32,
        OpSize::S32 => Code::Mov_rm32_imm32,
        OpSize::S16 => Code::Mov_rm16_imm16,
        OpSize::S8 => Code::Mov_rm8_imm8,
    }
}

fn bswap_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Bswap_r64,
        OpSize::S32 => Code::Bswap_r32,
        _ => unreachable!("bswap only for 32/64-bit"),
    }
}

// ---------------------------------------------------------------------------
// Encode context
// ---------------------------------------------------------------------------

struct EncodeContext {
    encoder: Encoder,
    pos: usize,
    labels: HashMap<u32, usize>,
    fixups: Vec<JumpFixup>,
    relocations: Vec<Relocation>,
}

impl EncodeContext {
    fn new() -> Self {
        Self {
            encoder: Encoder::new(64),
            pos: 0,
            labels: HashMap::new(),
            fixups: Vec::new(),
            relocations: Vec::new(),
        }
    }

    /// Encode a single instruction, appending bytes to the internal buffer.
    fn emit(&mut self, instr: Instruction) {
        let len = self
            .encoder
            .encode(&instr, self.pos as u64)
            .expect("iced-x86 encoding failed");
        self.pos += len;
    }

    /// Encode a mov reg, reg (64-bit) — used by pseudo-instruction expansions.
    fn emit_mov64(&mut self, dst: Gpr, src: Gpr) {
        if dst != src {
            self.emit(Instruction::with2(Code::Mov_rm64_r64, gpr64(dst), gpr64(src)).unwrap());
        }
    }

    /// Encode a branch instruction with a dummy target, recording a fixup.
    fn emit_branch(&mut self, code: Code, target_label: u32) {
        let start = self.pos;
        // Encode with target = 0; we'll patch the rel32 later.
        self.emit(Instruction::with_branch(code, 0).unwrap());
        let offsets = self.encoder.get_constant_offsets();
        self.fixups.push(JumpFixup {
            patch_offset: start + offsets.immediate_offset(),
            target_label,
        });
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Encode a sequence of machine instructions into bytes.
///
/// Uses a two-pass approach: first pass emits code with placeholder jump
/// offsets, second pass patches the actual relative displacements.
/// External call relocations are returned separately for the ELF emitter.
pub fn encode_function(insts: &[PInst]) -> EncodeResult {
    let mut ctx = EncodeContext::new();

    for inst in insts {
        encode_inst(inst, &mut ctx);
    }

    let mut buf = ctx.encoder.take_buffer();

    // Patch jump offsets.
    for fixup in &ctx.fixups {
        let target_addr = ctx.labels[&fixup.target_label];
        // rel32 is relative to the end of the displacement field (patch_offset + 4).
        let rel = target_addr as i32 - (fixup.patch_offset as i32 + 4);
        buf[fixup.patch_offset..fixup.patch_offset + 4].copy_from_slice(&rel.to_le_bytes());
    }

    EncodeResult {
        code: buf,
        relocations: ctx.relocations,
    }
}

// ---------------------------------------------------------------------------
// Per-instruction encoding
// ---------------------------------------------------------------------------

fn encode_inst(inst: &PInst, ctx: &mut EncodeContext) {
    match inst {
        // --- Register-register ALU ---
        MInst::MovRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    mov_rr_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::AddRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    add_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::SubRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    sub_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::ImulRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    imul_rr_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::OrRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    or_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::AndRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    and_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::XorRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    xor_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::CmpRR { size, src1, src2 } => {
            ctx.emit(
                Instruction::with2(
                    cmp_rr_code(*size),
                    gpr_to_iced(*src1, *size),
                    gpr_to_iced(*src2, *size),
                )
                .unwrap(),
            );
        }
        MInst::TestRR { size, src1, src2 } => {
            ctx.emit(
                Instruction::with2(
                    test_rr_code(*size),
                    gpr_to_iced(*src1, *size),
                    gpr_to_iced(*src2, *size),
                )
                .unwrap(),
            );
        }

        // --- Register-immediate ---
        MInst::MovRI { dst, imm, .. } => {
            // Always use 32-bit form (zero-extends to 64 bits).
            ctx.emit(
                Instruction::with2(
                    Code::Mov_r32_imm32,
                    gpr_to_iced(*dst, OpSize::S32),
                    *imm as u32,
                )
                .unwrap(),
            );
        }
        MInst::MovRI64 { dst, imm } => {
            ctx.emit(Instruction::with2(Code::Mov_r64_imm64, gpr64(*dst), *imm as u64).unwrap());
        }
        MInst::CmpRI { size, src, imm } => {
            ctx.emit(
                Instruction::with2(cmp_ri_code(*size), gpr_to_iced(*src, *size), *imm).unwrap(),
            );
        }
        MInst::AndRI { size, dst, imm } => {
            ctx.emit(
                Instruction::with2(and_ri_code(*size), gpr_to_iced(*dst, *size), *imm as i32)
                    .unwrap(),
            );
        }

        // --- Shifts ---
        MInst::ShlRCL { size, dst } => {
            ctx.emit(
                Instruction::with2(shl_cl_code(*size), gpr_to_iced(*dst, *size), Register::CL)
                    .unwrap(),
            );
        }
        MInst::ShrRCL { size, dst } => {
            ctx.emit(
                Instruction::with2(shr_cl_code(*size), gpr_to_iced(*dst, *size), Register::CL)
                    .unwrap(),
            );
        }
        MInst::SarRCL { size, dst } => {
            ctx.emit(
                Instruction::with2(sar_cl_code(*size), gpr_to_iced(*dst, *size), Register::CL)
                    .unwrap(),
            );
        }
        MInst::RolRCL { size, dst } => {
            ctx.emit(
                Instruction::with2(rol_cl_code(*size), gpr_to_iced(*dst, *size), Register::CL)
                    .unwrap(),
            );
        }
        MInst::RorRCL { size, dst } => {
            ctx.emit(
                Instruction::with2(ror_cl_code(*size), gpr_to_iced(*dst, *size), Register::CL)
                    .unwrap(),
            );
        }
        MInst::ShlImm { size, dst, imm } => {
            ctx.emit(
                Instruction::with2(shl_imm_code(*size), gpr_to_iced(*dst, *size), *imm as u32)
                    .unwrap(),
            );
        }
        MInst::ShrImm { size, dst, imm } => {
            ctx.emit(
                Instruction::with2(shr_imm_code(*size), gpr_to_iced(*dst, *size), *imm as u32)
                    .unwrap(),
            );
        }
        MInst::SarImm { size, dst, imm } => {
            ctx.emit(
                Instruction::with2(sar_imm_code(*size), gpr_to_iced(*dst, *size), *imm as u32)
                    .unwrap(),
            );
        }

        // --- Control flow ---
        MInst::Label { id } => {
            ctx.labels.insert(*id, ctx.pos);
        }
        MInst::Jmp { target } => {
            ctx.emit_branch(Code::Jmp_rel32_64, *target);
        }
        MInst::Jcc { cc, target } => {
            ctx.emit_branch(jcc_code(*cc), *target);
        }
        MInst::Ret => {
            ctx.emit(Instruction::with(Code::Retnq));
        }
        MInst::Ud2 => {
            ctx.emit(Instruction::with(Code::Ud2));
        }

        // --- Calls ---
        MInst::CallSym { name, .. } => {
            let start = ctx.pos;
            ctx.emit(Instruction::with_branch(Code::Call_rel32_64, 0).unwrap());
            let offsets = ctx.encoder.get_constant_offsets();
            ctx.relocations.push(Relocation {
                offset: start + offsets.immediate_offset(),
                symbol: name.clone(),
                kind: RelocKind::Call,
            });
        }
        MInst::CallReg { callee, .. } => {
            ctx.emit(Instruction::with1(Code::Call_rm64, gpr64(*callee)).unwrap());
        }

        // --- Stack ---
        MInst::Push { reg } => {
            ctx.emit(Instruction::with1(Code::Push_r64, gpr64(*reg)).unwrap());
        }
        MInst::Pop { reg } => {
            ctx.emit(Instruction::with1(Code::Pop_r64, gpr64(*reg)).unwrap());
        }
        MInst::SubSPI { imm } => {
            ctx.emit(Instruction::with2(Code::Sub_rm64_imm32, Register::RSP, *imm).unwrap());
        }
        MInst::AddSPI { imm } => {
            ctx.emit(Instruction::with2(Code::Add_rm64_imm32, Register::RSP, *imm).unwrap());
        }

        // --- Memory load ---
        MInst::MovRM {
            size,
            dst,
            base,
            offset,
        } => {
            match size {
                // Byte/word loads use zero-extending movzx to match original behavior.
                OpSize::S8 => {
                    ctx.emit(
                        Instruction::with2(
                            Code::Movzx_r32_rm8,
                            gpr_to_iced(*dst, OpSize::S32),
                            mem(*base, *offset),
                        )
                        .unwrap(),
                    );
                }
                OpSize::S16 => {
                    ctx.emit(
                        Instruction::with2(
                            Code::Movzx_r32_rm16,
                            gpr_to_iced(*dst, OpSize::S32),
                            mem(*base, *offset),
                        )
                        .unwrap(),
                    );
                }
                _ => {
                    ctx.emit(
                        Instruction::with2(
                            mov_load_code(*size),
                            gpr_to_iced(*dst, *size),
                            mem(*base, *offset),
                        )
                        .unwrap(),
                    );
                }
            }
        }

        // --- Memory store ---
        MInst::MovMR {
            size,
            base,
            offset,
            src,
        } => {
            ctx.emit(
                Instruction::with2(
                    mov_store_code(*size),
                    mem(*base, *offset),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::MovMI {
            size,
            base,
            offset,
            imm,
        } => {
            ctx.emit(
                Instruction::with2(mov_store_imm_code(*size), mem(*base, *offset), *imm).unwrap(),
            );
        }

        // --- LEA ---
        MInst::Lea { dst, base, offset } => {
            ctx.emit(
                Instruction::with2(Code::Lea_r64_m, gpr64(*dst), mem(*base, *offset)).unwrap(),
            );
        }
        MInst::LeaSymbol { dst, symbol } => {
            let start = ctx.pos;
            // lea dst, [rip+0] — displacement patched by linker.
            ctx.emit(
                Instruction::with2(
                    Code::Lea_r64_m,
                    gpr64(*dst),
                    MemoryOperand::with_base_displ(Register::RIP, 0),
                )
                .unwrap(),
            );
            let offsets = ctx.encoder.get_constant_offsets();
            ctx.relocations.push(Relocation {
                offset: start + offsets.displacement_offset(),
                symbol: symbol.clone(),
                kind: RelocKind::PcRel,
            });
        }

        // --- Conditional ---
        MInst::CMOVcc { size, cc, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    cmovcc_code(*cc, *size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::SetCC { cc, dst } => {
            ctx.emit(Instruction::with1(setcc_code(*cc), gpr_to_iced(*dst, OpSize::S8)).unwrap());
        }

        // --- Extensions ---
        MInst::MovzxB { dst, src } => {
            ctx.emit(
                Instruction::with2(
                    Code::Movzx_r64_rm8,
                    gpr64(*dst),
                    gpr_to_iced(*src, OpSize::S8),
                )
                .unwrap(),
            );
        }
        MInst::MovzxW { dst, src } => {
            ctx.emit(
                Instruction::with2(
                    Code::Movzx_r64_rm16,
                    gpr64(*dst),
                    gpr_to_iced(*src, OpSize::S16),
                )
                .unwrap(),
            );
        }
        MInst::MovsxB { dst, src } => {
            ctx.emit(
                Instruction::with2(
                    Code::Movsx_r64_rm8,
                    gpr64(*dst),
                    gpr_to_iced(*src, OpSize::S8),
                )
                .unwrap(),
            );
        }
        MInst::MovsxW { dst, src } => {
            ctx.emit(
                Instruction::with2(
                    Code::Movsx_r64_rm16,
                    gpr64(*dst),
                    gpr_to_iced(*src, OpSize::S16),
                )
                .unwrap(),
            );
        }
        MInst::MovsxD { dst, src } => {
            ctx.emit(
                Instruction::with2(
                    Code::Movsxd_r64_rm32,
                    gpr64(*dst),
                    gpr_to_iced(*src, OpSize::S32),
                )
                .unwrap(),
            );
        }
        MInst::Cqo => {
            ctx.emit(Instruction::with(Code::Cqo));
        }

        // --- Bit manipulation ---
        MInst::Popcnt { dst, src } => {
            ctx.emit(Instruction::with2(Code::Popcnt_r64_rm64, gpr64(*dst), gpr64(*src)).unwrap());
        }
        MInst::Lzcnt { dst, src } => {
            ctx.emit(Instruction::with2(Code::Lzcnt_r64_rm64, gpr64(*dst), gpr64(*src)).unwrap());
        }
        MInst::Tzcnt { dst, src } => {
            ctx.emit(Instruction::with2(Code::Tzcnt_r64_rm64, gpr64(*dst), gpr64(*src)).unwrap());
        }
        MInst::Bswap { size, dst } => {
            ctx.emit(Instruction::with1(bswap_code(*size), gpr_to_iced(*dst, *size)).unwrap());
        }

        // --- Pseudo-instructions ---
        MInst::MovRR2 {
            dst1,
            src1,
            dst2,
            src2,
        } => {
            encode_mov_rr2(ctx, *dst1, *src1, *dst2, *src2);
        }
        MInst::DivRem {
            dst,
            lhs,
            rhs,
            signed,
            rem,
        } => {
            encode_divrem(ctx, *dst, *lhs, *rhs, *signed, *rem);
        }
        MInst::FpBinOp {
            op,
            dst,
            lhs,
            rhs,
            double,
        } => {
            encode_fp_binop(ctx, *op, *dst, *lhs, *rhs, *double, Gpr::Rax);
        }
        MInst::CvtFpToInt { dst, src, double } => {
            encode_cvt_fp_to_int(ctx, *dst, *src, *double);
        }
        MInst::CvtIntToFp { dst, src, double } => {
            encode_cvt_int_to_fp(ctx, *dst, *src, *double, Gpr::Rax);
        }
        MInst::MoveXmmToGpr { dst, src, double } => {
            encode_move_xmm_to_gpr(ctx, *dst, *src, *double);
        }
        MInst::CvtFpToFp {
            dst,
            src,
            src_double,
        } => {
            encode_cvt_fp_to_fp(ctx, *dst, *src, *src_double, Gpr::Rax);
        }
        MInst::FpCmp {
            dst,
            lhs,
            rhs,
            kind,
            double,
        } => {
            encode_fp_cmp(ctx, *dst, *lhs, *rhs, *kind, *double, Gpr::Rax, Gpr::Rcx);
        }
    }
}

// ---------------------------------------------------------------------------
// Pseudo-instruction expansions
// ---------------------------------------------------------------------------

/// Parallel copy of two register pairs, handling all ordering cases.
fn encode_mov_rr2(ctx: &mut EncodeContext, dst1: Gpr, src1: Gpr, dst2: Gpr, src2: Gpr) {
    let need1 = dst1 != src1;
    let need2 = dst2 != src2;
    if !need1 && !need2 {
        return;
    }
    if !need1 {
        ctx.emit_mov64(dst2, src2);
        return;
    }
    if !need2 {
        ctx.emit_mov64(dst1, src1);
        return;
    }
    if dst1 == src2 && dst2 == src1 {
        // Cross-assignment: use xchg to swap.
        ctx.emit(Instruction::with2(Code::Xchg_rm64_r64, gpr64(dst1), gpr64(dst2)).unwrap());
    } else if dst1 != src2 {
        ctx.emit_mov64(dst1, src1);
        ctx.emit_mov64(dst2, src2);
    } else {
        // dst1 == src2, so write dst2 first to preserve src2's value.
        ctx.emit_mov64(dst2, src2);
        ctx.emit_mov64(dst1, src1);
    }
}

/// DivRem pseudo-instruction expansion.
///
/// Emits: mov rcx,rhs; mov rax,lhs; {xor edx,edx | cqo}; {div|idiv} rcx;
///        mov dst,{rax|rdx}
fn encode_divrem(ctx: &mut EncodeContext, dst: Gpr, lhs: Gpr, rhs: Gpr, signed: bool, rem: bool) {
    // Step 1: Get rhs into RCX and lhs into RAX without clobbering either.
    if rhs == Gpr::Rax && lhs == Gpr::Rcx {
        // Both are swapped — use xchg rax, rcx.
        ctx.emit(Instruction::with2(Code::Xchg_rm64_r64, Register::RCX, Register::RAX).unwrap());
    } else if rhs == Gpr::Rax {
        // rhs is in RAX — move it to RCX first, then move lhs to RAX.
        ctx.emit_mov64(Gpr::Rcx, Gpr::Rax);
        ctx.emit_mov64(Gpr::Rax, lhs);
    } else {
        // Move lhs to RAX first (safe: rhs is not in RAX).
        ctx.emit_mov64(Gpr::Rax, lhs);
        ctx.emit_mov64(Gpr::Rcx, rhs);
    }

    // Step 2: Set up RDX (zero for unsigned, sign-extend for signed).
    if signed {
        ctx.emit(Instruction::with(Code::Cqo));
    } else {
        // xor edx, edx
        ctx.emit(Instruction::with2(Code::Xor_rm32_r32, Register::EDX, Register::EDX).unwrap());
    }

    // Step 3: div/idiv rcx
    let div_code = if signed {
        Code::Idiv_rm64
    } else {
        Code::Div_rm64
    };
    ctx.emit(Instruction::with1(div_code, Register::RCX).unwrap());

    // Step 4: Move result to dst.
    let result_reg = if rem { Gpr::Rdx } else { Gpr::Rax };
    ctx.emit_mov64(dst, result_reg);
}

/// FpBinOp pseudo-instruction: SSE2 binary operation with direct XMM operations.
///
/// movsd dst,lhs; opsd dst,rhs
fn encode_fp_binop(
    ctx: &mut EncodeContext,
    op: FpBinOpKind,
    dst: Gpr,
    lhs: Gpr,
    rhs: Gpr,
    double: bool,
    _xmm_scratch: Gpr,
) {
    // Direct XMM register operations (no memory traffic)
    let (mov_code, op_code) = match (op, double) {
        (FpBinOpKind::Add, true) => (Code::Movsd_xmm_xmmm64, Code::Addsd_xmm_xmmm64),
        (FpBinOpKind::Add, false) => (Code::Movss_xmm_xmmm32, Code::Addss_xmm_xmmm32),
        (FpBinOpKind::Sub, true) => (Code::Movsd_xmm_xmmm64, Code::Subsd_xmm_xmmm64),
        (FpBinOpKind::Sub, false) => (Code::Movss_xmm_xmmm32, Code::Subss_xmm_xmmm32),
        (FpBinOpKind::Mul, true) => (Code::Movsd_xmm_xmmm64, Code::Mulsd_xmm_xmmm64),
        (FpBinOpKind::Mul, false) => (Code::Movss_xmm_xmmm32, Code::Mulss_xmm_xmmm32),
        (FpBinOpKind::Div, true) => (Code::Movsd_xmm_xmmm64, Code::Divsd_xmm_xmmm64),
        (FpBinOpKind::Div, false) => (Code::Movss_xmm_xmmm32, Code::Divss_xmm_xmmm32),
    };

    // movsd/movss dst, lhs
    ctx.emit(Instruction::with2(mov_code, xmm_to_iced(dst), xmm_to_iced(lhs)).unwrap());
    // op dst, rhs
    ctx.emit(Instruction::with2(op_code, xmm_to_iced(dst), xmm_to_iced(rhs)).unwrap());
}

/// CvtFpToInt: float (XMM) → signed integer (GPR) with direct conversion.
fn encode_cvt_fp_to_int(ctx: &mut EncodeContext, dst: Gpr, src: Gpr, double: bool) {
    // Direct XMM to GPR conversion
    let code = if double {
        Code::Cvttsd2si_r64_xmmm64
    } else {
        Code::Cvttss2si_r64_xmmm32
    };
    ctx.emit(Instruction::with2(code, gpr64(dst), xmm_to_iced(src)).unwrap());
}

/// CvtIntToFp: signed integer (GPR) → float (XMM) with direct conversion.
fn encode_cvt_int_to_fp(
    ctx: &mut EncodeContext,
    dst: Gpr,
    src: Gpr,
    double: bool,
    _xmm_scratch: Gpr,
) {
    // Direct GPR to XMM conversion
    let code = if double {
        Code::Cvtsi2sd_xmm_rm64
    } else {
        Code::Cvtsi2ss_xmm_rm64
    };
    ctx.emit(Instruction::with2(code, xmm_to_iced(dst), gpr64(src)).unwrap());
}

/// MoveXmmToGpr: XMM → GPR (for external float-returning calls).
fn encode_move_xmm_to_gpr(ctx: &mut EncodeContext, dst: Gpr, src: Gpr, double: bool) {
    let rsp_m8 = MemoryOperand::with_base_displ(Register::RSP, -8);
    // 1. movsd/movss [rsp-8], xmm_src
    let store_code = if double {
        Code::Movsd_xmmm64_xmm
    } else {
        Code::Movss_xmmm32_xmm
    };
    ctx.emit(Instruction::with2(store_code, rsp_m8, xmm_to_iced(src)).unwrap());
    // 2. mov dst, [rsp-8]
    let load_code = if double {
        Code::Mov_r64_rm64
    } else {
        Code::Mov_r32_rm32
    };
    let dst_reg = if double {
        gpr64(dst)
    } else {
        gpr_to_iced(dst, OpSize::S32)
    };
    ctx.emit(Instruction::with2(load_code, dst_reg, rsp_m8).unwrap());
}

/// CvtFpToFp: float format conversion (f32↔f64) with direct XMM operations.
fn encode_cvt_fp_to_fp(
    ctx: &mut EncodeContext,
    dst: Gpr,
    src: Gpr,
    src_double: bool,
    _xmm_scratch: Gpr,
) {
    // Direct XMM to XMM conversion
    if src_double {
        // f64 → f32 (narrowing)
        ctx.emit(
            Instruction::with2(
                Code::Cvtsd2ss_xmm_xmmm64,
                xmm_to_iced(dst),
                xmm_to_iced(src),
            )
            .unwrap(),
        );
    } else {
        // f32 → f64 (widening)
        ctx.emit(
            Instruction::with2(
                Code::Cvtss2sd_xmm_xmmm32,
                xmm_to_iced(dst),
                xmm_to_iced(src),
            )
            .unwrap(),
        );
    }
}

/// FpCmp: float comparison with direct XMM operations, result as 0/1 in dst GPR.
///
/// kind values match tuffy_ir::instruction::FCmpOp discriminants:
///   1=OEq, 2=OGt, 3=OGe, 4=OLt, 5=OLe, 6=ONe, 7=Ord, 8=Uno
#[allow(clippy::too_many_arguments)]
fn encode_fp_cmp(
    ctx: &mut EncodeContext,
    dst: Gpr,
    lhs: Gpr,
    rhs: Gpr,
    kind: u8,
    double: bool,
    _xmm_scratch0: Gpr,
    _xmm_scratch1: Gpr,
) {
    let dst8 = gpr_to_iced(dst, OpSize::S8);
    let dst32 = gpr_to_iced(dst, OpSize::S32);

    // Direct XMM comparison
    let ucomi = if double {
        Code::Ucomisd_xmm_xmmm64
    } else {
        Code::Ucomiss_xmm_xmmm32
    };

    // ucomisd/ucomiss lhs, rhs
    ctx.emit(Instruction::with2(ucomi, xmm_to_iced(lhs), xmm_to_iced(rhs)).unwrap());

    // Flags after ucomisd xmm0, xmm1:
    //   a > b:  ZF=0 PF=0 CF=0
    //   a < b:  ZF=0 PF=0 CF=1
    //   a == b: ZF=1 PF=0 CF=0
    //   NaN:    ZF=1 PF=1 CF=1
    match kind {
        2 => {
            // OGt: CF=0 AND ZF=0 → seta
            ctx.emit(Instruction::with1(Code::Seta_rm8, dst8).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
        3 => {
            // OGe: CF=0 → setae
            ctx.emit(Instruction::with1(Code::Setae_rm8, dst8).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
        6 => {
            // ONe: ZF=0 → setne
            ctx.emit(Instruction::with1(Code::Setne_rm8, dst8).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
        7 => {
            // Ord: PF=0 → setnp
            ctx.emit(Instruction::with1(Code::Setnp_rm8, dst8).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
        8 => {
            // Uno: PF=1 → setp
            ctx.emit(Instruction::with1(Code::Setp_rm8, dst8).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
        _ => {
            // OEq(1), OLt(4), OLe(5): need two setcc + AND
            let tmp = gpr_to_iced(Gpr::Rcx, OpSize::S8);
            let _tmp32 = gpr_to_iced(Gpr::Rcx, OpSize::S32);
            match kind {
                1 => {
                    // OEq: ZF=1 AND PF=0
                    ctx.emit(Instruction::with1(Code::Sete_rm8, dst8).unwrap());
                    ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp).unwrap());
                }
                4 => {
                    // OLt: CF=1 AND PF=0
                    ctx.emit(Instruction::with1(Code::Setb_rm8, dst8).unwrap());
                    ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp).unwrap());
                }
                5 => {
                    // OLe: (CF=1 OR ZF=1) AND PF=0
                    ctx.emit(Instruction::with1(Code::Setbe_rm8, dst8).unwrap());
                    ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp).unwrap());
                }
                _ => {
                    // Fallback: return 0
                    ctx.emit(Instruction::with2(Code::Xor_r32_rm32, dst32, dst32).unwrap());
                    return;
                }
            }
            ctx.emit(Instruction::with2(Code::And_r8_rm8, dst8, tmp).unwrap());
            ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
        }
    }
}
