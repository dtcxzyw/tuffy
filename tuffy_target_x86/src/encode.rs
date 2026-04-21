//! x86-64 machine code encoding using iced-x86.

use std::collections::HashMap;

use iced_x86::{Code, Encoder, Instruction, MemoryOperand, Register};

use crate::inst::{AtomicRmwOpKind, CondCode, FpBinOpKind, MInst, OpSize, PInst};
use crate::reg::Gpr;
use tuffy_target::reloc::{EncodeResult, RelocKind, Relocation};
use tuffy_target::types::DebugLineRecord;

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

/// Construct an indexed memory operand `[base + index * scale + offset]`.
fn mem_indexed(base: Gpr, index: Gpr, scale: u8, offset: i32) -> MemoryOperand {
    MemoryOperand::with_base_index_scale_displ_size(
        gpr64(base),
        gpr64(index),
        u32::from(scale),
        offset as i64,
        1,
    )
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

/// Return the iced-x86 opcode used for sub.
fn sub_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sub_rm64_r64,
        OpSize::S32 => Code::Sub_rm32_r32,
        OpSize::S16 => Code::Sub_rm16_r16,
        OpSize::S8 => Code::Sub_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for adc.
fn adc_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Adc_rm64_r64,
        OpSize::S32 => Code::Adc_rm32_r32,
        OpSize::S16 => Code::Adc_rm16_r16,
        OpSize::S8 => Code::Adc_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for sbb.
fn sbb_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sbb_rm64_r64,
        OpSize::S32 => Code::Sbb_rm32_r32,
        OpSize::S16 => Code::Sbb_rm16_r16,
        OpSize::S8 => Code::Sbb_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for or.
fn or_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Or_rm64_r64,
        OpSize::S32 => Code::Or_rm32_r32,
        OpSize::S16 => Code::Or_rm16_r16,
        OpSize::S8 => Code::Or_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for and.
fn and_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::And_rm64_r64,
        OpSize::S32 => Code::And_rm32_r32,
        OpSize::S16 => Code::And_rm16_r16,
        OpSize::S8 => Code::And_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for xor.
fn xor_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Xor_rm64_r64,
        OpSize::S32 => Code::Xor_rm32_r32,
        OpSize::S16 => Code::Xor_rm16_r16,
        OpSize::S8 => Code::Xor_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for cmp rr.
fn cmp_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Cmp_rm64_r64,
        OpSize::S32 => Code::Cmp_rm32_r32,
        OpSize::S16 => Code::Cmp_rm16_r16,
        OpSize::S8 => Code::Cmp_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for test rr.
fn test_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Test_rm64_r64,
        OpSize::S32 => Code::Test_rm32_r32,
        OpSize::S16 => Code::Test_rm16_r16,
        OpSize::S8 => Code::Test_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for mov rr.
fn mov_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_r64,
        OpSize::S32 => Code::Mov_rm32_r32,
        OpSize::S16 => Code::Mov_rm16_r16,
        OpSize::S8 => Code::Mov_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for imul rr.
fn imul_rr_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Imul_r64_rm64,
        OpSize::S32 => Code::Imul_r32_rm32,
        OpSize::S16 => Code::Imul_r16_rm16,
        OpSize::S8 => unreachable!("imul not supported for 8-bit"),
    }
}

/// Return the iced-x86 opcode used for cmp ri.
fn cmp_ri_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Cmp_rm64_imm32,
        OpSize::S32 => Code::Cmp_rm32_imm32,
        OpSize::S16 => Code::Cmp_rm16_imm16,
        OpSize::S8 => Code::Cmp_rm8_imm8,
    }
}

/// Return the iced-x86 opcode used for and ri.
fn and_ri_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::And_rm64_imm32,
        OpSize::S32 => Code::And_rm32_imm32,
        OpSize::S16 => Code::And_rm16_imm16,
        OpSize::S8 => Code::And_rm8_imm8,
    }
}

// --- Shift codes ---

/// Return the iced-x86 opcode used for shl cl.
fn shl_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shl_rm64_CL,
        OpSize::S32 => Code::Shl_rm32_CL,
        OpSize::S16 => Code::Shl_rm16_CL,
        OpSize::S8 => Code::Shl_rm8_CL,
    }
}

/// Return the iced-x86 opcode used for shr cl.
fn shr_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shr_rm64_CL,
        OpSize::S32 => Code::Shr_rm32_CL,
        OpSize::S16 => Code::Shr_rm16_CL,
        OpSize::S8 => Code::Shr_rm8_CL,
    }
}

/// Return the iced-x86 opcode used for sar cl.
fn sar_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sar_rm64_CL,
        OpSize::S32 => Code::Sar_rm32_CL,
        OpSize::S16 => Code::Sar_rm16_CL,
        OpSize::S8 => Code::Sar_rm8_CL,
    }
}

/// Return the iced-x86 opcode used for rol cl.
fn rol_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Rol_rm64_CL,
        OpSize::S32 => Code::Rol_rm32_CL,
        OpSize::S16 => Code::Rol_rm16_CL,
        OpSize::S8 => Code::Rol_rm8_CL,
    }
}

/// Return the iced-x86 opcode used for ror cl.
fn ror_cl_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Ror_rm64_CL,
        OpSize::S32 => Code::Ror_rm32_CL,
        OpSize::S16 => Code::Ror_rm16_CL,
        OpSize::S8 => Code::Ror_rm8_CL,
    }
}

/// Return the iced-x86 opcode used for shl imm.
fn shl_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shl_rm64_imm8,
        OpSize::S32 => Code::Shl_rm32_imm8,
        OpSize::S16 => Code::Shl_rm16_imm8,
        OpSize::S8 => Code::Shl_rm8_imm8,
    }
}

/// Return the iced-x86 opcode used for sar imm.
fn sar_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Sar_rm64_imm8,
        OpSize::S32 => Code::Sar_rm32_imm8,
        OpSize::S16 => Code::Sar_rm16_imm8,
        OpSize::S8 => Code::Sar_rm8_imm8,
    }
}

/// Return the iced-x86 opcode used for shr imm.
fn shr_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Shr_rm64_imm8,
        OpSize::S32 => Code::Shr_rm32_imm8,
        OpSize::S16 => Code::Shr_rm16_imm8,
        OpSize::S8 => Code::Shr_rm8_imm8,
    }
}

// --- Branch / conditional codes ---

/// Return the iced-x86 opcode used for jcc.
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
        CondCode::O => Code::Jo_rel32_64,
        CondCode::No => Code::Jno_rel32_64,
    }
}

/// Return the iced-x86 opcode used for cmovcc.
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
        (CondCode::O, OpSize::S64) => Code::Cmovo_r64_rm64,
        (CondCode::O, OpSize::S32) => Code::Cmovo_r32_rm32,
        (CondCode::O, OpSize::S16) => Code::Cmovo_r16_rm16,
        (CondCode::No, OpSize::S64) => Code::Cmovno_r64_rm64,
        (CondCode::No, OpSize::S32) => Code::Cmovno_r32_rm32,
        (CondCode::No, OpSize::S16) => Code::Cmovno_r16_rm16,
        (_, OpSize::S8) => unreachable!("cmovcc not supported for 8-bit"),
    }
}

/// Return the iced-x86 opcode used for setcc.
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
        CondCode::O => Code::Seto_rm8,
        CondCode::No => Code::Setno_rm8,
    }
}

// --- Memory load/store codes ---

/// Return the iced-x86 opcode used for mov load.
fn mov_load_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_r64_rm64,
        OpSize::S32 => Code::Mov_r32_rm32,
        OpSize::S16 => Code::Mov_r16_rm16,
        OpSize::S8 => Code::Mov_r8_rm8,
    }
}

/// Return the iced-x86 opcode used for mov store.
fn mov_store_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_r64,
        OpSize::S32 => Code::Mov_rm32_r32,
        OpSize::S16 => Code::Mov_rm16_r16,
        OpSize::S8 => Code::Mov_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for mov store imm.
fn mov_store_imm_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Mov_rm64_imm32,
        OpSize::S32 => Code::Mov_rm32_imm32,
        OpSize::S16 => Code::Mov_rm16_imm16,
        OpSize::S8 => Code::Mov_rm8_imm8,
    }
}

/// Return the iced-x86 opcode used for bswap.
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

/// Stateful encoder context for one physical x86 function.
struct EncodeContext {
    /// iced-x86 encoder used to append instructions.
    encoder: Encoder,
    /// Current code position in bytes.
    pos: usize,
    /// Resolved label positions keyed by label id.
    labels: HashMap<u32, usize>,
    /// Pending jump fixups waiting for label resolution.
    fixups: Vec<JumpFixup>,
    /// Recorded relocations for the encoded function.
    relocations: Vec<Relocation>,
    /// Raw call-site entries: (call_start, call_length, cleanup_label).
    /// `Some(label)` → cleanup landing pad; `None` → no handler (cs_lpad = 0).
    /// Resolved to byte offsets after encoding.
    call_site_cleanups: Vec<(usize, usize, Option<u32>)>,
    /// Whether this function has any cleanup blocks (used to decide whether to
    /// emit call-site entries for calls without cleanup labels).
    has_any_cleanup: bool,
}

impl EncodeContext {
    /// Internal x86 encoding helper `new`.
    fn new() -> Self {
        Self {
            encoder: Encoder::new(64),
            pos: 0,
            labels: HashMap::new(),
            fixups: Vec::new(),
            relocations: Vec::new(),
            call_site_cleanups: Vec::new(),
            has_any_cleanup: false,
        }
    }

    /// Encode a single instruction, appending bytes to the internal buffer.
    fn emit(&mut self, instr: Instruction) {
        let len = self
            .encoder
            .encode(&instr, self.pos as u64)
            .unwrap_or_else(|err| {
                panic!(
                    "iced-x86 encoding failed at byte {} for instruction {instr:?}: {err}",
                    self.pos
                )
            });
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
pub fn encode_function(insts: &[PInst], inst_sources: &[Option<u32>]) -> EncodeResult {
    let mut ctx = EncodeContext::new();
    let mut line_records = Vec::new();

    // Check if this function has any cleanup landing pads.  When it does,
    // every call instruction must have a call-site entry in the LSDA so
    // the unwinder doesn't mistake an IP in cleanup code for a nounwind
    // region (which would cause it to abort).
    ctx.has_any_cleanup = insts.iter().any(|inst| {
        matches!(
            inst,
            MInst::CallSym {
                cleanup_label: Some(_),
                ..
            } | MInst::CallReg {
                cleanup_label: Some(_),
                ..
            }
        )
    });

    for (inst, &source) in insts.iter().zip(inst_sources.iter()) {
        let start = ctx.pos;
        encode_inst(inst, &mut ctx);
        if let Some(source) = source
            && ctx.pos > start
            && line_records
                .last()
                .is_none_or(|last: &DebugLineRecord| last.source != source)
        {
            line_records.push(DebugLineRecord {
                offset: start as u32,
                source,
            });
        }
    }

    let mut buf = ctx.encoder.take_buffer();

    // Patch jump offsets.
    for fixup in &ctx.fixups {
        let target_addr = ctx.labels[&fixup.target_label];
        // rel32 is relative to the end of the displacement field (patch_offset + 4).
        let rel = target_addr as i32 - (fixup.patch_offset as i32 + 4);
        buf[fixup.patch_offset..fixup.patch_offset + 4].copy_from_slice(&rel.to_le_bytes());
    }

    // Resolve call-site entries to byte offsets.
    let call_site_table = ctx
        .call_site_cleanups
        .iter()
        .filter_map(|(start, len, label)| match label {
            Some(lbl) => ctx
                .labels
                .get(lbl)
                .map(|&lp| tuffy_target::types::CallSiteEntry {
                    call_start: *start,
                    call_length: *len,
                    landing_pad: lp,
                }),
            None => Some(tuffy_target::types::CallSiteEntry {
                call_start: *start,
                call_length: *len,
                landing_pad: 0,
            }),
        })
        .collect();

    EncodeResult {
        code: buf,
        relocations: ctx.relocations,
        call_site_table,
        line_records,
    }
}

// ---------------------------------------------------------------------------
// Per-instruction encoding
// ---------------------------------------------------------------------------

/// Encode one physical x86 instruction into the current context.
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
        MInst::AdcRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    adc_code(*size),
                    gpr_to_iced(*dst, *size),
                    gpr_to_iced(*src, *size),
                )
                .unwrap(),
            );
        }
        MInst::SbbRR { size, dst, src } => {
            ctx.emit(
                Instruction::with2(
                    sbb_code(*size),
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
        MInst::LandingPadCapture { .. } => {
            // No-op: exception pointer is already in RAX from the unwinder.
            // The register allocator maps `dst` to a physical register via MovRR.
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
        MInst::CallSym {
            name,
            cleanup_label,
            ..
        } => {
            let start = ctx.pos;
            ctx.emit(Instruction::with_branch(Code::Call_rel32_64, 0).unwrap());
            let call_end = ctx.pos;
            let offsets = ctx.encoder.get_constant_offsets();
            ctx.relocations.push(Relocation {
                offset: start + offsets.immediate_offset(),
                symbol: name.clone(),
                kind: RelocKind::Call,
            });
            if let Some(label) = cleanup_label {
                ctx.call_site_cleanups
                    .push((start, call_end - start, Some(*label)));
            } else if ctx.has_any_cleanup {
                ctx.call_site_cleanups.push((start, call_end - start, None));
            }
        }
        MInst::CallReg {
            callee,
            cleanup_label,
            ..
        } => {
            let start = ctx.pos;
            ctx.emit(Instruction::with1(Code::Call_rm64, gpr64(*callee)).unwrap());
            let call_end = ctx.pos;
            if let Some(label) = cleanup_label {
                ctx.call_site_cleanups
                    .push((start, call_end - start, Some(*label)));
            } else if ctx.has_any_cleanup {
                ctx.call_site_cleanups.push((start, call_end - start, None));
            }
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
        MInst::LeaIndexed {
            dst,
            base,
            index,
            scale,
            offset,
        } => {
            ctx.emit(
                Instruction::with2(
                    Code::Lea_r64_m,
                    gpr64(*dst),
                    mem_indexed(*base, *index, *scale, *offset),
                )
                .unwrap(),
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

        MInst::TlsLeaSymbol { dst, symbol } => {
            // Initial Exec TLS access: load thread-local address.
            // Step 1: mov dst, qword ptr fs:[0]
            // Encoding: 64 48 8b 04 25 00 00 00 00
            let dst_reg = gpr64(*dst);
            let abs_mem = MemoryOperand::with_displ(0u64, 4);
            let mut fs_mov = Instruction::with2(Code::Mov_r64_rm64, dst_reg, abs_mem).unwrap();
            fs_mov.set_segment_prefix(Register::FS);
            ctx.emit(fs_mov);

            // Step 2: add dst, qword ptr [rip+symbol@GOTTPOFF]
            let start2 = ctx.pos;
            let rip_mem = MemoryOperand::with_base_displ(Register::RIP, 0);
            ctx.emit(Instruction::with2(Code::Add_r64_rm64, dst_reg, rip_mem).unwrap());
            let offsets = ctx.encoder.get_constant_offsets();
            ctx.relocations.push(Relocation {
                offset: start2 + offsets.displacement_offset(),
                symbol: symbol.clone(),
                kind: RelocKind::TlsGotTpOff,
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
        MInst::Popcnt { size, dst, src } => {
            let code = match size {
                OpSize::S16 => Code::Popcnt_r16_rm16,
                OpSize::S32 => Code::Popcnt_r32_rm32,
                OpSize::S64 => Code::Popcnt_r64_rm64,
                OpSize::S8 => unreachable!("popcnt is not selected for 8-bit operands"),
            };
            ctx.emit(
                Instruction::with2(code, gpr_to_iced(*dst, *size), gpr_to_iced(*src, *size))
                    .unwrap(),
            );
        }
        MInst::Lzcnt { size, dst, src } => {
            let code = match size {
                OpSize::S16 => Code::Lzcnt_r16_rm16,
                OpSize::S32 => Code::Lzcnt_r32_rm32,
                OpSize::S64 => Code::Lzcnt_r64_rm64,
                OpSize::S8 => unreachable!("lzcnt is not selected for 8-bit operands"),
            };
            ctx.emit(
                Instruction::with2(code, gpr_to_iced(*dst, *size), gpr_to_iced(*src, *size))
                    .unwrap(),
            );
        }
        MInst::Tzcnt { size, dst, src } => {
            let code = match size {
                OpSize::S16 => Code::Tzcnt_r16_rm16,
                OpSize::S32 => Code::Tzcnt_r32_rm32,
                OpSize::S64 => Code::Tzcnt_r64_rm64,
                OpSize::S8 => unreachable!("tzcnt is not selected for 8-bit operands"),
            };
            ctx.emit(
                Instruction::with2(code, gpr_to_iced(*dst, *size), gpr_to_iced(*src, *size))
                    .unwrap(),
            );
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
        MInst::UMulOverflow {
            dst,
            overflow,
            lhs,
            rhs,
        } => {
            encode_umul_overflow(ctx, *dst, *overflow, *lhs, *rhs);
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
        MInst::GprToXmm { dst, src, double } => {
            encode_gpr_to_xmm(ctx, *dst, *src, *double);
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
            tmp,
            kind,
            double,
        } => {
            encode_fp_cmp(ctx, *dst, *lhs, *rhs, *tmp, *kind, *double);
        }
        MInst::AtomicRmw {
            op,
            size,
            dst,
            base,
            val,
        } => {
            encode_atomic_rmw(ctx, *op, *size, *dst, *base, *val);
        }
        MInst::AtomicCmpXchg {
            size,
            dst,
            base,
            expected,
            desired,
        } => {
            encode_atomic_cmpxchg(ctx, *size, *dst, *base, *expected, *desired);
        }
    }
}

// ---------------------------------------------------------------------------
// Pseudo-instruction expansions
// ---------------------------------------------------------------------------

/// Parallel copy of two register pairs, handling all ordering cases.
fn encode_mov_rr2(ctx: &mut EncodeContext, dst1: Gpr, src1: Gpr, dst2: Gpr, src2: Gpr) {
    debug_assert!(
        dst1 != dst2 || (dst1 == src1 && dst2 == src2),
        "MovRR2 dst1==dst2={dst1:?}, src1={src1:?}, src2={src2:?}"
    );
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

/// UMulOverflow pseudo-instruction expansion.
///
/// Emits: mov rax,lhs; mul rhs → RDX:RAX; test rdx,rdx; setne overflow;
///        movzx overflow; mov dst,rax.
///
/// Uses the one-operand MUL r64 which computes the full 128-bit unsigned
/// product in RDX:RAX.  Overflow is detected when RDX (the high 64 bits)
/// is non-zero.
fn encode_umul_overflow(ctx: &mut EncodeContext, dst: Gpr, overflow: Gpr, lhs: Gpr, rhs: Gpr) {
    // Step 1: Get lhs into RAX and rhs into RCX (scratch) without clobbering.
    // We reuse RCX as the scratch for rhs, same pattern as DivRem.
    if rhs == Gpr::Rax && lhs == Gpr::Rcx {
        // Both swapped — use xchg.
        ctx.emit(Instruction::with2(Code::Xchg_rm64_r64, Register::RCX, Register::RAX).unwrap());
    } else if rhs == Gpr::Rax {
        ctx.emit_mov64(Gpr::Rcx, Gpr::Rax);
        ctx.emit_mov64(Gpr::Rax, lhs);
    } else {
        ctx.emit_mov64(Gpr::Rax, lhs);
        ctx.emit_mov64(Gpr::Rcx, rhs);
    }

    // Step 2: mul rcx — RDX:RAX = RAX * RCX (unsigned)
    ctx.emit(Instruction::with1(Code::Mul_rm64, Register::RCX).unwrap());

    // Step 3: Check overflow (RDX != 0).
    ctx.emit(Instruction::with2(Code::Test_rm64_r64, Register::RDX, Register::RDX).unwrap());
    ctx.emit(Instruction::with1(Code::Setne_rm8, gpr_to_iced(overflow, OpSize::S8)).unwrap());
    ctx.emit(
        Instruction::with2(
            Code::Movzx_r64_rm8,
            gpr64(overflow),
            gpr_to_iced(overflow, OpSize::S8),
        )
        .unwrap(),
    );

    // Step 4: Move low result to dst.
    ctx.emit_mov64(dst, Gpr::Rax);
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
        (FpBinOpKind::Min, true) => (Code::Movsd_xmm_xmmm64, Code::Minsd_xmm_xmmm64),
        (FpBinOpKind::Min, false) => (Code::Movss_xmm_xmmm32, Code::Minss_xmm_xmmm32),
        (FpBinOpKind::Max, true) => (Code::Movsd_xmm_xmmm64, Code::Maxsd_xmm_xmmm64),
        (FpBinOpKind::Max, false) => (Code::Movss_xmm_xmmm32, Code::Maxss_xmm_xmmm32),
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

/// GprToXmm: GPR → XMM bit-reinterpretation via stack spill.
/// Uses [rsp-8] as a temporary scratch slot.
fn encode_gpr_to_xmm(ctx: &mut EncodeContext, dst: Gpr, src: Gpr, double: bool) {
    let rsp_m8 = MemoryOperand::with_base_displ(Register::RSP, -8);
    // 1. Store integer bit-pattern to [rsp-8]
    let store_code = if double {
        Code::Mov_rm64_r64
    } else {
        Code::Mov_rm32_r32
    };
    let src_reg = if double {
        gpr64(src)
    } else {
        gpr_to_iced(src, OpSize::S32)
    };
    ctx.emit(Instruction::with2(store_code, rsp_m8, src_reg).unwrap());
    // 2. Load as float into XMM
    let load_code = if double {
        Code::Movsd_xmm_xmmm64
    } else {
        Code::Movss_xmm_xmmm32
    };
    ctx.emit(Instruction::with2(load_code, xmm_to_iced(dst), rsp_m8).unwrap());
}
/// Encode a floating-point widening or narrowing conversion.
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
#[allow(
    clippy::too_many_arguments,
    reason = "Floating-point compare lowering needs both operands, result registers, predicate kind, and width."
)]
/// Internal x86 encoding helper `encode_fp_cmp`.
fn encode_fp_cmp(
    ctx: &mut EncodeContext,
    dst: Gpr,
    lhs: Gpr,
    rhs: Gpr,
    tmp: Gpr,
    kind: u8,
    double: bool,
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
    let tmp8 = gpr_to_iced(tmp, OpSize::S8);
    match kind {
        // --- Trivial ---
        0 => {
            // False: always 0
            ctx.emit(Instruction::with2(Code::Xor_r32_rm32, dst32, dst32).unwrap());
            return;
        }
        15 => {
            // True: always 1
            ctx.emit(Instruction::with2(Code::Xor_r32_rm32, dst32, dst32).unwrap());
            ctx.emit(Instruction::with2(Code::Inc_rm32, dst32, dst32).unwrap());
            return;
        }
        // --- Single setcc (ordered, no PF concern) ---
        2 => {
            // OGt: CF=0 AND ZF=0 → seta
            ctx.emit(Instruction::with1(Code::Seta_rm8, dst8).unwrap());
        }
        3 => {
            // OGe: CF=0 → setae (PF=0 implied when CF=0 except NaN→CF=1)
            ctx.emit(Instruction::with1(Code::Setae_rm8, dst8).unwrap());
        }
        6 => {
            // ONe: ZF=0 AND PF=0 → setne works because NaN sets ZF=1
            ctx.emit(Instruction::with1(Code::Setne_rm8, dst8).unwrap());
        }
        7 => {
            // Ord: PF=0 → setnp
            ctx.emit(Instruction::with1(Code::Setnp_rm8, dst8).unwrap());
        }
        8 => {
            // Uno: PF=1 → setp
            ctx.emit(Instruction::with1(Code::Setp_rm8, dst8).unwrap());
        }
        // --- Two setcc + AND (ordered, need PF=0 check) ---
        1 => {
            // OEq: ZF=1 AND PF=0
            ctx.emit(Instruction::with1(Code::Sete_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::And_r8_rm8, dst8, tmp8).unwrap());
        }
        4 => {
            // OLt: CF=1 AND PF=0
            ctx.emit(Instruction::with1(Code::Setb_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::And_r8_rm8, dst8, tmp8).unwrap());
        }
        5 => {
            // OLe: (CF=1 OR ZF=1) AND PF=0
            ctx.emit(Instruction::with1(Code::Setbe_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setnp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::And_r8_rm8, dst8, tmp8).unwrap());
        }
        // --- Two setcc + OR (unordered: true if NaN OR ordered condition) ---
        9 => {
            // UEq: ZF=1 OR PF=1
            ctx.emit(Instruction::with1(Code::Sete_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        10 => {
            // UGt: (CF=0 AND ZF=0) OR PF=1 → seta + setp + or
            ctx.emit(Instruction::with1(Code::Seta_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        11 => {
            // UGe: CF=0 OR PF=1 → setae + setp + or
            ctx.emit(Instruction::with1(Code::Setae_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        12 => {
            // ULt: CF=1 OR PF=1 → setb + setp + or
            ctx.emit(Instruction::with1(Code::Setb_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        13 => {
            // ULe: (CF=1 OR ZF=1) OR PF=1 → setbe + setp + or
            ctx.emit(Instruction::with1(Code::Setbe_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        14 => {
            // UNe: ZF=0 OR PF=1 → setne + setp + or
            ctx.emit(Instruction::with1(Code::Setne_rm8, dst8).unwrap());
            ctx.emit(Instruction::with1(Code::Setp_rm8, tmp8).unwrap());
            ctx.emit(Instruction::with2(Code::Or_r8_rm8, dst8, tmp8).unwrap());
        }
        _ => unreachable!("invalid FCmpOp kind: {kind}"),
    }
    ctx.emit(Instruction::with2(Code::Movzx_r32_rm8, dst32, dst8).unwrap());
}

// ---------------------------------------------------------------------------
// Atomic pseudo-instruction expansions
// ---------------------------------------------------------------------------

/// Return the iced-x86 opcode used for xadd.
fn xadd_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Xadd_rm64_r64,
        OpSize::S32 => Code::Xadd_rm32_r32,
        OpSize::S16 => Code::Xadd_rm16_r16,
        OpSize::S8 => Code::Xadd_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for xchg.
fn xchg_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Xchg_rm64_r64,
        OpSize::S32 => Code::Xchg_rm32_r32,
        OpSize::S16 => Code::Xchg_rm16_r16,
        OpSize::S8 => Code::Xchg_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for cmpxchg.
fn cmpxchg_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Cmpxchg_rm64_r64,
        OpSize::S32 => Code::Cmpxchg_rm32_r32,
        OpSize::S16 => Code::Cmpxchg_rm16_r16,
        OpSize::S8 => Code::Cmpxchg_rm8_r8,
    }
}

/// Return the iced-x86 opcode used for neg.
fn neg_code(size: OpSize) -> Code {
    match size {
        OpSize::S64 => Code::Neg_rm64,
        OpSize::S32 => Code::Neg_rm32,
        OpSize::S16 => Code::Neg_rm16,
        OpSize::S8 => Code::Neg_rm8,
    }
}

/// AtomicRmw pseudo-instruction expansion.
///
/// Emits the appropriate atomic instruction sequence depending on the operation:
/// - Xchg: xchg [base], val (implicit lock prefix on memory operands)
/// - Add:  lock xadd [base], val (returns old value)
/// - Sub:  neg val; lock xadd [base], val (returns old value)
/// - And/Or/Xor: cmpxchg loop
fn encode_atomic_rmw(
    ctx: &mut EncodeContext,
    op: AtomicRmwOpKind,
    size: OpSize,
    dst: Gpr,
    base: Gpr,
    val: Gpr,
) {
    // Move base and val to scratch registers (RCX for base, RAX for val)
    // to avoid clobbering input vregs.
    let moved_base = Gpr::Rcx;
    let moved_val = Gpr::Rax;

    // Handle the case where base and val might be in swapped positions.
    if base == Gpr::Rax && val == Gpr::Rcx {
        ctx.emit(Instruction::with2(Code::Xchg_rm64_r64, Register::RCX, Register::RAX).unwrap());
    } else if val == Gpr::Rcx {
        // val is in RCX, move it to RAX first, then move base to RCX
        ctx.emit_mov64(Gpr::Rax, val);
        ctx.emit_mov64(Gpr::Rcx, base);
    } else {
        ctx.emit_mov64(Gpr::Rcx, base);
        ctx.emit_mov64(Gpr::Rax, val);
    }

    let addr = MemoryOperand::with_base(gpr64(moved_base));

    match op {
        AtomicRmwOpKind::Xchg => {
            // xchg [base], rax — implicit lock on memory operand, returns old value in rax
            let inst =
                Instruction::with2(xchg_code(size), addr, gpr_to_iced(moved_val, size)).unwrap();
            ctx.emit(inst);
        }
        AtomicRmwOpKind::Add => {
            // lock xadd [base], rax — old value returned in rax
            let mut inst =
                Instruction::with2(xadd_code(size), addr, gpr_to_iced(moved_val, size)).unwrap();
            inst.set_has_lock_prefix(true);
            ctx.emit(inst);
        }
        AtomicRmwOpKind::Sub => {
            // neg rax; lock xadd [base], rax — old value returned in rax
            ctx.emit(Instruction::with1(neg_code(size), gpr_to_iced(moved_val, size)).unwrap());
            let mut inst =
                Instruction::with2(xadd_code(size), addr, gpr_to_iced(moved_val, size)).unwrap();
            inst.set_has_lock_prefix(true);
            ctx.emit(inst);
        }
        AtomicRmwOpKind::And | AtomicRmwOpKind::Or | AtomicRmwOpKind::Xor => {
            // Cmpxchg loop: RAX = old, RDX = new = old OP val
            // We use RDX as the scratch for the computed new value.
            //
            //   mov rax, [rcx]     ; load current value
            // loop:
            //   mov rdx, rax       ; copy old to rdx
            //   OP  rdx, <val>     ; compute new value (val was moved to a temporary)
            //   lock cmpxchg [rcx], rdx  ; if [rcx]==rax, [rcx]=rdx; else rax=[rcx]
            //   jne loop
            //
            // We store the original val in R11 (caller-saved scratch) since RAX is
            // modified by cmpxchg on failure.

            // Save val to R11 before the loop
            ctx.emit(Instruction::with2(Code::Mov_rm64_r64, Register::R11, Register::RAX).unwrap());

            // Load current value into RAX
            let load_code = match size {
                OpSize::S64 => Code::Mov_r64_rm64,
                OpSize::S32 => Code::Mov_r32_rm32,
                OpSize::S16 => Code::Mov_r16_rm16,
                OpSize::S8 => Code::Mov_r8_rm8,
            };
            ctx.emit(Instruction::with2(load_code, gpr_to_iced(Gpr::Rax, size), addr).unwrap());

            // Record loop start position for backward branch
            let loop_start = ctx.pos;

            // mov rdx, rax (copy current to compute new)
            ctx.emit(
                Instruction::with2(
                    mov_rr_code(size),
                    gpr_to_iced(Gpr::Rdx, size),
                    gpr_to_iced(Gpr::Rax, size),
                )
                .unwrap(),
            );

            // Apply the operation: rdx = rdx OP r11
            let op_code = match op {
                AtomicRmwOpKind::And => and_code(size),
                AtomicRmwOpKind::Or => or_code(size),
                AtomicRmwOpKind::Xor => xor_code(size),
                _ => unreachable!(),
            };
            ctx.emit(
                Instruction::with2(
                    op_code,
                    gpr_to_iced(Gpr::Rdx, size),
                    gpr_to_iced(Gpr::R11, size),
                )
                .unwrap(),
            );

            // lock cmpxchg [rcx], rdx
            let mut cmpxchg =
                Instruction::with2(cmpxchg_code(size), addr, gpr_to_iced(Gpr::Rdx, size)).unwrap();
            cmpxchg.set_has_lock_prefix(true);
            ctx.emit(cmpxchg);

            // jne loop_start (if cmpxchg failed, RAX has new current value, retry)
            ctx.emit(Instruction::with_branch(Code::Jne_rel32_64, loop_start as u64).unwrap());
        }
    }

    // Move result from RAX to dst
    ctx.emit_mov64(dst, Gpr::Rax);
}

/// AtomicCmpXchg pseudo-instruction expansion.
///
/// Emits: mov rax, expected; mov rcx, base; lock cmpxchg [rcx], desired_reg; mov dst, rax
///
/// The lock cmpxchg instruction compares [rcx] with RAX:
/// - If equal: stores desired into [rcx], RAX unchanged
/// - If not equal: loads [rcx] into RAX
///
/// Either way, RAX contains the old value.
fn encode_atomic_cmpxchg(
    ctx: &mut EncodeContext,
    size: OpSize,
    dst: Gpr,
    base: Gpr,
    expected: Gpr,
    desired: Gpr,
) {
    // We need: RAX = expected, RCX = base, some reg = desired
    // Use RDX as scratch for desired to avoid conflicts.

    // Handle potential register conflicts carefully.
    // Move desired to RDX first (it's the least likely to conflict).
    if desired == Gpr::Rax && expected == Gpr::Rdx {
        ctx.emit(Instruction::with2(Code::Xchg_rm64_r64, Register::RAX, Register::RDX).unwrap());
    } else {
        ctx.emit_mov64(Gpr::Rdx, desired);
        ctx.emit_mov64(Gpr::Rax, expected);
    }
    ctx.emit_mov64(Gpr::Rcx, base);

    let addr = MemoryOperand::with_base(gpr64(Gpr::Rcx));
    let mut inst =
        Instruction::with2(cmpxchg_code(size), addr, gpr_to_iced(Gpr::Rdx, size)).unwrap();
    inst.set_has_lock_prefix(true);
    ctx.emit(inst);

    // Result (old value) is in RAX
    ctx.emit_mov64(dst, Gpr::Rax);
}
