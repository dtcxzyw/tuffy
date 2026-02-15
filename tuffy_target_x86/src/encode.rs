//! x86-64 machine code encoding.

use std::collections::HashMap;

use crate::inst::{CondCode, MInst, OpSize, PInst};
use crate::reg::Gpr;
use tuffy_target::reloc::{EncodeResult, RelocKind, Relocation};

/// A fixup for a jump instruction whose target offset is not yet known.
struct JumpFixup {
    /// Byte offset in the buffer where the rel32 displacement starts.
    patch_offset: usize,
    /// The label ID this jump targets.
    target_label: u32,
}

/// Encode a sequence of machine instructions into bytes.
///
/// Uses a two-pass approach: first pass emits code with placeholder jump
/// offsets, second pass patches the actual relative displacements.
/// External call relocations are returned separately for the ELF emitter.
pub fn encode_function(insts: &[PInst]) -> EncodeResult {
    let mut buf = Vec::new();
    let mut labels: HashMap<u32, usize> = HashMap::new();
    let mut fixups: Vec<JumpFixup> = Vec::new();
    let mut relocations: Vec<Relocation> = Vec::new();

    for inst in insts {
        encode_inst(inst, &mut buf, &mut labels, &mut fixups, &mut relocations);
    }

    // Patch jump offsets.
    for fixup in &fixups {
        let target_addr = labels[&fixup.target_label];
        // rel32 is relative to the end of the jump instruction (patch_offset + 4).
        let rel = target_addr as i32 - (fixup.patch_offset as i32 + 4);
        let bytes = rel.to_le_bytes();
        buf[fixup.patch_offset..fixup.patch_offset + 4].copy_from_slice(&bytes);
    }

    EncodeResult {
        code: buf,
        relocations,
    }
}

fn encode_inst(
    inst: &PInst,
    buf: &mut Vec<u8>,
    labels: &mut HashMap<u32, usize>,
    fixups: &mut Vec<JumpFixup>,
    relocations: &mut Vec<Relocation>,
) {
    match inst {
        MInst::MovRR { size, dst, src } => encode_mov_rr(*size, *dst, *src, buf),
        MInst::MovRI { size, dst, imm } => encode_mov_ri(*size, *dst, *imm, buf),
        MInst::AddRR { size, dst, src } => encode_alu_rr(0x01, *size, *dst, *src, buf),
        MInst::SubRR { size, dst, src } => encode_alu_rr(0x29, *size, *dst, *src, buf),
        MInst::ImulRR { size, dst, src } => encode_imul_rr(*size, *dst, *src, buf),
        MInst::Ret => buf.push(0xc3),
        MInst::Ud2 => {
            buf.push(0x0f);
            buf.push(0x0b);
        }
        MInst::Label { id } => {
            labels.insert(*id, buf.len());
        }
        MInst::Jmp { target } => {
            buf.push(0xe9);
            fixups.push(JumpFixup {
                patch_offset: buf.len(),
                target_label: *target,
            });
            buf.extend_from_slice(&[0; 4]);
        }
        MInst::Jcc { cc, target } => {
            buf.push(0x0f);
            buf.push(0x80 + cc.encoding());
            fixups.push(JumpFixup {
                patch_offset: buf.len(),
                target_label: *target,
            });
            buf.extend_from_slice(&[0; 4]);
        }
        MInst::CmpRR { size, src1, src2 } => {
            emit_rex_and_opcode(*size, *src2, *src1, 0x39, buf);
        }
        MInst::CmpRI { size, src, imm } => {
            encode_cmp_ri(*size, *src, *imm, buf);
        }
        MInst::TestRR { size, src1, src2 } => {
            emit_rex_and_opcode(*size, *src2, *src1, 0x85, buf);
        }
        MInst::CallSym { name, .. } => {
            buf.push(0xe8);
            relocations.push(Relocation {
                offset: buf.len(),
                symbol: name.clone(),
                kind: RelocKind::Call,
            });
            buf.extend_from_slice(&[0; 4]);
        }
        MInst::CallReg { callee, .. } => {
            // FF /2 = call *%reg
            if callee.needs_rex() {
                buf.push(0x41); // REX.B
            }
            buf.push(0xff);
            buf.push(0xd0 | callee.encoding());
        }
        MInst::Push { reg } => {
            encode_push(*reg, buf);
        }
        MInst::Pop { reg } => {
            encode_pop(*reg, buf);
        }
        MInst::SubSPI { imm } => {
            encode_rsp_imm(0xec, *imm, buf);
        }
        MInst::AddSPI { imm } => {
            encode_rsp_imm(0xc4, *imm, buf);
        }
        MInst::MovRM {
            size,
            dst,
            base,
            offset,
        } => {
            encode_mov_rm(*size, *dst, *base, *offset, buf);
        }
        MInst::MovMR {
            size,
            base,
            offset,
            src,
        } => {
            encode_mov_mr(*size, *base, *offset, *src, buf);
        }
        MInst::Lea { dst, base, offset } => {
            encode_lea(*dst, *base, *offset, buf);
        }
        MInst::MovRI64 { dst, imm } => {
            encode_mov_ri64(*dst, *imm, buf);
        }
        MInst::MovMI {
            size,
            base,
            offset,
            imm,
        } => {
            encode_mov_mi(*size, *base, *offset, *imm, buf);
        }
        MInst::LeaSymbol { dst, symbol } => {
            encode_lea_symbol(*dst, symbol, buf, relocations);
        }
        MInst::OrRR { size, dst, src } => {
            encode_alu_rr(0x09, *size, *dst, *src, buf);
        }
        MInst::AndRR { size, dst, src } => {
            encode_alu_rr(0x21, *size, *dst, *src, buf);
        }
        MInst::XorRR { size, dst, src } => {
            encode_alu_rr(0x31, *size, *dst, *src, buf);
        }
        MInst::ShlRCL { size, dst } => {
            encode_shift_cl(4, *size, *dst, buf);
        }
        MInst::ShrRCL { size, dst } => {
            encode_shift_cl(5, *size, *dst, buf);
        }
        MInst::SarRCL { size, dst } => {
            encode_shift_cl(7, *size, *dst, buf);
        }
        MInst::ShlImm { size, dst, imm } => {
            encode_shift_imm(4, *size, *dst, *imm, buf);
        }
        MInst::SarImm { size, dst, imm } => {
            encode_shift_imm(7, *size, *dst, *imm, buf);
        }
        MInst::AndRI { size, dst, imm } => {
            encode_alu_ri(4, *size, *dst, *imm as i32, buf);
        }
        MInst::CMOVcc { size, cc, dst, src } => {
            encode_cmovcc(*size, *cc, *dst, *src, buf);
        }
        MInst::SetCC { cc, dst } => {
            encode_setcc(*cc, *dst, buf);
        }
        MInst::MovzxB { dst, src } => {
            encode_movzx_b(*dst, *src, buf);
        }
        MInst::MovzxW { dst, src } => {
            encode_movzx_w(*dst, *src, buf);
        }
        MInst::MovsxB { dst, src } => {
            encode_movsx_b(*dst, *src, buf);
        }
        MInst::MovsxW { dst, src } => {
            encode_movsx_w(*dst, *src, buf);
        }
        MInst::MovsxD { dst, src } => {
            encode_movsxd(*dst, *src, buf);
        }
        MInst::Cqo => {
            encode_cqo(buf);
        }
        MInst::DivRem {
            dst,
            lhs,
            rhs,
            signed,
            rem,
        } => {
            encode_divrem(*dst, *lhs, *rhs, *signed, *rem, buf);
        }
        MInst::Popcnt { dst, src } => {
            encode_popcnt(*dst, *src, buf);
        }
        MInst::Lzcnt { dst, src } => {
            encode_lzcnt(*dst, *src, buf);
        }
        MInst::Tzcnt { dst, src } => {
            encode_tzcnt(*dst, *src, buf);
        }
    }
}

/// Build REX prefix byte. Returns None if no REX needed.
fn rex(w: bool, r: Gpr, b: Gpr) -> Option<u8> {
    let w_bit = if w { 0x08 } else { 0 };
    let r_bit = if r.needs_rex() { 0x04 } else { 0 };
    let b_bit = if b.needs_rex() { 0x01 } else { 0 };
    let bits = w_bit | r_bit | b_bit;
    if bits != 0 { Some(0x40 | bits) } else { None }
}

/// Encode ModR/M byte: mod=11 (register-direct), reg, rm.
fn modrm(reg: u8, rm: u8) -> u8 {
    0b11_000_000 | (reg << 3) | rm
}

fn emit_rex_and_opcode(size: OpSize, reg: Gpr, rm: Gpr, opcode: u8, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex(w, reg, rm) {
        buf.push(r);
    }
    buf.push(opcode);
    buf.push(modrm(reg.encoding(), rm.encoding()));
}

fn encode_mov_rr(size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    emit_rex_and_opcode(size, src, dst, 0x89, buf);
}

fn encode_alu_rr(opcode: u8, size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    emit_rex_and_opcode(size, src, dst, opcode, buf);
}

fn encode_mov_ri(size: OpSize, dst: Gpr, imm: i64, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let r_bit = if dst.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | r_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0xb8 + dst.encoding());
    let bytes = (imm as u32).to_le_bytes();
    buf.extend_from_slice(&bytes);
}

fn encode_imul_rr(size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex(w, dst, src) {
        buf.push(r);
    }
    buf.push(0x0f);
    buf.push(0xaf);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

fn encode_cmp_ri(size: OpSize, src: Gpr, imm: i32, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if src.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0x81);
    buf.push(modrm(7, src.encoding()));
    buf.extend_from_slice(&imm.to_le_bytes());
}

fn encode_push(reg: Gpr, buf: &mut Vec<u8>) {
    if reg.needs_rex() {
        buf.push(0x41);
    }
    buf.push(0x50 + reg.encoding());
}

fn encode_pop(reg: Gpr, buf: &mut Vec<u8>) {
    if reg.needs_rex() {
        buf.push(0x41);
    }
    buf.push(0x58 + reg.encoding());
}

fn encode_rsp_imm(modrm_byte: u8, imm: i32, buf: &mut Vec<u8>) {
    buf.push(0x48); // REX.W
    buf.push(0x81);
    buf.push(modrm_byte);
    buf.extend_from_slice(&imm.to_le_bytes());
}

/// Encode ModR/M byte with [base+disp] addressing.
/// Special-cases RSP (needs SIB byte) and RBP (always uses disp).
fn modrm_mem(reg: u8, base: Gpr, offset: i32, buf: &mut Vec<u8>) {
    if offset == 0 && base.encoding() != 5 && base != Gpr::R13 {
        buf.push((reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24);
        }
    } else if (-128..=127).contains(&offset) {
        buf.push(0x40 | (reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24);
        }
        buf.push(offset as u8);
    } else {
        buf.push(0x80 | (reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24);
        }
        buf.extend_from_slice(&offset.to_le_bytes());
    }
}

fn rex_mem(w: bool, reg: Gpr, base: Gpr) -> Option<u8> {
    let w_bit = if w { 0x08 } else { 0 };
    let r_bit = if reg.needs_rex() { 0x04 } else { 0 };
    let b_bit = if base.needs_rex() { 0x01 } else { 0 };
    let bits = w_bit | r_bit | b_bit;
    if bits != 0 { Some(0x40 | bits) } else { None }
}

fn encode_mov_rm(size: OpSize, dst: Gpr, base: Gpr, offset: i32, buf: &mut Vec<u8>) {
    match size {
        OpSize::S8 => {
            // movzbl [mem], r32 — zero-extend byte to 32-bit (implicitly zeros upper 32).
            // REX prefix needed if dst or base is r8-r15.
            if let Some(r) = rex_mem(false, dst, base) {
                buf.push(r);
            }
            buf.push(0x0f);
            buf.push(0xb6);
            modrm_mem(dst.encoding(), base, offset, buf);
        }
        OpSize::S16 => {
            // movzwl [mem], r32 — zero-extend word to 32-bit.
            if let Some(r) = rex_mem(false, dst, base) {
                buf.push(r);
            }
            buf.push(0x0f);
            buf.push(0xb7);
            modrm_mem(dst.encoding(), base, offset, buf);
        }
        _ => {
            let w = matches!(size, OpSize::S64);
            if let Some(r) = rex_mem(w, dst, base) {
                buf.push(r);
            }
            buf.push(0x8b);
            modrm_mem(dst.encoding(), base, offset, buf);
        }
    }
}

fn encode_mov_mr(size: OpSize, base: Gpr, offset: i32, src: Gpr, buf: &mut Vec<u8>) {
    match size {
        OpSize::S8 => {
            // mov [mem], r8 — byte store.
            // Always emit REX when src encoding >= 4 to get SPL/BPL/SIL/DIL
            // instead of AH/CH/DH/BH.
            let need_rex = src.needs_rex() || base.needs_rex() || src.encoding() >= 4;
            if need_rex {
                let mut r = 0x40u8;
                if src.needs_rex() {
                    r |= 0x04;
                }
                if base.needs_rex() {
                    r |= 0x01;
                }
                buf.push(r);
            }
            buf.push(0x88);
            modrm_mem(src.encoding(), base, offset, buf);
        }
        OpSize::S16 => {
            // 0x66 prefix for 16-bit operand size.
            buf.push(0x66);
            if let Some(r) = rex_mem(false, src, base) {
                buf.push(r);
            }
            buf.push(0x89);
            modrm_mem(src.encoding(), base, offset, buf);
        }
        _ => {
            let w = matches!(size, OpSize::S64);
            if let Some(r) = rex_mem(w, src, base) {
                buf.push(r);
            }
            buf.push(0x89);
            modrm_mem(src.encoding(), base, offset, buf);
        }
    }
}

fn encode_lea(dst: Gpr, base: Gpr, offset: i32, buf: &mut Vec<u8>) {
    if let Some(r) = rex_mem(true, dst, base) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x8d);
    modrm_mem(dst.encoding(), base, offset, buf);
}

fn encode_mov_ri64(dst: Gpr, imm: i64, buf: &mut Vec<u8>) {
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    buf.push(0x48 | b_bit);
    buf.push(0xb8 + dst.encoding());
    buf.extend_from_slice(&imm.to_le_bytes());
}

fn encode_lea_symbol(dst: Gpr, symbol: &str, buf: &mut Vec<u8>, relocations: &mut Vec<Relocation>) {
    let r_bit = if dst.needs_rex() { 0x04 } else { 0 };
    buf.push(0x48 | r_bit);
    buf.push(0x8d);
    buf.push((dst.encoding() << 3) | 0x05);
    relocations.push(Relocation {
        offset: buf.len(),
        symbol: symbol.to_string(),
        kind: RelocKind::PcRel,
    });
    buf.extend_from_slice(&[0; 4]);
}

/// Encode a shift-by-CL instruction (SHL/SHR/SAR with reg field selecting the operation).
fn encode_shift_cl(reg_field: u8, size: OpSize, dst: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0xd3);
    buf.push(modrm(reg_field, dst.encoding()));
}

/// Encode a shift-by-immediate instruction (SHL/SAR r/m, imm8).
/// Opcode C1 /reg_field ib (REX.W for 64-bit).
fn encode_shift_imm(reg_field: u8, size: OpSize, dst: Gpr, imm: u8, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0xc1);
    buf.push(modrm(reg_field, dst.encoding()));
    buf.push(imm);
}

/// Encode ALU r/m, imm32 (AND/OR/etc with immediate).
/// Opcode 81 /reg_field id (REX.W for 64-bit).
fn encode_alu_ri(reg_field: u8, size: OpSize, dst: Gpr, imm: i32, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0x81);
    buf.push(modrm(reg_field, dst.encoding()));
    buf.extend_from_slice(&imm.to_le_bytes());
}

fn encode_mov_mi(size: OpSize, base: Gpr, offset: i32, imm: i32, buf: &mut Vec<u8>) {
    match size {
        OpSize::S8 => {
            let b_bit = if base.needs_rex() { 0x01 } else { 0 };
            if b_bit != 0 {
                buf.push(0x40 | b_bit);
            }
            buf.push(0xc6);
            modrm_mem(0, base, offset, buf);
            buf.push(imm as u8);
        }
        OpSize::S16 => {
            buf.push(0x66);
            let b_bit = if base.needs_rex() { 0x01 } else { 0 };
            if b_bit != 0 {
                buf.push(0x40 | b_bit);
            }
            buf.push(0xc7);
            modrm_mem(0, base, offset, buf);
            buf.extend_from_slice(&(imm as i16).to_le_bytes());
        }
        _ => {
            let w = matches!(size, OpSize::S64);
            let b_bit = if base.needs_rex() { 0x01 } else { 0 };
            let w_bit = if w { 0x08 } else { 0 };
            let rex_bits = w_bit | b_bit;
            if rex_bits != 0 {
                buf.push(0x40 | rex_bits);
            }
            buf.push(0xc7);
            modrm_mem(0, base, offset, buf);
            buf.extend_from_slice(&imm.to_le_bytes());
        }
    }
}

/// Encode CMOVcc r64, r/m64 (0F 40+cc /r with REX.W).
fn encode_cmovcc(size: OpSize, cc: CondCode, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex(w, dst, src) {
        buf.push(r);
    }
    buf.push(0x0f);
    buf.push(0x40 + cc.encoding());
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode SETcc r/m8 (0F 90+cc /0). Uses REX prefix if dst needs it.
/// A REX prefix is required for registers with encoding >= 4 (RSP, RBP,
/// RSI, RDI) to access their low byte (SPL, BPL, SIL, DIL) instead of
/// the legacy high-byte registers (AH, CH, DH, BH).
fn encode_setcc(cc: CondCode, dst: Gpr, buf: &mut Vec<u8>) {
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    if b_bit != 0 || dst.encoding() >= 4 {
        buf.push(0x40 | b_bit);
    }
    buf.push(0x0f);
    buf.push(0x90 + cc.encoding());
    buf.push(modrm(0, dst.encoding()));
}

/// Encode MOVZX r64, r8 (REX.W + 0F B6 /r).
fn encode_movzx_b(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xb6);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode MOVZX r64, r16 (REX.W + 0F B7 /r).
fn encode_movzx_w(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xb7);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode MOVSX r64, r8 (REX.W + 0F BE /r).
fn encode_movsx_b(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xbe);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode MOVSX r64, r16 (REX.W + 0F BF /r).
fn encode_movsx_w(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xbf);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode MOVSXD r64, r32 (REX.W + 63 /r).
fn encode_movsxd(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x63);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode CQO (REX.W + 99): sign-extend RAX into RDX:RAX.
fn encode_cqo(buf: &mut Vec<u8>) {
    buf.push(0x48);
    buf.push(0x99);
}

/// Encode the DivRem pseudo-instruction expansion.
///
/// Emits: mov rcx,rhs; mov rax,lhs; {xor edx,edx | cqo}; {div|idiv} rcx;
///        mov dst,{rax|rdx}
///
/// Care is taken to handle the case where lhs or rhs is already in one of
/// the scratch registers (RAX, RCX).
fn encode_divrem(dst: Gpr, lhs: Gpr, rhs: Gpr, signed: bool, rem: bool, buf: &mut Vec<u8>) {
    // Step 1: Get rhs into RCX and lhs into RAX without clobbering either.
    if rhs == Gpr::Rax && lhs == Gpr::Rcx {
        // Both are swapped — use xchg rax, rcx.
        // REX.W + 87 /r  (xchg rcx, rax)
        buf.push(0x48);
        buf.push(0x87);
        buf.push(modrm(Gpr::Rcx.encoding(), Gpr::Rax.encoding()));
    } else if rhs == Gpr::Rax {
        // rhs is in RAX — move it to RCX first, then move lhs to RAX.
        encode_mov_rr(OpSize::S64, Gpr::Rcx, Gpr::Rax, buf);
        if lhs != Gpr::Rax {
            encode_mov_rr(OpSize::S64, Gpr::Rax, lhs, buf);
        }
    } else {
        // Move lhs to RAX first (safe: rhs is not in RAX).
        if lhs != Gpr::Rax {
            encode_mov_rr(OpSize::S64, Gpr::Rax, lhs, buf);
        }
        if rhs != Gpr::Rcx {
            encode_mov_rr(OpSize::S64, Gpr::Rcx, rhs, buf);
        }
    }

    // Step 2: Set up RDX (zero for unsigned, sign-extend for signed).
    if signed {
        encode_cqo(buf);
    } else {
        // xor edx, edx (33 D2)
        buf.push(0x33);
        buf.push(modrm(Gpr::Rdx.encoding(), Gpr::Rdx.encoding()));
    }

    // Step 3: div/idiv rcx
    if signed {
        encode_idiv(OpSize::S64, Gpr::Rcx, buf);
    } else {
        encode_div(OpSize::S64, Gpr::Rcx, buf);
    }

    // Step 4: Move result to dst.
    let result_reg = if rem { Gpr::Rdx } else { Gpr::Rax };
    if dst != result_reg {
        encode_mov_rr(OpSize::S64, dst, result_reg, buf);
    }
}

/// Encode IDIV r/m (REX.W + F7 /7): signed divide RDX:RAX by src.
fn encode_idiv(size: OpSize, src: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if src.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0xf7);
    buf.push(modrm(7, src.encoding()));
}

/// Encode DIV r/m (REX.W + F7 /6): unsigned divide RDX:RAX by src.
fn encode_div(size: OpSize, src: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    let b_bit = if src.needs_rex() { 0x01 } else { 0 };
    let w_bit = if w { 0x08 } else { 0 };
    let rex_bits = w_bit | b_bit;
    if rex_bits != 0 {
        buf.push(0x40 | rex_bits);
    }
    buf.push(0xf7);
    buf.push(modrm(6, src.encoding()));
}

/// Encode POPCNT r64, r64 (F3 REX.W 0F B8 /r).
fn encode_popcnt(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    buf.push(0xf3);
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xb8);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode LZCNT r64, r64 (F3 REX.W 0F BD /r).
fn encode_lzcnt(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    buf.push(0xf3);
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xbd);
    buf.push(modrm(dst.encoding(), src.encoding()));
}

/// Encode TZCNT r64, r64 (F3 REX.W 0F BC /r).
fn encode_tzcnt(dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    buf.push(0xf3);
    if let Some(r) = rex(true, dst, src) {
        buf.push(r);
    } else {
        buf.push(0x48);
    }
    buf.push(0x0f);
    buf.push(0xbc);
    buf.push(modrm(dst.encoding(), src.encoding()));
}
