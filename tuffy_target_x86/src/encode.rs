//! x86-64 machine code encoding.

use std::collections::HashMap;

use crate::inst::{MInst, OpSize};
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
pub fn encode_function(insts: &[MInst]) -> EncodeResult {
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
    inst: &MInst,
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
        MInst::CallSym { name } => {
            buf.push(0xe8);
            relocations.push(Relocation {
                offset: buf.len(),
                symbol: name.clone(),
                kind: RelocKind::Call,
            });
            buf.extend_from_slice(&[0; 4]);
        }
        MInst::Push { reg } => {
            encode_push(*reg, buf);
        }
        MInst::Pop { reg } => {
            encode_pop(*reg, buf);
        }
        MInst::SubSPI { imm } => {
            encode_rsp_imm(0xe8, *imm, buf);
        }
        MInst::AddSPI { imm } => {
            encode_rsp_imm(0xc0, *imm, buf);
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
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex_mem(w, dst, base) {
        buf.push(r);
    }
    buf.push(0x8b);
    modrm_mem(dst.encoding(), base, offset, buf);
}

fn encode_mov_mr(size: OpSize, base: Gpr, offset: i32, src: Gpr, buf: &mut Vec<u8>) {
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex_mem(w, src, base) {
        buf.push(r);
    }
    buf.push(0x89);
    modrm_mem(src.encoding(), base, offset, buf);
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

fn encode_mov_mi(size: OpSize, base: Gpr, offset: i32, imm: i32, buf: &mut Vec<u8>) {
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
