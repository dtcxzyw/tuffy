//! x86-64 machine code encoding.

use tuffy_target_x86::inst::{MInst, OpSize};
use tuffy_target_x86::reg::Gpr;

/// Encode a sequence of machine instructions into bytes.
pub fn encode_function(insts: &[MInst]) -> Vec<u8> {
    let mut buf = Vec::new();
    for inst in insts {
        encode_inst(inst, &mut buf);
    }
    buf
}

fn encode_inst(inst: &MInst, buf: &mut Vec<u8>) {
    match inst {
        MInst::MovRR { size, dst, src } => encode_mov_rr(*size, *dst, *src, buf),
        MInst::MovRI { size, dst, imm } => encode_mov_ri(*size, *dst, *imm, buf),
        MInst::AddRR { size, dst, src } => encode_alu_rr(0x01, *size, *dst, *src, buf),
        MInst::SubRR { size, dst, src } => encode_alu_rr(0x29, *size, *dst, *src, buf),
        MInst::ImulRR { size, dst, src } => encode_imul_rr(*size, *dst, *src, buf),
        MInst::Ret => buf.push(0xc3),
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
    // MOV r/m, r: 0x89 /r  (src is reg field, dst is rm field)
    emit_rex_and_opcode(size, src, dst, 0x89, buf);
}

fn encode_alu_rr(opcode: u8, size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    // ADD r/m, r: 0x01 /r | SUB r/m, r: 0x29 /r
    emit_rex_and_opcode(size, src, dst, opcode, buf);
}

fn encode_mov_ri(size: OpSize, dst: Gpr, imm: i64, buf: &mut Vec<u8>) {
    // MOV r32, imm32: 0xB8+rd id
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
    // IMUL r, r/m: 0x0F 0xAF /r  (dst is reg field, src is rm field)
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex(w, dst, src) {
        buf.push(r);
    }
    buf.push(0x0f);
    buf.push(0xaf);
    buf.push(modrm(dst.encoding(), src.encoding()));
}
