//! x86-64 machine code encoding.

use std::collections::HashMap;

use tuffy_target_x86::inst::{MInst, OpSize};
use tuffy_target_x86::reg::Gpr;

/// A fixup for a jump instruction whose target offset is not yet known.
struct JumpFixup {
    /// Byte offset in the buffer where the rel32 displacement starts.
    patch_offset: usize,
    /// The label ID this jump targets.
    target_label: u32,
}

/// Kind of relocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocKind {
    /// PC-relative call (R_X86_64_PLT32).
    Call,
    /// PC-relative data reference (R_X86_64_PC32).
    PcRel,
}

/// A relocation for an external symbol reference (e.g., CALL or LEA).
#[derive(Debug, Clone)]
pub struct Relocation {
    /// Byte offset in the code buffer where the rel32 displacement starts.
    pub offset: usize,
    /// The symbol name this relocation targets.
    pub symbol: String,
    /// Kind of relocation.
    pub kind: RelocKind,
}

/// Result of encoding a function.
pub struct EncodeResult {
    /// Encoded machine code bytes.
    pub code: Vec<u8>,
    /// Relocations for external symbol references.
    pub relocations: Vec<Relocation>,
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
            // CALL rel32: 0xE8 cd
            buf.push(0xe8);
            relocations.push(Relocation {
                offset: buf.len(),
                symbol: name.clone(),
                kind: RelocKind::Call,
            });
            buf.extend_from_slice(&[0; 4]); // placeholder for linker
        }
        MInst::Push { reg } => {
            encode_push(*reg, buf);
        }
        MInst::Pop { reg } => {
            encode_pop(*reg, buf);
        }
        MInst::SubSPI { imm } => {
            encode_rsp_imm(0xe8, *imm, buf); // SUB rsp, imm32
        }
        MInst::AddSPI { imm } => {
            encode_rsp_imm(0xc0, *imm, buf); // ADD rsp, imm32
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
            // OR r/m, r: 0x09 /r
            encode_alu_rr(0x09, *size, *dst, *src, buf);
        }
        MInst::ShlRCL { size, dst } => {
            // SHL r/m, CL: 0xD3 /4
            let w = matches!(size, OpSize::S64);
            let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
            let w_bit = if w { 0x08 } else { 0 };
            let rex_bits = w_bit | b_bit;
            if rex_bits != 0 {
                buf.push(0x40 | rex_bits);
            }
            buf.push(0xd3);
            buf.push(modrm(4, dst.encoding()));
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

fn encode_cmp_ri(size: OpSize, src: Gpr, imm: i32, buf: &mut Vec<u8>) {
    // CMP r/m, imm32: 0x81 /7 id
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
    // PUSH r64: 0x50+rd (REX.B if extended register)
    if reg.needs_rex() {
        buf.push(0x41);
    }
    buf.push(0x50 + reg.encoding());
}

fn encode_pop(reg: Gpr, buf: &mut Vec<u8>) {
    // POP r64: 0x58+rd (REX.B if extended register)
    if reg.needs_rex() {
        buf.push(0x41);
    }
    buf.push(0x58 + reg.encoding());
}

fn encode_rsp_imm(modrm_byte: u8, imm: i32, buf: &mut Vec<u8>) {
    // REX.W + 0x81 /0 id (ADD) or /5 id (SUB) with rsp as rm
    // modrm_byte: 0xc0 for ADD rsp, 0xe8 for SUB rsp
    buf.push(0x48); // REX.W
    buf.push(0x81);
    buf.push(modrm_byte);
    buf.extend_from_slice(&imm.to_le_bytes());
}

/// Encode ModR/M byte with [base+disp32] addressing (mod=10).
/// Special-cases RSP (needs SIB byte) and RBP (always uses disp).
fn modrm_mem(reg: u8, base: Gpr, offset: i32, buf: &mut Vec<u8>) {
    if offset == 0 && base.encoding() != 5 && base != Gpr::R13 {
        // mod=00: [base] with no displacement
        buf.push((reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24); // SIB: scale=0, index=RSP(none), base=RSP
        }
    } else if (-128..=127).contains(&offset) {
        // mod=01: [base+disp8]
        buf.push(0x40 | (reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24); // SIB byte
        }
        buf.push(offset as u8);
    } else {
        // mod=10: [base+disp32]
        buf.push(0x80 | (reg << 3) | base.encoding());
        if base == Gpr::Rsp || base == Gpr::R12 {
            buf.push(0x24); // SIB byte
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
    // MOV r, r/m: 0x8B /r with memory operand
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex_mem(w, dst, base) {
        buf.push(r);
    }
    buf.push(0x8b);
    modrm_mem(dst.encoding(), base, offset, buf);
}

fn encode_mov_mr(size: OpSize, base: Gpr, offset: i32, src: Gpr, buf: &mut Vec<u8>) {
    // MOV r/m, r: 0x89 /r with memory operand
    let w = matches!(size, OpSize::S64);
    if let Some(r) = rex_mem(w, src, base) {
        buf.push(r);
    }
    buf.push(0x89);
    modrm_mem(src.encoding(), base, offset, buf);
}

fn encode_lea(dst: Gpr, base: Gpr, offset: i32, buf: &mut Vec<u8>) {
    // LEA r64, [base+offset]: REX.W + 0x8D /r
    if let Some(r) = rex_mem(true, dst, base) {
        buf.push(r);
    } else {
        buf.push(0x48); // REX.W always needed for 64-bit LEA
    }
    buf.push(0x8d);
    modrm_mem(dst.encoding(), base, offset, buf);
}

fn encode_mov_ri64(dst: Gpr, imm: i64, buf: &mut Vec<u8>) {
    // MOV r64, imm64: REX.W + 0xB8+rd io
    let b_bit = if dst.needs_rex() { 0x01 } else { 0 };
    buf.push(0x48 | b_bit); // REX.W
    buf.push(0xb8 + dst.encoding());
    buf.extend_from_slice(&imm.to_le_bytes());
}

fn encode_lea_symbol(dst: Gpr, symbol: &str, buf: &mut Vec<u8>, relocations: &mut Vec<Relocation>) {
    // LEA reg, [rip+disp32]: REX.W + 0x8D /r with ModRM mod=00, rm=5 (RIP-relative)
    let r_bit = if dst.needs_rex() { 0x04 } else { 0 };
    buf.push(0x48 | r_bit); // REX.W (+ REX.R if needed)
    buf.push(0x8d);
    buf.push((dst.encoding() << 3) | 0x05); // mod=00, reg=dst, rm=5 (RIP)
    relocations.push(Relocation {
        offset: buf.len(),
        symbol: symbol.to_string(),
        kind: RelocKind::PcRel,
    });
    buf.extend_from_slice(&[0; 4]); // placeholder for linker
}

fn encode_mov_mi(size: OpSize, base: Gpr, offset: i32, imm: i32, buf: &mut Vec<u8>) {
    // MOV r/m, imm32: 0xC7 /0 id with memory operand
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
