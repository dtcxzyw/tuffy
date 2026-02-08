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
        MInst::AddRR { size, dst, src } => encode_add_rr(*size, *dst, *src, buf),
        MInst::Ret => buf.push(0xc3),
    }
}

/// Encode ModR/M byte: mod=11 (register-direct), reg, rm.
fn modrm(reg: u8, rm: u8) -> u8 {
    0b11_000_000 | (reg << 3) | rm
}

fn encode_mov_rr(size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    // MOV r32, r32: 0x89 /r  (src is reg field, dst is rm field)
    // MOV r64, r64: REX.W + 0x89 /r
    match size {
        OpSize::S64 => buf.push(0x48), // REX.W
        OpSize::S32 => {}
    }
    buf.push(0x89);
    buf.push(modrm(src.encoding(), dst.encoding()));
}

fn encode_add_rr(size: OpSize, dst: Gpr, src: Gpr, buf: &mut Vec<u8>) {
    // ADD r32, r32: 0x01 /r  (src is reg field, dst is rm field)
    // ADD r64, r64: REX.W + 0x01 /r
    match size {
        OpSize::S64 => buf.push(0x48), // REX.W
        OpSize::S32 => {}
    }
    buf.push(0x01);
    buf.push(modrm(src.encoding(), dst.encoding()));
}
