//! Stack frame setup: prologue/epilogue insertion (post-regalloc).

use crate::inst::{MInst, OpSize, PInst};
use crate::reg::Gpr;
use tuffy_regalloc::PReg;

/// Convert a PReg to a Gpr for push/pop instructions.
fn preg_to_gpr(p: PReg) -> Gpr {
    match p.0 {
        0 => Gpr::Rax,
        1 => Gpr::Rcx,
        2 => Gpr::Rdx,
        3 => Gpr::Rbx,
        4 => Gpr::Rsp,
        5 => Gpr::Rbp,
        6 => Gpr::Rsi,
        7 => Gpr::Rdi,
        8 => Gpr::R8,
        9 => Gpr::R9,
        10 => Gpr::R10,
        11 => Gpr::R11,
        12 => Gpr::R12,
        13 => Gpr::R13,
        14 => Gpr::R14,
        15 => Gpr::R15,
        _ => unreachable!("invalid PReg encoding: {}", p.0),
    }
}

/// Insert prologue and epilogue around a post-regalloc instruction sequence.
///
/// `isel_frame_size`: stack space from StackSlot ops (from isel).
/// `spill_slots`: additional spill slots from regalloc.
/// `has_calls`: whether the function contains call instructions.
/// `callee_saved`: callee-saved registers that must be preserved.
pub fn insert_prologue_epilogue(
    body: Vec<PInst>,
    isel_frame_size: i32,
    spill_slots: u32,
    has_calls: bool,
    callee_saved: &[PReg],
) -> Vec<PInst> {
    let total_frame = isel_frame_size + (spill_slots as i32) * 8;
    let needs_frame = total_frame > 0 || has_calls || !callee_saved.is_empty();

    if !needs_frame {
        return body;
    }

    let aligned = (total_frame + 15) & !15;
    let mut out = Vec::with_capacity(body.len() + 6 + callee_saved.len() * 2);

    // Prologue: push rbp, set up frame, allocate stack, save callee-saved regs.
    out.push(MInst::Push { reg: Gpr::Rbp });
    out.push(MInst::MovRR {
        size: OpSize::S64,
        dst: Gpr::Rbp,
        src: Gpr::Rsp,
    });
    out.push(MInst::SubSPI { imm: aligned });
    for &p in callee_saved {
        out.push(MInst::Push {
            reg: preg_to_gpr(p),
        });
    }

    for inst in body {
        if matches!(inst, MInst::Ret) {
            // Epilogue: restore callee-saved regs, tear down frame.
            for &p in callee_saved.iter().rev() {
                out.push(MInst::Pop {
                    reg: preg_to_gpr(p),
                });
            }
            out.push(MInst::AddSPI { imm: aligned });
            out.push(MInst::Pop { reg: Gpr::Rbp });
        }
        out.push(inst);
    }

    out
}
