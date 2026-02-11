//! Stack frame setup: prologue/epilogue insertion (post-regalloc).

use crate::inst::{MInst, OpSize, PInst};
use crate::reg::Gpr;

/// Insert prologue and epilogue around a post-regalloc instruction sequence.
///
/// `isel_frame_size`: stack space from StackSlot ops (from isel).
/// `spill_slots`: additional spill slots from regalloc.
/// `has_calls`: whether the function contains call instructions.
pub fn insert_prologue_epilogue(
    body: Vec<PInst>,
    isel_frame_size: i32,
    spill_slots: u32,
    has_calls: bool,
) -> Vec<PInst> {
    let total_frame = isel_frame_size + (spill_slots as i32) * 8;
    let needs_frame = total_frame > 0 || has_calls;

    if !needs_frame {
        return body;
    }

    let aligned = (total_frame + 15) & !15;
    let mut out = Vec::with_capacity(body.len() + 6);

    out.push(MInst::Push { reg: Gpr::Rbp });
    out.push(MInst::MovRR {
        size: OpSize::S64,
        dst: Gpr::Rbp,
        src: Gpr::Rsp,
    });
    out.push(MInst::SubSPI { imm: aligned });

    for inst in body {
        if matches!(inst, MInst::Ret) {
            out.push(MInst::AddSPI { imm: aligned });
            out.push(MInst::Pop { reg: Gpr::Rbp });
        }
        out.push(inst);
    }

    out
}
