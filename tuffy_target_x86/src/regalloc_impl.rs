//! RegAllocInst implementation for MInst<VReg>.

use tuffy_regalloc::{OpKind, PReg, RegAllocInst, RegOp, VReg};

use crate::inst::{MInst, VInst};

/// Caller-saved registers clobbered by a call instruction.
const CALL_CLOBBERS: [PReg; 9] = [
    PReg(0),  // Rax
    PReg(1),  // Rcx
    PReg(2),  // Rdx
    PReg(6),  // Rsi
    PReg(7),  // Rdi
    PReg(8),  // R8
    PReg(9),  // R9
    PReg(10), // R10
    PReg(11), // R11
];

fn use_op(vreg: VReg) -> RegOp {
    RegOp {
        vreg,
        kind: OpKind::Use,
    }
}

fn def_op(vreg: VReg) -> RegOp {
    RegOp {
        vreg,
        kind: OpKind::Def,
    }
}

fn usedef_op(vreg: VReg) -> RegOp {
    RegOp {
        vreg,
        kind: OpKind::UseDef,
    }
}

impl RegAllocInst for VInst {
    fn reg_operands(&self, ops: &mut Vec<RegOp>) {
        match self {
            // dst = src
            MInst::MovRR { dst, src, .. } => {
                ops.push(def_op(*dst));
                ops.push(use_op(*src));
            }
            // dst = imm
            MInst::MovRI { dst, .. } | MInst::MovRI64 { dst, .. } => {
                ops.push(def_op(*dst));
            }
            // dst op= src (read-modify-write)
            MInst::AddRR { dst, src, .. }
            | MInst::SubRR { dst, src, .. }
            | MInst::ImulRR { dst, src, .. }
            | MInst::OrRR { dst, src, .. }
            | MInst::AndRR { dst, src, .. }
            | MInst::XorRR { dst, src, .. } => {
                ops.push(usedef_op(*dst));
                ops.push(use_op(*src));
            }
            // cmp/test: read-only
            MInst::CmpRR { src1, src2, .. } | MInst::TestRR { src1, src2, .. } => {
                ops.push(use_op(*src1));
                ops.push(use_op(*src2));
            }
            MInst::CmpRI { src, .. } => {
                ops.push(use_op(*src));
            }
            // shift by CL: dst is read-modify-write
            MInst::ShlRCL { dst, .. } | MInst::ShrRCL { dst, .. } | MInst::SarRCL { dst, .. } => {
                ops.push(usedef_op(*dst));
            }
            // shift by immediate
            MInst::ShlImm { dst, .. } | MInst::SarImm { dst, .. } => {
                ops.push(usedef_op(*dst));
            }
            // and dst, imm
            MInst::AndRI { dst, .. } => {
                ops.push(usedef_op(*dst));
            }
            // load: dst = [base+offset]
            MInst::MovRM { dst, base, .. } => {
                ops.push(def_op(*dst));
                ops.push(use_op(*base));
            }
            // store: [base+offset] = src
            MInst::MovMR { base, src, .. } => {
                ops.push(use_op(*base));
                ops.push(use_op(*src));
            }
            // store immediate: [base+offset] = imm
            MInst::MovMI { base, .. } => {
                ops.push(use_op(*base));
            }
            // lea dst, [base+offset]
            MInst::Lea { dst, base, .. } => {
                ops.push(def_op(*dst));
                ops.push(use_op(*base));
            }
            // lea dst, [rip+symbol]
            MInst::LeaSymbol { dst, .. } => {
                ops.push(def_op(*dst));
            }
            // cmovcc dst, src — dst is read if condition false
            MInst::CMOVcc { dst, src, .. } => {
                ops.push(usedef_op(*dst));
                ops.push(use_op(*src));
            }
            // setcc dst — writes low byte
            MInst::SetCC { dst, .. } => {
                ops.push(def_op(*dst));
            }
            // zero/sign extend: dst = extend(src)
            MInst::MovzxB { dst, src }
            | MInst::MovzxW { dst, src }
            | MInst::MovsxB { dst, src }
            | MInst::MovsxW { dst, src }
            | MInst::MovsxD { dst, src }
            | MInst::Popcnt { dst, src }
            | MInst::Lzcnt { dst, src }
            | MInst::Tzcnt { dst, src } => {
                ops.push(def_op(*dst));
                ops.push(use_op(*src));
            }
            // push/pop
            MInst::Push { reg } => {
                ops.push(use_op(*reg));
            }
            MInst::Pop { reg } => {
                ops.push(def_op(*reg));
            }
            // div/idiv: implicit RAX/RDX, explicit divisor
            MInst::Idiv { src, .. } | MInst::Div { src, .. } => {
                ops.push(use_op(*src));
            }
            // Indirect call: callee register is a use operand
            MInst::CallReg { callee } => {
                ops.push(use_op(*callee));
            }
            // No register operands
            MInst::Ret
            | MInst::Label { .. }
            | MInst::Jmp { .. }
            | MInst::Jcc { .. }
            | MInst::CallSym { .. }
            | MInst::SubSPI { .. }
            | MInst::AddSPI { .. }
            | MInst::Cqo
            | MInst::Ud2 => {}
        }
    }

    fn label_id(&self) -> Option<u32> {
        match self {
            MInst::Label { id } => Some(*id),
            _ => None,
        }
    }

    fn branch_targets(&self, targets: &mut Vec<u32>) {
        match self {
            MInst::Jmp { target } => targets.push(*target),
            MInst::Jcc { target, .. } => targets.push(*target),
            _ => {}
        }
    }

    fn clobbers(&self, clobbers: &mut Vec<PReg>) {
        if matches!(self, MInst::CallSym { .. } | MInst::CallReg { .. }) {
            clobbers.extend_from_slice(&CALL_CLOBBERS);
        }
    }

    fn is_terminator(&self) -> bool {
        matches!(
            self,
            MInst::Ret | MInst::Jmp { .. } | MInst::Jcc { .. } | MInst::Ud2
        )
    }

    fn falls_through(&self) -> bool {
        // Jcc falls through (conditional); Jmp/Ret/Ud2 do not.
        !matches!(self, MInst::Ret | MInst::Jmp { .. } | MInst::Ud2)
    }
}
