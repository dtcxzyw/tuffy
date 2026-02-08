//! Instruction selection: lower tuffy IR to x86-64 machine instructions.

use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op};
use tuffy_ir::value::ValueRef;
use tuffy_target_x86::inst::{CondCode, MInst, OpSize};
use tuffy_target_x86::reg::Gpr;

/// Result of instruction selection for a single function.
pub struct IselResult {
    pub name: String,
    pub insts: Vec<MInst>,
}

/// Map from IR value to physical register.
struct RegMap {
    map: Vec<Option<Gpr>>,
}

impl RegMap {
    fn new(capacity: usize) -> Self {
        Self {
            map: vec![None; capacity],
        }
    }

    fn assign(&mut self, val: ValueRef, reg: Gpr) {
        self.map[val.index() as usize] = Some(reg);
    }

    fn get(&self, val: ValueRef) -> Gpr {
        self.map[val.index() as usize].expect("register not assigned")
    }
}

/// Tracks ICmp results so BrIf can emit Jcc directly.
struct CmpMap {
    map: Vec<Option<CondCode>>,
}

impl CmpMap {
    fn new(capacity: usize) -> Self {
        Self {
            map: vec![None; capacity],
        }
    }

    fn set(&mut self, val: ValueRef, cc: CondCode) {
        self.map[val.index() as usize] = Some(cc);
    }

    fn get(&self, val: ValueRef) -> Option<CondCode> {
        self.map[val.index() as usize]
    }
}

/// System V AMD64 ABI: first 6 integer args in rdi, rsi, rdx, rcx, r8, r9.
const ARG_REGS: [Gpr; 6] = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx, Gpr::R8, Gpr::R9];

/// Perform instruction selection on a tuffy IR function.
///
/// Iterates all basic blocks in the root region, emitting labels and
/// machine instructions for each block.
///
/// Returns None if the function contains unsupported IR ops.
pub fn isel(func: &Function) -> Option<IselResult> {
    let mut out = Vec::new();
    let mut regs = RegMap::new(func.instructions.len());
    let mut cmps = CmpMap::new(func.instructions.len());

    let root = &func.regions[func.root_region.index() as usize];
    for child in &root.children {
        if let CfgNode::Block(block_ref) = child {
            out.push(MInst::Label {
                id: block_ref.index(),
            });
            for (vref, inst) in func.block_insts_with_values(*block_ref) {
                select_inst(vref, &inst.op, &mut regs, &mut cmps, &mut out)?;
            }
        }
    }

    Some(IselResult {
        name: func.name.clone(),
        insts: out,
    })
}

fn select_inst(
    vref: ValueRef,
    op: &Op,
    regs: &mut RegMap,
    cmps: &mut CmpMap,
    out: &mut Vec<MInst>,
) -> Option<()> {
    match op {
        Op::Param(idx) => {
            let arg_reg = ARG_REGS.get(*idx as usize)?;
            regs.assign(vref, *arg_reg);
        }

        Op::Const(imm) => {
            out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: Gpr::Rax,
                imm: *imm,
            });
            regs.assign(vref, Gpr::Rax);
        }

        Op::Add(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Add, regs, out);
        }

        Op::Sub(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Sub, regs, out);
        }

        Op::Mul(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Mul, regs, out);
        }

        Op::ICmp(cmp_op, lhs, rhs) => {
            let lhs_reg = regs.get(lhs.value);
            let rhs_reg = regs.get(rhs.value);
            out.push(MInst::CmpRR {
                size: OpSize::S32,
                src1: lhs_reg,
                src2: rhs_reg,
            });
            let cc = icmp_to_cc(*cmp_op);
            cmps.set(vref, cc);
        }

        Op::Br(target, _args) => {
            out.push(MInst::Jmp {
                target: target.index(),
            });
        }

        Op::BrIf(cond, then_block, _then_args, else_block, _else_args) => {
            if let Some(cc) = cmps.get(cond.value) {
                // Condition came from ICmp: use Jcc directly.
                out.push(MInst::Jcc {
                    cc,
                    target: then_block.index(),
                });
            } else {
                // Condition is a general value: test and branch if non-zero.
                let cond_reg = regs.get(cond.value);
                out.push(MInst::TestRR {
                    size: OpSize::S32,
                    src1: cond_reg,
                    src2: cond_reg,
                });
                out.push(MInst::Jcc {
                    cc: CondCode::Ne,
                    target: then_block.index(),
                });
            }
            out.push(MInst::Jmp {
                target: else_block.index(),
            });
        }

        Op::Ret(val) => {
            if let Some(v) = val {
                let src = regs.get(v.value);
                if src != Gpr::Rax {
                    out.push(MInst::MovRR {
                        size: OpSize::S32,
                        dst: Gpr::Rax,
                        src,
                    });
                }
            }
            out.push(MInst::Ret);
        }

        // Ops not yet supported in isel
        Op::Load(_)
        | Op::Store(..)
        | Op::StackSlot(_)
        | Op::Call(..)
        | Op::Bitcast(_)
        | Op::Sext(..)
        | Op::Zext(..)
        | Op::SDiv(..)
        | Op::UDiv(..)
        | Op::And(..)
        | Op::Or(..)
        | Op::Xor(..)
        | Op::Shl(..)
        | Op::Lshr(..)
        | Op::Ashr(..)
        | Op::PtrAdd(..)
        | Op::PtrDiff(..)
        | Op::PtrToInt(_)
        | Op::PtrToAddr(_)
        | Op::IntToPtr(_)
        | Op::FAdd(..)
        | Op::FSub(..)
        | Op::FMul(..)
        | Op::FDiv(..)
        | Op::FNeg(_)
        | Op::FAbs(_)
        | Op::CopySign(..)
        | Op::LoadAtomic(..)
        | Op::StoreAtomic(..)
        | Op::AtomicRmw(..)
        | Op::AtomicCmpXchg(..)
        | Op::Fence(_)
        | Op::Continue(_)
        | Op::RegionYield(_) => return None,
    }
    Some(())
}

/// Helper enum for binary ALU operations.
enum BinOp {
    Add,
    Sub,
    Mul,
}

fn select_binop_rr(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BinOp,
    regs: &mut RegMap,
    out: &mut Vec<MInst>,
) {
    let lhs_reg = regs.get(lhs);
    let rhs_reg = regs.get(rhs);

    if lhs_reg != Gpr::Rax {
        out.push(MInst::MovRR {
            size: OpSize::S32,
            dst: Gpr::Rax,
            src: lhs_reg,
        });
    }
    let inst = match op {
        BinOp::Add => MInst::AddRR {
            size: OpSize::S32,
            dst: Gpr::Rax,
            src: rhs_reg,
        },
        BinOp::Sub => MInst::SubRR {
            size: OpSize::S32,
            dst: Gpr::Rax,
            src: rhs_reg,
        },
        BinOp::Mul => MInst::ImulRR {
            size: OpSize::S32,
            dst: Gpr::Rax,
            src: rhs_reg,
        },
    };
    out.push(inst);
    regs.assign(vref, Gpr::Rax);
}

fn icmp_to_cc(op: ICmpOp) -> CondCode {
    match op {
        ICmpOp::Eq => CondCode::E,
        ICmpOp::Ne => CondCode::Ne,
        ICmpOp::Slt => CondCode::L,
        ICmpOp::Sle => CondCode::Le,
        ICmpOp::Sgt => CondCode::G,
        ICmpOp::Sge => CondCode::Ge,
        ICmpOp::Ult => CondCode::B,
        ICmpOp::Ule => CondCode::Be,
        ICmpOp::Ugt => CondCode::A,
        ICmpOp::Uge => CondCode::Ae,
    }
}
