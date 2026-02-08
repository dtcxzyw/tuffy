//! Instruction selection: lower tuffy IR to x86-64 machine instructions.

use tuffy_ir::function::Function;
use tuffy_ir::instruction::Op;
use tuffy_ir::value::ValueRef;
use tuffy_target_x86::inst::{MInst, OpSize};
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

/// System V AMD64 ABI: first 6 integer args in rdi, rsi, rdx, rcx, r8, r9.
const ARG_REGS: [Gpr; 2] = [Gpr::Rdi, Gpr::Rsi];

/// Perform instruction selection on a tuffy IR function.
///
/// Currently handles only the minimal subset needed for:
///   fn add(a: i32, b: i32) -> i32 { a + b }
pub fn isel(func: &Function) -> IselResult {
    let mut out = Vec::new();
    let mut regs = RegMap::new(func.instructions.len());

    let entry = func.entry_block();
    for (vref, inst) in func.block_insts_with_values(entry) {
        select_inst(vref, &inst.op, &mut regs, &mut out);
    }

    IselResult {
        name: func.name.clone(),
        insts: out,
    }
}

fn select_inst(vref: ValueRef, op: &Op, regs: &mut RegMap, out: &mut Vec<MInst>) {
    match op {
        Op::Param(idx) => {
            let arg_reg = ARG_REGS[*idx as usize];
            regs.assign(vref, arg_reg);
        }

        Op::AssertSext(src, _bits) => {
            regs.assign(vref, regs.get(*src));
        }

        Op::AssertZext(src, _bits) => {
            regs.assign(vref, regs.get(*src));
        }

        Op::Add(lhs, rhs) => {
            let lhs_reg = regs.get(*lhs);
            let rhs_reg = regs.get(*rhs);

            if lhs_reg != Gpr::Rax {
                out.push(MInst::MovRR {
                    size: OpSize::S32,
                    dst: Gpr::Rax,
                    src: lhs_reg,
                });
            }
            out.push(MInst::AddRR {
                size: OpSize::S32,
                dst: Gpr::Rax,
                src: rhs_reg,
            });
            regs.assign(vref, Gpr::Rax);
        }

        Op::Ret(val) => {
            if let Some(v) = val {
                let src = regs.get(*v);
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

        _ => panic!("unsupported IR op in isel: {:?}", op),
    }
}
