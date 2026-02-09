//! Instruction selection: lower tuffy IR to x86-64 machine instructions.

use std::collections::HashMap;

use crate::inst::{CondCode, MInst, OpSize};
use crate::reg::Gpr;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op};
use tuffy_ir::value::ValueRef;

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

/// Tracks stack slot allocations (offset from RBP).
struct StackMap {
    /// Maps IR value index → offset from RBP (negative).
    slots: Vec<Option<i32>>,
    /// Current stack frame size (grows downward).
    frame_size: i32,
}

impl StackMap {
    fn new(capacity: usize) -> Self {
        Self {
            slots: vec![None; capacity],
            frame_size: 0,
        }
    }

    fn alloc(&mut self, val: ValueRef, bytes: u32) -> i32 {
        self.frame_size += bytes as i32;
        // Align to natural alignment (at least 8 bytes for pointers).
        let align = std::cmp::max(bytes as i32, 8);
        self.frame_size = (self.frame_size + align - 1) & !(align - 1);
        let offset = -self.frame_size;
        self.slots[val.index() as usize] = Some(offset);
        offset
    }

    fn get(&self, val: ValueRef) -> Option<i32> {
        self.slots[val.index() as usize]
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

/// Pool of caller-saved registers for general allocation.
/// Excludes RSP and RBP (frame), and argument registers are included
/// but may be overwritten by calls.
const ALLOC_REGS: [Gpr; 9] = [
    Gpr::Rax,
    Gpr::Rcx,
    Gpr::Rdx,
    Gpr::R8,
    Gpr::R9,
    Gpr::R10,
    Gpr::R11,
    Gpr::Rsi,
    Gpr::Rdi,
];

/// Simple round-robin register allocator.
struct RegAlloc {
    next: usize,
}

impl RegAlloc {
    fn new() -> Self {
        Self { next: 0 }
    }

    fn alloc(&mut self) -> Gpr {
        let reg = ALLOC_REGS[self.next % ALLOC_REGS.len()];
        self.next += 1;
        reg
    }
}

/// Materialize a value into a physical register.
///
/// If the value is already in RegMap, returns its register.
/// If the value is a StackSlot (in StackMap), emits LEA to compute
/// the address (rbp+offset) into a fresh register.
fn ensure_in_reg(
    val: ValueRef,
    regs: &RegMap,
    stack: &StackMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) -> Gpr {
    if let Some(reg) = regs.map[val.index() as usize] {
        return reg;
    }
    if let Some(offset) = stack.get(val) {
        let dst = alloc.alloc();
        out.push(MInst::Lea {
            dst,
            base: Gpr::Rbp,
            offset,
        });
        return dst;
    }
    panic!("value not in reg or stack map");
}

/// Perform instruction selection on a tuffy IR function.
///
/// Iterates all basic blocks in the root region, emitting labels and
/// machine instructions for each block.
///
/// Returns None if the function contains unsupported IR ops.
pub fn isel(
    func: &Function,
    call_targets: &HashMap<u32, String>,
    static_refs: &HashMap<u32, String>,
    rdx_captures: &HashMap<u32, ()>,
    rdx_moves: &HashMap<u32, u32>,
) -> Option<IselResult> {
    let mut body = Vec::new();
    let mut regs = RegMap::new(func.instructions.len());
    let mut cmps = CmpMap::new(func.instructions.len());
    let mut stack = StackMap::new(func.instructions.len());
    let mut alloc = RegAlloc::new();

    let root = &func.regions[func.root_region.index() as usize];
    for child in &root.children {
        if let CfgNode::Block(block_ref) = child {
            body.push(MInst::Label {
                id: block_ref.index(),
            });
            for (vref, inst) in func.block_insts_with_values(*block_ref) {
                select_inst(
                    vref,
                    &inst.op,
                    &mut regs,
                    &mut cmps,
                    &mut stack,
                    &mut alloc,
                    call_targets,
                    static_refs,
                    rdx_captures,
                    rdx_moves,
                    &mut body,
                )?;
            }
        }
    }

    // Build final instruction sequence with prologue/epilogue.
    let mut out = Vec::new();
    let needs_frame = stack.frame_size > 0;

    if needs_frame {
        // Align frame size to 16 bytes (System V ABI requirement).
        let aligned = (stack.frame_size + 15) & !15;
        out.push(MInst::Push { reg: Gpr::Rbp });
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst: Gpr::Rbp,
            src: Gpr::Rsp,
        });
        out.push(MInst::SubSPI { imm: aligned });
    }

    // Insert body, replacing Ret with epilogue + ret.
    for inst in body {
        if matches!(inst, MInst::Ret) && needs_frame {
            let aligned = (stack.frame_size + 15) & !15;
            out.push(MInst::AddSPI { imm: aligned });
            out.push(MInst::Pop { reg: Gpr::Rbp });
        }
        out.push(inst);
    }

    Some(IselResult {
        name: func.name.clone(),
        insts: out,
    })
}

#[allow(clippy::too_many_arguments)]
fn select_inst(
    vref: ValueRef,
    op: &Op,
    regs: &mut RegMap,
    cmps: &mut CmpMap,
    stack: &mut StackMap,
    alloc: &mut RegAlloc,
    call_targets: &HashMap<u32, String>,
    static_refs: &HashMap<u32, String>,
    rdx_captures: &HashMap<u32, ()>,
    rdx_moves: &HashMap<u32, u32>,
    out: &mut Vec<MInst>,
) -> Option<()> {
    match op {
        Op::Param(idx) => {
            let arg_reg = ARG_REGS.get(*idx as usize)?;
            regs.assign(vref, *arg_reg);
        }

        Op::Const(imm) => {
            if rdx_captures.contains_key(&vref.index()) {
                // This value captures RDX from the preceding call.
                regs.assign(vref, Gpr::Rdx);
            } else if let Some(src_idx) = rdx_moves.get(&vref.index()) {
                // Move a value into RDX (for fat return components).
                let src_vref = ValueRef::inst_result(*src_idx);
                let src_reg = regs.get(src_vref);
                if src_reg != Gpr::Rdx {
                    out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: Gpr::Rdx,
                        src: src_reg,
                    });
                }
                regs.assign(vref, Gpr::Rdx);
            } else if let Some(sym) = static_refs.get(&vref.index()) {
                // Static data reference: emit LEA rip-relative.
                let dst = alloc.alloc();
                out.push(MInst::LeaSymbol {
                    dst,
                    symbol: sym.clone(),
                });
                regs.assign(vref, dst);
            } else {
                let dst = alloc.alloc();
                out.push(MInst::MovRI {
                    size: OpSize::S32,
                    dst,
                    imm: *imm,
                });
                regs.assign(vref, dst);
            }
        }

        Op::Add(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Add, regs, alloc, out);
        }

        Op::Sub(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Sub, regs, alloc, out);
        }

        Op::Mul(lhs, rhs) => {
            select_binop_rr(vref, lhs.value, rhs.value, BinOp::Mul, regs, alloc, out);
        }

        Op::ICmp(cmp_op, lhs, rhs) => {
            let lhs_reg = regs.get(lhs.value);
            let rhs_reg = regs.get(rhs.value);
            out.push(MInst::CmpRR {
                size: OpSize::S64,
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
                    size: OpSize::S64,
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
                let src = ensure_in_reg(v.value, regs, stack, alloc, out);
                if src != Gpr::Rax {
                    out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: Gpr::Rax,
                        src,
                    });
                }
            }
            out.push(MInst::Ret);
        }

        Op::Call(_callee, args) => {
            // Move arguments into System V ABI registers.
            for (i, arg) in args.iter().enumerate() {
                if i >= ARG_REGS.len() {
                    // Stack args not yet supported.
                    return None;
                }
                let src = ensure_in_reg(arg.value, regs, stack, alloc, out);
                let dst = ARG_REGS[i];
                if src != dst {
                    out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst,
                        src,
                    });
                }
            }

            // Look up the symbol name from call_targets.
            let sym = call_targets.get(&vref.index())?;
            out.push(MInst::CallSym { name: sym.clone() });

            // Result is in rax per System V ABI.
            regs.assign(vref, Gpr::Rax);
        }

        Op::StackSlot(bytes) => {
            let _offset = stack.alloc(vref, *bytes);
            // The value of a StackSlot is the address (pointer).
            // We use LEA to compute rbp+offset when needed.
            // For now, just record it in the stack map; Load/Store will use it.
        }

        Op::Load(ptr) => {
            let dst = alloc.alloc();
            // If the pointer comes from a StackSlot, load from [rbp+offset].
            if let Some(offset) = stack.get(ptr.value) {
                out.push(MInst::MovRM {
                    size: OpSize::S64,
                    dst,
                    base: Gpr::Rbp,
                    offset,
                });
            } else {
                let ptr_reg = regs.get(ptr.value);
                out.push(MInst::MovRM {
                    size: OpSize::S64,
                    dst,
                    base: ptr_reg,
                    offset: 0,
                });
            }
            regs.assign(vref, dst);
        }

        Op::Store(val, ptr) => {
            let val_reg = regs.get(val.value);
            if let Some(offset) = stack.get(ptr.value) {
                out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: Gpr::Rbp,
                    offset,
                    src: val_reg,
                });
            } else {
                let ptr_reg = regs.get(ptr.value);
                out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: ptr_reg,
                    offset: 0,
                    src: val_reg,
                });
            }
        }

        Op::Or(lhs, rhs) => {
            select_bitop_rr(vref, lhs.value, rhs.value, BitOp::Or, regs, alloc, out);
        }

        Op::And(lhs, rhs) => {
            select_bitop_rr(vref, lhs.value, rhs.value, BitOp::And, regs, alloc, out);
        }

        Op::Xor(lhs, rhs) => {
            select_bitop_rr(vref, lhs.value, rhs.value, BitOp::Xor, regs, alloc, out);
        }

        Op::Shl(lhs, rhs) => {
            select_shift_cl(vref, lhs.value, rhs.value, ShiftOp::Shl, regs, alloc, out);
        }

        Op::Lshr(lhs, rhs) => {
            select_shift_cl(vref, lhs.value, rhs.value, ShiftOp::Shr, regs, alloc, out);
        }

        Op::Ashr(lhs, rhs) => {
            select_shift_cl(vref, lhs.value, rhs.value, ShiftOp::Sar, regs, alloc, out);
        }

        Op::PtrAdd(ptr, offset) => {
            let ptr_reg = ensure_in_reg(ptr.value, regs, stack, alloc, out);
            let off_reg = ensure_in_reg(offset.value, regs, stack, alloc, out);
            let dst = alloc.alloc();
            if ptr_reg != dst {
                out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: ptr_reg,
                });
            }
            out.push(MInst::AddRR {
                size: OpSize::S64,
                dst,
                src: off_reg,
            });
            regs.assign(vref, dst);
        }

        Op::Unreachable => {
            out.push(MInst::Ud2);
        }

        // Ops not yet supported in isel
        Op::Bitcast(_)
        | Op::Sext(..)
        | Op::Zext(..)
        | Op::SDiv(..)
        | Op::UDiv(..)
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
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) {
    let lhs_reg = regs.get(lhs);
    let rhs_reg = regs.get(rhs);
    let dst = alloc.alloc();

    // Move lhs into dst.
    if lhs_reg != dst {
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: lhs_reg,
        });
    }
    let inst = match op {
        BinOp::Add => MInst::AddRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
        BinOp::Sub => MInst::SubRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
        BinOp::Mul => MInst::ImulRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
    };
    out.push(inst);
    regs.assign(vref, dst);
}

/// Helper enum for bitwise operations (OR, AND, XOR).
enum BitOp {
    Or,
    And,
    Xor,
}

fn select_bitop_rr(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BitOp,
    regs: &mut RegMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) {
    let lhs_reg = regs.get(lhs);
    let rhs_reg = regs.get(rhs);
    let dst = alloc.alloc();

    if lhs_reg != dst {
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: lhs_reg,
        });
    }
    let inst = match op {
        BitOp::Or => MInst::OrRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
        BitOp::And => MInst::AndRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
        BitOp::Xor => MInst::XorRR {
            size: OpSize::S64,
            dst,
            src: rhs_reg,
        },
    };
    out.push(inst);
    regs.assign(vref, dst);
}

/// Helper enum for shift operations.
enum ShiftOp {
    Shl,
    Shr,
    Sar,
}

fn select_shift_cl(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: ShiftOp,
    regs: &mut RegMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) {
    let lhs_reg = regs.get(lhs);
    let rhs_reg = regs.get(rhs);
    // Shift uses CL for shift amount, so dst must not be RCX.
    let mut dst = alloc.alloc();
    if dst == Gpr::Rcx {
        dst = alloc.alloc();
    }
    if lhs_reg != dst {
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: lhs_reg,
        });
    }
    if rhs_reg != Gpr::Rcx {
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst: Gpr::Rcx,
            src: rhs_reg,
        });
    }
    let inst = match op {
        ShiftOp::Shl => MInst::ShlRCL {
            size: OpSize::S64,
            dst,
        },
        ShiftOp::Shr => MInst::ShrRCL {
            size: OpSize::S64,
            dst,
        },
        ShiftOp::Sar => MInst::SarRCL {
            size: OpSize::S64,
            dst,
        },
    };
    out.push(inst);
    regs.assign(vref, dst);
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
