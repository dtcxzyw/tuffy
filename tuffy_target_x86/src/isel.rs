//! Instruction selection: lower tuffy IR to x86-64 machine instructions.

use std::collections::HashMap;

use crate::inst::{CondCode, MInst, OpSize};
use crate::reg::Gpr;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand};
use tuffy_ir::types::Annotation;
use tuffy_ir::value::ValueRef;

/// Result of instruction selection for a single function.
pub struct IselResult {
    pub name: String,
    pub insts: Vec<MInst>,
}

/// Map from IR value to physical register.
struct RegMap {
    /// Instruction result values.
    map: Vec<Option<Gpr>>,
    /// Block argument values (separate namespace).
    block_arg_map: Vec<Option<Gpr>>,
}

impl RegMap {
    fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            map: vec![None; inst_capacity],
            block_arg_map: vec![None; block_arg_capacity],
        }
    }

    fn assign(&mut self, val: ValueRef, reg: Gpr) {
        if val.is_block_arg() {
            self.block_arg_map[val.index() as usize] = Some(reg);
        } else {
            self.map[val.index() as usize] = Some(reg);
        }
    }

    fn get(&self, val: ValueRef) -> Option<Gpr> {
        if val.is_block_arg() {
            *self.block_arg_map.get(val.index() as usize)?
        } else {
            *self.map.get(val.index() as usize)?
        }
    }
}

/// Tracks stack slot allocations (offset from RBP).
struct StackMap {
    /// Maps IR value index → offset from RBP (negative).
    slots: Vec<Option<i32>>,
    /// Block argument stack slots (separate namespace).
    block_arg_slots: Vec<Option<i32>>,
    /// Current stack frame size (grows downward).
    frame_size: i32,
}

impl StackMap {
    fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            slots: vec![None; inst_capacity],
            block_arg_slots: vec![None; block_arg_capacity],
            frame_size: 0,
        }
    }

    fn alloc(&mut self, val: ValueRef, bytes: u32) -> i32 {
        self.frame_size += bytes as i32;
        // Align to natural alignment (at least 8 bytes for pointers).
        let align = std::cmp::max(bytes as i32, 8);
        self.frame_size = (self.frame_size + align - 1) & !(align - 1);
        let offset = -self.frame_size;
        if val.is_block_arg() {
            self.block_arg_slots[val.index() as usize] = Some(offset);
        } else {
            self.slots[val.index() as usize] = Some(offset);
        }
        offset
    }

    fn get(&self, val: ValueRef) -> Option<i32> {
        if val.is_block_arg() {
            *self.block_arg_slots.get(val.index() as usize)?
        } else {
            *self.slots.get(val.index() as usize)?
        }
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

/// Convert a byte count to an x86 operand size.
fn bytes_to_opsize(bytes: u32) -> OpSize {
    match bytes {
        4 => OpSize::S32,
        _ => OpSize::S64,
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
) -> Option<Gpr> {
    if let Some(reg) = regs.get(val) {
        return Some(reg);
    }
    if let Some(offset) = stack.get(val) {
        let dst = alloc.alloc();
        out.push(MInst::Lea {
            dst,
            base: Gpr::Rbp,
            offset,
        });
        return Some(dst);
    }
    None
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
    let ba_cap = func.block_args.len();
    let mut regs = RegMap::new(func.instructions.len(), ba_cap);
    let mut cmps = CmpMap::new(func.instructions.len());
    let mut stack = StackMap::new(func.instructions.len(), ba_cap);
    let mut alloc = RegAlloc::new();
    let mut next_label = func.blocks.len() as u32;

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
                    func,
                    &mut regs,
                    &mut cmps,
                    &mut stack,
                    &mut alloc,
                    &mut next_label,
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
    let has_calls = body.iter().any(|i| matches!(i, MInst::CallSym { .. }));
    let needs_frame = stack.frame_size > 0 || has_calls;

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
    func: &Function,
    regs: &mut RegMap,
    cmps: &mut CmpMap,
    stack: &mut StackMap,
    alloc: &mut RegAlloc,
    next_label: &mut u32,
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
                let src_reg = regs.get(src_vref)?;
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
            select_binop_rr(
                vref,
                lhs.value,
                rhs.value,
                BinOp::Add,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Sub(lhs, rhs) => {
            select_binop_rr(
                vref,
                lhs.value,
                rhs.value,
                BinOp::Sub,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Mul(lhs, rhs) => {
            select_binop_rr(
                vref,
                lhs.value,
                rhs.value,
                BinOp::Mul,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::ICmp(cmp_op, lhs, rhs) => {
            let lhs_reg = ensure_in_reg(lhs.value, regs, stack, alloc, out)?;
            let rhs_reg = ensure_in_reg(rhs.value, regs, stack, alloc, out)?;
            out.push(MInst::CmpRR {
                size: OpSize::S64,
                src1: lhs_reg,
                src2: rhs_reg,
            });
            let cc = icmp_to_cc(*cmp_op, lhs.annotation);
            cmps.set(vref, cc);
        }

        Op::Br(target, args) => {
            // Copy branch arguments to target block's block-arg registers.
            let ba_vrefs = func.block_arg_values(*target);
            for (arg, ba_vref) in args.iter().zip(ba_vrefs.iter()) {
                let src = ensure_in_reg(arg.value, regs, stack, alloc, out)?;
                let dst = alloc.alloc();
                if src != dst {
                    out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst,
                        src,
                    });
                }
                regs.assign(*ba_vref, dst);
            }
            out.push(MInst::Jmp {
                target: target.index(),
            });
        }

        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            let has_args = !then_args.is_empty() || !else_args.is_empty();

            if has_args {
                // Need intermediate label so we can copy different args
                // for each branch target.
                //   Jcc intermediate_then
                //   <copy else_args>
                //   Jmp else_block
                // intermediate_then:
                //   <copy then_args>
                //   Jmp then_block
                let intermediate = *next_label;
                *next_label += 1;

                if let Some(cc) = cmps.get(cond.value) {
                    out.push(MInst::Jcc {
                        cc,
                        target: intermediate,
                    });
                } else {
                    let cond_reg = regs.get(cond.value)?;
                    out.push(MInst::TestRR {
                        size: OpSize::S64,
                        src1: cond_reg,
                        src2: cond_reg,
                    });
                    out.push(MInst::Jcc {
                        cc: CondCode::Ne,
                        target: intermediate,
                    });
                }

                // Else path: copy else_args, jump to else_block.
                let else_ba_vrefs = func.block_arg_values(*else_block);
                for (arg, ba_vref) in else_args.iter().zip(else_ba_vrefs.iter()) {
                    let src = ensure_in_reg(arg.value, regs, stack, alloc, out)?;
                    let dst = alloc.alloc();
                    if src != dst {
                        out.push(MInst::MovRR {
                            size: OpSize::S64,
                            dst,
                            src,
                        });
                    }
                    regs.assign(*ba_vref, dst);
                }
                out.push(MInst::Jmp {
                    target: else_block.index(),
                });

                // Then path: intermediate label, copy then_args, jump.
                out.push(MInst::Label { id: intermediate });
                let then_ba_vrefs = func.block_arg_values(*then_block);
                for (arg, ba_vref) in then_args.iter().zip(then_ba_vrefs.iter()) {
                    let src = ensure_in_reg(arg.value, regs, stack, alloc, out)?;
                    let dst = alloc.alloc();
                    if src != dst {
                        out.push(MInst::MovRR {
                            size: OpSize::S64,
                            dst,
                            src,
                        });
                    }
                    regs.assign(*ba_vref, dst);
                }
                out.push(MInst::Jmp {
                    target: then_block.index(),
                });
            } else {
                // No block args — simple Jcc + Jmp.
                if let Some(cc) = cmps.get(cond.value) {
                    out.push(MInst::Jcc {
                        cc,
                        target: then_block.index(),
                    });
                } else {
                    let cond_reg = regs.get(cond.value)?;
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
        }

        Op::Ret(val) => {
            if let Some(v) = val {
                let src = ensure_in_reg(v.value, regs, stack, alloc, out)?;
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
                    return None;
                }
                let src = ensure_in_reg(arg.value, regs, stack, alloc, out)?;
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
            if let Some(sym) = call_targets.get(&vref.index()) {
                out.push(MInst::CallSym { name: sym.clone() });
            } else {
                // Unresolvable call (e.g., indirect or failed symbol resolution).
                // Emit ud2 instead of dropping the entire function, which would
                // cascade into undefined symbols for all callers.
                out.push(MInst::Ud2);
            }

            // Result is in rax per System V ABI.
            regs.assign(vref, Gpr::Rax);
        }

        Op::StackSlot(bytes) => {
            let _offset = stack.alloc(vref, *bytes);
            // The value of a StackSlot is the address (pointer).
            // We use LEA to compute rbp+offset when needed.
            // For now, just record it in the stack map; Load/Store will use it.
        }

        Op::Load(ptr, bytes) => {
            let dst = alloc.alloc();
            let size = bytes_to_opsize(*bytes);
            // If the pointer comes from a StackSlot, load from [rbp+offset].
            if let Some(offset) = stack.get(ptr.value) {
                out.push(MInst::MovRM {
                    size,
                    dst,
                    base: Gpr::Rbp,
                    offset,
                });
            } else {
                let ptr_reg = regs.get(ptr.value)?;
                out.push(MInst::MovRM {
                    size,
                    dst,
                    base: ptr_reg,
                    offset: 0,
                });
            }
            regs.assign(vref, dst);
        }

        Op::Store(val, ptr, bytes) => {
            let val_reg = ensure_in_reg(val.value, regs, stack, alloc, out)?;
            let size = bytes_to_opsize(*bytes);
            if let Some(offset) = stack.get(ptr.value) {
                out.push(MInst::MovMR {
                    size,
                    base: Gpr::Rbp,
                    offset,
                    src: val_reg,
                });
            } else {
                let ptr_reg = ensure_in_reg(ptr.value, regs, stack, alloc, out)?;
                out.push(MInst::MovMR {
                    size,
                    base: ptr_reg,
                    offset: 0,
                    src: val_reg,
                });
            }
        }

        Op::Or(lhs, rhs) => {
            select_bitop_rr(
                vref,
                lhs.value,
                rhs.value,
                BitOp::Or,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::And(lhs, rhs) => {
            select_bitop_rr(
                vref,
                lhs.value,
                rhs.value,
                BitOp::And,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Xor(lhs, rhs) => {
            select_bitop_rr(
                vref,
                lhs.value,
                rhs.value,
                BitOp::Xor,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Shl(lhs, rhs) => {
            select_shift_cl(
                vref,
                lhs.value,
                rhs.value,
                ShiftOp::Shl,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Shr(lhs, rhs) => {
            let shift_op = match lhs.annotation {
                Some(Annotation::Signed(_)) => ShiftOp::Sar,
                _ => ShiftOp::Shr,
            };
            select_shift_cl(
                vref, lhs.value, rhs.value, shift_op, regs, stack, alloc, out,
            )?;
        }

        Op::PtrAdd(ptr, offset) => {
            let ptr_reg = ensure_in_reg(ptr.value, regs, stack, alloc, out)?;
            let off_reg = ensure_in_reg(offset.value, regs, stack, alloc, out)?;
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

        Op::Unreachable | Op::Trap => {
            out.push(MInst::Ud2);
        }

        Op::Select(cond, tv, fv) => {
            let tv_reg = ensure_in_reg(tv.value, regs, stack, alloc, out)?;
            let fv_reg = ensure_in_reg(fv.value, regs, stack, alloc, out)?;
            let dst = alloc.alloc();
            // Start with false_val in dst.
            if fv_reg != dst {
                out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: fv_reg,
                });
            }
            if let Some(cc) = cmps.get(cond.value) {
                // Condition from ICmp: CMOVcc dst, tv_reg.
                out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc,
                    dst,
                    src: tv_reg,
                });
            } else {
                // General bool value: TEST + CMOVne.
                let cond_reg = regs.get(cond.value)?;
                out.push(MInst::TestRR {
                    size: OpSize::S64,
                    src1: cond_reg,
                    src2: cond_reg,
                });
                out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::Ne,
                    dst,
                    src: tv_reg,
                });
            }
            regs.assign(vref, dst);
        }

        Op::CountOnes(val) => {
            let src = ensure_in_reg(val.value, regs, stack, alloc, out)?;
            let dst = alloc.alloc();
            out.push(MInst::Popcnt { dst, src });
            regs.assign(vref, dst);
        }

        Op::BoolToInt(val) => {
            if let Some(cc) = cmps.get(val.value) {
                // Condition from ICmp: SETcc + MOVZX.
                let dst = alloc.alloc();
                out.push(MInst::SetCC { cc, dst });
                out.push(MInst::MovzxB { dst, src: dst });
                regs.assign(vref, dst);
            } else {
                // General bool value: just propagate the register
                // (already 0 or 1 from a previous bool_to_int or icmp chain).
                let src = regs.get(val.value)?;
                regs.assign(vref, src);
            }
        }

        Op::Bitcast(val) | Op::PtrToInt(val) | Op::PtrToAddr(val) | Op::IntToPtr(val) => {
            let src = ensure_in_reg(val.value, regs, stack, alloc, out)?;
            regs.assign(vref, src);
        }

        Op::PtrDiff(lhs, rhs) => {
            select_binop_rr(
                vref,
                lhs.value,
                rhs.value,
                BinOp::Sub,
                regs,
                stack,
                alloc,
                out,
            )?;
        }

        Op::Sext(val, _target_bits) => {
            let src = ensure_in_reg(val.value, regs, stack, alloc, out)?;
            let dst = alloc.alloc();
            match val.annotation {
                Some(Annotation::Signed(8)) | Some(Annotation::Unsigned(8)) => {
                    out.push(MInst::MovsxB { dst, src });
                }
                Some(Annotation::Signed(16)) | Some(Annotation::Unsigned(16)) => {
                    out.push(MInst::MovsxW { dst, src });
                }
                Some(Annotation::Signed(32)) | Some(Annotation::Unsigned(32)) => {
                    out.push(MInst::MovsxD { dst, src });
                }
                _ => {
                    // Default: assume 32-bit source.
                    out.push(MInst::MovsxD { dst, src });
                }
            }
            regs.assign(vref, dst);
        }

        Op::Zext(val, _target_bits) => {
            let src = ensure_in_reg(val.value, regs, stack, alloc, out)?;
            let dst = alloc.alloc();
            match val.annotation {
                Some(Annotation::Signed(8)) | Some(Annotation::Unsigned(8)) => {
                    out.push(MInst::MovzxB { dst, src });
                }
                Some(Annotation::Signed(16)) | Some(Annotation::Unsigned(16)) => {
                    out.push(MInst::MovzxW { dst, src });
                }
                _ => {
                    // 32→64 zero-extend: mov r32 implicitly zero-extends.
                    out.push(MInst::MovRR {
                        size: OpSize::S32,
                        dst,
                        src,
                    });
                }
            }
            regs.assign(vref, dst);
        }

        Op::Div(lhs, rhs) => {
            select_divrem(vref, lhs, rhs, DivRemKind::Div, regs, stack, alloc, out)?;
        }

        Op::Rem(lhs, rhs) => {
            select_divrem(vref, lhs, rhs, DivRemKind::Rem, regs, stack, alloc, out)?;
        }
        Op::FAdd(..) => return None,
        Op::FSub(..) => return None,
        Op::FMul(..) => return None,
        Op::FDiv(..) => return None,
        Op::FNeg(_) => return None,
        Op::FAbs(_) => return None,
        Op::CopySign(..) => return None,
        Op::LoadAtomic(..) => return None,
        Op::StoreAtomic(..) => return None,
        Op::AtomicRmw(..) => return None,
        Op::AtomicCmpXchg(..) => return None,
        Op::SymbolAddr(_) => return None,
        Op::Fence(_) => return None,
        Op::Continue(_) => return None,
        Op::RegionYield(_) => return None,
    }
    Some(())
}

/// Helper enum for binary ALU operations.
enum BinOp {
    Add,
    Sub,
    Mul,
}

#[allow(clippy::too_many_arguments)]
fn select_binop_rr(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BinOp,
    regs: &mut RegMap,
    stack: &StackMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) -> Option<()> {
    let lhs_reg = ensure_in_reg(lhs, regs, stack, alloc, out)?;
    let rhs_reg = ensure_in_reg(rhs, regs, stack, alloc, out)?;
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
    Some(())
}

/// Helper enum for bitwise operations (OR, AND, XOR).
enum BitOp {
    Or,
    And,
    Xor,
}

#[allow(clippy::too_many_arguments)]
fn select_bitop_rr(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BitOp,
    regs: &mut RegMap,
    stack: &StackMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) -> Option<()> {
    let lhs_reg = ensure_in_reg(lhs, regs, stack, alloc, out)?;
    let rhs_reg = ensure_in_reg(rhs, regs, stack, alloc, out)?;
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
    Some(())
}

/// Helper enum for shift operations.
enum ShiftOp {
    Shl,
    Shr,
    Sar,
}

#[allow(clippy::too_many_arguments)]
fn select_shift_cl(
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: ShiftOp,
    regs: &mut RegMap,
    stack: &StackMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) -> Option<()> {
    let lhs_reg = ensure_in_reg(lhs, regs, stack, alloc, out)?;
    let rhs_reg = ensure_in_reg(rhs, regs, stack, alloc, out)?;
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
    Some(())
}

/// Whether we want the quotient or remainder from division.
enum DivRemKind {
    Div,
    Rem,
}

#[allow(clippy::too_many_arguments)]
fn select_divrem(
    vref: ValueRef,
    lhs: &Operand,
    rhs: &Operand,
    kind: DivRemKind,
    regs: &mut RegMap,
    stack: &StackMap,
    alloc: &mut RegAlloc,
    out: &mut Vec<MInst>,
) -> Option<()> {
    let lhs_reg = ensure_in_reg(lhs.value, regs, stack, alloc, out)?;
    let rhs_reg = ensure_in_reg(rhs.value, regs, stack, alloc, out)?;
    let signed = matches!(lhs.annotation, Some(Annotation::Signed(_)));

    // If rhs is in RAX or RDX, move it to a safe temp first since
    // DIV/IDIV clobber both RAX and RDX.
    let divisor = if rhs_reg == Gpr::Rax || rhs_reg == Gpr::Rdx {
        let tmp = alloc.alloc();
        // Make sure tmp isn't RAX or RDX either.
        let tmp = if tmp == Gpr::Rax || tmp == Gpr::Rdx {
            alloc.alloc()
        } else {
            tmp
        };
        let tmp = if tmp == Gpr::Rax || tmp == Gpr::Rdx {
            alloc.alloc()
        } else {
            tmp
        };
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst: tmp,
            src: rhs_reg,
        });
        tmp
    } else {
        rhs_reg
    };

    // Move dividend into RAX.
    if lhs_reg != Gpr::Rax {
        out.push(MInst::MovRR {
            size: OpSize::S64,
            dst: Gpr::Rax,
            src: lhs_reg,
        });
    }

    if signed {
        // CQO: sign-extend RAX into RDX:RAX.
        out.push(MInst::Cqo);
        out.push(MInst::Idiv {
            size: OpSize::S64,
            src: divisor,
        });
    } else {
        // Zero RDX for unsigned division.
        out.push(MInst::XorRR {
            size: OpSize::S32,
            dst: Gpr::Rdx,
            src: Gpr::Rdx,
        });
        out.push(MInst::Div {
            size: OpSize::S64,
            src: divisor,
        });
    }

    // Quotient in RAX, remainder in RDX.
    let result_reg = match kind {
        DivRemKind::Div => Gpr::Rax,
        DivRemKind::Rem => Gpr::Rdx,
    };
    regs.assign(vref, result_reg);
    Some(())
}

fn icmp_to_cc(op: ICmpOp, ann: Option<Annotation>) -> CondCode {
    let signed = matches!(ann, Some(Annotation::Signed(_)));
    match op {
        ICmpOp::Eq => CondCode::E,
        ICmpOp::Ne => CondCode::Ne,
        ICmpOp::Lt => {
            if signed {
                CondCode::L
            } else {
                CondCode::B
            }
        }
        ICmpOp::Le => {
            if signed {
                CondCode::Le
            } else {
                CondCode::Be
            }
        }
        ICmpOp::Gt => {
            if signed {
                CondCode::G
            } else {
                CondCode::A
            }
        }
        ICmpOp::Ge => {
            if signed {
                CondCode::Ge
            } else {
                CondCode::Ae
            }
        }
    }
}
