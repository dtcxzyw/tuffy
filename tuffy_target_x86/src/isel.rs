//! Instruction selection: lower tuffy IR to x86-64 machine instructions.
//!
//! Emits `MInst<VReg>` (virtual register instructions). The register allocator
//! later rewrites these to `MInst<Gpr>` (physical register instructions).

use std::collections::HashMap;

use crate::inst::{CondCode, MInst, OpSize, VInst};
use crate::reg::Gpr;
use num_traits::ToPrimitive;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::Annotation;
use tuffy_ir::value::ValueRef;
use tuffy_regalloc::{PReg, VReg};

/// Result of instruction selection for a single function.
pub struct IselResult {
    pub name: String,
    pub insts: Vec<VInst>,
    /// Number of virtual registers allocated.
    pub vreg_count: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    /// None means the allocator is free to choose.
    pub constraints: Vec<Option<PReg>>,
    /// Stack frame size from StackSlot operations only (not spills).
    pub isel_frame_size: i32,
    /// Whether the function contains any call instructions.
    pub has_calls: bool,
}

/// Map from IR value to virtual register.
struct VRegMap {
    /// Instruction result values.
    map: Vec<Option<VReg>>,
    /// Block argument values (separate namespace).
    block_arg_map: Vec<Option<VReg>>,
}

impl VRegMap {
    fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            map: vec![None; inst_capacity],
            block_arg_map: vec![None; block_arg_capacity],
        }
    }

    fn assign(&mut self, val: ValueRef, vreg: VReg) {
        if val.is_block_arg() {
            self.block_arg_map[val.index() as usize] = Some(vreg);
        } else {
            self.map[val.index() as usize] = Some(vreg);
        }
    }

    fn get(&self, val: ValueRef) -> Option<VReg> {
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

/// Sequential virtual register allocator.
struct VRegAlloc {
    next: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    constraints: Vec<Option<PReg>>,
}

impl VRegAlloc {
    fn new() -> Self {
        Self {
            next: 0,
            constraints: Vec::new(),
        }
    }

    /// Allocate a fresh virtual register with no constraint.
    fn alloc(&mut self) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(None);
        vreg
    }

    /// Allocate a fresh virtual register constrained to a physical register.
    fn alloc_fixed(&mut self, preg: PReg) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(Some(preg));
        vreg
    }
}

/// Mutable instruction selection state, bundled to reduce parameter counts.
struct IselCtx {
    regs: VRegMap,
    cmps: CmpMap,
    stack: StackMap,
    alloc: VRegAlloc,
    next_label: u32,
    out: Vec<VInst>,
}

impl IselCtx {
    /// Materialize a value into a virtual register.
    ///
    /// If the value is already in VRegMap, returns its vreg.
    /// If the value is a StackSlot (in StackMap), emits LEA to compute
    /// the address (rbp+offset) into a fresh vreg.
    fn ensure_in_reg(&mut self, val: ValueRef) -> Option<VReg> {
        if let Some(vreg) = self.regs.get(val) {
            return Some(vreg);
        }
        if let Some(offset) = self.stack.get(val) {
            let rbp = self.alloc.alloc_fixed(Gpr::Rbp.to_preg());
            let dst = self.alloc.alloc();
            self.out.push(MInst::Lea {
                dst,
                base: rbp,
                offset,
            });
            return Some(dst);
        }
        None
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

/// Perform instruction selection on a tuffy IR function.
///
/// Emits `MInst<VReg>` with constraint metadata. Prologue/epilogue
/// insertion is deferred to a post-regalloc step.
///
/// Returns None if the function contains unsupported IR ops.
pub fn isel(
    func: &Function,
    symbols: &SymbolTable,
    rdx_captures: &HashMap<u32, ()>,
    rdx_moves: &HashMap<u32, u32>,
) -> Option<IselResult> {
    let ba_cap = func.block_args.len();
    let mut ctx = IselCtx {
        regs: VRegMap::new(func.instructions.len(), ba_cap),
        cmps: CmpMap::new(func.instructions.len()),
        stack: StackMap::new(func.instructions.len(), ba_cap),
        alloc: VRegAlloc::new(),
        next_label: func.blocks.len() as u32,
        out: Vec::new(),
    };

    let root = &func.regions[func.root_region.index() as usize];
    for child in &root.children {
        if let CfgNode::Block(block_ref) = child {
            ctx.out.push(MInst::Label {
                id: block_ref.index(),
            });
            for (vref, inst) in func.block_insts_with_values(*block_ref) {
                select_inst(
                    &mut ctx,
                    vref,
                    &inst.op,
                    func,
                    symbols,
                    rdx_captures,
                    rdx_moves,
                )?;
            }
        }
    }

    let has_calls = ctx.out.iter().any(|i| matches!(i, MInst::CallSym { .. }));

    Some(IselResult {
        name: symbols.resolve(func.name).to_string(),
        insts: ctx.out,
        vreg_count: ctx.alloc.next,
        constraints: ctx.alloc.constraints,
        isel_frame_size: ctx.stack.frame_size,
        has_calls,
    })
}

fn select_inst(
    ctx: &mut IselCtx,
    vref: ValueRef,
    op: &Op,
    func: &Function,
    symbols: &SymbolTable,
    rdx_captures: &HashMap<u32, ()>,
    rdx_moves: &HashMap<u32, u32>,
) -> Option<()> {
    match op {
        Op::Param(idx) => {
            let arg_gpr = ARG_REGS.get(*idx as usize)?;
            let vreg = ctx.alloc.alloc_fixed(arg_gpr.to_preg());
            ctx.regs.assign(vref, vreg);
        }

        Op::Const(imm) => {
            if rdx_captures.contains_key(&vref.index()) {
                let vreg = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
                ctx.regs.assign(vref, vreg);
            } else if let Some(src_idx) = rdx_moves.get(&vref.index()) {
                let src_vref = ValueRef::inst_result(*src_idx);
                let src_vreg = ctx.regs.get(src_vref)?;
                let dst = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: src_vreg,
                });
                ctx.regs.assign(vref, dst);
            } else {
                let imm_i64 = imm.to_i64()?;
                let dst = ctx.alloc.alloc();
                if imm_i64 >= 0 && imm_i64 <= u32::MAX as i64 {
                    ctx.out.push(MInst::MovRI {
                        size: OpSize::S32,
                        dst,
                        imm: imm_i64,
                    });
                } else {
                    ctx.out.push(MInst::MovRI64 { dst, imm: imm_i64 });
                }
                ctx.regs.assign(vref, dst);
            }
        }

        Op::Add(lhs, rhs) => {
            select_binop_rr(ctx, vref, lhs.value, rhs.value, BinOp::Add)?;
        }

        Op::Sub(lhs, rhs) => {
            select_binop_rr(ctx, vref, lhs.value, rhs.value, BinOp::Sub)?;
        }

        Op::Mul(lhs, rhs) => {
            select_binop_rr(ctx, vref, lhs.value, rhs.value, BinOp::Mul)?;
        }

        Op::ICmp(cmp_op, lhs, rhs) => {
            let lhs_vreg = ctx.ensure_in_reg(lhs.value)?;
            let rhs_vreg = ctx.ensure_in_reg(rhs.value)?;
            ctx.out.push(MInst::CmpRR {
                size: OpSize::S64,
                src1: lhs_vreg,
                src2: rhs_vreg,
            });
            let cc = icmp_to_cc(*cmp_op, lhs.annotation);
            ctx.cmps.set(vref, cc);
        }

        Op::Br(target, args) => {
            let ba_vrefs = func.block_arg_values(*target);
            for (arg, ba_vref) in args.iter().zip(ba_vrefs.iter()) {
                let src = ctx.ensure_in_reg(arg.value)?;
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src,
                });
                ctx.regs.assign(*ba_vref, dst);
            }
            ctx.out.push(MInst::Jmp {
                target: target.index(),
            });
        }

        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            select_brif(
                ctx, cond, then_block, then_args, else_block, else_args, func,
            )?;
        }

        Op::Ret(val, _mem) => {
            if let Some(v) = val {
                let src = ctx.ensure_in_reg(v.value)?;
                let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: rax,
                    src,
                });
            }
            ctx.out.push(MInst::Ret);
        }

        Op::Call(callee, args, _mem) => {
            select_call(ctx, vref, callee, args, func, symbols)?;
        }

        Op::StackSlot(bytes) => {
            let _offset = ctx.stack.alloc(vref, *bytes);
        }

        Op::Load(ptr, bytes, _mem) => {
            let dst = ctx.alloc.alloc();
            let size = bytes_to_opsize(*bytes);
            if let Some(offset) = ctx.stack.get(ptr.value) {
                let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                ctx.out.push(MInst::MovRM {
                    size,
                    dst,
                    base: rbp,
                    offset,
                });
            } else {
                let ptr_vreg = ctx.regs.get(ptr.value)?;
                ctx.out.push(MInst::MovRM {
                    size,
                    dst,
                    base: ptr_vreg,
                    offset: 0,
                });
            }
            ctx.regs.assign(vref, dst);
        }

        Op::Store(val, ptr, bytes, _mem) => {
            let val_vreg = ctx.ensure_in_reg(val.value)?;
            let size = bytes_to_opsize(*bytes);
            if let Some(offset) = ctx.stack.get(ptr.value) {
                let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                ctx.out.push(MInst::MovMR {
                    size,
                    base: rbp,
                    offset,
                    src: val_vreg,
                });
            } else {
                let ptr_vreg = ctx.ensure_in_reg(ptr.value)?;
                ctx.out.push(MInst::MovMR {
                    size,
                    base: ptr_vreg,
                    offset: 0,
                    src: val_vreg,
                });
            }
        }

        Op::Or(lhs, rhs) => {
            select_bitop_rr(ctx, vref, lhs.value, rhs.value, BitOp::Or)?;
        }
        Op::And(lhs, rhs) => {
            select_bitop_rr(ctx, vref, lhs.value, rhs.value, BitOp::And)?;
        }
        Op::Xor(lhs, rhs) => {
            select_bitop_rr(ctx, vref, lhs.value, rhs.value, BitOp::Xor)?;
        }

        Op::Shl(lhs, rhs) => {
            select_shift_cl(ctx, vref, lhs.value, rhs.value, ShiftOp::Shl)?;
        }
        Op::Shr(lhs, rhs) => {
            let shift_op = match lhs.annotation {
                Some(Annotation::Signed(_)) => ShiftOp::Sar,
                _ => ShiftOp::Shr,
            };
            select_shift_cl(ctx, vref, lhs.value, rhs.value, shift_op)?;
        }

        Op::PtrAdd(ptr, offset) => {
            let ptr_vreg = ctx.ensure_in_reg(ptr.value)?;
            let off_vreg = ctx.ensure_in_reg(offset.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: ptr_vreg,
            });
            ctx.out.push(MInst::AddRR {
                size: OpSize::S64,
                dst,
                src: off_vreg,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::Unreachable | Op::Trap => {
            ctx.out.push(MInst::Ud2);
        }

        Op::Select(cond, tv, fv) => {
            select_select(ctx, vref, cond, tv, fv)?;
        }

        Op::Min(lhs, rhs) => {
            select_minmax(ctx, vref, lhs, rhs, MinMaxKind::Min)?;
        }
        Op::Max(lhs, rhs) => {
            select_minmax(ctx, vref, lhs, rhs, MinMaxKind::Max)?;
        }

        Op::CountOnes(val) => {
            let src = ctx.ensure_in_reg(val.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::Popcnt { dst, src });
            ctx.regs.assign(vref, dst);
        }

        Op::BoolToInt(val) => {
            if let Some(cc) = ctx.cmps.get(val.value) {
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::SetCC { cc, dst });
                ctx.out.push(MInst::MovzxB { dst, src: dst });
                ctx.regs.assign(vref, dst);
            } else {
                let src = ctx.regs.get(val.value)?;
                ctx.regs.assign(vref, src);
            }
        }

        Op::Bitcast(val) | Op::PtrToInt(val) | Op::PtrToAddr(val) | Op::IntToPtr(val) => {
            let src = ctx.ensure_in_reg(val.value)?;
            ctx.regs.assign(vref, src);
        }

        Op::PtrDiff(lhs, rhs) => {
            select_binop_rr(ctx, vref, lhs.value, rhs.value, BinOp::Sub)?;
        }

        Op::Sext(val, _target_bits) => {
            select_sext(ctx, vref, val)?;
        }

        Op::Zext(val, _target_bits) => {
            select_zext(ctx, vref, val)?;
        }

        Op::Div(lhs, rhs) => {
            select_divrem(ctx, vref, lhs, rhs, DivRemKind::Div)?;
        }
        Op::Rem(lhs, rhs) => {
            select_divrem(ctx, vref, lhs, rhs, DivRemKind::Rem)?;
        }

        Op::FAdd(..) | Op::FSub(..) | Op::FMul(..) | Op::FDiv(..) => return None,
        Op::FNeg(_) | Op::FAbs(_) | Op::CopySign(..) => return None,
        Op::LoadAtomic(..) | Op::StoreAtomic(..) => return None,
        Op::AtomicRmw(..) | Op::AtomicCmpXchg(..) => return None,

        Op::SymbolAddr(sym_id) => {
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::LeaSymbol {
                dst,
                symbol: symbols.resolve(*sym_id).to_string(),
            });
            ctx.regs.assign(vref, dst);
        }

        Op::Fence(..) | Op::Continue(_) | Op::RegionYield(_) => return None,
    }
    Some(())
}

// --- Helper functions ---

/// Helper enum for binary ALU operations.
enum BinOp {
    Add,
    Sub,
    Mul,
}

fn select_binop_rr(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BinOp,
) -> Option<()> {
    let lhs_vreg = ctx.ensure_in_reg(lhs)?;
    let rhs_vreg = ctx.ensure_in_reg(rhs)?;
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: lhs_vreg,
    });
    let inst = match op {
        BinOp::Add => MInst::AddRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
        BinOp::Sub => MInst::SubRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
        BinOp::Mul => MInst::ImulRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
    };
    ctx.out.push(inst);
    ctx.regs.assign(vref, dst);
    Some(())
}

/// Helper enum for shift operations.
enum ShiftOp {
    Shl,
    Shr,
    Sar,
}

fn select_shift_cl(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: ShiftOp,
) -> Option<()> {
    let lhs_vreg = ctx.ensure_in_reg(lhs)?;
    let rhs_vreg = ctx.ensure_in_reg(rhs)?;
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: lhs_vreg,
    });
    // Move shift amount into a CL-constrained vreg.
    let rcx = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst: rcx,
        src: rhs_vreg,
    });
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
    ctx.out.push(inst);
    ctx.regs.assign(vref, dst);
    Some(())
}
/// Helper enum for bitwise operations (OR, AND, XOR).
enum BitOp {
    Or,
    And,
    Xor,
}

fn select_bitop_rr(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: ValueRef,
    rhs: ValueRef,
    op: BitOp,
) -> Option<()> {
    let lhs_vreg = ctx.ensure_in_reg(lhs)?;
    let rhs_vreg = ctx.ensure_in_reg(rhs)?;
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: lhs_vreg,
    });
    let inst = match op {
        BitOp::Or => MInst::OrRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
        BitOp::And => MInst::AndRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
        BitOp::Xor => MInst::XorRR {
            size: OpSize::S64,
            dst,
            src: rhs_vreg,
        },
    };
    ctx.out.push(inst);
    ctx.regs.assign(vref, dst);
    Some(())
}

fn select_brif(
    ctx: &mut IselCtx,
    cond: &Operand,
    then_block: &tuffy_ir::value::BlockRef,
    then_args: &[Operand],
    else_block: &tuffy_ir::value::BlockRef,
    else_args: &[Operand],
    func: &Function,
) -> Option<()> {
    let has_args = !then_args.is_empty() || !else_args.is_empty();

    if has_args {
        let intermediate = ctx.next_label;
        ctx.next_label += 1;

        if let Some(cc) = ctx.cmps.get(cond.value) {
            ctx.out.push(MInst::Jcc {
                cc,
                target: intermediate,
            });
        } else {
            let cond_vreg = ctx.regs.get(cond.value)?;
            ctx.out.push(MInst::TestRR {
                size: OpSize::S64,
                src1: cond_vreg,
                src2: cond_vreg,
            });
            ctx.out.push(MInst::Jcc {
                cc: CondCode::Ne,
                target: intermediate,
            });
        }

        // Else path.
        let else_ba_vrefs = func.block_arg_values(*else_block);
        for (arg, ba_vref) in else_args.iter().zip(else_ba_vrefs.iter()) {
            let src = ctx.ensure_in_reg(arg.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.regs.assign(*ba_vref, dst);
        }
        ctx.out.push(MInst::Jmp {
            target: else_block.index(),
        });

        // Then path.
        ctx.out.push(MInst::Label { id: intermediate });
        let then_ba_vrefs = func.block_arg_values(*then_block);
        for (arg, ba_vref) in then_args.iter().zip(then_ba_vrefs.iter()) {
            let src = ctx.ensure_in_reg(arg.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.regs.assign(*ba_vref, dst);
        }
        ctx.out.push(MInst::Jmp {
            target: then_block.index(),
        });
    } else {
        if let Some(cc) = ctx.cmps.get(cond.value) {
            ctx.out.push(MInst::Jcc {
                cc,
                target: then_block.index(),
            });
        } else {
            let cond_vreg = ctx.regs.get(cond.value)?;
            ctx.out.push(MInst::TestRR {
                size: OpSize::S64,
                src1: cond_vreg,
                src2: cond_vreg,
            });
            ctx.out.push(MInst::Jcc {
                cc: CondCode::Ne,
                target: then_block.index(),
            });
        }
        ctx.out.push(MInst::Jmp {
            target: else_block.index(),
        });
    }
    Some(())
}

fn select_call(
    ctx: &mut IselCtx,
    vref: ValueRef,
    callee: &Operand,
    args: &[Operand],
    func: &Function,
    symbols: &SymbolTable,
) -> Option<()> {
    for (i, arg) in args.iter().enumerate() {
        if i >= ARG_REGS.len() {
            return None;
        }
        let src = ctx.ensure_in_reg(arg.value)?;
        let dst = ctx.alloc.alloc_fixed(ARG_REGS[i].to_preg());
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src,
        });
    }

    let callee_idx = callee.value.index();
    if let Op::SymbolAddr(sym_id) = &func.inst(callee_idx).op {
        let name = symbols.resolve(*sym_id).to_string();
        ctx.out.push(MInst::CallSym { name });
    } else {
        ctx.out.push(MInst::Ud2);
    }

    let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
    ctx.regs.assign(vref, rax);
    Some(())
}

fn select_select(
    ctx: &mut IselCtx,
    vref: ValueRef,
    cond: &Operand,
    tv: &Operand,
    fv: &Operand,
) -> Option<()> {
    let tv_vreg = ctx.ensure_in_reg(tv.value)?;
    let fv_vreg = ctx.ensure_in_reg(fv.value)?;
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: fv_vreg,
    });
    if let Some(cc) = ctx.cmps.get(cond.value) {
        ctx.out.push(MInst::CMOVcc {
            size: OpSize::S64,
            cc,
            dst,
            src: tv_vreg,
        });
    } else {
        let cond_vreg = ctx.regs.get(cond.value)?;
        ctx.out.push(MInst::TestRR {
            size: OpSize::S64,
            src1: cond_vreg,
            src2: cond_vreg,
        });
        ctx.out.push(MInst::CMOVcc {
            size: OpSize::S64,
            cc: CondCode::Ne,
            dst,
            src: tv_vreg,
        });
    }
    ctx.regs.assign(vref, dst);
    Some(())
}

/// Whether we want min or max.
enum MinMaxKind {
    Min,
    Max,
}

fn select_minmax(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: &Operand,
    rhs: &Operand,
    kind: MinMaxKind,
) -> Option<()> {
    let lhs_vreg = ctx.ensure_in_reg(lhs.value)?;
    let rhs_vreg = ctx.ensure_in_reg(rhs.value)?;
    let dst = ctx.alloc.alloc();
    // Start with rhs in dst; conditionally move lhs if it's the winner.
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: rhs_vreg,
    });
    ctx.out.push(MInst::CmpRR {
        size: OpSize::S64,
        src1: lhs_vreg,
        src2: rhs_vreg,
    });
    let signed = matches!(lhs.annotation, Some(Annotation::Signed(_)));
    let cc = match kind {
        // Min: pick lhs if lhs < rhs
        MinMaxKind::Min => {
            if signed {
                CondCode::L
            } else {
                CondCode::B
            }
        }
        // Max: pick lhs if lhs > rhs
        MinMaxKind::Max => {
            if signed {
                CondCode::G
            } else {
                CondCode::A
            }
        }
    };
    ctx.out.push(MInst::CMOVcc {
        size: OpSize::S64,
        cc,
        dst,
        src: lhs_vreg,
    });
    ctx.regs.assign(vref, dst);
    Some(())
}

fn select_sext(ctx: &mut IselCtx, vref: ValueRef, val: &Operand) -> Option<()> {
    let src = ctx.ensure_in_reg(val.value)?;
    let dst = ctx.alloc.alloc();
    match val.annotation {
        Some(Annotation::Signed(8)) | Some(Annotation::Unsigned(8)) => {
            ctx.out.push(MInst::MovsxB { dst, src });
        }
        Some(Annotation::Signed(16)) | Some(Annotation::Unsigned(16)) => {
            ctx.out.push(MInst::MovsxW { dst, src });
        }
        Some(Annotation::Signed(32)) | Some(Annotation::Unsigned(32)) => {
            ctx.out.push(MInst::MovsxD { dst, src });
        }
        Some(Annotation::Signed(_)) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
        }
        Some(Annotation::Unsigned(n)) => {
            let shift = 64 - n;
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst,
                imm: shift as u8,
            });
            ctx.out.push(MInst::SarImm {
                size: OpSize::S64,
                dst,
                imm: shift as u8,
            });
        }
        _ => {
            ctx.out.push(MInst::MovsxD { dst, src });
        }
    }
    ctx.regs.assign(vref, dst);
    Some(())
}

fn select_zext(ctx: &mut IselCtx, vref: ValueRef, val: &Operand) -> Option<()> {
    let src = ctx.ensure_in_reg(val.value)?;
    let dst = ctx.alloc.alloc();
    match val.annotation {
        Some(Annotation::Signed(8)) | Some(Annotation::Unsigned(8)) => {
            ctx.out.push(MInst::MovzxB { dst, src });
        }
        Some(Annotation::Signed(16)) | Some(Annotation::Unsigned(16)) => {
            ctx.out.push(MInst::MovzxW { dst, src });
        }
        Some(Annotation::Signed(32)) | Some(Annotation::Unsigned(32)) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S32,
                dst,
                src,
            });
        }
        Some(Annotation::Unsigned(_)) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
        }
        Some(Annotation::Signed(n)) => {
            let mask = (1i64 << n) - 1;
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.out.push(MInst::AndRI {
                size: OpSize::S64,
                dst,
                imm: mask,
            });
        }
        _ => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S32,
                dst,
                src,
            });
        }
    }
    ctx.regs.assign(vref, dst);
    Some(())
}

/// Whether we want the quotient or remainder from division.
enum DivRemKind {
    Div,
    Rem,
}

fn select_divrem(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: &Operand,
    rhs: &Operand,
    kind: DivRemKind,
) -> Option<()> {
    let lhs_vreg = ctx.ensure_in_reg(lhs.value)?;
    let rhs_vreg = ctx.ensure_in_reg(rhs.value)?;
    let signed = matches!(lhs.annotation, Some(Annotation::Signed(_)));

    // Move divisor to an unconstrained vreg to avoid RAX/RDX conflicts.
    let divisor = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst: divisor,
        src: rhs_vreg,
    });

    // Move dividend into RAX-constrained vreg.
    let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst: rax,
        src: lhs_vreg,
    });

    if signed {
        ctx.out.push(MInst::Cqo);
        ctx.out.push(MInst::Idiv {
            size: OpSize::S64,
            src: divisor,
        });
    } else {
        // Zero RDX for unsigned division.
        let rdx_zero = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
        ctx.out.push(MInst::XorRR {
            size: OpSize::S32,
            dst: rdx_zero,
            src: rdx_zero,
        });
        ctx.out.push(MInst::Div {
            size: OpSize::S64,
            src: divisor,
        });
    }

    // Quotient in RAX, remainder in RDX.
    let result = match kind {
        DivRemKind::Div => ctx.alloc.alloc_fixed(Gpr::Rax.to_preg()),
        DivRemKind::Rem => ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg()),
    };
    ctx.regs.assign(vref, result);
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
