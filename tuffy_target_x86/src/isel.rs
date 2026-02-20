//! Instruction selection: lower tuffy IR to x86-64 machine instructions.
//!
//! Emits `MInst<VReg>` (virtual register instructions). The register allocator
//! later rewrites these to `MInst<Gpr>` (physical register instructions).

#[path = "isel_gen.rs"]
mod isel_gen;

use std::collections::{HashMap, HashSet};

use crate::inst::{CondCode, FpBinOpKind, MInst, OpSize, VInst};
use crate::reg::Gpr;
use num_traits::ToPrimitive;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::ValueRef;
use tuffy_regalloc::VReg;
use tuffy_target::isel::{CmpMap, IselResult, StackMap, VRegAlloc, VRegMap};

/// Mutable instruction selection state, bundled to reduce parameter counts.
struct IselCtx {
    regs: VRegMap,
    cmps: CmpMap<CondCode>,
    stack: StackMap,
    alloc: VRegAlloc,
    next_label: u32,
    out: Vec<VInst>,
    /// Deferred symbol addresses: value index → symbol name.
    /// `LeaSymbol` is only emitted when `ensure_in_reg` is called,
    /// avoiding dead code when the symbol is only used as a direct call callee.
    sym_addrs: HashMap<u32, String>,
    /// Captured RDX vregs from calls with secondary returns.
    /// Maps call instruction index → unconstrained vreg holding the RDX value.
    rdx_captured: HashMap<u32, VReg>,
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
        if let Some(symbol) = self.sym_addrs.get(&val.index()).cloned() {
            let dst = self.alloc.alloc();
            self.out.push(MInst::LeaSymbol { dst, symbol });
            self.regs.assign(val, dst);
            return Some(dst);
        }
        // Materialize a deferred icmp result into a register via SetCC + MovzxB.
        if let Some(cc) = self.cmps.get(val) {
            let tmp = self.alloc.alloc();
            self.out.push(MInst::SetCC { cc, dst: tmp });
            self.out.push(MInst::MovzxB { dst: tmp, src: tmp });
            self.regs.assign(val, tmp);
            return Some(tmp);
        }
        None
    }
}

/// Convert a byte count to an x86 operand size.
fn bytes_to_opsize(bytes: u32) -> OpSize {
    match bytes {
        1 => OpSize::S8,
        2 => OpSize::S16,
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
    rdx_captures: &HashMap<u32, u32>,
    rdx_moves: &HashMap<u32, u32>,
    call_has_ret2: &HashSet<u32>,
) -> Option<IselResult<VInst>> {
    let ba_cap = func.block_args.len();
    let mut ctx = IselCtx {
        regs: VRegMap::new(func.instructions.len(), ba_cap),
        cmps: CmpMap::new(func.instructions.len()),
        stack: StackMap::new(func.instructions.len(), ba_cap),
        alloc: VRegAlloc::new(),
        next_label: func.blocks.len() as u32,
        out: Vec::new(),
        sym_addrs: HashMap::new(),
        rdx_captured: HashMap::new(),
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
                    call_has_ret2,
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

#[allow(clippy::too_many_arguments)]
fn select_inst(
    ctx: &mut IselCtx,
    vref: ValueRef,
    op: &Op,
    func: &Function,
    symbols: &SymbolTable,
    rdx_captures: &HashMap<u32, u32>,
    rdx_moves: &HashMap<u32, u32>,
    call_has_ret2: &HashSet<u32>,
) -> Option<()> {
    // Try generated rules first (covers Add, Sub, Mul, Or, And, Xor,
    // Shl, Shr, Min, Max, CountOnes, CountLeadingZeros, CountTrailingZeros,
    // ICmp, PtrAdd, PtrDiff).
    if isel_gen::try_select_generated(ctx, vref, op).is_some() {
        return Some(());
    }
    match op {
        Op::Param(idx) => {
            if let Some(arg_gpr) = ARG_REGS.get(*idx as usize) {
                let fixed = ctx.alloc.alloc_fixed(arg_gpr.to_preg());
                // Immediately copy the argument register into a fresh unconstrained
                // vreg. This lets the register allocator assign it to a callee-saved
                // register when the value is live across calls (which clobber
                // caller-saved argument registers like rdi, rsi, etc.).
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: fixed,
                });
                ctx.regs.assign(vref, dst);
            } else {
                // Stack-passed argument (7th+).  After the prologue
                // (push rbp; mov rbp, rsp) the caller's stack args sit at
                // positive offsets from RBP:
                //   [rbp + 16] = arg idx=6, [rbp + 24] = arg idx=7, ...
                let stack_idx = *idx as i32 - ARG_REGS.len() as i32;
                let offset = 16 + stack_idx * 8;
                let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRM {
                    size: OpSize::S64,
                    dst,
                    base: rbp,
                    offset,
                });
                ctx.regs.assign(vref, dst);
            }
        }

        Op::Const(imm) => {
            if let Some(call_idx) = rdx_captures.get(&vref.index()) {
                // Look up the RDX vreg captured at the call site.
                let captured = ctx
                    .rdx_captured
                    .get(call_idx)
                    .copied()
                    .expect("rdx_captured must be set for call with secondary return");
                ctx.regs.assign(vref, captured);
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
                let imm_i64 = imm.to_i64().or_else(|| imm.to_u64().map(|v| v as i64))?;
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

        Op::BConst(val) => {
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst,
                imm: if *val { 1 } else { 0 },
            });
            ctx.regs.assign(vref, dst);
        }

        Op::Br(target, args) => {
            let ba_vrefs = func.block_arg_values(*target);
            for (arg, ba_vref) in args.iter().zip(ba_vrefs.iter()) {
                // Skip mem-typed block arguments — they have no runtime register.
                if func.value_type(*ba_vref) == Some(&Type::Mem) {
                    continue;
                }
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
            select_call(ctx, vref, callee, args, func, symbols, call_has_ret2)?;
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
                let ptr_vreg = ctx.ensure_in_reg(ptr.value)?;
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

        Op::Unreachable | Op::Trap => {
            ctx.out.push(MInst::Ud2);
        }

        Op::Select(cond, tv, fv) => {
            select_select(ctx, vref, cond, tv, fv)?;
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

        Op::IntToBool(val) => {
            // Int to Bool: test the integer and store the condition code.
            // If the value is already in a register, TEST it against itself;
            // downstream BrIf/Select will consume the condition code directly.
            let src = ctx.ensure_in_reg(val.value)?;
            ctx.out.push(MInst::TestRR {
                size: OpSize::S64,
                src1: src,
                src2: src,
            });
            ctx.cmps.set(vref, CondCode::Ne);
            // Also materialize into a register for non-flag consumers.
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::SetCC {
                cc: CondCode::Ne,
                dst,
            });
            ctx.out.push(MInst::MovzxB { dst, src: dst });
            ctx.regs.assign(vref, dst);
        }

        Op::Bitcast(val) | Op::PtrToInt(val) | Op::PtrToAddr(val) | Op::IntToPtr(val) => {
            let src = ctx.ensure_in_reg(val.value)?;
            ctx.regs.assign(vref, src);
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

        Op::FAdd(lhs, rhs, _) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Add,
                dst,
                lhs: l,
                rhs: r,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FSub(lhs, rhs, _) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Sub,
                dst,
                lhs: l,
                rhs: r,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FMul(lhs, rhs, _) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Mul,
                dst,
                lhs: l,
                rhs: r,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FDiv(lhs, rhs, _) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Div,
                dst,
                lhs: l,
                rhs: r,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FNeg(_) | Op::FAbs(_) | Op::CopySign(..) => return None,
        Op::LoadAtomic(..) | Op::StoreAtomic(..) => return None,
        Op::AtomicRmw(..) | Op::AtomicCmpXchg(..) => return None,

        Op::SymbolAddr(sym_id) => {
            // Defer LeaSymbol emission — only emit when ensure_in_reg is called.
            // This avoids dead code when the symbol is only used as a direct call callee
            // (select_call emits CallSym directly without needing the address in a register).
            ctx.sym_addrs
                .insert(vref.index(), symbols.resolve(*sym_id).to_string());
        }

        Op::Fence(..) | Op::Continue(_) | Op::RegionYield(_) => return None,

        // Ops handled by isel_gen::try_select_generated above.
        _ => return None,
    }
    Some(())
}

// --- Helper functions ---

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
            if func.value_type(*ba_vref) == Some(&Type::Mem) {
                continue;
            }
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
            if func.value_type(*ba_vref) == Some(&Type::Mem) {
                continue;
            }
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
    call_has_ret2: &HashSet<u32>,
) -> Option<()> {
    // Phase 1: materialize all args into unconstrained vregs.
    // This must happen before any fixed-register moves, otherwise
    // ensure_in_reg may emit LEA/MOV instructions whose destinations
    // get allocated to argument registers (e.g. rdx), clobbering
    // values already placed there by earlier fixed-register moves.
    let mut arg_vregs = Vec::new();
    for arg in args.iter() {
        let src = ctx.ensure_in_reg(arg.value)?;
        arg_vregs.push(src);
    }

    // Phase 2: push stack arguments (args beyond the 6 register slots).
    // System V AMD64 ABI: args 7+ go on the stack, pushed right-to-left.
    // RSP must be 16-byte aligned before the call instruction.
    let num_stack_args = arg_vregs.len().saturating_sub(ARG_REGS.len());
    let stack_cleanup = if num_stack_args > 0 {
        // Pad for 16-byte alignment if odd number of stack args.
        let padding = if num_stack_args % 2 != 0 { 8 } else { 0 };
        if padding > 0 {
            ctx.out.push(MInst::SubSPI { imm: padding });
        }
        // Push in reverse order so arg[6] ends up at lowest address (top of stack).
        for i in (ARG_REGS.len()..arg_vregs.len()).rev() {
            ctx.out.push(MInst::Push { reg: arg_vregs[i] });
        }
        (num_stack_args as i32 * 8) + padding
    } else {
        0
    };

    // Phase 3: move register arguments to fixed argument registers.
    // If the source vreg is already constrained to the target register,
    // skip the redundant MovRR to avoid register allocator conflicts
    // (e.g. param1 fixed to rsi being evicted when a new rsi vreg is created).
    let reg_arg_count = arg_vregs.len().min(ARG_REGS.len());
    for i in 0..reg_arg_count {
        let src = arg_vregs[i];
        let target_preg = ARG_REGS[i].to_preg();
        let already_there = ctx.alloc.constraints.get(src.0 as usize) == Some(&Some(target_preg));
        if already_there {
            continue;
        }
        let dst = ctx.alloc.alloc_fixed(target_preg);
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src,
        });
    }

    // The primary result of a call is the mem token (no register needed).
    // If the call returns a value, it's the secondary result — assign rax to it.
    // We emit an explicit MovRR from the rax-fixed vreg to an unconstrained
    // vreg so the return value doesn't conflict with other rax-constrained
    // vregs (e.g. the Ret handler also allocates a fixed rax vreg).
    let inst = func.inst(vref.index());
    let ret_vreg = if inst.secondary_ty.is_some() {
        let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
        Some(rax)
    } else {
        None
    };

    // If this call has a secondary return (RDX), allocate a fixed RDX vreg.
    let has_ret2 = call_has_ret2.contains(&vref.index());
    let ret2_vreg = if has_ret2 {
        let rdx = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
        Some(rdx)
    } else {
        None
    };

    let callee_idx = callee.value.index();
    if let Op::SymbolAddr(sym_id) = &func.inst(callee_idx).op {
        let name = symbols.resolve(*sym_id).to_string();
        ctx.out.push(MInst::CallSym {
            name,
            ret: ret_vreg,
            ret2: ret2_vreg,
        });
    } else {
        // Indirect call through a register (e.g. virtual dispatch).
        let callee_vreg = ctx.ensure_in_reg(callee.value)?;
        ctx.out.push(MInst::CallReg {
            callee: callee_vreg,
            ret: ret_vreg,
            ret2: ret2_vreg,
        });
    }

    // Copy the rax-fixed vreg into an unconstrained vreg for downstream use.
    if let Some(rax) = ret_vreg {
        let dst = ctx.alloc.alloc();
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: rax,
        });
        let secondary = ValueRef::inst_secondary_result(vref.index());
        ctx.regs.assign(secondary, dst);
    }

    // Copy the rdx-fixed vreg into an unconstrained vreg for downstream use.
    // The rdx_captures iconst handler will look this up later.
    if let Some(rdx) = ret2_vreg {
        let dst = ctx.alloc.alloc();
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: rdx,
        });
        ctx.rdx_captured.insert(vref.index(), dst);
    }

    // Clean up stack arguments after the call.
    if stack_cleanup > 0 {
        ctx.out.push(MInst::AddSPI { imm: stack_cleanup });
    }

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
    let rem = matches!(kind, DivRemKind::Rem);

    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::DivRem {
        dst,
        lhs: lhs_vreg,
        rhs: rhs_vreg,
        signed,
        rem,
    });
    ctx.regs.assign(vref, dst);
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
