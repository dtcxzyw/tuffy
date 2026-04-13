//! Instruction selection: lower tuffy IR to x86-64 machine instructions.
//!
//! Emits `MInst<VReg>` (virtual register instructions). The register allocator
//! later rewrites these to `MInst<Gpr>` (physical register instructions).

#[path = "isel_gen.rs"]
/// Generated instruction-selection rules for common patterns.
mod isel_gen;

use std::collections::{HashMap, HashSet};

use crate::inst::{AtomicRmwOpKind, CondCode, FpBinOpKind, MInst, OpSize, VInst};
use crate::reg::Gpr;
use num_traits::ToPrimitive;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;
use tuffy_regalloc::{PReg, VReg};
use tuffy_target::isel::{
    CmpMap, IselResult, SelectedValueLocations, StackMap, VRegAlloc, VRegMap,
};

/// Mutable instruction selection state, bundled to reduce parameter counts.
struct IselCtx {
    /// Value-to-register map for already selected values.
    regs: VRegMap,
    /// Deferred compare-flag results.
    cmps: CmpMap<CondCode>,
    /// Stack-slot allocations created during selection.
    stack: StackMap,
    /// Virtual-register allocator and fixed-register constraints.
    alloc: VRegAlloc,
    /// Next synthetic label id.
    next_label: u32,
    /// Output machine instructions collected so far.
    out: Vec<VInst>,
    /// Deferred symbol addresses: value index → symbol name.
    /// `LeaSymbol` is only emitted when `ensure_in_reg` is called,
    /// avoiding dead code when the symbol is only used as a direct call callee.
    sym_addrs: HashMap<u32, String>,
    /// Deferred TLS symbol addresses: value index → symbol name.
    tls_sym_addrs: HashMap<u32, String>,
    /// Deferred small integer constants: value index → immediate.
    int_consts: HashMap<u32, i64>,
    /// Deferred scaled ptradd offsets: value index → (index value, scale).
    scaled_ptradd_offsets: HashMap<u32, (ValueRef, u8)>,
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
        if let Some((offset, align)) = self.stack.get_with_align(val) {
            let rbp = self.alloc.alloc_fixed(Gpr::Rbp.to_preg());
            let dst = self.alloc.alloc();
            self.out.push(MInst::Lea {
                dst,
                base: rbp,
                offset,
            });
            // For alignment > 16 (exceeding ABI stack alignment), the
            // RBP-relative address is not guaranteed to be aligned because
            // RBP is only 16-aligned. Emit AND to dynamically align.
            if align > 16 {
                self.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst,
                    imm: -(align as i64),
                });
            }
            return Some(dst);
        }
        if let Some(symbol) = self.sym_addrs.get(&val.index()).cloned() {
            let dst = self.alloc.alloc();
            self.out.push(MInst::LeaSymbol { dst, symbol });
            // Do NOT cache in self.regs: symbol_addr values may be used
            // on divergent control-flow paths (e.g. main path AND cleanup
            // blocks). Caching would emit the LEA only at the first use
            // site, leaving the vreg uninitialised on other paths.
            // Re-materialising a LEA at each use is cheap and correct.
            return Some(dst);
        }
        if let Some(symbol) = self.tls_sym_addrs.get(&val.index()).cloned() {
            let dst = self.alloc.alloc();
            self.out.push(MInst::TlsLeaSymbol { dst, symbol });
            return Some(dst);
        }
        if let Some(imm) = self.int_consts.get(&val.index()).copied() {
            let dst = self.alloc.alloc();
            if imm >= 0 && imm <= u32::MAX as i64 {
                self.out.push(MInst::MovRI {
                    size: OpSize::S32,
                    dst,
                    imm,
                });
            } else {
                self.out.push(MInst::MovRI64 { dst, imm });
            }
            self.regs.assign(val, dst);
            return Some(dst);
        }
        // Materialize a deferred icmp result into a register via SetCC + MovzxB.
        // Use separate VRegs so that the spill slot for `dst` (the final result)
        // is only written after MovzxB — ensuring a clean 0/1 value on reload.
        if let Some(cc) = self.cmps.get(val) {
            let tmp_cc = self.alloc.alloc();
            let dst = self.alloc.alloc();
            self.out.push(MInst::SetCC { cc, dst: tmp_cc });
            self.out.push(MInst::MovzxB { dst, src: tmp_cc });
            self.regs.assign(val, dst);
            return Some(dst);
        }
        None
    }

    /// Look up or allocate the virtual register assigned to a block argument.
    fn block_arg_reg(&mut self, val: ValueRef) -> VReg {
        debug_assert!(val.is_block_arg());
        if let Some(vreg) = self.regs.get(val) {
            return vreg;
        }
        let vreg = self.alloc.alloc();
        self.regs.assign(val, vreg);
        vreg
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

/// Convert an integer annotation bit-width to an x86 operand size.
fn int_ann_to_opsize(annotation: IntAnnotation) -> OpSize {
    match annotation.bit_width {
        8 => OpSize::S8,
        16 => OpSize::S16,
        32 => OpSize::S32,
        _ => OpSize::S64,
    }
}

/// Emit parallel copies into the target block-argument registers.
fn emit_block_arg_copies(
    ctx: &mut IselCtx,
    target: tuffy_ir::value::BlockRef,
    args: &[Operand],
    func: &Function,
) -> Option<()> {
    let ba_vrefs = func.block_arg_values(target);
    let mut pending = Vec::new();

    for (arg, ba_vref) in args.iter().zip(ba_vrefs.iter()) {
        // Mem block args are SSA threading only and do not occupy machine regs.
        if func.value_type(*ba_vref) == Some(&Type::Mem) {
            continue;
        }
        let src = ctx.ensure_in_reg(arg.value)?;
        let dst = ctx.block_arg_reg(*ba_vref);
        let tmp = ctx.alloc.alloc();
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst: tmp,
            src,
        });
        pending.push((tmp, dst));
    }

    // Finish the edge as a parallel copy into the block-argument vregs.
    for (tmp, dst) in pending {
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src: tmp,
        });
    }

    Some(())
}

/// Emit a store of exactly `bytes` bytes from `src` to `base + offset`.
///
/// For non-power-of-2 sizes (3, 5, 6, 7), splits into standard-size stores to
/// avoid writing past the intended range (which would corrupt adjacent memory).
fn emit_partial_store(ctx: &mut IselCtx, base: VReg, base_offset: i32, src: VReg, bytes: u32) {
    match bytes {
        1 => ctx.out.push(MInst::MovMR {
            size: OpSize::S8,
            base,
            offset: base_offset,
            src,
        }),
        2 => ctx.out.push(MInst::MovMR {
            size: OpSize::S16,
            base,
            offset: base_offset,
            src,
        }),
        3 => {
            // 2-byte store (bits 0–15) + 1-byte store (bits 16–23).
            ctx.out.push(MInst::MovMR {
                size: OpSize::S16,
                base,
                offset: base_offset,
                src,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: tmp,
                src,
            });
            ctx.out.push(MInst::ShrImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 16,
            });
            ctx.out.push(MInst::MovMR {
                size: OpSize::S8,
                base,
                offset: base_offset + 2,
                src: tmp,
            });
        }
        4 => ctx.out.push(MInst::MovMR {
            size: OpSize::S32,
            base,
            offset: base_offset,
            src,
        }),
        5 => {
            ctx.out.push(MInst::MovMR {
                size: OpSize::S32,
                base,
                offset: base_offset,
                src,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: tmp,
                src,
            });
            ctx.out.push(MInst::ShrImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::MovMR {
                size: OpSize::S8,
                base,
                offset: base_offset + 4,
                src: tmp,
            });
        }
        6 => {
            ctx.out.push(MInst::MovMR {
                size: OpSize::S32,
                base,
                offset: base_offset,
                src,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: tmp,
                src,
            });
            ctx.out.push(MInst::ShrImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::MovMR {
                size: OpSize::S16,
                base,
                offset: base_offset + 4,
                src: tmp,
            });
        }
        7 => {
            ctx.out.push(MInst::MovMR {
                size: OpSize::S32,
                base,
                offset: base_offset,
                src,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: tmp,
                src,
            });
            ctx.out.push(MInst::ShrImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::MovMR {
                size: OpSize::S16,
                base,
                offset: base_offset + 4,
                src: tmp,
            });
            let tmp2 = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: tmp2,
                src,
            });
            ctx.out.push(MInst::ShrImm {
                size: OpSize::S64,
                dst: tmp2,
                imm: 48,
            });
            ctx.out.push(MInst::MovMR {
                size: OpSize::S8,
                base,
                offset: base_offset + 6,
                src: tmp2,
            });
        }
        _ => {
            // 8+ bytes: use the nearest opsize (handled by caller for wide stores).
            ctx.out.push(MInst::MovMR {
                size: bytes_to_opsize(bytes),
                base,
                offset: base_offset,
                src,
            });
        }
    }
}

/// Load exactly `bytes` bytes from `[base + base_offset]` into `dst`, zero-extending.
///
/// For non-power-of-2 sizes (3, 5, 6, 7), splits into standard-size loads and ORs them
/// together to avoid reading past the intended range (which would produce garbage).
fn emit_partial_load(ctx: &mut IselCtx, base: VReg, base_offset: i32, dst: VReg, bytes: u32) {
    match bytes {
        1 => ctx.out.push(MInst::MovRM {
            size: OpSize::S8,
            dst,
            base,
            offset: base_offset,
        }),
        2 => ctx.out.push(MInst::MovRM {
            size: OpSize::S16,
            dst,
            base,
            offset: base_offset,
        }),
        3 => {
            // 2-byte load (bits 0–15) + 1-byte load (bits 16–23), ORed together.
            ctx.out.push(MInst::MovRM {
                size: OpSize::S16,
                dst,
                base,
                offset: base_offset,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRM {
                size: OpSize::S8,
                dst: tmp,
                base,
                offset: base_offset + 2,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 16,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: tmp,
            });
        }
        4 => ctx.out.push(MInst::MovRM {
            size: OpSize::S32,
            dst,
            base,
            offset: base_offset,
        }),
        5 => {
            ctx.out.push(MInst::MovRM {
                size: OpSize::S32,
                dst,
                base,
                offset: base_offset,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRM {
                size: OpSize::S8,
                dst: tmp,
                base,
                offset: base_offset + 4,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: tmp,
            });
        }
        6 => {
            ctx.out.push(MInst::MovRM {
                size: OpSize::S32,
                dst,
                base,
                offset: base_offset,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRM {
                size: OpSize::S16,
                dst: tmp,
                base,
                offset: base_offset + 4,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: tmp,
            });
        }
        7 => {
            ctx.out.push(MInst::MovRM {
                size: OpSize::S32,
                dst,
                base,
                offset: base_offset,
            });
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRM {
                size: OpSize::S16,
                dst: tmp,
                base,
                offset: base_offset + 4,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst: tmp,
                imm: 32,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: tmp,
            });
            let tmp2 = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRM {
                size: OpSize::S8,
                dst: tmp2,
                base,
                offset: base_offset + 6,
            });
            ctx.out.push(MInst::ShlImm {
                size: OpSize::S64,
                dst: tmp2,
                imm: 48,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: tmp2,
            });
        }
        _ => {
            ctx.out.push(MInst::MovRM {
                size: bytes_to_opsize(bytes),
                dst,
                base,
                offset: base_offset,
            });
        }
    }
}

/// Resolve the direct-call symbol referenced by a callee value when possible.
fn direct_call_symbol(func: &Function, value: ValueRef) -> Option<tuffy_ir::module::SymbolId> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    match &func.inst(value.index()).op {
        Op::SymbolAddr(sym) => Some(*sym),
        _ => None,
    }
}

/// Extract IntAnnotation from a ValueRef's result_annotation.
pub(super) fn get_int_annotation(func: &Function, val: ValueRef) -> Option<IntAnnotation> {
    if val.is_block_arg() {
        None
    } else {
        let node = func.inst_pool.get(val.index())?;
        match &node.inst.result_annotation {
            Some(Annotation::Int(ann)) => Some(*ann),
            _ => None,
        }
    }
}

/// Get the upper 64-bit machine part of a wide integer value as a VReg.
///
/// First checks the secondary result register (set by previous wide-int ops).
/// If not available, derives the upper part from the low part using sign- or
/// zero-extension based on annotation.
fn ensure_hi_in_reg(
    ctx: &mut IselCtx,
    val: ValueRef,
    annotation: Option<IntAnnotation>,
) -> Option<VReg> {
    let secondary = ValueRef::inst_secondary_result(val.index());
    if let Some(vreg) = ctx.regs.get(secondary) {
        return Some(vreg);
    }
    // Derive hi from lo half.
    let lo = ctx.regs.get(val)?;
    let hi = ctx.alloc.alloc();
    match annotation {
        Some(IntAnnotation {
            signedness: IntSignedness::Signed,
            ..
        }) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: hi,
                src: lo,
            });
            ctx.out.push(MInst::SarImm {
                size: OpSize::S64,
                dst: hi,
                imm: 63,
            });
        }
        _ => {
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: hi,
                imm: 0,
            });
        }
    }
    Some(hi)
}

/// Handle exact double-width integer operations lowered into two GPR-sized halves.
///
/// Keeps lo half in the primary vreg and hi half in the secondary vreg.
/// Returns Some(()) if the operation was handled, None to fall through.
fn select_double_width_int_op(
    ctx: &mut IselCtx,
    vref: ValueRef,
    op: &Op,
    func: &Function,
) -> Option<()> {
    let _ann = func.inst(vref.index()).result_annotation.clone();
    match op {
        Op::Add(lhs, rhs)
        | Op::Sub(lhs, rhs)
        | Op::And(lhs, rhs)
        | Op::Or(lhs, rhs)
        | Op::Xor(lhs, rhs)
        | Op::Mul(lhs, rhs) => {
            let lo_l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let lo_r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let hi_l = ensure_hi_in_reg(
                ctx,
                lhs.clone().raw().value,
                get_int_annotation(func, lhs.clone().raw().value),
            )?;
            let hi_r = ensure_hi_in_reg(
                ctx,
                rhs.clone().raw().value,
                get_int_annotation(func, rhs.clone().raw().value),
            )?;

            let lo_result = ctx.alloc.alloc();
            let hi_result = ctx.alloc.alloc();

            match op {
                Op::Add(_, _) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::AddRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::AdcRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_r,
                    });
                }
                Op::Sub(_, _) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::SubRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::SbbRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_r,
                    });
                }
                Op::Xor(_, _) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::XorRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::XorRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_r,
                    });
                }
                Op::Or(_, _) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::OrRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::OrRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_r,
                    });
                }
                Op::And(_, _) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::AndRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::AndRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: hi_r,
                    });
                }
                Op::Mul(_, _) => {
                    // Double-width multiply: lo = lo_l * lo_r (mod 2^64)
                    // hi = lo_l*hi_r + hi_l*lo_r (partial; ignores carry from lo*lo)
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::ImulRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo_r,
                    });
                    let tmp1 = ctx.alloc.alloc();
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: tmp1,
                        src: lo_l,
                    });
                    ctx.out.push(MInst::ImulRR {
                        size: OpSize::S64,
                        dst: tmp1,
                        src: hi_r,
                    });
                    let tmp2 = ctx.alloc.alloc();
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: tmp2,
                        src: hi_l,
                    });
                    ctx.out.push(MInst::ImulRR {
                        size: OpSize::S64,
                        dst: tmp2,
                        src: lo_r,
                    });
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: tmp1,
                    });
                    ctx.out.push(MInst::AddRR {
                        size: OpSize::S64,
                        dst: hi_result,
                        src: tmp2,
                    });
                }
                _ => unreachable!(),
            }

            ctx.regs.assign(vref, lo_result);
            ctx.regs
                .assign(ValueRef::inst_secondary_result(vref.index()), hi_result);
            Some(())
        }

        Op::Sext(val, _) => {
            let lo = ctx.ensure_in_reg(val.clone().raw().value)?;
            let lo_result = ctx.alloc.alloc();
            // Sign-extend lo based on source bit-width.
            let src_ann = get_int_annotation(func, val.clone().raw().value);
            match src_ann.map(|a| a.bit_width) {
                Some(8) => {
                    ctx.out.push(MInst::MovsxB {
                        dst: lo_result,
                        src: lo,
                    });
                }
                Some(16) => {
                    ctx.out.push(MInst::MovsxW {
                        dst: lo_result,
                        src: lo,
                    });
                }
                Some(32) => {
                    ctx.out.push(MInst::MovsxD {
                        dst: lo_result,
                        src: lo,
                    });
                }
                _ => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo,
                    });
                }
            }
            // hi = sign extension of lo_result
            let hi_result = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: hi_result,
                src: lo_result,
            });
            ctx.out.push(MInst::SarImm {
                size: OpSize::S64,
                dst: hi_result,
                imm: 63,
            });
            ctx.regs.assign(vref, lo_result);
            ctx.regs
                .assign(ValueRef::inst_secondary_result(vref.index()), hi_result);
            Some(())
        }

        Op::Zext(val, _) => {
            let lo = ctx.ensure_in_reg(val.clone().raw().value)?;
            let lo_result = ctx.alloc.alloc();
            // Zero-extend lo based on source bit-width.
            let src_ann = get_int_annotation(func, val.clone().raw().value);
            match src_ann.map(|a| a.bit_width) {
                Some(8) => {
                    ctx.out.push(MInst::MovzxB {
                        dst: lo_result,
                        src: lo,
                    });
                }
                Some(16) => {
                    ctx.out.push(MInst::MovzxW {
                        dst: lo_result,
                        src: lo,
                    });
                }
                Some(32) => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S32,
                        dst: lo_result,
                        src: lo,
                    });
                }
                _ => {
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: lo_result,
                        src: lo,
                    });
                }
            }
            // hi = 0
            let hi_result = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: hi_result,
                imm: 0,
            });
            ctx.regs.assign(vref, lo_result);
            ctx.regs
                .assign(ValueRef::inst_secondary_result(vref.index()), hi_result);
            Some(())
        }

        _ => None,
    }
}

/// Integer argument registers used by the SysV x86-64 ABI.
const ARG_REGS: [Gpr; 6] = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx, Gpr::R8, Gpr::R9];
/// Maximum number of XMM argument registers used by the SysV x86-64 ABI.
const MAX_XMM_ARGS: usize = 8;
/// Bit width of one general-purpose register.
const GPR_BITS: u32 = 64;
/// Bit width covered by two general-purpose registers.
const DOUBLE_GPR_BITS: u32 = GPR_BITS * 2;

/// Return whether an annotation describes an exact two-register integer width.
fn is_exact_double_gpr_int_annotation(ann: Option<&Annotation>) -> bool {
    matches!(
        ann,
        Some(Annotation::Int(IntAnnotation { bit_width, .. })) if *bit_width == DOUBLE_GPR_BITS
    )
}

/// ABI location for a function parameter or call argument under SysV x86-64.
enum ParamAbi {
    /// Passed in the n-th integer register (rdi, rsi, rdx, rcx, r8, r9).
    Gpr(usize),
    /// Passed in the n-th XMM register (xmm0 .. xmm7); `double` = f64.
    Xmm {
        /// XMM argument register index.
        idx: usize,
        /// Whether the argument is carried as `f64`.
        double: bool,
    },
    /// Passed on the stack; `stack_idx` is 0-based (0 → [rbp+16]).
    Stack(i32),
}

/// Classify where parameter `param_idx` goes under SysV x86-64 ABI,
/// given the complete ordered parameter type list.
fn is_wide_scalar_type(ty: &Type, ann: &Option<Annotation>) -> bool {
    matches!(ty, Type::Int) && is_exact_double_gpr_int_annotation(ann.as_ref())
}

/// Classify one parameter under the SysV x86-64 ABI.
fn classify_param_abi(
    params: &[Type],
    param_annotations: &[Option<Annotation>],
    byval_sizes: &[Option<u32>],
    param_idx: usize,
) -> ParamAbi {
    let mut int_count = 0usize;
    let mut float_count = 0usize;
    let mut stack_idx: i32 = 0;
    for (i, param_ty) in params.iter().enumerate().take(param_idx) {
        // Byval params always go on the stack and consume ceil(size/8) slots.
        if let Some(sz) = byval_sizes.get(i).copied().flatten() {
            stack_idx += ((sz as i32) + 7) / 8;
            continue;
        }
        let param_ann = &param_annotations[i];
        let is_wide =
            !matches!(param_ty, Type::Float(_)) && is_wide_scalar_type(param_ty, param_ann);
        match param_ty {
            Type::Float(_) => {
                if float_count < MAX_XMM_ARGS {
                    float_count += 1;
                } else {
                    stack_idx += 1;
                }
            }
            _ => {
                // Wide scalars lowered to two machine parts use two consecutive GPR slots.
                let slots = if is_wide { 2 } else { 1 };
                if int_count + slots <= ARG_REGS.len() {
                    int_count += slots;
                } else {
                    stack_idx += slots as i32;
                }
            }
        }
    }
    // Byval params always go on the stack.
    if let Some(sz) = byval_sizes.get(param_idx).copied().flatten() {
        let _ = sz;
        return ParamAbi::Stack(stack_idx);
    }
    match &params[param_idx] {
        Type::Float(ft) => {
            if float_count < MAX_XMM_ARGS {
                ParamAbi::Xmm {
                    idx: float_count,
                    double: matches!(ft, FloatType::F64),
                }
            } else {
                ParamAbi::Stack(stack_idx)
            }
        }
        _ => {
            if int_count < ARG_REGS.len() {
                ParamAbi::Gpr(int_count)
            } else {
                ParamAbi::Stack(stack_idx)
            }
        }
    }
}

#[derive(Clone, Copy)]
/// Return-shape classification for one call instruction.
struct CallAbiPlan {
    /// Whether the call returns a primary data value in addition to memory.
    has_primary_return: bool,
    /// Whether the call returns a second data value.
    has_secondary_return: bool,
}

/// Collect call instructions whose secondary return is observed through `call_ret2`.
fn collect_call_ret2_users(func: &Function) -> HashSet<u32> {
    let mut calls = HashSet::new();
    for (_, inst) in func.inst_pool.iter_insts() {
        if let Op::CallRet2(mem) = &inst.op {
            calls.insert(mem.clone().raw().value.index());
        }
    }
    calls
}

/// Return whether an instruction produces an exact double-width integer result.
fn has_exact_double_gpr_int_result(func: &Function, inst_idx: u32) -> bool {
    let inst = func.inst(inst_idx);
    inst.secondary_ty.is_some()
        && is_exact_double_gpr_int_annotation(inst.secondary_result_annotation.as_ref())
}

/// Classify the return ABI for one call instruction.
fn classify_call_abi(
    func: &Function,
    call_vref: ValueRef,
    call_has_ret2: &HashSet<u32>,
) -> CallAbiPlan {
    let call_idx = call_vref.index();
    let inst = func.inst(call_idx);
    let exact_double = has_exact_double_gpr_int_result(func, call_idx);
    CallAbiPlan {
        // In tuffy IR, call data is encoded in the call's secondary result.
        has_primary_return: inst.secondary_ty.is_some(),
        has_secondary_return: call_has_ret2.contains(&call_idx) || exact_double,
    }
}

/// Perform instruction selection on a tuffy IR function.
///
/// Emits `MInst<VReg>` with constraint metadata. Prologue/epilogue
/// insertion is deferred to a post-regalloc step.
///
/// # Errors
///
/// Returns an error if any IR instruction cannot be lowered to x86.
pub fn isel(func: &Function, symbols: &SymbolTable) -> Result<IselResult<VInst>, String> {
    let call_has_ret2 = collect_call_ret2_users(func);
    let ba_cap = func.block_args.len();
    let pool_cap = func.inst_pool.next_index() as usize;
    let mut ctx = IselCtx {
        regs: VRegMap::new(pool_cap, ba_cap),
        cmps: CmpMap::new(pool_cap),
        stack: StackMap::new(pool_cap, ba_cap),
        alloc: VRegAlloc::new(),
        next_label: func.blocks.len() as u32,
        out: Vec::new(),
        sym_addrs: HashMap::new(),
        tls_sym_addrs: HashMap::new(),
        int_consts: HashMap::new(),
        scaled_ptradd_offsets: HashMap::new(),
        rdx_captured: HashMap::new(),
    };
    let mut inst_sources = Vec::new();

    for block_ref in collect_block_order(func, func.root_region) {
        // Emit all blocks, including unwind-entry cleanup blocks that are
        // intentionally unreachable from normal control flow.
        ctx.out.push(MInst::Label {
            id: block_ref.index(),
        });
        inst_sources.push(None);
        for block_arg in func.block_arg_values(block_ref) {
            if func.value_type(block_arg) != Some(&Type::Mem) {
                let _ = ctx.block_arg_reg(block_arg);
            }
        }
        for (vref, inst) in func.block_insts_with_values(block_ref) {
            if select_inst(
                &mut ctx,
                vref,
                &inst.op,
                &inst.ty,
                func,
                symbols,
                &call_has_ret2,
            )
            .is_none()
            {
                return Err(format!(
                    "instruction selection failed for {} at value {}: {:?}",
                    symbols.resolve(func.name),
                    vref.index(),
                    inst.op,
                ));
            }
            let source = inst.origin.sources.first().copied();
            inst_sources.resize(ctx.out.len(), source);
        }
    }

    let has_calls = ctx.out.iter().any(|i| matches!(i, MInst::CallSym { .. }));
    let isel_frame_size = ctx.stack.frame_size;
    let value_locations = SelectedValueLocations::from_maps(ctx.regs, ctx.stack);

    Ok(IselResult {
        name: symbols.resolve(func.name).to_string(),
        insts: ctx.out,
        inst_sources,
        value_locations,
        vreg_count: ctx.alloc.next,
        constraints: ctx.alloc.constraints,
        vreg_classes: ctx.alloc.vreg_classes,
        isel_frame_size,
        has_calls,
    })
}

/// Collect blocks in region order for lowering.
fn collect_block_order(
    func: &Function,
    region: tuffy_ir::value::RegionRef,
) -> Vec<tuffy_ir::value::BlockRef> {
    let mut out = Vec::new();
    collect_block_order_into(func, region, &mut out);
    out
}

/// Append blocks in region order to an existing output vector.
fn collect_block_order_into(
    func: &Function,
    region: tuffy_ir::value::RegionRef,
    out: &mut Vec<tuffy_ir::value::BlockRef>,
) {
    for child in &func.region(region).children {
        match child {
            CfgNode::Block(block) => out.push(*block),
            CfgNode::Region(region) => collect_block_order_into(func, *region, out),
        }
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "Instruction lowering depends on the current IR node, function context, symbols, and call-return analysis."
)]
/// Lower one IR instruction to x86 machine instructions.
fn select_inst(
    ctx: &mut IselCtx,
    vref: ValueRef,
    op: &Op,
    inst_ty: &Type,
    func: &Function,
    symbols: &SymbolTable,
    call_has_ret2: &HashSet<u32>,
) -> Option<()> {
    // Handle exact double-width integer operations before the generated rules.
    if has_exact_double_gpr_int_result(func, vref.index())
        && select_double_width_int_op(ctx, vref, op, func).is_some()
    {
        return Some(());
    }
    match op {
        Op::Shl(lhs, rhs) => {
            if let Some(imm) = int_const(func, rhs.clone().raw().value)
                .and_then(|imm| u8::try_from(imm).ok())
                .filter(|imm| (1..=3).contains(imm))
                && value_only_used_by_ptradd_offset(func, vref)
            {
                ctx.scaled_ptradd_offsets
                    .insert(vref.index(), (lhs.clone().raw().value, 1u8 << imm));
                return Some(());
            }
            let lhs_vreg = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let size = get_int_annotation(func, vref)
                .or_else(|| operand_int_annotation(func, &lhs.clone().raw()))
                .map(int_ann_to_opsize)
                .unwrap_or(OpSize::S64);
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: lhs_vreg,
            });
            if let Some(imm) = int_const(func, rhs.clone().raw().value)
                .and_then(|imm| u8::try_from(imm).ok())
                .filter(|imm| *imm <= 63)
            {
                ctx.out.push(MInst::ShlImm { size, dst, imm });
            } else {
                let rhs_vreg = ctx.ensure_in_reg(rhs.clone().raw().value)?;
                let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: cl,
                    src: rhs_vreg,
                });
                ctx.out.push(MInst::ShlRCL { size, dst });
            }
            ctx.regs.assign(vref, dst);
            return Some(());
        }
        Op::Shr(lhs, rhs) => {
            let lhs_vreg = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let lhs_ann = operand_int_annotation(func, &lhs.clone().raw());
            let size = lhs_ann.map(int_ann_to_opsize).unwrap_or(OpSize::S64);
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: lhs_vreg,
            });
            if let Some(imm) = int_const(func, rhs.clone().raw().value)
                .and_then(|imm| u8::try_from(imm).ok())
                .filter(|imm| *imm <= 63)
            {
                match lhs_ann {
                    Some(ann) if ann.signedness == IntSignedness::Signed => {
                        ctx.out.push(MInst::SarImm { size, dst, imm });
                    }
                    _ => {
                        ctx.out.push(MInst::ShrImm { size, dst, imm });
                    }
                }
            } else {
                let rhs_vreg = ctx.ensure_in_reg(rhs.clone().raw().value)?;
                let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: cl,
                    src: rhs_vreg,
                });
                match lhs_ann {
                    Some(ann) if ann.signedness == IntSignedness::Signed => {
                        ctx.out.push(MInst::SarRCL { size, dst });
                    }
                    _ => {
                        ctx.out.push(MInst::ShrRCL { size, dst });
                    }
                }
            }
            ctx.regs.assign(vref, dst);
            return Some(());
        }
        Op::Mul(lhs, rhs) => {
            if let Some((index_value, scale)) = mul_scale_operands(func, lhs, rhs)
                && value_only_used_by_ptradd_offset(func, vref)
            {
                ctx.scaled_ptradd_offsets
                    .insert(vref.index(), (index_value, scale));
                return Some(());
            }
        }
        Op::PtrAdd(ptr, offset) => {
            let base = ctx.ensure_in_reg(ptr.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            if let Some(imm) =
                int_const(func, offset.clone().raw().value).and_then(|imm| i32::try_from(imm).ok())
            {
                ctx.out.push(MInst::Lea {
                    dst,
                    base,
                    offset: imm,
                });
            } else if let Some((index_value, scale)) = ctx
                .scaled_ptradd_offsets
                .get(&offset.clone().raw().value.index())
                .copied()
            {
                let index = ctx.ensure_in_reg(index_value)?;
                ctx.out.push(MInst::LeaIndexed {
                    dst,
                    base,
                    index,
                    scale,
                    offset: 0,
                });
            } else {
                let index = ctx.ensure_in_reg(offset.clone().raw().value)?;
                ctx.out.push(MInst::LeaIndexed {
                    dst,
                    base,
                    index,
                    scale: 1,
                    offset: 0,
                });
            }
            ctx.regs.assign(vref, dst);
            return Some(());
        }
        Op::CountLeadingZeros(a, bits)
            if *bits == 128
                && get_int_annotation(func, a.clone().raw().value)
                    .is_some_and(|ann| ann.bit_width == 128) =>
        {
            let lo = ctx.ensure_in_reg(a.clone().raw().value)?;
            let hi = ensure_hi_in_reg(
                ctx,
                a.clone().raw().value,
                get_int_annotation(func, a.clone().raw().value),
            )?;
            let clz_hi = ctx.alloc.alloc();
            ctx.out.push(MInst::Lzcnt {
                size: OpSize::S64,
                dst: clz_hi,
                src: hi,
            });
            let clz_lo = ctx.alloc.alloc();
            ctx.out.push(MInst::Lzcnt {
                size: OpSize::S64,
                dst: clz_lo,
                src: lo,
            });
            let plus = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: plus,
                src: clz_lo,
            });
            let sixty_four = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI64 {
                dst: sixty_four,
                imm: 64,
            });
            ctx.out.push(MInst::AddRR {
                size: OpSize::S64,
                dst: plus,
                src: sixty_four,
            });
            let zero = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: zero,
                imm: 0,
            });
            let result = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: clz_hi,
            });
            ctx.out.push(MInst::CmpRR {
                size: OpSize::S64,
                src1: hi,
                src2: zero,
            });
            ctx.out.push(MInst::CMOVcc {
                size: OpSize::S64,
                cc: CondCode::E,
                dst: result,
                src: plus,
            });
            ctx.regs.assign(vref, result);
            return Some(());
        }
        Op::CountTrailingZeros(a)
            if get_int_annotation(func, a.clone().raw().value)
                .is_some_and(|ann| ann.bit_width == 128) =>
        {
            let lo = ctx.ensure_in_reg(a.clone().raw().value)?;
            let hi = ensure_hi_in_reg(
                ctx,
                a.clone().raw().value,
                get_int_annotation(func, a.clone().raw().value),
            )?;
            let ctz_lo = ctx.alloc.alloc();
            ctx.out.push(MInst::Tzcnt {
                size: OpSize::S64,
                dst: ctz_lo,
                src: lo,
            });
            let ctz_hi = ctx.alloc.alloc();
            ctx.out.push(MInst::Tzcnt {
                size: OpSize::S64,
                dst: ctz_hi,
                src: hi,
            });
            let plus = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: plus,
                src: ctz_hi,
            });
            let sixty_four = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI64 {
                dst: sixty_four,
                imm: 64,
            });
            ctx.out.push(MInst::AddRR {
                size: OpSize::S64,
                dst: plus,
                src: sixty_four,
            });
            let zero = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: zero,
                imm: 0,
            });
            let result = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: ctz_lo,
            });
            ctx.out.push(MInst::CmpRR {
                size: OpSize::S64,
                src1: lo,
                src2: zero,
            });
            ctx.out.push(MInst::CMOVcc {
                size: OpSize::S64,
                cc: CondCode::E,
                dst: result,
                src: plus,
            });
            ctx.regs.assign(vref, result);
            return Some(());
        }
        _ => {}
    }
    // Try generated rules first (covers Add, Sub, Mul, Or, And, Xor,
    // Shl, Shr, Min, Max, CountOnes, CountLeadingZeros, CountTrailingZeros,
    // ICmp, PtrAdd, PtrDiff).
    if isel_gen::try_select_generated(ctx, vref, op, func).is_some() {
        return Some(());
    }
    match op {
        Op::Param(idx) => {
            let idx = *idx as usize;
            let wide = is_wide_scalar_type(&func.params[idx], &func.param_annotations[idx]);
            let is_byval = func.byval_sizes.get(idx).copied().flatten().is_some();
            match classify_param_abi(
                &func.params,
                &func.param_annotations,
                &func.byval_sizes,
                idx,
            ) {
                ParamAbi::Gpr(i) => {
                    let fixed = ctx.alloc.alloc_fixed(ARG_REGS[i].to_preg());
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
                    // Exact double-width integer scalars occupy two consecutive GPRs.
                    // Capture the hi half from the next argument register.
                    if wide && i + 1 < ARG_REGS.len() {
                        let hi_fixed = ctx.alloc.alloc_fixed(ARG_REGS[i + 1].to_preg());
                        let hi_dst = ctx.alloc.alloc();
                        ctx.out.push(MInst::MovRR {
                            size: OpSize::S64,
                            dst: hi_dst,
                            src: hi_fixed,
                        });
                        ctx.regs
                            .assign(ValueRef::inst_secondary_result(vref.index()), hi_dst);
                    }
                }
                ParamAbi::Xmm {
                    idx: xmm_idx,
                    double,
                } => {
                    // Float param: arrives in XMM register; move bits to a GPR.
                    // PReg(0x20 + n) encodes XMMn (register class 1).
                    let xmm = ctx.alloc.alloc_fixed(PReg(0x20 + xmm_idx as u8));
                    let dst = ctx.alloc.alloc();
                    ctx.out.push(MInst::MoveXmmToGpr {
                        dst,
                        src: xmm,
                        double,
                    });
                    ctx.regs.assign(vref, dst);
                }
                ParamAbi::Stack(stack_idx) => {
                    // Stack-passed argument.  After the prologue
                    // (push rbp; mov rbp, rsp) the caller's stack args sit at
                    // positive offsets from RBP:
                    //   [rbp + 16] = first stack arg, [rbp + 24] = second, ...
                    let offset = 16 + stack_idx * 8;
                    let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                    let dst = ctx.alloc.alloc();
                    if is_byval {
                        // Byval param: the data sits on the stack; produce
                        // a pointer to it via LEA instead of loading a value.
                        ctx.out.push(MInst::Lea {
                            dst,
                            base: rbp,
                            offset,
                        });
                    } else {
                        ctx.out.push(MInst::MovRM {
                            size: OpSize::S64,
                            dst,
                            base: rbp,
                            offset,
                        });
                    }
                    ctx.regs.assign(vref, dst);
                }
            }
        }

        Op::Const(imm) => {
            // Try to fit in i64
            if let Some(imm_i64) = imm.to_i64().or_else(|| imm.to_u64().map(|v| v as i64)) {
                if int_const_can_stay_deferred(func, vref, imm_i64) {
                    ctx.int_consts.insert(vref.index(), imm_i64);
                    return Some(());
                }
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
            } else {
                // i128 constant: allocate stack slot (16 bytes for i128)
                let offset = ctx.stack.alloc(vref, 16, 16);
                let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());

                // Convert to two's complement u128 representation
                let u128_repr = if imm.sign() == num_bigint::Sign::Minus {
                    // For negative: u128 = 2^128 + value
                    let modulus = num_bigint::BigInt::from(1u128) << 128;
                    modulus + imm.clone()
                } else {
                    imm.clone()
                };

                // Extract low 64 bits using modulo
                let modulo = num_bigint::BigInt::from(1u64) << 64;
                let lo_bigint: num_bigint::BigInt = &u128_repr % &modulo;
                let lo_val = lo_bigint.to_u64().unwrap_or(0) as i64;
                let lo_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: lo_reg,
                    imm: lo_val,
                });
                ctx.out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: rbp,
                    offset,
                    src: lo_reg,
                });

                // Extract high 64 bits
                let divisor = num_bigint::BigInt::from(1u64) << 64;
                let hi_bigint: num_bigint::BigInt = u128_repr / divisor;
                let hi_val = hi_bigint.to_u64().unwrap_or(0) as i64;
                let hi_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: hi_reg,
                    imm: hi_val,
                });
                ctx.out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: rbp,
                    offset: offset + 8,
                    src: hi_reg,
                });

                // Assign lo as primary, hi as secondary
                ctx.regs.assign(vref, lo_reg);
                let secondary = ValueRef::inst_secondary_result(vref.index());
                ctx.regs.assign(secondary, hi_reg);
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

        Op::BAnd(a, b) => {
            let lhs = ctx.ensure_in_reg(a.clone().raw().value)?;
            let rhs = ctx.ensure_in_reg(b.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                dst,
                src: lhs,
                // Bool values are materialized as canonical 0/1 integers.
                // Keep them full-width so later `test reg, reg` sees clean bits.
                size: OpSize::S64,
            });
            ctx.out.push(MInst::AndRR {
                dst,
                src: rhs,
                size: OpSize::S64,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::BOr(a, b) => {
            let lhs = ctx.ensure_in_reg(a.clone().raw().value)?;
            let rhs = ctx.ensure_in_reg(b.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                dst,
                src: lhs,
                size: OpSize::S64,
            });
            ctx.out.push(MInst::OrRR {
                dst,
                src: rhs,
                size: OpSize::S64,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::BXor(a, b) => {
            let lhs = ctx.ensure_in_reg(a.clone().raw().value)?;
            let rhs = ctx.ensure_in_reg(b.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                dst,
                src: lhs,
                size: OpSize::S64,
            });
            ctx.out.push(MInst::XorRR {
                dst,
                src: rhs,
                size: OpSize::S64,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::FConst(value) => {
            if !matches!(
                value.float_type(),
                FloatType::F16 | FloatType::BF16 | FloatType::F32 | FloatType::F64
            ) {
                return None;
            }
            let dst = ctx.alloc.alloc();
            let raw_bits = u64::try_from(value.to_bits()).ok()?;
            ctx.out.push(MInst::MovRI64 {
                dst,
                imm: i64::from_ne_bytes(raw_bits.to_ne_bytes()),
            });
            ctx.regs.assign(vref, dst);
        }

        Op::Br(target, args) => {
            emit_block_arg_copies(ctx, *target, args, func)?;
            ctx.out.push(MInst::Jmp {
                target: target.index(),
            });
        }

        Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
            select_brif(
                ctx,
                &cond.clone().raw(),
                then_block,
                then_args,
                else_block,
                else_args,
                func,
            )?;
        }

        Op::Ret(val, ret2, _mem) => {
            // If this ret has a secondary return value (upper machine part),
            // we need to place lo in RAX and hi in RDX.  We must be
            // careful about ordering to avoid clobbering: read both
            // source registers first, then write to the fixed regs.
            let hi_src = match ret2.as_ref() {
                Some(op) => Some(ctx.ensure_in_reg(op.value)?),
                None => None,
            };
            // Check if this function returns a float (SysV ABI: f32/f64 in XMM0).
            let ret_is_float = matches!(func.ret_ty, Some(tuffy_ir::types::Type::Float(_)));
            if let Some(v) = val {
                let lo_src = ctx.ensure_in_reg(v.value)?;
                // Save hi to a temp before we touch RAX/RDX.
                let hi_tmp = hi_src.map(|h| {
                    let tmp = ctx.alloc.alloc();
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: tmp,
                        src: h,
                    });
                    tmp
                });
                if ret_is_float {
                    // Float return: SysV ABI puts f32/f64 in XMM0.
                    // Our representation keeps float bits in GPRs, so move to XMM0.
                    let is_double = matches!(
                        func.ret_ty,
                        Some(tuffy_ir::types::Type::Float(
                            tuffy_ir::types::FloatType::F64
                        ))
                    );
                    let xmm0 = ctx.alloc.alloc_fixed(PReg(0x20)); // XMM0
                    ctx.out.push(MInst::GprToXmm {
                        dst: xmm0,
                        src: lo_src,
                        double: is_double,
                    });
                } else {
                    let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst: rax,
                        src: lo_src,
                    });
                    if let Some(tmp) = hi_tmp {
                        let rdx = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
                        ctx.out.push(MInst::MovRR {
                            size: OpSize::S64,
                            dst: rdx,
                            src: tmp,
                        });
                    }
                }
            } else if let Some(h) = hi_src {
                let rdx = ctx.alloc.alloc_fixed(Gpr::Rdx.to_preg());
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: rdx,
                    src: h,
                });
            }
            ctx.out.push(MInst::Ret);
        }

        Op::Call(callee, args, _mem, _cleanup_label) => {
            select_call(
                ctx,
                vref,
                &callee.clone().raw(),
                args,
                func,
                symbols,
                call_has_ret2,
            )?;
        }

        Op::CallRet2(mem) => {
            let captured = ctx
                .rdx_captured
                .get(&mem.clone().raw().value.index())
                .copied()
                .expect("call_ret2 must follow a call with secondary return");
            ctx.regs.assign(vref, captured);
        }

        Op::StackSlot(bytes, align) => {
            let _offset = ctx.stack.alloc(vref, *bytes, *align);
        }

        Op::Load(ptr, bytes, _mem) => {
            if *bytes == 0 {
                // Zero-byte load (ZST): produce a dummy zero value so
                // downstream uses have a valid vreg, but emit no memory access.
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI {
                    size: OpSize::S32,
                    dst,
                    imm: 0,
                });
                ctx.regs.assign(vref, dst);
            } else if *bytes >= 9 {
                // 9-16 byte load: lo 8 bytes + remaining hi bytes as a second load.
                let lo_dst = ctx.alloc.alloc();
                let hi_dst = ctx.alloc.alloc();
                let hi_bytes = *bytes - 8;
                // For high-alignment slots (align > 16), skip the raw-offset
                // fast path and go through ensure_in_reg which applies LEA+AND.
                let use_fast = match ctx.stack.get_with_align(ptr.clone().raw().value) {
                    Some((_, align)) if align > 16 => false,
                    Some(_) => true,
                    None => false,
                };
                if use_fast {
                    let offset = ctx.stack.get(ptr.clone().raw().value).unwrap();
                    let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                    ctx.out.push(MInst::MovRM {
                        size: OpSize::S64,
                        dst: lo_dst,
                        base: rbp,
                        offset,
                    });
                    emit_partial_load(ctx, rbp, offset + 8, hi_dst, hi_bytes);
                } else {
                    let ptr_vreg = ctx.ensure_in_reg(ptr.clone().raw().value)?;
                    ctx.out.push(MInst::MovRM {
                        size: OpSize::S64,
                        dst: lo_dst,
                        base: ptr_vreg,
                        offset: 0,
                    });
                    emit_partial_load(ctx, ptr_vreg, 8, hi_dst, hi_bytes);
                }
                ctx.regs.assign(vref, lo_dst);
                ctx.regs
                    .assign(ValueRef::inst_secondary_result(vref.index()), hi_dst);
            } else {
                let dst = ctx.alloc.alloc();
                match ctx.stack.get_with_align(ptr.clone().raw().value) {
                    Some((offset, align)) if align <= 16 => {
                        let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                        emit_partial_load(ctx, rbp, offset, dst, *bytes);
                    }
                    _ => {
                        let ptr_vreg = ctx.ensure_in_reg(ptr.clone().raw().value)?;
                        emit_partial_load(ctx, ptr_vreg, 0, dst, *bytes);
                    }
                }
                ctx.regs.assign(vref, dst);
            }
        }

        Op::Store(val, ptr, bytes, _mem) => {
            // Zero-byte store is a no-op (ZST); skip to avoid emitting
            // spurious writes that corrupt the stack frame.
            if *bytes == 0 {
                // Still "use" the operands so the ISel doesn't fail on them.
            } else {
                let val_vreg = ctx.ensure_in_reg(val.value)?;
                // Determine the base register and base offset for the target address.
                let (base, base_offset) = match ctx.stack.get_with_align(ptr.clone().raw().value) {
                    Some((offset, align)) if align <= 16 => {
                        let rbp = ctx.alloc.alloc_fixed(Gpr::Rbp.to_preg());
                        (rbp, offset)
                    }
                    _ => (ctx.ensure_in_reg(ptr.clone().raw().value)?, 0i32),
                };
                if *bytes >= 9 {
                    // 9-16 byte store: lo 8 bytes + remaining from hi half.
                    ctx.out.push(MInst::MovMR {
                        size: OpSize::S64,
                        base,
                        offset: base_offset,
                        src: val_vreg,
                    });
                    let hi_vreg =
                        ensure_hi_in_reg(ctx, val.value, get_int_annotation(func, val.value))?;
                    let hi_bytes = *bytes - 8;
                    if hi_bytes == 8 {
                        ctx.out.push(MInst::MovMR {
                            size: OpSize::S64,
                            base,
                            offset: base_offset + 8,
                            src: hi_vreg,
                        });
                    } else {
                        emit_partial_store(ctx, base, base_offset + 8, hi_vreg, hi_bytes);
                    }
                } else {
                    // Emit stores; for non-power-of-2 sizes split into standard-size pieces.
                    emit_partial_store(ctx, base, base_offset, val_vreg, *bytes);
                }
            } // end of bytes != 0 else
        }

        Op::MemCopy(dst, src, count, _mem) => {
            select_memcopy(
                ctx,
                &dst.clone().raw(),
                &src.clone().raw(),
                &count.clone().raw(),
                func,
            )?;
        }

        Op::MemMove(dst, src, count, _mem) => {
            select_memmove(
                ctx,
                &dst.clone().raw(),
                &src.clone().raw(),
                &count.clone().raw(),
                func,
            )?;
        }

        Op::MemSet(dst, val, count, _mem) => {
            select_memset(ctx, &dst.clone().raw(), val, &count.clone().raw())?;
        }

        Op::Unreachable | Op::Trap => {
            ctx.out.push(MInst::Ud2);
        }

        Op::LandingPad => {
            // The unwinder deposits the exception pointer in %rax.
            // Define a fixed-RAX vreg, then copy to an unconstrained vreg
            // so the register allocator can manage it freely.
            let rax_vreg = ctx.alloc.alloc_fixed(crate::reg::Gpr::Rax.to_preg());
            ctx.out.push(MInst::LandingPadCapture { dst: rax_vreg });
            let exc_ptr = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: exc_ptr,
                src: rax_vreg,
            });
            ctx.regs.assign(vref, exc_ptr);
        }

        Op::Select(cond, tv, fv) => {
            select_select(ctx, vref, &cond.clone().raw(), tv, fv)?;
        }

        Op::Bitcast(val) => {
            let src = ctx.ensure_in_reg(val.value)?;
            ctx.regs.assign(vref, src);
        }

        Op::PtrToInt(val) | Op::PtrToAddr(val) => {
            let src = ctx.ensure_in_reg(val.clone().raw().value)?;
            ctx.regs.assign(vref, src);
        }

        Op::IntToPtr(val) => {
            let src = ctx.ensure_in_reg(val.clone().raw().value)?;
            ctx.regs.assign(vref, src);
        }

        Op::ExtractValue(..) | Op::InsertValue(..) => {
            return None; // These aggregate ops must be lowered before x86 isel.
        }

        Op::Sext(val, _target_bits) => {
            select_sext(ctx, vref, &val.clone().raw(), func)?;
        }

        Op::Zext(val, _target_bits) => {
            select_zext(ctx, vref, &val.clone().raw(), func)?;
        }

        Op::FpToSi(val) | Op::FpToUi(val) => {
            let src_gpr = ctx.ensure_in_reg(val.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            // Determine f32 vs f64 from the source value's type
            let double = !matches!(
                func.value_type(val.clone().raw().value),
                Some(Type::Float(tuffy_ir::types::FloatType::F32))
            );
            // Float values live in GPRs as bit-patterns; move to XMM for conversion.
            let src_xmm = ctx.alloc.alloc_class(1);
            ctx.out.push(MInst::GprToXmm {
                dst: src_xmm,
                src: src_gpr,
                double,
            });
            ctx.out.push(MInst::CvtFpToInt {
                dst,
                src: src_xmm,
                double,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::SiToFp(val, ft) | Op::UiToFp(val, ft) => {
            let val_ann = get_int_annotation(func, val.clone().raw().value);
            let is_exact_double_gpr_int =
                val_ann.is_some_and(|ann| ann.bit_width == DOUBLE_GPR_BITS);

            if is_exact_double_gpr_int {
                // Double-width integer to float: not yet fully implemented
                // TODO: implement i128 to float conversion
                return None;
            }

            let src = ctx.ensure_in_reg(val.clone().raw().value)?;
            let double = !matches!(ft, tuffy_ir::types::FloatType::F32);
            let gpr_dst = ctx.alloc.alloc();

            let is_u64 = matches!(op, Op::UiToFp(..))
                && matches!(val_ann.map(|a| a.bit_width), Some(64) | None);

            if is_u64 {
                // u64 → float: values > i64::MAX need special handling.
                // If top bit is clear (value fits in i64), cvtsi2ss/cvtsi2sd works.
                // Otherwise: halve (preserving bit 0), convert, then double.
                let done_label = ctx.next_label;
                ctx.next_label += 1;
                let large_label = ctx.next_label;
                ctx.next_label += 1;

                let xmm_dst = ctx.alloc.alloc_class(1);

                // test src, src — check if top bit is set (signed interpretation < 0)
                ctx.out.push(MInst::TestRR {
                    size: OpSize::S64,
                    src1: src,
                    src2: src,
                });
                // js large_label (sign bit set → top bit set → value > i64::MAX)
                ctx.out.push(MInst::Jcc {
                    cc: CondCode::L,
                    target: large_label,
                });

                // Small case: fits in i64, convert directly
                ctx.out.push(MInst::CvtIntToFp {
                    dst: xmm_dst,
                    src,
                    double,
                });
                ctx.out.push(MInst::Jmp { target: done_label });

                // Large case: halve + preserve bit0 + convert + double
                ctx.out.push(MInst::Label { id: large_label });
                let halved = ctx.alloc.alloc();
                let bit0 = ctx.alloc.alloc();
                let xmm_halved = ctx.alloc.alloc_class(1);
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: halved,
                    src,
                });
                ctx.out.push(MInst::ShrImm {
                    size: OpSize::S64,
                    dst: halved,
                    imm: 1,
                });
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: bit0,
                    src,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: bit0,
                    imm: 1,
                });
                ctx.out.push(MInst::OrRR {
                    size: OpSize::S64,
                    dst: halved,
                    src: bit0,
                });
                ctx.out.push(MInst::CvtIntToFp {
                    dst: xmm_halved,
                    src: halved,
                    double,
                });
                // double the result: addss/addsd xmm_dst, xmm_halved, xmm_halved
                ctx.out.push(MInst::FpBinOp {
                    op: FpBinOpKind::Add,
                    dst: xmm_dst,
                    lhs: xmm_halved,
                    rhs: xmm_halved,
                    double,
                });

                ctx.out.push(MInst::Label { id: done_label });
                ctx.out.push(MInst::MoveXmmToGpr {
                    dst: gpr_dst,
                    src: xmm_dst,
                    double,
                });
            } else {
                // For signed narrow integers (i8, i16, i32), sign-extend before
                // cvtsi2ss/cvtsi2sd, which expects a full-width signed 64-bit integer.
                // Without sign extension, a byte like 0xDA (-38 as i8) would be
                // seen as 218 by the instruction, producing the wrong float result.
                let src_for_fp = if matches!(op, Op::SiToFp(..)) {
                    match val_ann.map(|a| a.bit_width) {
                        Some(8) => {
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovsxB { dst: ext, src });
                            ext
                        }
                        Some(16) => {
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovsxW { dst: ext, src });
                            ext
                        }
                        Some(32) => {
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovsxD { dst: ext, src });
                            ext
                        }
                        _ => src,
                    }
                } else {
                    // For unsigned sub-64-bit conversions, zero-extend
                    // before cvtsi2ss/cvtsi2sd.  The instruction treats
                    // the source as signed 64-bit, so the upper bits must
                    // be clear to get the correct unsigned interpretation.
                    match val_ann.map(|a| a.bit_width) {
                        Some(8) => {
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovzxB { dst: ext, src });
                            ext
                        }
                        Some(16) => {
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovzxW { dst: ext, src });
                            ext
                        }
                        Some(32) => {
                            // 32-bit mov zeros upper 32 bits on x86-64.
                            let ext = ctx.alloc.alloc();
                            ctx.out.push(MInst::MovRR {
                                size: OpSize::S32,
                                dst: ext,
                                src,
                            });
                            ext
                        }
                        _ => src,
                    }
                };
                let xmm_dst = ctx.alloc.alloc_class(1);
                ctx.out.push(MInst::CvtIntToFp {
                    dst: xmm_dst,
                    src: src_for_fp,
                    double,
                });
                ctx.out.push(MInst::MoveXmmToGpr {
                    dst: gpr_dst,
                    src: xmm_dst,
                    double,
                });
            }

            ctx.regs.assign(vref, gpr_dst);
        }

        Op::FpConvert(val) => {
            let src_gpr = ctx.ensure_in_reg(val.clone().raw().value)?;
            // Determine source float type from the operand's type
            let src_double = !matches!(
                func.value_type(val.clone().raw().value),
                Some(Type::Float(tuffy_ir::types::FloatType::F32))
            );
            // Float values live in GPRs; move to XMM, convert, move result back to GPR.
            let src_xmm = ctx.alloc.alloc_class(1);
            ctx.out.push(MInst::GprToXmm {
                dst: src_xmm,
                src: src_gpr,
                double: src_double,
            });
            let dst_xmm = ctx.alloc.alloc_class(1);
            ctx.out.push(MInst::CvtFpToFp {
                dst: dst_xmm,
                src: src_xmm,
                src_double,
            });
            let dst_double = !src_double; // output type is the opposite of input
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double: dst_double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }

        Op::Div(lhs, rhs) => {
            select_divrem(
                ctx,
                vref,
                &lhs.clone().raw(),
                &rhs.clone().raw(),
                DivRemKind::Div,
                func,
            )?;
        }
        Op::Rem(lhs, rhs) => {
            select_divrem(
                ctx,
                vref,
                &lhs.clone().raw(),
                &rhs.clone().raw(),
                DivRemKind::Rem,
                func,
            )?;
        }

        Op::FAdd(lhs, rhs, _) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Add,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FSub(lhs, rhs, _) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Sub,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FMul(lhs, rhs, _) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Mul,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FDiv(lhs, rhs, _) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Div,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FMinNum(lhs, rhs) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Min,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FMaxNum(lhs, rhs) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            let dst_xmm = ctx.alloc.alloc_class(1);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            ctx.out.push(MInst::FpBinOp {
                op: FpBinOpKind::Max,
                dst: dst_xmm,
                lhs: l_xmm,
                rhs: r_xmm,
                double,
            });
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: dst_xmm,
                double,
            });
            ctx.regs.assign(vref, gpr_dst);
        }
        Op::FCmp(kind, lhs, rhs) => {
            let l_gpr = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r_gpr = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let double = !matches!(
                func.value_type(lhs.clone().raw().value),
                Some(Type::Float(tuffy_ir::types::FloatType::F32))
            );
            let l_xmm = ctx.alloc.alloc_class(1);
            let r_xmm = ctx.alloc.alloc_class(1);
            ctx.out.push(MInst::GprToXmm {
                dst: l_xmm,
                src: l_gpr,
                double,
            });
            ctx.out.push(MInst::GprToXmm {
                dst: r_xmm,
                src: r_gpr,
                double,
            });
            let dst = ctx.alloc.alloc();
            let tmp = ctx.alloc.alloc();
            ctx.out.push(MInst::FpCmp {
                dst,
                lhs: l_xmm,
                rhs: r_xmm,
                tmp,
                kind: *kind as u8,
                double,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FNeg(val) => {
            let src = ctx.ensure_in_reg(val.clone().raw().value)?;
            // Float values live in GPRs as bit-patterns; XOR the sign bit directly.
            let dst = ctx.alloc.alloc();
            let is_f32 = matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let sign_mask: i64 = if is_f32 {
                0x80000000_u32 as i64
            } else {
                i64::MIN // 0x8000000000000000
            };
            let mask_reg = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI64 {
                dst: mask_reg,
                imm: sign_mask,
            });
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.out.push(MInst::XorRR {
                size: OpSize::S64,
                dst,
                src: mask_reg,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::FAbs(val) => {
            let src = ctx.ensure_in_reg(val.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            let is_f32 = matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let clear_mask: i64 = if is_f32 {
                0x7FFFFFFF_i64
            } else {
                i64::MAX // 0x7FFFFFFFFFFFFFFF
            };
            let mask_reg = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI64 {
                dst: mask_reg,
                imm: clear_mask,
            });
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
            ctx.out.push(MInst::AndRR {
                size: OpSize::S64,
                dst,
                src: mask_reg,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::CopySign(mag, sign) => {
            let mag_r = ctx.ensure_in_reg(mag.clone().raw().value)?;
            let sign_r = ctx.ensure_in_reg(sign.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            let is_f32 = matches!(inst_ty, Type::Float(tuffy_ir::types::FloatType::F32));
            let sign_mask: i64 = if is_f32 {
                0x80000000_u32 as i64
            } else {
                i64::MIN
            };
            let clear_mask: i64 = if is_f32 { 0x7FFFFFFF_i64 } else { i64::MAX };
            // dst = (mag & clear_mask) | (sign & sign_mask)
            let m1 = ctx.alloc.alloc();
            let m2 = ctx.alloc.alloc();
            let mask1 = ctx.alloc.alloc();
            let mask2 = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI64 {
                dst: mask1,
                imm: clear_mask,
            });
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: m1,
                src: mag_r,
            });
            ctx.out.push(MInst::AndRR {
                size: OpSize::S64,
                dst: m1,
                src: mask1,
            });
            ctx.out.push(MInst::MovRI64 {
                dst: mask2,
                imm: sign_mask,
            });
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: m2,
                src: sign_r,
            });
            ctx.out.push(MInst::AndRR {
                size: OpSize::S64,
                dst: m2,
                src: mask2,
            });
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: m1,
            });
            ctx.out.push(MInst::OrRR {
                size: OpSize::S64,
                dst,
                src: m2,
            });
            ctx.regs.assign(vref, dst);
        }
        Op::LoadAtomic(addr, _ty, _ordering) => {
            // Fallback: treat as regular load (x86 has strong memory model).
            let base = ctx.ensure_in_reg(addr.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            // The data annotation is on secondary_result_annotation (data is secondary result).
            let inst_ann = func.inst_pool.get(vref.index()).and_then(|n| {
                match &n.inst.secondary_result_annotation {
                    Some(Annotation::Int(ann)) => Some(*ann),
                    _ => None,
                }
            });
            let size = match inst_ann {
                Some(ann) if ann.bit_width > 0 => bytes_to_opsize(ann.bit_width / 8),
                _ => OpSize::S64,
            };
            ctx.out.push(MInst::MovRM {
                size,
                dst,
                base,
                offset: 0,
            });
            let data_vref = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(data_vref, dst);
        }
        Op::StoreAtomic(val, addr, _ordering, _mem) => {
            // Fallback: treat as regular store.
            let src = ctx.ensure_in_reg(val.value)?;
            let base = ctx.ensure_in_reg(addr.clone().raw().value)?;
            let val_ann = get_int_annotation(func, val.value);
            let size = match val_ann {
                Some(ann) if ann.bit_width > 0 => bytes_to_opsize(ann.bit_width / 8),
                _ => OpSize::S64,
            };
            ctx.out.push(MInst::MovMR {
                size,
                base,
                offset: 0,
                src,
            });
        }
        Op::AtomicRmw(rmw_op, ptr, val, _ordering, _mem) => {
            let base = ctx.ensure_in_reg(ptr.clone().raw().value)?;
            let val_reg = ctx.ensure_in_reg(val.value)?;
            // The size annotation is on secondary_result_annotation.
            let inst_ann = func.inst_pool.get(vref.index()).and_then(|n| {
                match &n.inst.secondary_result_annotation {
                    Some(Annotation::Int(ann)) => Some(*ann),
                    _ => None,
                }
            });
            let size = match inst_ann {
                Some(ann) if ann.bit_width > 0 => bytes_to_opsize(ann.bit_width / 8),
                _ => {
                    // Fall back to input value annotation.
                    let val_ann = get_int_annotation(func, val.value);
                    match val_ann {
                        Some(ann) => bytes_to_opsize(ann.bit_width / 8),
                        None => OpSize::S64,
                    }
                }
            };
            let op_kind = match rmw_op {
                tuffy_ir::instruction::AtomicRmwOp::Xchg => AtomicRmwOpKind::Xchg,
                tuffy_ir::instruction::AtomicRmwOp::Add => AtomicRmwOpKind::Add,
                tuffy_ir::instruction::AtomicRmwOp::Sub => AtomicRmwOpKind::Sub,
                tuffy_ir::instruction::AtomicRmwOp::And => AtomicRmwOpKind::And,
                tuffy_ir::instruction::AtomicRmwOp::Or => AtomicRmwOpKind::Or,
                tuffy_ir::instruction::AtomicRmwOp::Xor => AtomicRmwOpKind::Xor,
            };
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::AtomicRmw {
                op: op_kind,
                size,
                dst,
                base,
                val: val_reg,
            });
            let data_vref = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(data_vref, dst);
        }
        Op::AtomicCmpXchg(ptr, expected, desired, _succ_ord, _fail_ord, _mem) => {
            let base = ctx.ensure_in_reg(ptr.clone().raw().value)?;
            let expected_reg = ctx.ensure_in_reg(expected.value)?;
            let desired_reg = ctx.ensure_in_reg(desired.value)?;
            let inst_ann = func.inst_pool.get(vref.index()).and_then(|n| {
                match &n.inst.secondary_result_annotation {
                    Some(Annotation::Int(ann)) => Some(*ann),
                    _ => None,
                }
            });
            let size = match inst_ann {
                Some(ann) if ann.bit_width > 0 => bytes_to_opsize(ann.bit_width / 8),
                _ => {
                    let exp_ann = get_int_annotation(func, expected.value);
                    match exp_ann {
                        Some(ann) => bytes_to_opsize(ann.bit_width / 8),
                        None => OpSize::S64,
                    }
                }
            };
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::AtomicCmpXchg {
                size,
                dst,
                base,
                expected: expected_reg,
                desired: desired_reg,
            });
            let data_vref = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(data_vref, dst);
        }

        Op::Bswap(val, byte_count) => {
            if *byte_count > 8 {
                // 128-bit bswap: swap two 64-bit halves and swap bytes within each
                let ptr = ctx.ensure_in_reg(val.clone().raw().value)?;
                let lo = ctx.alloc.alloc();
                let hi = ctx.alloc.alloc();

                // Load low 8 bytes
                ctx.out.push(MInst::MovRM {
                    size: OpSize::S64,
                    dst: lo,
                    base: ptr,
                    offset: 0,
                });
                // Load high 8 bytes
                ctx.out.push(MInst::MovRM {
                    size: OpSize::S64,
                    dst: hi,
                    base: ptr,
                    offset: 8,
                });

                // Bswap each half
                ctx.out.push(MInst::Bswap {
                    size: OpSize::S64,
                    dst: lo,
                });
                ctx.out.push(MInst::Bswap {
                    size: OpSize::S64,
                    dst: hi,
                });

                // Store swapped: lo goes to high position, hi goes to low position
                ctx.out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: ptr,
                    offset: 8,
                    src: lo,
                });
                ctx.out.push(MInst::MovMR {
                    size: OpSize::S64,
                    base: ptr,
                    offset: 0,
                    src: hi,
                });

                ctx.regs.assign(vref, ptr);
            } else {
                let s = ctx.ensure_in_reg(val.clone().raw().value)?;
                let dst = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: s,
                });
                let size = if *byte_count >= 8 {
                    OpSize::S64
                } else {
                    OpSize::S32
                };
                ctx.out.push(MInst::Bswap { size, dst });
                if *byte_count == 2 {
                    // bswap r32 puts result in high 16 bits of 32-bit reg; shift right
                    ctx.out.push(MInst::ShrImm {
                        size: OpSize::S64,
                        dst,
                        imm: 16,
                    });
                }
                ctx.regs.assign(vref, dst);
            }
        }

        Op::RotateLeft(val, amt, bits) => {
            let size = bytes_to_opsize(bits / 8);
            let v = ctx.ensure_in_reg(val.clone().raw().value)?;
            let a = ctx.ensure_in_reg(amt.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR { size, dst, src: v });
            let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: cl,
                src: a,
            });
            ctx.out.push(MInst::RolRCL { size, dst });
            ctx.regs.assign(vref, dst);
        }

        Op::RotateRight(val, amt, bits) => {
            let size = bytes_to_opsize(bits / 8);
            let v = ctx.ensure_in_reg(val.clone().raw().value)?;
            let a = ctx.ensure_in_reg(amt.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR { size, dst, src: v });
            let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: cl,
                src: a,
            });
            ctx.out.push(MInst::RorRCL { size, dst });
            ctx.regs.assign(vref, dst);
        }

        Op::BitReverse(val, bits) => {
            // Byte-swap + reverse bits within each byte via shift-mask sequence
            let s = ctx.ensure_in_reg(val.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: s,
            });
            let _bc = *bits / 8;
            // Always BSWAP64 to reverse byte order so that the final
            // right-shift by (64 - bits) extracts the correct result.
            ctx.out.push(MInst::Bswap {
                size: OpSize::S64,
                dst,
            });
            // Reverse bits within each byte: 3 rounds of swap-adjacent-groups
            for (mask, shift) in [
                (0x5555555555555555u64, 1u8),
                (0x3333333333333333u64, 2u8),
                (0x0F0F0F0F0F0F0F0Fu64, 4u8),
            ] {
                // t1 = (dst >> shift) & mask
                let t1 = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: t1,
                    src: dst,
                });
                let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
                ctx.out.push(MInst::MovRI {
                    size: OpSize::S32,
                    dst: cl,
                    imm: shift as i64,
                });
                ctx.out.push(MInst::ShrRCL {
                    size: OpSize::S64,
                    dst: t1,
                });
                let m = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: m,
                    imm: mask as i64,
                });
                ctx.out.push(MInst::AndRR {
                    size: OpSize::S64,
                    dst: t1,
                    src: m,
                });
                // t2 = (dst & mask) << shift
                let t2 = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: t2,
                    src: dst,
                });
                let m2 = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: m2,
                    imm: mask as i64,
                });
                ctx.out.push(MInst::AndRR {
                    size: OpSize::S64,
                    dst: t2,
                    src: m2,
                });
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: t2,
                    imm: shift,
                });
                // dst = t1 | t2
                ctx.out.push(MInst::OrRR {
                    size: OpSize::S64,
                    dst: t1,
                    src: t2,
                });
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: t1,
                });
            }
            if *bits < 64 {
                let cl = ctx.alloc.alloc_fixed(Gpr::Rcx.to_preg());
                ctx.out.push(MInst::MovRI {
                    size: OpSize::S32,
                    dst: cl,
                    imm: (64 - *bits) as i64,
                });
                ctx.out.push(MInst::ShrRCL {
                    size: OpSize::S64,
                    dst,
                });
            }
            ctx.regs.assign(vref, dst);
        }

        Op::SaturatingAdd(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: l,
            });
            ctx.out.push(MInst::AddRR {
                size: OpSize::S64,
                dst,
                src: r,
            });
            if *bits < 64 {
                let max_val = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst,
                    imm: max_val as i64,
                });
                // Check overflow: if result < lhs (masked), saturate
                let lm = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: lm,
                    src: l,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: lm,
                    imm: max_val as i64,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: lm,
                });
                let sat = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat,
                    imm: max_val as i64,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::B,
                    dst,
                    src: sat,
                });
            } else {
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: l,
                });
                let sat = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat,
                    imm: -1i64,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::B,
                    dst,
                    src: sat,
                });
            }
            ctx.regs.assign(vref, dst);
        }

        Op::SaturatingSub(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: l,
            });
            if *bits < 64 {
                let max_val = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst,
                    imm: max_val as i64,
                });
                let rm = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: rm,
                    src: r,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: rm,
                    imm: max_val as i64,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: rm,
                });
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst,
                    src: rm,
                });
            } else {
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: r,
                });
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst,
                    src: r,
                });
            }
            let zero = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRI {
                size: OpSize::S32,
                dst: zero,
                imm: 0,
            });
            ctx.out.push(MInst::CMOVcc {
                size: OpSize::S64,
                cc: CondCode::B,
                dst,
                src: zero,
            });
            ctx.regs.assign(vref, dst);
        }

        Op::SignedSaturatingAdd(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: l,
            });
            if *bits < 64 {
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst,
                    src: r,
                });
                let max_val = (1i64 << (bits - 1)) - 1;
                let min_val = -(1i64 << (bits - 1));
                let sat_hi = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat_hi,
                    imm: max_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: sat_hi,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::G,
                    dst,
                    src: sat_hi,
                });
                let sat_lo = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat_lo,
                    imm: min_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: sat_lo,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::L,
                    dst,
                    src: sat_lo,
                });
            } else {
                // 64-bit: use overflow flag. sat = (a >> 63) XOR I64_MAX = I64_MAX if a>=0, I64_MIN if a<0.
                // Compute the saturation value BEFORE the addition so
                // that SAR/XOR don't clobber the overflow flag.
                let sat = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: sat,
                    src: l,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: sat,
                    imm: 63,
                });
                let imax = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: imax,
                    imm: i64::MAX,
                });
                ctx.out.push(MInst::XorRR {
                    size: OpSize::S64,
                    dst: sat,
                    src: imax,
                });
                // Now do the addition — OF flag is set here.
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst,
                    src: r,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::O,
                    dst,
                    src: sat,
                });
            }
            ctx.regs.assign(vref, dst);
        }

        Op::SignedSaturatingSub(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: l,
            });
            if *bits < 64 {
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst,
                    src: r,
                });
                let max_val = (1i64 << (bits - 1)) - 1;
                let min_val = -(1i64 << (bits - 1));
                let sat_hi = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat_hi,
                    imm: max_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: sat_hi,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::G,
                    dst,
                    src: sat_hi,
                });
                let sat_lo = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: sat_lo,
                    imm: min_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: dst,
                    src2: sat_lo,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::L,
                    dst,
                    src: sat_lo,
                });
            } else {
                // 64-bit: use overflow flag. sat = (a >> 63) XOR I64_MAX.
                // Compute the saturation value BEFORE the subtraction so
                // that SAR/XOR don't clobber the overflow flag.
                let sat = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: sat,
                    src: l,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: sat,
                    imm: 63,
                });
                let imax = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: imax,
                    imm: i64::MAX,
                });
                ctx.out.push(MInst::XorRR {
                    size: OpSize::S64,
                    dst: sat,
                    src: imax,
                });
                // Now do the subtraction — OF flag is set here.
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst,
                    src: r,
                });
                ctx.out.push(MInst::CMOVcc {
                    size: OpSize::S64,
                    cc: CondCode::O,
                    dst,
                    src: sat,
                });
            }
            ctx.regs.assign(vref, dst);
        }

        Op::SAddWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: l,
            });
            // Sign-extend sub-word operands so 64-bit arithmetic
            // produces a correctly-signed result for range checking.
            if *bits < 64 {
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
            } else {
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r,
                });
            }
            if *bits == 64 {
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::O,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
            } else {
                let max_val = (1i64 << (bits - 1)) - 1;
                let min_val = -(1i64 << (bits - 1));
                let hi = ctx.alloc.alloc();
                let max_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: max_reg,
                    imm: max_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: max_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::G,
                    dst: hi,
                });
                let lo = ctx.alloc.alloc();
                let min_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: min_reg,
                    imm: min_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: min_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::L,
                    dst: lo,
                });
                ctx.out.push(MInst::MovzxB { dst: hi, src: hi });
                ctx.out.push(MInst::MovzxB { dst: lo, src: lo });
                ctx.out.push(MInst::OrRR {
                    size: OpSize::S64,
                    dst: hi,
                    src: lo,
                });
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: overflow,
                    src: hi,
                });
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::UAddWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: l,
            });
            // Zero-extend sub-word operands so 64-bit arithmetic
            // doesn't carry junk upper bits into the overflow check.
            if *bits < 64 {
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: mask as i64,
                });
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
            } else {
                ctx.out.push(MInst::AddRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r,
                });
            }
            if *bits == 64 {
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::B,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
            } else {
                let tmp = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: tmp,
                    src: result,
                });
                ctx.out.push(MInst::ShrImm {
                    size: OpSize::S64,
                    dst: tmp,
                    imm: *bits as u8,
                });
                ctx.out.push(MInst::TestRR {
                    size: OpSize::S64,
                    src1: tmp,
                    src2: tmp,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::Ne,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::SSubWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: l,
            });
            // Sign-extend sub-word operands so 64-bit arithmetic
            // produces a correctly-signed result for range checking.
            if *bits < 64 {
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
            } else {
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r,
                });
            }
            if *bits == 64 {
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::O,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
            } else {
                let max_val = (1i64 << (bits - 1)) - 1;
                let min_val = -(1i64 << (bits - 1));
                let hi = ctx.alloc.alloc();
                let max_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: max_reg,
                    imm: max_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: max_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::G,
                    dst: hi,
                });
                let lo = ctx.alloc.alloc();
                let min_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: min_reg,
                    imm: min_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: min_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::L,
                    dst: lo,
                });
                ctx.out.push(MInst::MovzxB { dst: hi, src: hi });
                ctx.out.push(MInst::MovzxB { dst: lo, src: lo });
                ctx.out.push(MInst::OrRR {
                    size: OpSize::S64,
                    dst: hi,
                    src: lo,
                });
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: overflow,
                    src: hi,
                });
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::USubWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: l,
            });
            // Zero-extend sub-word operands so 64-bit arithmetic
            // doesn't carry junk upper bits into the overflow check.
            if *bits < 64 {
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: mask as i64,
                });
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
            } else {
                ctx.out.push(MInst::SubRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r,
                });
            }
            if *bits == 64 {
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::B,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
            } else {
                ctx.out.push(MInst::TestRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: result,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::L,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::SMulWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst: result,
                src: l,
            });
            // Sign-extend sub-word operands so 64-bit arithmetic
            // produces a correctly-signed result for range checking.
            if *bits < 64 {
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: shift,
                });
                ctx.out.push(MInst::ImulRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
            } else {
                ctx.out.push(MInst::ImulRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r,
                });
            }
            if *bits == 64 {
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::O,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
            } else {
                let max_val = (1i64 << (bits - 1)) - 1;
                let min_val = -(1i64 << (bits - 1));
                let hi = ctx.alloc.alloc();
                let max_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: max_reg,
                    imm: max_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: max_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::G,
                    dst: hi,
                });
                let lo = ctx.alloc.alloc();
                let min_reg = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRI64 {
                    dst: min_reg,
                    imm: min_val,
                });
                ctx.out.push(MInst::CmpRR {
                    size: OpSize::S64,
                    src1: result,
                    src2: min_reg,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::L,
                    dst: lo,
                });
                ctx.out.push(MInst::MovzxB { dst: hi, src: hi });
                ctx.out.push(MInst::MovzxB { dst: lo, src: lo });
                ctx.out.push(MInst::OrRR {
                    size: OpSize::S64,
                    dst: hi,
                    src: lo,
                });
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: overflow,
                    src: hi,
                });
                let shift = 64u8 - *bits as u8;
                ctx.out.push(MInst::ShlImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
                ctx.out.push(MInst::SarImm {
                    size: OpSize::S64,
                    dst: result,
                    imm: shift,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::UMulWithOverflow(lhs, rhs, bits) => {
            let l = ctx.ensure_in_reg(lhs.clone().raw().value)?;
            let r = ctx.ensure_in_reg(rhs.clone().raw().value)?;
            let result = ctx.alloc.alloc();
            let overflow = ctx.alloc.alloc();
            if *bits == 64 {
                // Use one-operand MUL (RDX:RAX = RAX * src) for proper
                // unsigned overflow detection: overflow iff RDX != 0.
                ctx.out.push(MInst::UMulOverflow {
                    dst: result,
                    overflow,
                    lhs: l,
                    rhs: r,
                });
            } else {
                // Zero-extend sub-word operands before multiply.
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: result,
                    src: l,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
                let r_ext = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: r_ext,
                    src: r,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: r_ext,
                    imm: mask as i64,
                });
                ctx.out.push(MInst::ImulRR {
                    size: OpSize::S64,
                    dst: result,
                    src: r_ext,
                });
                let tmp = ctx.alloc.alloc();
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst: tmp,
                    src: result,
                });
                ctx.out.push(MInst::ShrImm {
                    size: OpSize::S64,
                    dst: tmp,
                    imm: *bits as u8,
                });
                ctx.out.push(MInst::TestRR {
                    size: OpSize::S64,
                    src1: tmp,
                    src2: tmp,
                });
                ctx.out.push(MInst::SetCC {
                    cc: CondCode::Ne,
                    dst: overflow,
                });
                ctx.out.push(MInst::MovzxB {
                    dst: overflow,
                    src: overflow,
                });
                let mask = (1u64 << bits) - 1;
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst: result,
                    imm: mask as i64,
                });
            }
            ctx.regs.assign(vref, result);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, overflow);
        }

        Op::SymbolAddr(sym_id) => {
            // Defer LeaSymbol emission — only emit when ensure_in_reg is called.
            // This avoids dead code when the symbol is only used as a direct call callee
            // (select_call emits CallSym directly without needing the address in a register).
            ctx.sym_addrs
                .insert(vref.index(), symbols.resolve(*sym_id).to_string());
        }

        Op::TlsSymbolAddr(sym_id) => {
            ctx.tls_sym_addrs
                .insert(vref.index(), symbols.resolve(*sym_id).to_string());
        }

        Op::Fence(..) => {
            // Memory fence — no-op on x86 (strong memory model).
        }
        Op::Continue(_) | Op::RegionYield(_) => {
            return None;
        }

        // Ops handled by isel_gen::try_select_generated above.
        _ => return None,
    }
    Some(())
}

// --- Helper functions ---

/// Lower a `brif` terminator.
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
    let branch_test = decode_branch_test(ctx, func, cond.value);

    if has_args {
        let intermediate = ctx.next_label;
        ctx.next_label += 1;

        emit_branch_jump(ctx, branch_test, cond.value, intermediate, func)?;

        // Else path.
        emit_block_arg_copies(ctx, *else_block, else_args, func)?;
        ctx.out.push(MInst::Jmp {
            target: else_block.index(),
        });

        // Then path.
        ctx.out.push(MInst::Label { id: intermediate });
        emit_block_arg_copies(ctx, *then_block, then_args, func)?;
        ctx.out.push(MInst::Jmp {
            target: then_block.index(),
        });
    } else {
        emit_branch_jump(ctx, branch_test, cond.value, then_block.index(), func)?;
        ctx.out.push(MInst::Jmp {
            target: else_block.index(),
        });
    }
    Some(())
}

#[allow(
    clippy::too_many_arguments,
    reason = "Call lowering needs callee, arguments, cleanup metadata, and return-shape analysis together."
)]
/// Lower a call instruction.
fn select_call(
    ctx: &mut IselCtx,
    vref: ValueRef,
    callee: &Operand,
    args: &[Operand],
    func: &Function,
    symbols: &SymbolTable,
    call_has_ret2: &HashSet<u32>,
) -> Option<()> {
    let cleanup_label = match &func.inst(vref.index()).op {
        Op::Call(_, _, _, cleanup) => *cleanup,
        _ => None,
    };
    if cleanup_label.is_none()
        && let Some(sym_id) = direct_call_symbol(func, callee.value)
    {
        let name = symbols.resolve(sym_id);
        if (name == "memcpy" || name == "memmove")
            && args.len() == 3
            && let Some(bytes) = const_byte_count(func, &args[2])
            && lower_small_memtransfer(ctx, &args[0], &args[1], bytes).is_some()
        {
            if func.inst(vref.index()).secondary_ty.is_some() {
                let dst = ctx.ensure_in_reg(args[0].value)?;
                let secondary = ValueRef::inst_secondary_result(vref.index());
                ctx.regs.assign(secondary, dst);
            }
            return Some(());
        }
    }

    // Phase 1: materialize all args into unconstrained vregs.
    // This must happen before any fixed-register moves, otherwise
    // ensure_in_reg may emit LEA/MOV instructions whose destinations
    // get allocated to argument registers (e.g. rdx), clobbering
    // values already placed there by earlier fixed-register moves.
    let mut arg_vregs: Vec<VReg> = Vec::new();
    for arg in args.iter() {
        let src = ctx.ensure_in_reg(arg.value)?;
        arg_vregs.push(src);
    }

    // Phase 1b: handle SRET (structure return) by passing a hidden pointer
    // as the first argument (RDI) when the call's result is stored in a
    // stack slot (i.e., a large struct). The stack slot address is obtained
    // by ensuring the call result is in a register, which for stack slots
    // produces a LEA of the slot address.
    let has_sret = ctx.stack.get(vref).is_some();
    if has_sret {
        // The call returns a struct via a hidden pointer argument.
        // Ensure we have the address of the return slot.
        let ret_addr = ctx.ensure_in_reg(vref)?;
        // Insert as the first argument (always integer/pointer, never float).
        arg_vregs.insert(0, ret_addr);
    }

    // Phase 2: classify each arg as GPR, XMM, or stack per SysV x86-64 ABI.
    // Integer/pointer args use rdi, rsi, rdx, rcx, r8, r9 (then stack).
    // Float args (f32/f64) use xmm0..xmm7 (then stack).
    // The two register classes are independent.
    let sret_offset = if has_sret { 1 } else { 0 };
    let mut int_count = 0usize;
    let mut float_count = 0usize;

    #[derive(Clone, Copy)]
    enum ArgDest {
        Gpr(usize),
        Xmm {
            idx: usize,
            double: bool,
        },
        Stack,
        /// C ABI byval: the vreg holds a *pointer* to a struct that must be
        /// copied onto the call stack.  `size` is the byte count rounded up
        /// to the next multiple of 8.
        Byval {
            size: u32,
        },
    }

    let mut arg_dests: Vec<ArgDest> = Vec::new();
    let mut stack_arg_indices: Vec<usize> = Vec::new();

    for (i, src) in arg_vregs.iter().enumerate() {
        let _ = src;

        // Check for Byval annotation on this arg (C ABI MEMORY-class param).
        let byval_size = if i >= sret_offset {
            match &args[i - sret_offset].annotation {
                Some(Annotation::Byval(sz)) => Some(*sz),
                _ => None,
            }
        } else {
            None
        };

        if let Some(sz) = byval_size {
            // Byval args skip GPR allocation entirely; the struct goes
            // on the stack.  Round size up to eightbyte boundary.
            let rounded = sz.div_ceil(8) * 8;
            stack_arg_indices.push(i);
            arg_dests.push(ArgDest::Byval { size: rounded });
            continue;
        }

        let is_float = if i < sret_offset {
            false // SRET pointer is always integer
        } else {
            let arg_val = args[i - sret_offset].value;
            matches!(func.value_type(arg_val), Some(Type::Float(_)))
        };

        let dest = if is_float {
            let double = if i >= sret_offset {
                let arg_val = args[i - sret_offset].value;
                matches!(func.value_type(arg_val), Some(Type::Float(FloatType::F64)))
            } else {
                false
            };
            if float_count < MAX_XMM_ARGS {
                let idx = float_count;
                float_count += 1;
                ArgDest::Xmm { idx, double }
            } else {
                stack_arg_indices.push(i);
                ArgDest::Stack
            }
        } else {
            if int_count < ARG_REGS.len() {
                let idx = int_count;
                int_count += 1;
                ArgDest::Gpr(idx)
            } else {
                stack_arg_indices.push(i);
                ArgDest::Stack
            }
        };
        arg_dests.push(dest);
    }

    // Phase 3: push stack arguments right-to-left.
    // RSP must be 16-byte aligned before the call instruction.
    // Calculate total stack bytes: regular args = 8 each, byval = their size.
    let total_stack_bytes: i32 = stack_arg_indices
        .iter()
        .map(|&i| match arg_dests[i] {
            ArgDest::Byval { size } => size as i32,
            _ => 8,
        })
        .sum();
    let stack_cleanup = if total_stack_bytes > 0 {
        // Pad for 16-byte alignment.
        let padding = if total_stack_bytes % 16 != 0 {
            16 - (total_stack_bytes % 16)
        } else {
            0
        };
        if padding > 0 {
            ctx.out.push(MInst::SubSPI { imm: padding });
        }
        // Push in reverse order so first stack arg ends up at lowest address.
        for &i in stack_arg_indices.iter().rev() {
            match arg_dests[i] {
                ArgDest::Byval { size } => {
                    // Copy struct data from the pointer (in arg_vregs[i])
                    // onto the stack, qword by qword in reverse order.
                    let num_qwords = (size / 8) as i32;
                    let src_ptr = arg_vregs[i];
                    for q in (0..num_qwords).rev() {
                        let offset = q * 8;
                        // Load qword from [src_ptr + offset]
                        let tmp = ctx.alloc.alloc();
                        ctx.out.push(MInst::MovRM {
                            size: OpSize::S64,
                            dst: tmp,
                            base: src_ptr,
                            offset,
                        });
                        ctx.out.push(MInst::Push { reg: tmp });
                    }
                }
                _ => {
                    ctx.out.push(MInst::Push { reg: arg_vregs[i] });
                }
            }
        }
        total_stack_bytes + padding
    } else {
        0
    };

    // Phase 4: move register arguments to their fixed registers.
    for (i, dest) in arg_dests.iter().enumerate() {
        let src = arg_vregs[i];
        match *dest {
            ArgDest::Gpr(gpr_idx) => {
                let target_preg = ARG_REGS[gpr_idx].to_preg();
                let already_there =
                    ctx.alloc.constraints.get(src.0 as usize) == Some(&Some(target_preg));
                if !already_there {
                    let dst = ctx.alloc.alloc_fixed(target_preg);
                    ctx.out.push(MInst::MovRR {
                        size: OpSize::S64,
                        dst,
                        src,
                    });
                }
            }
            ArgDest::Xmm {
                idx: xmm_idx,
                double,
            } => {
                // Float arg: convert GPR bit-pattern → XMM register.
                // PReg(0x20 + n) encodes XMMn (register class 1).
                let xmm = ctx.alloc.alloc_fixed(PReg(0x20 + xmm_idx as u8));
                ctx.out.push(MInst::GprToXmm {
                    dst: xmm,
                    src,
                    double,
                });
            }
            ArgDest::Stack => {}        // already pushed in Phase 3
            ArgDest::Byval { .. } => {} // already pushed in Phase 3
        }
    }

    // Classify call ABI behavior in one place, then lower according to the plan.
    let abi = classify_call_abi(func, vref, call_has_ret2);
    // Detect SRET: if the call's primary result is allocated to a stack slot
    // (i.e., a large struct), the hidden pointer argument has already been
    // inserted as the first argument and the callee does not return a value
    // in RAX. In this case we suppress the primary return handling.
    let is_sret = ctx.stack.get(vref).is_some();

    // Detect float return: C ABI returns f32/f64 in XMM0, not RAX.
    // Our internal ABI keeps float values as bit-patterns in GPRs, so we
    // must read XMM0 and move the bits into a GPR after the call.
    let call_idx = vref.index();
    let return_float_type = func.inst(call_idx).secondary_ty.as_ref().and_then(|ty| {
        if let Type::Float(ft) = ty {
            Some(*ft)
        } else {
            None
        }
    });
    let return_is_float = return_float_type.is_some();
    let return_is_bool = matches!(func.inst(call_idx).secondary_ty, Some(Type::Bool));

    let ret_vreg = if abi.has_primary_return && !is_sret {
        if return_is_float {
            // XMM0 = class 1, register 0 → PReg(0x20)
            let xmm0 = ctx.alloc.alloc_fixed(PReg(0x20));
            Some(xmm0)
        } else {
            let rax = ctx.alloc.alloc_fixed(Gpr::Rax.to_preg());
            Some(rax)
        }
    } else {
        None
    };

    // If this call has a secondary return (RDX), allocate a fixed RDX vreg.
    let ret2_vreg = if abi.has_secondary_return {
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
            cleanup_label,
        });
    } else {
        // Indirect call through a register (e.g. virtual dispatch).
        let callee_vreg = ctx.ensure_in_reg(callee.value)?;
        ctx.out.push(MInst::CallReg {
            callee: callee_vreg,
            ret: ret_vreg,
            ret2: ret2_vreg,
            cleanup_label,
        });
    }

    // Copy return values from fixed registers to unconstrained vregs.
    // When both RAX and RDX are live for a wide integer return, use MovRR2 to
    // copy both as a single pseudo-instruction. This prevents the register
    // allocator from assigning one copy's destination to the other's source
    // register, which would clobber the value before it's read.
    match (ret_vreg, ret2_vreg) {
        (Some(rax), Some(rdx)) => {
            let dst_rax = ctx.alloc.alloc();
            let dst_rdx = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR2 {
                dst1: dst_rax,
                src1: rax,
                dst2: dst_rdx,
                src2: rdx,
            });
            ctx.rdx_captured.insert(vref.index(), dst_rdx);
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, dst_rax);
        }
        (Some(xmm_or_rax), None) if return_is_float => {
            // Float return: C ABI puts the value in XMM0. Move bits to GPR
            // to maintain our invariant that float values live in GPRs.
            let ft = return_float_type.unwrap();
            let double = matches!(ft, tuffy_ir::types::FloatType::F64);
            let gpr_dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MoveXmmToGpr {
                dst: gpr_dst,
                src: xmm_or_rax,
                double,
            });
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, gpr_dst);
        }
        (Some(rax), None) => {
            let dst = ctx.alloc.alloc();
            if return_is_bool {
                // Bool returns only define al; zero-extend to clear
                // upper bits that the callee may leave as garbage.
                ctx.out.push(MInst::MovzxB { dst, src: rax });
            } else {
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src: rax,
                });
            }
            let secondary = ValueRef::inst_secondary_result(vref.index());
            ctx.regs.assign(secondary, dst);
        }
        (None, Some(rdx)) => {
            let dst = ctx.alloc.alloc();
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src: rdx,
            });
            ctx.rdx_captured.insert(vref.index(), dst);
        }
        (None, None) => {}
    }

    // Clean up stack arguments after the call.
    if stack_cleanup > 0 {
        ctx.out.push(MInst::AddSPI { imm: stack_cleanup });
    }

    Some(())
}

/// Lower a `select` instruction.
fn select_select(
    ctx: &mut IselCtx,
    vref: ValueRef,
    cond: &Operand,
    tv: &Operand,
    fv: &Operand,
) -> Option<()> {
    // Pre-materialize the condition from flags into a register BEFORE calling
    // ensure_in_reg on tv/fv. Those calls may emit CmpRR instructions that
    // overwrite the condition flags, causing a stale-flag bug (e.g. in 128-bit
    // comparisons where hi_eq, lo_cmp, and hi_cmp are three separate ICmps).
    // By capturing the condition first we guarantee the TestRR+CMOVne below
    // reads the correct value.
    if ctx.cmps.get(cond.value).is_some() && ctx.regs.get(cond.value).is_none() {
        let cc = ctx.cmps.get(cond.value).unwrap();
        let tmp = ctx.alloc.alloc();
        ctx.out.push(MInst::SetCC { cc, dst: tmp });
        ctx.out.push(MInst::MovzxB { dst: tmp, src: tmp });
        ctx.regs.assign(cond.value, tmp);
    }
    let tv_vreg = ctx.ensure_in_reg(tv.value)?;
    let fv_vreg = ctx.ensure_in_reg(fv.value)?;
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR {
        size: OpSize::S64,
        dst,
        src: fv_vreg,
    });
    // Always use the register-based path. The flags-based path (cmps.get) is
    // unreliable here because ensure_in_reg calls above may have emitted
    // additional CmpRR instructions that overwrite the condition flags.
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
    ctx.regs.assign(vref, dst);
    Some(())
}

/// Lower a sign-extension instruction.
fn select_sext(ctx: &mut IselCtx, vref: ValueRef, val: &Operand, func: &Function) -> Option<()> {
    let src = ctx.ensure_in_reg(val.value)?;
    let dst = ctx.alloc.alloc();
    // Prefer operand's use-site annotation over the def-site annotation.
    let src_ann = val
        .annotation
        .as_ref()
        .and_then(|a| match a {
            Annotation::Int(ia) => Some(*ia),
            _ => None,
        })
        .or_else(|| get_int_annotation(func, val.value));
    match src_ann.map(|a| a.bit_width) {
        Some(8) => {
            ctx.out.push(MInst::MovsxB { dst, src });
        }
        Some(16) => {
            ctx.out.push(MInst::MovsxW { dst, src });
        }
        Some(32) => {
            ctx.out.push(MInst::MovsxD { dst, src });
        }
        Some(64) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
        }
        Some(n) => {
            // Non-standard bit width: check signedness
            let is_signed = src_ann
                .is_some_and(|a| matches!(a.signedness, tuffy_ir::types::IntSignedness::Signed));
            if is_signed {
                // Already signed, no extension needed
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src,
                });
            } else {
                // Unsigned source: use shift-based sign extension
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
        }
        None => {
            // No type information, default to 64-bit
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
                dst,
                src,
            });
        }
    }
    ctx.regs.assign(vref, dst);
    Some(())
}

/// Lower a zero-extension instruction.
fn select_zext(ctx: &mut IselCtx, vref: ValueRef, val: &Operand, func: &Function) -> Option<()> {
    let src = ctx.ensure_in_reg(val.value)?;
    let dst = ctx.alloc.alloc();
    // Prefer operand's use-site annotation over the def-site annotation.
    let src_ann = val
        .annotation
        .as_ref()
        .and_then(|a| match a {
            Annotation::Int(ia) => Some(*ia),
            _ => None,
        })
        .or_else(|| get_int_annotation(func, val.value));
    match src_ann.map(|a| a.bit_width) {
        Some(8) => {
            ctx.out.push(MInst::MovzxB { dst, src });
        }
        Some(16) => {
            ctx.out.push(MInst::MovzxW { dst, src });
        }
        Some(32) => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S32,
                dst,
                src,
            });
        }
        Some(n) => {
            // Non-standard bit width: check signedness
            let is_unsigned = src_ann
                .is_none_or(|a| matches!(a.signedness, tuffy_ir::types::IntSignedness::Unsigned));
            if is_unsigned || n >= 64 {
                // Already unsigned or full width, no masking needed
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src,
                });
            } else {
                // Signed source: mask to clear potential sign bits
                let mask = (1u64 << n) - 1;
                ctx.out.push(MInst::MovRR {
                    size: OpSize::S64,
                    dst,
                    src,
                });
                ctx.out.push(MInst::AndRI {
                    size: OpSize::S64,
                    dst,
                    imm: mask as i64,
                });
            }
        }
        None => {
            ctx.out.push(MInst::MovRR {
                size: OpSize::S64,
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
    /// Produce the quotient.
    Div,
    /// Produce the remainder.
    Rem,
}

/// Lower integer division and remainder instructions.
fn select_divrem(
    ctx: &mut IselCtx,
    vref: ValueRef,
    lhs: &Operand,
    rhs: &Operand,
    kind: DivRemKind,
    func: &Function,
) -> Option<()> {
    let mut lhs_vreg = ctx.ensure_in_reg(lhs.value)?;
    let mut rhs_vreg = ctx.ensure_in_reg(rhs.value)?;
    // Use the Div/Rem instruction's own annotation (which carries the
    // correct signedness from the frontend), not the LHS operand's
    // defining instruction (which may have DontCare or Unsigned).
    let inst_ann = get_int_annotation(func, vref);
    let signed = matches!(
        inst_ann,
        Some(IntAnnotation {
            signedness: IntSignedness::Signed,
            ..
        })
    );

    // For signed sub-64-bit division, sign-extend operands to 64 bits.
    // encode_divrem uses 64-bit idiv with CQO, which sign-extends based on
    // bit 63. Sub-64-bit negative values are zero-extended in registers
    // (e.g. -292i16 = 0x000000000000FEDC), so CQO sees them as positive.
    if signed {
        let bit_width = inst_ann.map(|a| a.bit_width).unwrap_or(64);
        if bit_width < 64 {
            let ext_lhs = ctx.alloc.alloc();
            let ext_rhs = ctx.alloc.alloc();
            match bit_width {
                8 => {
                    ctx.out.push(MInst::MovsxB {
                        dst: ext_lhs,
                        src: lhs_vreg,
                    });
                    ctx.out.push(MInst::MovsxB {
                        dst: ext_rhs,
                        src: rhs_vreg,
                    });
                }
                16 => {
                    ctx.out.push(MInst::MovsxW {
                        dst: ext_lhs,
                        src: lhs_vreg,
                    });
                    ctx.out.push(MInst::MovsxW {
                        dst: ext_rhs,
                        src: rhs_vreg,
                    });
                }
                32 => {
                    ctx.out.push(MInst::MovsxD {
                        dst: ext_lhs,
                        src: lhs_vreg,
                    });
                    ctx.out.push(MInst::MovsxD {
                        dst: ext_rhs,
                        src: rhs_vreg,
                    });
                }
                _ => {}
            }
            if bit_width <= 32 {
                lhs_vreg = ext_lhs;
                rhs_vreg = ext_rhs;
            }
        }
    }

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

/// Map an integer-compare predicate and annotation to an x86 condition code.
fn icmp_to_cc(op: ICmpOp, ann: Option<IntAnnotation>) -> CondCode {
    let signed = matches!(
        ann,
        Some(IntAnnotation {
            signedness: IntSignedness::Signed,
            ..
        })
    );
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

/// Lower a `memcopy` operation.
fn select_memcopy(
    ctx: &mut IselCtx,
    dst: &Operand,
    src: &Operand,
    count: &Operand,
    func: &Function,
) -> Option<()> {
    if let Some(bytes) = const_byte_count(func, count)
        && lower_small_memtransfer(ctx, dst, src, bytes).is_some()
    {
        return Some(());
    }
    emit_libc_call(ctx, "memcpy", &[dst, src, count])
}

/// Lower a `memmove` operation.
fn select_memmove(
    ctx: &mut IselCtx,
    dst: &Operand,
    src: &Operand,
    count: &Operand,
    func: &Function,
) -> Option<()> {
    if let Some(bytes) = const_byte_count(func, count)
        && lower_small_memtransfer(ctx, dst, src, bytes).is_some()
    {
        return Some(());
    }
    emit_libc_call(ctx, "memmove", &[dst, src, count])
}

/// Lower a `memset` operation.
fn select_memset(ctx: &mut IselCtx, dst: &Operand, val: &Operand, count: &Operand) -> Option<()> {
    emit_libc_call(ctx, "memset", &[dst, val, count])
}

/// Emit a helper call to a libc routine.
fn emit_libc_call(ctx: &mut IselCtx, name: &str, args: &[&Operand]) -> Option<()> {
    let arg_regs = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx];
    for (i, arg) in args.iter().enumerate() {
        let src = ctx.ensure_in_reg(arg.value)?;
        let dst = ctx.alloc.alloc_fixed(arg_regs[i].to_preg());
        ctx.out.push(MInst::MovRR {
            size: OpSize::S64,
            dst,
            src,
        });
    }
    ctx.out.push(MInst::CallSym {
        name: name.to_string(),
        ret: None,
        ret2: None,
        cleanup_label: None,
    });
    Some(())
}

#[derive(Clone, Copy)]
/// Decoded branch test used to lower `brif`.
enum BranchTest {
    /// Branch outcome is already known.
    Always(bool),
    /// Branch on the current flags register state.
    Flags(CondCode),
    /// Branch by testing a materialized integer value.
    Value {
        /// Register holding the tested value.
        reg: VReg,
        /// Operand size used by the emitted test instruction.
        size: OpSize,
    },
}

/// Emit the branch jump sequence for a decoded branch test.
fn emit_branch_jump(
    ctx: &mut IselCtx,
    branch_test: Option<BranchTest>,
    cond_value: ValueRef,
    target: u32,
    func: &Function,
) -> Option<()> {
    match branch_test.or_else(|| fallback_branch_test(ctx, cond_value, func))? {
        BranchTest::Always(true) => {
            ctx.out.push(MInst::Jmp { target });
        }
        BranchTest::Always(false) => {}
        BranchTest::Flags(cc) => {
            ctx.out.push(MInst::Jcc { cc, target });
        }
        BranchTest::Value { reg, size } => {
            ctx.out.push(MInst::TestRR {
                size,
                src1: reg,
                src2: reg,
            });
            ctx.out.push(MInst::Jcc {
                cc: CondCode::Ne,
                target,
            });
        }
    }
    Some(())
}

/// Build a fallback branch test when no flag-producing compare is available.
fn fallback_branch_test(
    ctx: &mut IselCtx,
    cond_value: ValueRef,
    func: &Function,
) -> Option<BranchTest> {
    if let Some(cc) = ctx.cmps.get(cond_value) {
        return Some(BranchTest::Flags(cc));
    }
    let size = if func.value_type(cond_value) == Some(&Type::Bool) {
        OpSize::S8
    } else {
        OpSize::S64
    };
    Some(BranchTest::Value {
        reg: ctx.ensure_in_reg(cond_value)?,
        size,
    })
}

/// Decode a value into a branch-test form when possible.
fn decode_branch_test(ctx: &mut IselCtx, func: &Function, value: ValueRef) -> Option<BranchTest> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::BConst(value) => Some(BranchTest::Always(*value)),
        Op::BXor(lhs, rhs) => {
            let lhs_bool = bool_const(func, lhs.clone().raw().value);
            let rhs_bool = bool_const(func, rhs.clone().raw().value);
            if lhs_bool == Some(true) {
                Some(invert_branch_test(decode_branch_test(
                    ctx,
                    func,
                    rhs.clone().raw().value,
                )?))
            } else if rhs_bool == Some(true) {
                Some(invert_branch_test(decode_branch_test(
                    ctx,
                    func,
                    lhs.clone().raw().value,
                )?))
            } else if lhs_bool == Some(false) {
                decode_branch_test(ctx, func, rhs.clone().raw().value)
            } else if rhs_bool == Some(false) {
                decode_branch_test(ctx, func, lhs.clone().raw().value)
            } else {
                None
            }
        }
        Op::Select(cond, true_value, false_value) => {
            let true_const = int_const(func, true_value.value)?;
            let false_const = int_const(func, false_value.value)?;
            if true_const == 1 && false_const == 0 {
                decode_branch_test(ctx, func, cond.clone().raw().value)
            } else if true_const == 0 && false_const == 1 {
                Some(invert_branch_test(decode_branch_test(
                    ctx,
                    func,
                    cond.clone().raw().value,
                )?))
            } else {
                None
            }
        }
        Op::And(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if int_const(func, lhs_value).is_some_and(is_non_negative_odd) {
                decode_branch_test(ctx, func, rhs_value)
            } else if int_const(func, rhs_value).is_some_and(is_non_negative_odd) {
                decode_branch_test(ctx, func, lhs_value)
            } else {
                None
            }
        }
        Op::Xor(lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if int_const(func, lhs_value) == Some(1) {
                Some(invert_branch_test(decode_branch_test(
                    ctx, func, rhs_value,
                )?))
            } else if int_const(func, rhs_value) == Some(1) {
                Some(invert_branch_test(decode_branch_test(
                    ctx, func, lhs_value,
                )?))
            } else {
                None
            }
        }
        Op::ICmp(pred, lhs, rhs) => {
            let lhs_value = lhs.clone().raw().value;
            let rhs_value = rhs.clone().raw().value;
            if let Some(constant) = int_const(func, rhs_value)
                && let Some(branch_test) = decode_intified_bool_compare(
                    ctx,
                    func,
                    *pred,
                    lhs.clone().raw().value,
                    constant,
                )
            {
                return Some(branch_test);
            }
            if let Some(constant) = int_const(func, lhs_value)
                && let Some(branch_test) = decode_intified_bool_compare(
                    ctx,
                    func,
                    flip_cmp_inputs(*pred),
                    rhs.clone().raw().value,
                    constant,
                )
            {
                return Some(branch_test);
            }
            let cc = emit_icmp_compare(ctx, func, *pred, &lhs.clone().raw(), &rhs.clone().raw())?;
            Some(BranchTest::Flags(cc))
        }
        _ => None,
    }
}

/// Decode compares whose boolean result has been intified.
fn decode_intified_bool_compare(
    ctx: &mut IselCtx,
    func: &Function,
    pred: ICmpOp,
    intified_value: ValueRef,
    compare_const: i64,
) -> Option<BranchTest> {
    if compare_const != 0 && compare_const != 1 {
        return None;
    }
    let branch_test = decode_branch_test(ctx, func, intified_value)?;
    match (pred, compare_const) {
        (ICmpOp::Eq, 0) | (ICmpOp::Ne, 1) => Some(invert_branch_test(branch_test)),
        (ICmpOp::Eq, 1) | (ICmpOp::Ne, 0) => Some(branch_test),
        _ => None,
    }
}

/// Invert a decoded branch test.
fn invert_branch_test(branch_test: BranchTest) -> BranchTest {
    match branch_test {
        BranchTest::Always(value) => BranchTest::Always(!value),
        BranchTest::Flags(cc) => BranchTest::Flags(invert_cc(cc)),
        BranchTest::Value { reg, size } => BranchTest::Value { reg, size },
    }
}

/// Invert an x86 condition code.
fn invert_cc(cc: CondCode) -> CondCode {
    match cc {
        CondCode::E => CondCode::Ne,
        CondCode::Ne => CondCode::E,
        CondCode::L => CondCode::Ge,
        CondCode::Le => CondCode::G,
        CondCode::G => CondCode::Le,
        CondCode::Ge => CondCode::L,
        CondCode::B => CondCode::Ae,
        CondCode::Be => CondCode::A,
        CondCode::A => CondCode::Be,
        CondCode::Ae => CondCode::B,
        CondCode::O => CondCode::No,
        CondCode::No => CondCode::O,
    }
}

/// Flip an integer-compare predicate when swapping operands.
fn flip_cmp_inputs(pred: ICmpOp) -> ICmpOp {
    match pred {
        ICmpOp::Eq => ICmpOp::Eq,
        ICmpOp::Ne => ICmpOp::Ne,
        ICmpOp::Lt => ICmpOp::Gt,
        ICmpOp::Le => ICmpOp::Ge,
        ICmpOp::Gt => ICmpOp::Lt,
        ICmpOp::Ge => ICmpOp::Le,
    }
}

/// Emit the compare instructions for an integer comparison.
fn emit_icmp_compare(
    ctx: &mut IselCtx,
    func: &Function,
    pred: ICmpOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<CondCode> {
    let lhs_reg = ctx.ensure_in_reg(lhs.value)?;
    let rhs_reg = ctx.ensure_in_reg(rhs.value)?;
    let cmp_size = operand_int_annotation(func, lhs)
        .or_else(|| operand_int_annotation(func, rhs))
        .map(|ann| match ann.bit_width {
            8 => OpSize::S8,
            16 => OpSize::S16,
            32 => OpSize::S32,
            _ => OpSize::S64,
        })
        .unwrap_or(OpSize::S64);
    ctx.out.push(MInst::CmpRR {
        size: cmp_size,
        src1: lhs_reg,
        src2: rhs_reg,
    });
    Some(icmp_to_cc(
        pred,
        operand_int_annotation(func, lhs).or_else(|| operand_int_annotation(func, rhs)),
    ))
}

/// Look up the integer annotation carried by an operand.
fn operand_int_annotation(func: &Function, operand: &Operand) -> Option<IntAnnotation> {
    operand
        .annotation
        .as_ref()
        .and_then(|annotation| match annotation {
            Annotation::Int(ann) => Some(*ann),
            _ => None,
        })
        .or_else(|| get_int_annotation(func, operand.value))
}

/// Resolve an integer operand to a constant byte count when possible.
fn const_byte_count(func: &Function, operand: &Operand) -> Option<u32> {
    int_const(func, operand.value).and_then(|constant| u32::try_from(constant).ok())
}

/// Inline a small fixed-size memory transfer.
fn lower_small_memtransfer(
    ctx: &mut IselCtx,
    dst: &Operand,
    src: &Operand,
    bytes: u32,
) -> Option<()> {
    if bytes == 0 {
        return Some(());
    }
    if bytes > 16 {
        return None;
    }

    let dst_reg = ctx.ensure_in_reg(dst.value)?;
    let src_reg = ctx.ensure_in_reg(src.value)?;
    if bytes <= 8 {
        let tmp = ctx.alloc.alloc();
        emit_partial_load(ctx, src_reg, 0, tmp, bytes);
        emit_partial_store(ctx, dst_reg, 0, tmp, bytes);
        return Some(());
    }

    let lo = ctx.alloc.alloc();
    let hi = ctx.alloc.alloc();
    emit_partial_load(ctx, src_reg, 0, lo, 8);
    emit_partial_load(ctx, src_reg, 8, hi, bytes - 8);
    emit_partial_store(ctx, dst_reg, 0, lo, 8);
    emit_partial_store(ctx, dst_reg, 8, hi, bytes - 8);
    Some(())
}

/// Resolve a value to a constant integer when possible.
fn int_const(func: &Function, value: ValueRef) -> Option<i64> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    let Op::Const(constant) = &node.inst.op else {
        return None;
    };
    constant.to_i64()
}

/// Return whether a small integer constant can stay deferred until a non-immediate use appears.
fn int_const_can_stay_deferred(func: &Function, value: ValueRef, imm: i64) -> bool {
    if func.use_count(value) == 0 {
        return true;
    }
    func.uses_of(value).all(|use_node| {
        int_const_use_is_immediate_compatible(func, use_node.user, use_node.operand_index, imm)
    })
}

/// Return whether one use site can consume an integer constant without materializing a register.
fn int_const_use_is_immediate_compatible(
    func: &Function,
    user: u32,
    operand_index: u32,
    imm: i64,
) -> bool {
    let Some(node) = func.inst_pool.get(user) else {
        return false;
    };
    match &node.inst.op {
        Op::Shl(_, _) | Op::Shr(_, _) => operand_index == 1 && (0..=63).contains(&imm),
        Op::PtrAdd(_, _) => operand_index == 1 && i32::try_from(imm).is_ok(),
        Op::MemCopy(..) | Op::MemMove(..) | Op::MemSet(..) => {
            operand_index == 2 && u32::try_from(imm).is_ok()
        }
        _ => false,
    }
}

/// Return whether a value is only used as operand 1 of `ptradd`.
fn value_only_used_by_ptradd_offset(func: &Function, value: ValueRef) -> bool {
    func.use_count(value) > 0
        && func.uses_of(value).all(|use_node| {
            use_node.operand_index == 1
                && func
                    .inst_pool
                    .get(use_node.user)
                    .is_some_and(|node| matches!(node.inst.op, Op::PtrAdd(_, _)))
        })
}

/// Resolve a multiplication into an x86 scaled-index pair when possible.
fn mul_scale_operands(
    func: &Function,
    lhs: &tuffy_ir::typed::IntOperand,
    rhs: &tuffy_ir::typed::IntOperand,
) -> Option<(ValueRef, u8)> {
    let lhs_value = lhs.clone().raw().value;
    let rhs_value = rhs.clone().raw().value;
    let lhs_const = int_const(func, lhs_value);
    let rhs_const = int_const(func, rhs_value);
    let (index, factor) = match (lhs_const, rhs_const) {
        (Some(factor), None) => (rhs_value, factor),
        (None, Some(factor)) => (lhs_value, factor),
        _ => return None,
    };
    let scale = match factor {
        1 => 1,
        2 => 2,
        4 => 4,
        8 => 8,
        _ => return None,
    };
    Some((index, scale))
}

/// Resolve a value to a constant boolean when possible.
fn bool_const(func: &Function, value: ValueRef) -> Option<bool> {
    if value.is_block_arg() || value.is_secondary_result() {
        return None;
    }
    let node = func.inst_pool.get(value.index())?;
    match &node.inst.op {
        Op::BConst(value) => Some(*value),
        _ => None,
    }
}

/// Return whether an integer is non-negative and odd.
fn is_non_negative_odd(value: i64) -> bool {
    value >= 0 && value & 1 == 1
}
