//! Intrinsic handling for MIR → IR translation.

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty::{self, Instance, TyCtxt};

use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::{ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::LocalMap;
use super::types::{type_align, type_size};

/// Handle compiler intrinsics inline during MIR translation.
/// Returns true if the intrinsic was handled, false to fall through to normal call.
#[allow(clippy::too_many_arguments)]
pub(super) fn translate_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ir_args: &[ValueRef],
    destination_local: mir::Local,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    symbols: &mut SymbolTable,
    current_mem: ValueRef,
    _dest_override: Option<ValueRef>,
) -> bool {
    // Helper: coerce an Int value to Ptr (needed when NonNull<T> or similar
    // #[repr(transparent)] pointer wrappers are loaded as Int).
    let ensure_ptr = |builder: &mut Builder<'_>, val: ValueRef| -> ValueRef {
        if matches!(builder.value_type(val), Some(Type::Int)) {
            builder.inttoptr(val.into(), 0, Origin::synthetic())
        } else {
            val
        }
    };

    match name {
        // black_box: identity function, prevents optimizations.
        // Just copy the argument to the destination.
        "black_box" => {
            if let Some(&v) = ir_args.first() {
                locals.set(destination_local, v);
            }
            true
        }

        // assume: optimizer hint, no runtime effect. Treat as no-op.
        "assume" => true,

        // assert_inhabited / assert_zero_valid / assert_mem_uninitialized_valid:
        // compile-time checks, no runtime effect.
        "assert_inhabited" | "assert_zero_valid" | "assert_mem_uninitialized_valid" => true,

        // ctpop: population count (count set bits).
        "ctpop" => {
            if let Some(&v) = ir_args.first() {
                let result = builder.count_ones(v.into(), Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // ctlz / ctlz_nonzero: count leading zeros.
        "ctlz" | "ctlz_nonzero" => {
            if let Some(&v) = ir_args.first() {
                let bits = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .map(|sz| (sz * 8) as u32)
                    .unwrap_or(64);
                let result = builder.count_leading_zeros(v.into(), bits, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // cttz / cttz_nonzero: count trailing zeros.
        "cttz" | "cttz_nonzero" => {
            if let Some(&v) = ir_args.first() {
                let result = builder.count_trailing_zeros(v.into(), Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // bswap: byte-swap an integer value.
        "bswap" => {
            if let Some(&v) = ir_args.first() {
                let byte_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .unwrap_or(8);
                if byte_size <= 1 {
                    locals.set(destination_local, v);
                } else {
                    let result =
                        builder.bswap(v.into(), byte_size as u32, Origin::synthetic());
                    locals.set(destination_local, result);
                }
            }
            true
        }

        // bitreverse: reverse bit order of an integer value.
        "bitreverse" => {
            if let Some(&v) = ir_args.first() {
                let bit_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .map(|sz| (sz * 8) as u32)
                    .unwrap_or(64);
                if bit_size <= 1 {
                    locals.set(destination_local, v);
                } else {
                    let result =
                        builder.bit_reverse(v.into(), bit_size, Origin::synthetic());
                    locals.set(destination_local, result);
                }
            }
            true
        }

        // rotate_left / rotate_right: bitwise rotation.
        "rotate_left" | "rotate_right" => {
            if ir_args.len() >= 2 {
                let x = ir_args[0];
                let n = ir_args[1];
                let bits = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .map(|sz| (sz * 8) as u32)
                    .unwrap_or(64);
                let result = if name == "rotate_left" {
                    builder.rotate_left(x.into(), n.into(), bits, Origin::synthetic())
                } else {
                    builder.rotate_right(x.into(), n.into(), bits, Origin::synthetic())
                };
                locals.set(destination_local, result);
            }
            true
        }

        // is_val_statically_known: always false in a non-optimizing backend.
        "is_val_statically_known" => {
            let result = builder.bconst(false, Origin::synthetic());
            locals.set(destination_local, result);
            true
        }

        // size_of<T>: return the size of type T as a compile-time constant.
        "size_of" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                let sz = type_size(tcx, t).unwrap_or(0);
                let result = builder.iconst(sz as i64, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // min_align_of / align_of: return the alignment of type T.
        "min_align_of" | "pref_align_of" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                let align = type_align(tcx, t).unwrap_or(1);
                let result = builder.iconst(align as i64, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // size_of_val: return the size of the pointed-to type.
        // For sized types this is a compile-time constant.
        // For unsized types (slices), compute len * elem_size at runtime.
        "size_of_val" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                // Check if the type is unsized first — type_size returns
                // Some(0) for unsized types like [T] (zero-element slice),
                // so we can't rely on type_size alone.
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let tail = tcx.struct_tail_for_codegen(t, typing_env);
                if matches!(tail.kind(), ty::Slice(..) | ty::Str | ty::Dynamic(..)) {
                    // Unsized type: compute size at runtime from metadata.
                    if let ty::Slice(elem_ty) = tail.kind() {
                        let elem_sz = type_size(tcx, *elem_ty).unwrap_or(0);
                        if ir_args.len() >= 2 {
                            let len = ir_args[1];
                            if elem_sz == 1 {
                                locals.set(destination_local, len);
                            } else {
                                let esz = builder.iconst(elem_sz as i64, Origin::synthetic());
                                let result =
                                    builder.mul(len.into(), esz.into(), None, Origin::synthetic());
                                locals.set(destination_local, result);
                            }
                        } else {
                            let result = builder.iconst(0, Origin::synthetic());
                            locals.set(destination_local, result);
                        }
                    } else {
                        // str: size = len (metadata is byte length).
                        if let ty::Str = tail.kind() {
                            if ir_args.len() >= 2 {
                                locals.set(destination_local, ir_args[1]);
                            } else {
                                let result = builder.iconst(0, Origin::synthetic());
                                locals.set(destination_local, result);
                            }
                        } else {
                            // dyn Trait: read size from vtable (fallback to 0 for now).
                            let result = builder.iconst(0, Origin::synthetic());
                            locals.set(destination_local, result);
                        }
                    }
                } else if let Some(sz) = type_size(tcx, t) {
                    // Sized type: compile-time constant.
                    let result = builder.iconst(sz as i64, Origin::synthetic());
                    locals.set(destination_local, result);
                } else {
                    let result = builder.iconst(0, Origin::synthetic());
                    locals.set(destination_local, result);
                }
            }
            true
        }

        // min_align_of_val / align_of_val: return the alignment of the type.
        "min_align_of_val" | "align_of_val" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                let align = type_align(tcx, t).unwrap_or(1);
                let result = builder.iconst(align as i64, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // arith_offset<T>(ptr, offset) → ptr + offset * sizeof(T)
        "arith_offset" => {
            if ir_args.len() >= 2 {
                let ptr = ensure_ptr(builder, ir_args[0]);
                let offset = ir_args[1];
                let elem_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .unwrap_or(1);
                let byte_offset = if elem_size == 1 {
                    offset
                } else {
                    let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                    builder.mul(offset.into(), sz.into(), None, Origin::synthetic())
                };
                let result = builder.ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // ptr_offset_from_unsigned<T>(ptr1, ptr2) → (ptr1 - ptr2) / sizeof(T)
        "ptr_offset_from_unsigned" | "ptr_offset_from" => {
            if ir_args.len() >= 2 {
                let ptr1 = ensure_ptr(builder, ir_args[0]);
                let ptr2 = ensure_ptr(builder, ir_args[1]);
                let diff = builder.ptrdiff(ptr1.into(), ptr2.into(), Origin::synthetic());
                let elem_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .unwrap_or(1);
                let result = if elem_size <= 1 {
                    diff
                } else {
                    let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                    builder.div(diff.into(), sz.into(), None, Origin::synthetic())
                };
                locals.set(destination_local, result);
            }
            true
        }

        // saturating_add<T>(a, b): add with saturation at max value.
        "saturating_add" => {
            if ir_args.len() >= 2 {
                let bits = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .map(|sz| (sz * 8) as u32)
                    .unwrap_or(64);
                let result = builder.saturating_add(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    bits,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }

        // saturating_sub<T>(a, b): subtract with saturation at zero.
        "saturating_sub" => {
            if ir_args.len() >= 2 {
                let bits = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .map(|sz| (sz * 8) as u32)
                    .unwrap_or(64);
                let result = builder.saturating_sub(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    bits,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }

        // abort: call libc abort().
        "abort" => {
            let sym_id = symbols.intern("abort");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            builder.call(
                callee.into(),
                vec![],
                Type::Unit,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            true
        }

        // unchecked arithmetic: same as wrapping ops (no overflow check).
        "unchecked_add" => {
            if ir_args.len() >= 2 {
                let result = builder.add(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    None,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }
        "unchecked_sub" => {
            if ir_args.len() >= 2 {
                let result = builder.sub(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    None,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }
        "unchecked_mul" => {
            if ir_args.len() >= 2 {
                let result = builder.mul(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    None,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }
        "unchecked_shl" => {
            if ir_args.len() >= 2 {
                let result = builder.shl(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    None,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }
        "unchecked_shr" => {
            if ir_args.len() >= 2 {
                let result = builder.shr(
                    ir_args[0].into(),
                    ir_args[1].into(),
                    None,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }

        // Unhandled intrinsics must be reported.
        _ => unimplemented!("MIR intrinsic: {}", name),
    }
}

/// Lower memory intrinsics to libc calls with adjusted arguments.
/// Handles write_bytes, copy_nonoverlapping, copy, and raw_eq.
/// Returns `Some(new_mem)` if the intrinsic was handled, `None` to fall through.
#[allow(clippy::too_many_arguments)]
pub(super) fn translate_memory_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ir_args: &[ValueRef],
    destination_local: mir::Local,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    symbols: &mut SymbolTable,
    current_mem: ValueRef,
) -> Option<ValueRef> {
    // Extract the type parameter T and compute its size.
    let elem_size = match substs.first().and_then(|a| a.as_type()) {
        Some(t) => type_size(tcx, t).unwrap_or(0),
        None => return None,
    };

    match name {
        // write_bytes<T>(dst, val, count) → memset(dst, val, count * sizeof(T))
        "write_bytes" | "volatile_set_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let dst = ir_args[0];
            let val = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            let sym_id = symbols.intern("memset");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), val.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // copy_nonoverlapping<T>(src, dst, count) → memcpy(dst, src, count * sizeof(T))
        "copy_nonoverlapping" | "volatile_copy_nonoverlapping_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let src = ir_args[0];
            let dst = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            // memcpy(dst, src, n) — note swapped argument order.
            let sym_id = symbols.intern("memcpy");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), src.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // copy<T>(src, dst, count) → memmove(dst, src, count * sizeof(T))
        "copy" | "volatile_copy_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let src = ir_args[0];
            let dst = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            let sym_id = symbols.intern("memmove");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), src.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // raw_eq<T>(a, b) → memcmp(a, b, sizeof(T)) == 0
        "raw_eq" => {
            if ir_args.len() < 2 {
                return None;
            }
            let a = ir_args[0];
            let b = ir_args[1];
            let sz = builder.iconst(elem_size as i64, Origin::synthetic());
            let sym_id = symbols.intern("memcmp");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![a.into(), b.into(), sz.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            // raw_eq returns bool (0 or 1): true when memcmp returns 0.
            let cmp_result = data.unwrap_or_else(|| builder.iconst(0, Origin::synthetic()));
            let zero = builder.iconst(0, Origin::synthetic());
            let eq = builder.icmp(
                tuffy_ir::instruction::ICmpOp::Eq,
                cmp_result.into(),
                zero.into(),
                Origin::synthetic(),
            );
            locals.set(destination_local, eq);
            Some(mem_out)
        }

        // typed_swap_nonoverlapping<T>(x, y) — swap values at two pointers.
        "typed_swap_nonoverlapping" => {
            if ir_args.len() < 2 {
                return None;
            }
            let x = if matches!(builder.value_type(ir_args[0]), Some(Type::Int)) {
                builder.inttoptr(ir_args[0].into(), 0, Origin::synthetic())
            } else {
                ir_args[0]
            };
            let y = if matches!(builder.value_type(ir_args[1]), Some(Type::Int)) {
                builder.inttoptr(ir_args[1].into(), 0, Origin::synthetic())
            } else {
                ir_args[1]
            };
            let mut mem = current_mem;
            let num_words = (elem_size as u64).div_ceil(8);
            for i in 0..num_words {
                let off = i * 8;
                let chunk = std::cmp::min(8, elem_size as u64 - off) as u32;
                let (xa, ya) = if off == 0 {
                    (x, y)
                } else {
                    let o = builder.iconst(off as i64, Origin::synthetic());
                    (
                        builder.ptradd(x.into(), o.into(), 0, Origin::synthetic()),
                        builder.ptradd(y.into(), o.into(), 0, Origin::synthetic()),
                    )
                };
                let vx = builder.load(
                    xa.into(),
                    chunk,
                    Type::Int,
                    mem.into(),
                    None,
                    Origin::synthetic(),
                );
                let vy = builder.load(
                    ya.into(),
                    chunk,
                    Type::Int,
                    mem.into(),
                    None,
                    Origin::synthetic(),
                );
                mem = builder.store(vy.into(), xa.into(), chunk, mem.into(), Origin::synthetic());
                mem = builder.store(vx.into(), ya.into(), chunk, mem.into(), Origin::synthetic());
            }
            Some(mem)
        }

        // ── Atomic intrinsics ──────────────────────────────────────────
        // For single-threaded programs all atomics reduce to plain
        // loads / stores / read-modify-write sequences.

        // atomic_load_relaxed, atomic_load_acquire, atomic_load_seqcst
        _ if name.starts_with("atomic_load") => {
            if ir_args.is_empty() {
                return None;
            }
            let ptr = ir_args[0];
            let size = elem_size as u32;
            let val = builder.load(
                ptr.into(),
                size,
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            locals.set(destination_local, val);
            Some(current_mem)
        }

        // atomic_store_relaxed, atomic_store_release, atomic_store_seqcst
        _ if name.starts_with("atomic_store") => {
            if ir_args.len() < 2 {
                return None;
            }
            let ptr = ir_args[0];
            let val = ir_args[1];
            let size = elem_size as u32;
            let new_mem = builder.store(
                val.into(),
                ptr.into(),
                size,
                current_mem.into(),
                Origin::synthetic(),
            );
            Some(new_mem)
        }

        // atomic_cxchg_*, atomic_cxchgweak_* → (old_val, success: bool)
        _ if name.starts_with("atomic_cxchg") => {
            if ir_args.len() < 3 {
                return None;
            }
            let ptr = ir_args[0];
            let expected = ir_args[1];
            let new_val = ir_args[2];
            let size = elem_size as u32;

            // Load current value.
            let old = builder.load(
                ptr.into(),
                size,
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );

            // Compare old == expected.
            let eq = builder.icmp(
                tuffy_ir::instruction::ICmpOp::Eq,
                old.into(),
                expected.into(),
                Origin::synthetic(),
            );

            // Conditionally store: new_val if equal, else old (no-op store).
            let store_val = builder.select(
                eq.into(),
                new_val.into(),
                old.into(),
                Type::Int,
                Origin::synthetic(),
            );
            let new_mem = builder.store(
                store_val.into(),
                ptr.into(),
                size,
                current_mem.into(),
                Origin::synthetic(),
            );

            // Write (old, eq) into the destination stack slot.
            if let Some(slot) = locals.get(destination_local) {
                let mem2 = builder.store(
                    old.into(),
                    slot.into(),
                    size,
                    new_mem.into(),
                    Origin::synthetic(),
                );
                let bool_off = builder.iconst(elem_size as i64, Origin::synthetic());
                let bool_ptr = builder.ptradd(slot.into(), bool_off.into(), 0, Origin::synthetic());
                let mem3 = builder.store(
                    eq.into(),
                    bool_ptr.into(),
                    1,
                    mem2.into(),
                    Origin::synthetic(),
                );
                Some(mem3)
            } else {
                // Destination not yet allocated — just set the scalar
                // (field projection will handle it like checked ops).
                locals.set(destination_local, old);
                Some(new_mem)
            }
        }

        // atomic_xchg_* → returns old value
        _ if name.starts_with("atomic_xchg") => {
            if ir_args.len() < 2 {
                return None;
            }
            let ptr = ir_args[0];
            let new_val = ir_args[1];
            let size = elem_size as u32;
            let old = builder.load(
                ptr.into(),
                size,
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            let new_mem = builder.store(
                new_val.into(),
                ptr.into(),
                size,
                current_mem.into(),
                Origin::synthetic(),
            );
            locals.set(destination_local, old);
            Some(new_mem)
        }

        // atomic_fence_*, atomic_singlethreadfence_* → no-op
        _ if name.starts_with("atomic_fence") || name.starts_with("atomic_singlethreadfence") => {
            Some(current_mem)
        }

        // Read-modify-write: atomic_{and,or,xor,nand,xadd,xsub,
        //                     max,min,umax,umin}_*
        // All return the OLD value.
        _ if name.starts_with("atomic_and")
            || name.starts_with("atomic_or")
            || name.starts_with("atomic_xor")
            || name.starts_with("atomic_nand")
            || name.starts_with("atomic_xadd")
            || name.starts_with("atomic_xsub")
            || name.starts_with("atomic_max")
            || name.starts_with("atomic_min")
            || name.starts_with("atomic_umax")
            || name.starts_with("atomic_umin") =>
        {
            if ir_args.len() < 2 {
                return None;
            }
            let ptr = ir_args[0];
            let operand = ir_args[1];
            let size = elem_size as u32;

            let old = builder.load(
                ptr.into(),
                size,
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );

            // Compute new value based on the operation.
            let new_val = if name.starts_with("atomic_and") {
                builder.and(old.into(), operand.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_or") {
                builder.or(old.into(), operand.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_xor") {
                builder.xor(old.into(), operand.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_nand") {
                let a = builder.and(old.into(), operand.into(), None, Origin::synthetic());
                let all_ones = builder.iconst(-1, Origin::synthetic());
                builder.xor(a.into(), all_ones.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_xadd") {
                builder.add(old.into(), operand.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_xsub") {
                builder.sub(old.into(), operand.into(), None, Origin::synthetic())
            } else if name.starts_with("atomic_umax") {
                let bits = (elem_size * 8) as u32;
                let gt = builder.icmp(
                    ICmpOp::Gt,
                    IrOperand::annotated(old, Annotation::Unsigned(bits)),
                    IrOperand::annotated(operand, Annotation::Unsigned(bits)),
                    Origin::synthetic(),
                );
                builder.select(
                    gt.into(),
                    old.into(),
                    operand.into(),
                    Type::Int,
                    Origin::synthetic(),
                )
            } else if name.starts_with("atomic_umin") {
                let bits = (elem_size * 8) as u32;
                let lt = builder.icmp(
                    ICmpOp::Lt,
                    IrOperand::annotated(old, Annotation::Unsigned(bits)),
                    IrOperand::annotated(operand, Annotation::Unsigned(bits)),
                    Origin::synthetic(),
                );
                builder.select(
                    lt.into(),
                    old.into(),
                    operand.into(),
                    Type::Int,
                    Origin::synthetic(),
                )
            } else if name.starts_with("atomic_max") {
                let bits = (elem_size * 8) as u32;
                let gt = builder.icmp(
                    ICmpOp::Gt,
                    IrOperand::annotated(old, Annotation::Signed(bits)),
                    IrOperand::annotated(operand, Annotation::Signed(bits)),
                    Origin::synthetic(),
                );
                builder.select(
                    gt.into(),
                    old.into(),
                    operand.into(),
                    Type::Int,
                    Origin::synthetic(),
                )
            } else {
                // atomic_min
                let bits = (elem_size * 8) as u32;
                let lt = builder.icmp(
                    ICmpOp::Lt,
                    IrOperand::annotated(old, Annotation::Signed(bits)),
                    IrOperand::annotated(operand, Annotation::Signed(bits)),
                    Origin::synthetic(),
                );
                builder.select(
                    lt.into(),
                    old.into(),
                    operand.into(),
                    Type::Int,
                    Origin::synthetic(),
                )
            };

            let new_mem = builder.store(
                new_val.into(),
                ptr.into(),
                size,
                current_mem.into(),
                Origin::synthetic(),
            );
            locals.set(destination_local, old);
            Some(new_mem)
        }

        _ => unimplemented!("MIR memory intrinsic: {}", name),
    }
}

/// Check if a Call terminator's callee is a known intrinsic.
/// Returns the intrinsic name and the generic args (for extracting type parameters).
pub(super) fn detect_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_op: &Operand<'tcx>,
    caller: Instance<'tcx>,
) -> Option<(String, &'tcx ty::List<ty::GenericArg<'tcx>>)> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        _ => return None,
    };
    let ty = tcx.instantiate_and_normalize_erasing_regions(
        caller.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(ty),
    );
    if let ty::FnDef(def_id, args) = ty.kind()
        && let Some(intrinsic) = tcx.intrinsic(*def_id)
    {
        return Some((intrinsic.name.as_str().to_string(), args));
    }
    None
}

/// Map compiler intrinsics to libc/compiler-rt symbol names.
/// Returns None for intrinsics that need inline handling or aren't supported.
pub(super) fn intrinsic_to_libc(name: &str) -> Option<&'static str> {
    match name {
        // compare_bytes(left, right, count) -> i32 maps directly to memcmp.
        "compare_bytes" => Some("memcmp"),
        _ => None,
    }
}
