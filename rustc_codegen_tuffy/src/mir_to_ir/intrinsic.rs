//! Intrinsic handling for MIR → IR translation.

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty;

use tuffy_ir::instruction::{AtomicRmwOp, FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{
    Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, MemoryOrdering, Type,
};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::int_annotation_for_bytes;
use super::types::{int_ann_for_bytes, is_signed_int, translate_annotation, type_align, type_size};

const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

/// Parse memory ordering from atomic intrinsic name suffix.
fn parse_atomic_ordering(name: &str) -> MemoryOrdering {
    if name.ends_with("_relaxed") {
        MemoryOrdering::Relaxed
    } else if name.ends_with("_acquire") {
        MemoryOrdering::Acquire
    } else if name.ends_with("_release") {
        MemoryOrdering::Release
    } else if name.ends_with("_acqrel") {
        MemoryOrdering::AcqRel
    } else {
        MemoryOrdering::SeqCst
    }
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Handle compiler intrinsics inline during MIR translation.
    /// Returns `true` if the intrinsic was handled, `false` to fall through to normal call.
    pub(super) fn translate_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        _dest_override: Option<ValueRef>,
    ) -> bool {
        let tcx = self.tcx;

        match name {
            // black_box: identity function, prevents optimizations.
            // Just copy the argument to the destination.
            "black_box" => {
                if let Some(&v) = ir_args.first() {
                    self.locals.set(destination_local, v);
                }
                // For fat pointer args the arg loader pushes a second
                // element (the metadata).  Propagate it so that the
                // ScalarPair survives the identity operation.
                if ir_args.len() >= 2 {
                    self.fat_locals.set(destination_local, ir_args[1]);
                }
                true
            }

            // transmute: bitwise reinterpretation. The intrinsic arg loader
            // already loaded the value from memory, so just copy it.
            "transmute" => {
                if let Some(&v) = ir_args.first() {
                    self.locals.set(destination_local, v);
                }
                true
            }

            // assume / cold_path: optimizer hints, no runtime effect. Treat as no-ops.
            "assume" | "cold_path" => true,

            // disjoint_bitor: bitwise OR with the hint that operands have
            // no overlapping bits.  Semantically just OR.
            "disjoint_bitor" => {
                if ir_args.len() >= 2 {
                    let mut a = ir_args[0];
                    let mut b = ir_args[1];
                    let ann = substs
                        .types()
                        .next()
                        .and_then(|t| translate_annotation(t))
                        .and_then(|a| match a {
                            Annotation::Int(ia) => Some(ia),
                            _ => None,
                        })
                        .unwrap_or(IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::DontCare,
                        });
                    // Bool-typed values (e.g. overflow flags) must be widened
                    // to Int before the bitwise OR.
                    if matches!(self.builder.value_type(a), Some(Type::Bool)) {
                        a = self
                            .builder
                            .zext(a.into(), ann.bit_width, Origin::synthetic())
                            .raw();
                    }
                    if matches!(self.builder.value_type(b), Some(Type::Bool)) {
                        b = self
                            .builder
                            .zext(b.into(), ann.bit_width, Origin::synthetic())
                            .raw();
                    }
                    let result = self
                        .builder
                        .or(a.into(), b.into(), ann, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // select_unpredictable: branchless conditional select.
            // Equivalent to `if cond { true_val } else { false_val }`.
            "select_unpredictable" => {
                if ir_args.len() >= 3 {
                    let cond = ir_args[0];
                    let true_val = ir_args[1];
                    let false_val = ir_args[2];

                    // cond may be Bool or Int — normalise to Bool.
                    let cond_bool = if matches!(self.builder.value_type(cond), Some(Type::Bool)) {
                        cond
                    } else {
                        let cond_int = self.coerce_to_int(cond);
                        let zero = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .icmp(
                                ICmpOp::Ne,
                                cond_int.into(),
                                zero.into(),
                                Origin::synthetic(),
                            )
                            .raw()
                    };

                    let result_ty = self
                        .builder
                        .value_type(true_val)
                        .cloned()
                        .unwrap_or(Type::Ptr(0));
                    // Derive annotation: use the generic type param T first,
                    // falling back to byte-width annotation when T is a pointer
                    // or otherwise unannotated.
                    let ann = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| translate_annotation(t))
                        .or_else(|| {
                            if matches!(result_ty, Type::Int) {
                                int_annotation_for_bytes(8)
                            } else {
                                None
                            }
                        });
                    let result = self.builder.select(
                        cond_bool.into(),
                        true_val.into(),
                        false_val.into(),
                        result_ty,
                        ann,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result);
                }
                true
            }

            // assert_inhabited / assert_zero_valid / assert_mem_uninitialized_valid:
            // compile-time checks, no runtime effect.
            "assert_inhabited" | "assert_zero_valid" | "assert_mem_uninitialized_valid" => true,

            // caller_location: returns the implicit &Location parameter
            // received by the enclosing #[track_caller] function.
            "caller_location" => {
                let loc = self.caller_location_param.unwrap_or_else(|| {
                    self.make_caller_location(mir::SourceInfo::outermost(self.mir.span))
                });
                self.locals.set(destination_local, loc);
                true
            }

            // ctpop: population count (count set bits).
            // Bit manipulation intrinsics (ctpop, ctlz, cttz, bswap, bitreverse, rotate).
            "ctpop" | "ctlz" | "ctlz_nonzero" | "cttz" | "cttz_nonzero" | "bswap"
            | "bitreverse" | "rotate_left" | "rotate_right"
                if let Some(result) =
                    self.translate_bit_intrinsic(name, substs, ir_args, destination_local) =>
            {
                result
            }

            // is_val_statically_known: always false in a non-optimizing backend.
            "is_val_statically_known" => {
                let result = self.builder.bconst(false, Origin::synthetic());
                self.locals.set(destination_local, result.raw());
                true
            }

            // size_of<T>: return the size of type T as a compile-time constant.
            "size_of" => {
                if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                    let sz = type_size(tcx, t).unwrap_or(0);
                    let result = self.builder.iconst(
                        sz as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // min_align_of / align_of: return the alignment of type T.
            "min_align_of" | "pref_align_of" => {
                if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                    let align = type_align(tcx, t).unwrap_or(1);
                    let result = self.builder.iconst(
                        align as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
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
                    let tail = self.tcx.struct_tail_for_codegen(t, typing_env);
                    if matches!(tail.kind(), ty::Slice(..) | ty::Str | ty::Dynamic(..)) {
                        // Unsized type: compute size at runtime from metadata.
                        if let ty::Slice(elem_ty) = tail.kind() {
                            let elem_sz = type_size(tcx, *elem_ty).unwrap_or(0);
                            if ir_args.len() >= 2 {
                                let len = ir_args[1];
                                if elem_sz == 1 {
                                    self.locals.set(destination_local, len);
                                } else {
                                    let esz = self.builder.iconst(
                                        elem_sz as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    let result = self.builder.mul(
                                        len.into(),
                                        esz.into(),
                                        I64,
                                        Origin::synthetic(),
                                    );
                                    self.locals.set(destination_local, result.raw());
                                }
                            } else {
                                let result = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.locals.set(destination_local, result.raw());
                            }
                        } else {
                            // str: size = len (metadata is byte length).
                            if let ty::Str = tail.kind() {
                                if ir_args.len() >= 2 {
                                    self.locals.set(destination_local, ir_args[1]);
                                } else {
                                    let result = self.builder.iconst(
                                        0,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    self.locals.set(destination_local, result.raw());
                                }
                            } else if matches!(tail.kind(), ty::Dynamic(..)) {
                                // dyn Trait: read size from vtable[1].
                                // ir_args[1] is the vtable pointer (metadata).
                                if ir_args.len() >= 2 {
                                    let vtable_ptr = self.coerce_to_ptr(ir_args[1]);
                                    let offset = self.builder.iconst(
                                        8,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    let size_ptr = self.builder.ptradd(
                                        vtable_ptr.into(),
                                        offset.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    let result = self.builder.load(
                                        size_ptr.into(),
                                        8,
                                        Type::Int,
                                        self.current_mem.into(),
                                        Some(Annotation::Int(I64)),
                                        Origin::synthetic(),
                                    );
                                    self.locals.set(destination_local, result);
                                }
                            } else {
                                let result = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.locals.set(destination_local, result.raw());
                            }
                        }
                    } else if let Some(sz) = type_size(tcx, t) {
                        // Sized type: compile-time constant.
                        let result = self.builder.iconst(
                            sz as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    } else {
                        let result = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    }
                }
                true
            }

            // min_align_of_val / align_of_val: return the alignment of the type.
            "min_align_of_val" | "align_of_val" => {
                if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                    let typing_env = ty::TypingEnv::fully_monomorphized();
                    let tail = self.tcx.struct_tail_for_codegen(t, typing_env);
                    if matches!(tail.kind(), ty::Dynamic(..)) {
                        // dyn Trait: read align from vtable[2].
                        if ir_args.len() >= 2 {
                            let vtable_ptr = self.coerce_to_ptr(ir_args[1]);
                            let offset = self.builder.iconst(
                                16,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let align_ptr = self.builder.ptradd(
                                vtable_ptr.into(),
                                offset.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let result = self.builder.load(
                                align_ptr.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                Some(Annotation::Int(I64)),
                                Origin::synthetic(),
                            );
                            self.locals.set(destination_local, result);
                        }
                    } else if matches!(tail.kind(), ty::Slice(..) | ty::Str) {
                        // Slice/str: alignment is known at compile time.
                        // Use the alignment of the containing type (not the element),
                        // so that #[repr(packed)] structs report their packed alignment.
                        let align = type_align(tcx, t).unwrap_or(1);
                        let result = self.builder.iconst(
                            align as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    } else {
                        let align = type_align(tcx, t).unwrap_or(1);
                        let result = self.builder.iconst(
                            align as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    }
                }
                true
            }

            // vtable_size: read size from vtable[1] (offset 8).
            "vtable_size" => {
                if !ir_args.is_empty() {
                    let vtable_ptr = self.coerce_to_ptr(ir_args[0]);
                    let offset =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let size_ptr = self.builder.ptradd(
                        vtable_ptr.into(),
                        offset.into(),
                        0,
                        Origin::synthetic(),
                    );
                    let result = self.builder.load(
                        size_ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        Some(Annotation::Int(I64)),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result);
                }
                true
            }

            // vtable_align: read alignment from vtable[2] (offset 16).
            "vtable_align" => {
                if !ir_args.is_empty() {
                    let vtable_ptr = self.coerce_to_ptr(ir_args[0]);
                    let offset =
                        self.builder
                            .iconst(16, 64, IntSignedness::DontCare, Origin::synthetic());
                    let align_ptr = self.builder.ptradd(
                        vtable_ptr.into(),
                        offset.into(),
                        0,
                        Origin::synthetic(),
                    );
                    let result = self.builder.load(
                        align_ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        Some(Annotation::Int(I64)),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result);
                }
                true
            }

            // arith_offset<T>(ptr, offset) → ptr + offset * sizeof(T)
            // Arithmetic intrinsics (saturating, unchecked, offset, carrying_mul, exact_div, funnel shift).
            "arith_offset"
            | "ptr_offset_from_unsigned"
            | "ptr_offset_from"
            | "saturating_add"
            | "saturating_sub"
            | "abort"
            | "catch_unwind"
            | "r#try"
            | "try"
            | "unchecked_add"
            | "unchecked_sub"
            | "unchecked_mul"
            | "carrying_mul_add"
            | "exact_div"
            | "unchecked_shl"
            | "unchecked_shr"
            | "unchecked_funnel_shl"
            | "unchecked_funnel_shr"
                if let Some(result) = self.translate_arithmetic_intrinsic(
                    name,
                    substs,
                    ir_args,
                    destination_local,
                ) =>
            {
                result
            }
            // Float intrinsics (algebraic ops, min/max).
            "fadd_algebraic"
            | "fsub_algebraic"
            | "fmul_algebraic"
            | "fdiv_algebraic"
            | "frem_algebraic"
            | "minimumf32"
            | "minimumf64"
            | "minnumf32"
            | "minnumf64"
            | "minimum_number_nsz_f32"
            | "minimum_number_nsz_f64"
            | "maximumf32"
            | "maximumf64"
            | "maxnumf32"
            | "maxnumf64"
            | "maximum_number_nsz_f32"
            | "maximum_number_nsz_f64"
                if let Some(result) =
                    self.translate_float_intrinsic(name, substs, ir_args, destination_local) =>
            {
                result
            }
            // ── SIMD platform intrinsics ──────────────────────────────────
            _ if name.starts_with("simd_") => self
                .translate_simd_intrinsic(name, substs, ir_args, destination_local)
                .unwrap_or(false),

            // Not handled here — fall through to translate_memory_intrinsic.
            _ => false,
        }
    }

    /// Lower memory intrinsics to IR memory operations.
    /// Handles write_bytes, copy_nonoverlapping, copy, and raw_eq.
    /// Returns `Some(new_mem)` if the intrinsic was handled, `None` to fall through.
    pub(super) fn translate_memory_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<ValueRef> {
        let current_mem = self.current_mem;
        let tcx = self.tcx;
        // Extract the type parameter T and compute its size and alignment.
        let (elem_size, elem_align) = match substs.first().and_then(|a| a.as_type()) {
            Some(t) => (
                type_size(tcx, t).unwrap_or(0),
                type_align(tcx, t).unwrap_or(1),
            ),
            None => return None,
        };

        match name {
            // write_bytes<T>(dst, val, count) → MemSet(dst, val, count * sizeof(T), align)
            "write_bytes" | "volatile_set_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let dst = ir_args[0];
                let val = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_set(
                    dst_annotated.into(),
                    val.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // copy_nonoverlapping<T>(src, dst, count) → MemCopy(dst, src, count * sizeof(T), align)
            "copy_nonoverlapping" | "volatile_copy_nonoverlapping_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let src = ir_args[0];
                let dst = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let src_annotated = IrOperand::annotated(src, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_copy(
                    dst_annotated.into(),
                    src_annotated.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // copy<T>(src, dst, count) → MemMove(dst, src, count * sizeof(T), align)
            "copy" | "volatile_copy_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let src = ir_args[0];
                let dst = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let src_annotated = IrOperand::annotated(src, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_move(
                    dst_annotated.into(),
                    src_annotated.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // raw_eq<T>(a, b) → memcmp(a, b, sizeof(T)) == 0
            "raw_eq" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let a = ir_args[0];
                let b = ir_args[1];
                let sz = self.builder.iconst(
                    elem_size as i64,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let sym_id = self.symbols.intern("memcmp");
                let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                let (mem_out, data) = self.builder.call(
                    callee.into(),
                    vec![a.into(), b.into(), sz.into()],
                    Type::Int,
                    current_mem.into(),
                    int_annotation_for_bytes(4),
                    Origin::synthetic(),
                );
                // raw_eq returns bool (0 or 1): true when memcmp returns 0.
                let cmp_result = data.unwrap_or_else(|| {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                });
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw();
                let eq = self.builder.icmp(
                    tuffy_ir::instruction::ICmpOp::Eq,
                    cmp_result.into(),
                    zero.into(),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, eq.raw());
                Some(mem_out.raw())
            }

            // typed_swap_nonoverlapping<T>(x, y) — swap values at two pointers.
            "typed_swap_nonoverlapping" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let x = self.coerce_to_ptr(ir_args[0]);
                let y = self.coerce_to_ptr(ir_args[1]);
                let mut mem = current_mem;
                let num_words = elem_size.div_ceil(8);
                for i in 0..num_words {
                    let off = i * 8;
                    let chunk = std::cmp::min(8, elem_size - off) as u32;
                    let (xa, ya) = if off == 0 {
                        (x, y)
                    } else {
                        let o = self.builder.iconst(
                            off as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        (
                            self.builder
                                .ptradd(x.into(), o.into(), 0, Origin::synthetic())
                                .raw(),
                            self.builder
                                .ptradd(y.into(), o.into(), 0, Origin::synthetic())
                                .raw(),
                        )
                    };
                    let vx = self.builder.load(
                        xa.into(),
                        chunk,
                        Type::Int,
                        mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    let vy = self.builder.load(
                        ya.into(),
                        chunk,
                        Type::Int,
                        mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    mem = self
                        .builder
                        .store(vy.into(), xa.into(), chunk, mem.into(), Origin::synthetic())
                        .raw();
                    mem = self
                        .builder
                        .store(vx.into(), ya.into(), chunk, mem.into(), Origin::synthetic())
                        .raw();
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
                let ordering = parse_atomic_ordering(name);
                let (new_mem, val) = self.builder.load_atomic(
                    ptr.into(),
                    Type::Int,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, val);
                Some(new_mem.raw())
            }

            // atomic_store_relaxed, atomic_store_release, atomic_store_seqcst
            _ if name.starts_with("atomic_store") => {
                if ir_args.len() < 2 {
                    return None;
                }
                let ptr = ir_args[0];
                let val = ir_args[1];
                let ordering = parse_atomic_ordering(name);
                let new_mem = self.builder.store_atomic(
                    val.into(),
                    ptr.into(),
                    ordering,
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(new_mem.raw())
            }

            // atomic_cxchg_*, atomic_cxchgweak_* → (old_val, success: bool)
            _ if name.starts_with("atomic_cxchg") => {
                if ir_args.len() < 3 {
                    return None;
                }
                let ptr = ir_args[0];
                let expected = self.coerce_to_int(ir_args[1]);
                let new_val = self.coerce_to_int(ir_args[2]);
                let ordering = parse_atomic_ordering(name);

                let (new_mem, actual_old) = self.builder.atomic_cmpxchg(
                    ptr.into(),
                    expected.into(),
                    new_val.into(),
                    Type::Int,
                    ordering,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );

                // Compare actual_old == expected to get success bool.
                let eq = self.builder.icmp(
                    tuffy_ir::instruction::ICmpOp::Eq,
                    actual_old.into(),
                    expected.into(),
                    Origin::synthetic(),
                );

                // Write (old, eq) into the destination stack slot.
                if let Some(slot) = self.locals.get(destination_local) {
                    let size = elem_size as u32;
                    let mem2 = self.builder.store(
                        actual_old.into(),
                        slot.into(),
                        size,
                        new_mem.into(),
                        Origin::synthetic(),
                    );
                    let bool_off = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let bool_ptr =
                        self.builder
                            .ptradd(slot.into(), bool_off.into(), 0, Origin::synthetic());
                    let mem3 = self.builder.store(
                        eq.into(),
                        bool_ptr.into(),
                        1,
                        mem2.into(),
                        Origin::synthetic(),
                    );
                    Some(mem3.raw())
                } else {
                    self.locals.set(destination_local, actual_old);
                    Some(new_mem.raw())
                }
            }

            // atomic_xchg_* → returns old value
            _ if name.starts_with("atomic_xchg") => {
                if ir_args.len() < 2 {
                    return None;
                }
                let ptr = ir_args[0];
                let new_val = ir_args[1];
                let ordering = parse_atomic_ordering(name);
                let (new_mem, old) = self.builder.atomic_rmw(
                    AtomicRmwOp::Xchg,
                    ptr.into(),
                    new_val.into(),
                    Type::Int,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, old);
                Some(new_mem.raw())
            }

            // atomic_fence_*, atomic_singlethreadfence_* → fence instruction
            _ if name.starts_with("atomic_fence")
                || name.starts_with("atomic_singlethreadfence") =>
            {
                let ordering = parse_atomic_ordering(name);
                let new_mem = self
                    .builder
                    .fence(ordering, current_mem.into(), Origin::synthetic());
                Some(new_mem.raw())
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
                let ordering = parse_atomic_ordering(name);

                // Use atomic_rmw for supported operations.
                if name.starts_with("atomic_xadd") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Add,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xsub") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Sub,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_and") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::And,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_or") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Or,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xor") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Xor,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else {
                    // Unsupported ops: nand, max, min, umax, umin — use atomic load/store.
                    let elem_bytes = elem_size as u32;
                    let elem_bits = elem_bytes * 8;
                    let elem_ann = int_annotation_for_bytes(elem_bytes);
                    let int_ty = IntAnnotation {
                        bit_width: elem_bits,
                        signedness: IntSignedness::DontCare,
                    };

                    let (mem1, old) = self.builder.load_atomic(
                        ptr.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        elem_ann,
                        Origin::synthetic(),
                    );

                    let new_val = if name.starts_with("atomic_nand") {
                        let a = self.builder.and(
                            old.into(),
                            operand.into(),
                            int_ty,
                            Origin::synthetic(),
                        );
                        let all_ones = self.builder.iconst(
                            -1,
                            elem_bits,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .xor(a.into(), all_ones.into(), int_ty, Origin::synthetic())
                            .raw()
                    } else if name.starts_with("atomic_umax") {
                        let gt = self.builder.icmp(
                            ICmpOp::Gt,
                            old.into(),
                            operand.into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            gt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann,
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_umin") {
                        let lt = self.builder.icmp(
                            ICmpOp::Lt,
                            old.into(),
                            operand.into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            lt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann,
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_max") {
                        let signed_ann = Annotation::Int(IntAnnotation {
                            bit_width: elem_bits,
                            signedness: IntSignedness::Signed,
                        });
                        let gt = self.builder.icmp(
                            ICmpOp::Gt,
                            IrOperand::annotated(old, signed_ann).into(),
                            IrOperand::annotated(operand, signed_ann).into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            gt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann,
                            Origin::synthetic(),
                        )
                    } else {
                        // atomic_min
                        let signed_ann = Annotation::Int(IntAnnotation {
                            bit_width: elem_bits,
                            signedness: IntSignedness::Signed,
                        });
                        let lt = self.builder.icmp(
                            ICmpOp::Lt,
                            IrOperand::annotated(old, signed_ann).into(),
                            IrOperand::annotated(operand, signed_ann).into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            lt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann,
                            Origin::synthetic(),
                        )
                    };

                    let new_mem = self.builder.store_atomic(
                        new_val.into(),
                        ptr.into(),
                        ordering,
                        mem1.into(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                }
            }

            // write_via_move<T>(dst, src) — write src to *dst.
            "write_via_move" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let dst = self.coerce_to_ptr(ir_args[0]);
                let src = ir_args[1];
                if elem_size == 0 {
                    Some(current_mem)
                } else if self.builder.is_memory_address(src) {
                    // Source is a memory address (aggregate); use mem_copy.
                    let src_ptr = self.coerce_to_ptr(src);
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let mem_out = self.builder.mem_copy(
                        dst.into(),
                        src_ptr.into(),
                        sz.into(),
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    Some(mem_out.raw())
                } else {
                    let store_size = elem_size.min(8) as u32;
                    let mem_out = self.builder.store(
                        src.into(),
                        dst.into(),
                        store_size,
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    Some(mem_out.raw())
                }
            }

            // read_via_copy<T>(src) → *src
            "read_via_copy" => {
                if ir_args.is_empty() {
                    return None;
                }
                let src = self.coerce_to_ptr(ir_args[0]);
                if elem_size == 0 {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.locals.set(destination_local, zero.raw());
                    Some(current_mem)
                } else if elem_size > 8 {
                    // Large type: allocate stack slot and mem_copy into it.
                    let slot =
                        self.builder
                            .stack_slot(elem_size.max(8) as u32, 0, Origin::synthetic());
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let mem_out = self.builder.mem_copy(
                        slot.into(),
                        src.into(),
                        sz.into(),
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, slot);
                    self.stack_locals.mark(destination_local);
                    Some(mem_out.raw())
                } else {
                    let load_size = elem_size.min(8) as u32;
                    let ann = int_annotation_for_bytes(load_size);
                    let val = self.builder.load(
                        src.into(),
                        load_size,
                        Type::Int,
                        current_mem.into(),
                        ann,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, val);
                    Some(current_mem)
                }
            }

            _ => None,
        }
    }

    fn translate_bit_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<bool> {
        let tcx = self.tcx;

        Some(match name {
            "ctpop" => {
                if let Some(&v) = ir_args.first() {
                    let bits = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz as u32) * 8)
                        .unwrap_or(64);
                    // For sub-64-bit types, mask to type width before popcount
                    // to ignore garbage in upper register bits (e.g. after NOT).
                    let operand = if bits < 64 {
                        let mask_ann = IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::Unsigned,
                        };
                        let mask = self.builder.iconst(
                            (1i64 << bits) - 1,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        self.builder
                            .and(v.into(), mask.into(), mask_ann, Origin::synthetic())
                            .raw()
                    } else {
                        v
                    };
                    let result = self
                        .builder
                        .count_ones(operand.into(), 64, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // ctlz / ctlz_nonzero: count leading zeros.
            // Always emit a 64-bit CLZ and adjust in the frontend for sub-64-bit
            // types, because the legalization pass only runs when the function
            // has 128-bit values.
            "ctlz" | "ctlz_nonzero" => {
                if let Some(&v) = ir_args.first() {
                    let bits = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    if bits <= 64 {
                        // For sub-64-bit types, mask the value to clear any
                        // sign-extended upper bits. Without this, lzcnt64 on
                        // e.g. 0xFFFFFFFFFFFFFF80 (-128i8 as u8) returns 0
                        // instead of 56.
                        let masked = if bits < 64 {
                            let mask = self.builder.iconst(
                                (1i64 << bits) - 1,
                                64,
                                IntSignedness::Unsigned,
                                Origin::synthetic(),
                            );
                            self.builder
                                .and(v.into(), mask.into(), I64, Origin::synthetic())
                                .raw()
                        } else {
                            v
                        };
                        // Emit lzcnt64 and adjust for sub-64-bit types.
                        let clz = self.builder.count_leading_zeros(
                            masked.into(),
                            64,
                            64,
                            Origin::synthetic(),
                        );
                        if bits < 64 {
                            let adjust = self.builder.iconst(
                                (64 - bits) as i64,
                                64,
                                IntSignedness::Unsigned,
                                Origin::synthetic(),
                            );
                            let result = self.builder.sub(
                                clz.into(),
                                adjust.into(),
                                I64,
                                Origin::synthetic(),
                            );
                            self.locals.set(destination_local, result.raw());
                        } else {
                            self.locals.set(destination_local, clz.raw());
                        }
                    } else {
                        // 128-bit: emit with 128-bit operand width; legalization splits it.
                        // Result is at most 128 and fits in 64 bits, so use 64-bit result
                        // annotation to avoid the value being marked as "wide".
                        let result = self.builder.count_leading_zeros(
                            v.into(),
                            bits,
                            64,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    }
                }
                true
            }

            // cttz / cttz_nonzero: count trailing zeros.
            // For sub-64-bit types, set bit at position `bits` so tzcnt64
            // stops at the type boundary (tzcnt64(0) = 64, but cttz::<u32>(0) = 32).
            "cttz" | "cttz_nonzero" => {
                if let Some(&v) = ir_args.first() {
                    let bits = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    if bits < 64 {
                        // OR with (1 << bits) to cap at type width.
                        let sentinel = self.builder.iconst(
                            1i64 << bits,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let capped =
                            self.builder
                                .or(v.into(), sentinel.into(), I64, Origin::synthetic());
                        let result = self.builder.count_trailing_zeros(
                            capped.into(),
                            64,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    } else if bits <= 64 {
                        let result =
                            self.builder
                                .count_trailing_zeros(v.into(), 64, Origin::synthetic());
                        self.locals.set(destination_local, result.raw());
                    } else {
                        // 128-bit: emit with 64-bit width; legalization splits it.
                        let result =
                            self.builder
                                .count_trailing_zeros(v.into(), 64, Origin::synthetic());
                        self.locals.set(destination_local, result.raw());
                    }
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
                        self.locals.set(destination_local, v);
                    } else {
                        let result =
                            self.builder
                                .bswap(v.into(), byte_size as u32, Origin::synthetic());
                        self.locals.set(destination_local, result.raw());
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
                        self.locals.set(destination_local, v);
                    } else {
                        let result =
                            self.builder
                                .bit_reverse(v.into(), bit_size, Origin::synthetic());
                        self.locals.set(destination_local, result.raw());
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
                        self.builder
                            .rotate_left(x.into(), n.into(), bits, Origin::synthetic())
                    } else {
                        self.builder
                            .rotate_right(x.into(), n.into(), bits, Origin::synthetic())
                    };
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            _ => return None,
        })
    }

    fn translate_arithmetic_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<bool> {
        let current_mem = self.current_mem;
        let tcx = self.tcx;

        Some(match name {
            "arith_offset" => {
                if ir_args.len() >= 2 {
                    let ptr = self.coerce_to_ptr(ir_args[0]);
                    let offset = ir_args[1];
                    let elem_size = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .unwrap_or(1);
                    let byte_offset = if elem_size == 1 {
                        offset
                    } else {
                        let sz = self.builder.iconst(
                            elem_size as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .mul(offset.into(), sz.into(), I64, Origin::synthetic())
                            .raw()
                    };
                    let result =
                        self.builder
                            .ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // ptr_offset_from<T>(ptr1, ptr2) → (ptr1 - ptr2) / sizeof(T) (signed)
            // ptr_offset_from_unsigned<T>(ptr1, ptr2) → (ptr1 - ptr2) / sizeof(T) (unsigned)
            "ptr_offset_from_unsigned" | "ptr_offset_from" => {
                if ir_args.len() >= 2 {
                    let is_signed = name == "ptr_offset_from";
                    let ptr1 = self.coerce_to_ptr(ir_args[0]);
                    let ptr2 = self.coerce_to_ptr(ir_args[1]);
                    let diff =
                        self.builder
                            .ptrdiff(ptr1.into(), ptr2.into(), 64, Origin::synthetic());
                    let elem_size = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .unwrap_or(1);
                    let result = if elem_size <= 1 {
                        diff
                    } else {
                        let div_ann = IntAnnotation {
                            bit_width: 64,
                            signedness: if is_signed {
                                IntSignedness::Signed
                            } else {
                                IntSignedness::Unsigned
                            },
                        };
                        let sz = self.builder.iconst(
                            elem_size as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .div(diff.into(), sz.into(), div_ann, Origin::synthetic())
                    };
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // saturating_add<T>(a, b): add with saturation at max value.
            "saturating_add" => {
                if ir_args.len() >= 2 {
                    let ty = substs.first().and_then(|a| a.as_type());
                    let bits = ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    let is_signed =
                        ty.is_some_and(|t| matches!(t.kind(), rustc_middle::ty::Int(_)));
                    let result = if is_signed {
                        self.builder.signed_saturating_add(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            bits,
                            Origin::synthetic(),
                        )
                    } else {
                        self.builder.saturating_add(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            bits,
                            Origin::synthetic(),
                        )
                    };
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // saturating_sub<T>(a, b): subtract with saturation at zero.
            "saturating_sub" => {
                if ir_args.len() >= 2 {
                    let ty = substs.first().and_then(|a| a.as_type());
                    let bits = ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    let is_signed =
                        ty.is_some_and(|t| matches!(t.kind(), rustc_middle::ty::Int(_)));
                    let result = if is_signed {
                        self.builder.signed_saturating_sub(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            bits,
                            Origin::synthetic(),
                        )
                    } else {
                        self.builder.saturating_sub(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            bits,
                            Origin::synthetic(),
                        )
                    };
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // abort: call libc abort().
            "abort" => {
                let sym_id = self.symbols.intern("abort");
                let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                self.builder.call(
                    callee.into(),
                    vec![],
                    Type::Unit,
                    current_mem.into(),
                    None,
                    Origin::synthetic(),
                );
                true
            }

            // try intrinsic: used by catch_unwind / panicking::try.
            // Lowers to a call to __rust_try(try_fn, data, catch_fn) -> i32.
            "catch_unwind" | "r#try" | "try" => {
                if ir_args.len() >= 3 {
                    let sym_id = self.symbols.intern("__rust_try");
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                    let (mem_out, data) = self.builder.call(
                        callee.into(),
                        vec![ir_args[0].into(), ir_args[1].into(), ir_args[2].into()],
                        Type::Int,
                        current_mem.into(),
                        int_annotation_for_bytes(4),
                        Origin::synthetic(),
                    );
                    self.current_mem = mem_out.raw();
                    if let Some(result) = data {
                        self.locals.set(destination_local, result);
                    }
                }
                true
            }

            // unchecked arithmetic: same as wrapping ops (no overflow check).
            "unchecked_add" => {
                if ir_args.len() >= 2 {
                    let result = self.builder.add(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        I64,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            "unchecked_sub" => {
                if ir_args.len() >= 2 {
                    let result = self.builder.sub(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        I64,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            "unchecked_mul" => {
                if ir_args.len() >= 2 {
                    let result = self.builder.mul(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        I64,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            // carrying_mul_add(a, b, carry, add) -> (lo, hi)
            // Computes a*b + carry + add as a widened result.
            "carrying_mul_add" => {
                if ir_args.len() >= 4 {
                    let elem_ty = substs.first().and_then(|a| a.as_type());
                    let elem_bytes = elem_ty.and_then(|t| type_size(tcx, t)).unwrap_or(8) as u32;
                    let is_signed = elem_ty.is_some_and(|t| is_signed_int(t));
                    let narrow_bits = elem_bytes * 8;

                    if narrow_bits == 128 {
                        // 128-bit: compute 256-bit product using 64-bit partial products
                        self.emit_carrying_mul_add_128(ir_args, destination_local, is_signed);
                    } else {
                        let wide_bits = elem_bytes * 8 * 2;
                        let wide_ann = IntAnnotation {
                            bit_width: wide_bits,
                            signedness: if is_signed {
                                IntSignedness::Signed
                            } else {
                                IntSignedness::Unsigned
                            },
                        };

                        let a_wide = if is_signed {
                            self.builder
                                .sext(ir_args[0].into(), wide_bits, Origin::synthetic())
                        } else {
                            self.builder
                                .zext(ir_args[0].into(), wide_bits, Origin::synthetic())
                        };
                        let b_wide = if is_signed {
                            self.builder
                                .sext(ir_args[1].into(), wide_bits, Origin::synthetic())
                        } else {
                            self.builder
                                .zext(ir_args[1].into(), wide_bits, Origin::synthetic())
                        };
                        let product = self.builder.mul(
                            a_wide.into(),
                            b_wide.into(),
                            wide_ann,
                            Origin::synthetic(),
                        );

                        let carry_wide = if is_signed {
                            self.builder
                                .sext(ir_args[2].into(), wide_bits, Origin::synthetic())
                        } else {
                            self.builder
                                .zext(ir_args[2].into(), wide_bits, Origin::synthetic())
                        };
                        let add_wide = if is_signed {
                            self.builder
                                .sext(ir_args[3].into(), wide_bits, Origin::synthetic())
                        } else {
                            self.builder
                                .zext(ir_args[3].into(), wide_bits, Origin::synthetic())
                        };
                        let sum1 = self.builder.add(
                            product.into(),
                            carry_wide.into(),
                            wide_ann,
                            Origin::synthetic(),
                        );
                        let full = self.builder.add(
                            sum1.into(),
                            add_wide.into(),
                            wide_ann,
                            Origin::synthetic(),
                        );

                        let shift_amt = self.builder.iconst(
                            narrow_bits as i64,
                            narrow_bits,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let shift_wide =
                            self.builder
                                .zext(shift_amt.into(), wide_bits, Origin::synthetic());
                        // For signed types use arithmetic right shift to
                        // preserve the sign of the high half.
                        let shift_ann = IntAnnotation {
                            bit_width: wide_bits,
                            signedness: if is_signed {
                                IntSignedness::Signed
                            } else {
                                IntSignedness::Unsigned
                            },
                        };
                        let hi_wide = self.builder.shr(
                            full.into(),
                            shift_wide.into(),
                            shift_ann,
                            Origin::synthetic(),
                        );

                        // Store full result (lo|hi) into a stack slot.
                        // The lower `elem_bytes` of `full` is lo, the lower
                        // `elem_bytes` of `hi_wide` is hi.
                        let slot = self
                            .builder
                            .stack_slot(elem_bytes * 2, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                full.raw().into(),
                                slot.into(),
                                elem_bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        let hi_offset = self.builder.iconst(
                            elem_bytes as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let hi_addr = self.builder.ptradd(
                            slot.into(),
                            hi_offset.into(),
                            0,
                            Origin::synthetic(),
                        );
                        self.current_mem = self
                            .builder
                            .store(
                                hi_wide.raw().into(),
                                hi_addr.raw().into(),
                                elem_bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        self.locals.set(destination_local, slot);
                        self.stack_locals.mark(destination_local);
                    }
                }
                true
            }
            // exact_div: division where the remainder is guaranteed to be zero.
            "exact_div" => {
                if ir_args.len() >= 2 {
                    let ty = substs.first().and_then(|a| a.as_type());
                    let signed = ty.map(|t| is_signed_int(t)).unwrap_or(false);
                    let ann = ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| {
                            let bits = (sz as u32) * 8;
                            IntAnnotation {
                                bit_width: bits,
                                signedness: if signed {
                                    IntSignedness::Signed
                                } else {
                                    IntSignedness::Unsigned
                                },
                            }
                        })
                        .unwrap_or(I64);
                    // Annotate operands so legalization picks the correct
                    // library call (signed vs unsigned) for 128-bit types.
                    let full_ann = Annotation::Int(ann);
                    let a_op = tuffy_ir::instruction::Operand::annotated(ir_args[0], full_ann);
                    let b_op = tuffy_ir::instruction::Operand::annotated(ir_args[1], full_ann);
                    let result =
                        self.builder
                            .div(a_op.into(), b_op.into(), ann, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            "unchecked_shl" => {
                if ir_args.len() >= 2 {
                    let ann = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| int_ann_for_bytes(sz as u32))
                        .unwrap_or_else(|| int_ann_for_bytes(8));
                    let result = self.builder.shl(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        ann,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            "unchecked_shr" => {
                if ir_args.len() >= 2 {
                    let ann = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| int_ann_for_bytes(sz as u32))
                        .unwrap_or_else(|| int_ann_for_bytes(8));
                    let result = self.builder.shr(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        ann,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // Funnel shifts: fshl(a, b, c) = (a << c) | (b >> (bits - c))
            //                fshr(a, b, c) = (a << (bits - c)) | (b >> c)
            // For sub-64-bit types, use a combined 64-bit value to avoid
            // x86 shift masking issues (shr r32, 32 is a no-op on x86).
            "unchecked_funnel_shl" | "unchecked_funnel_shr" => {
                if ir_args.len() >= 3 {
                    let a = ir_args[0];
                    let b = ir_args[1];
                    let c = ir_args[2];
                    let ty = substs.first().and_then(|arg| arg.as_type());
                    let bits = ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);

                    if bits < 64 {
                        // Sub-64-bit: pack into a 64-bit combined value.
                        // fshl(a,b,c): combined = (a << bits) | (b & mask)
                        //              result = (combined >> (bits - c)) & mask
                        // fshr(a,b,c): combined = (a << bits) | (b & mask)
                        //              result = (combined >> c) & mask
                        let mask_val = self.builder.iconst(
                            (1i64 << bits) - 1,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let b_masked =
                            self.builder
                                .and(b.into(), mask_val.into(), I64, Origin::synthetic());
                        let bits_val = self.builder.iconst(
                            bits as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let a_shifted =
                            self.builder
                                .shl(a.into(), bits_val.into(), I64, Origin::synthetic());
                        let combined = self.builder.or(
                            a_shifted.into(),
                            b_masked.into(),
                            I64,
                            Origin::synthetic(),
                        );
                        let shift_amt: tuffy_ir::typed::IntOperand =
                            if name == "unchecked_funnel_shl" {
                                self.builder
                                    .sub(bits_val.into(), c.into(), I64, Origin::synthetic())
                                    .into()
                            } else {
                                c.into()
                            };
                        let shifted =
                            self.builder
                                .shr(combined.into(), shift_amt, I64, Origin::synthetic());
                        let result = self.builder.and(
                            shifted.into(),
                            mask_val.into(),
                            I64,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    } else if bits == 64 {
                        let int_ann = IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::Unsigned,
                        };
                        let bits_val = self.builder.iconst(
                            64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let complement =
                            self.builder
                                .sub(bits_val.into(), c.into(), I64, Origin::synthetic());
                        let zero = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let (hi, lo, is_shl) = if name == "unchecked_funnel_shl" {
                            (
                                self.builder
                                    .shl(a.into(), c.into(), int_ann, Origin::synthetic()),
                                self.builder.shr(
                                    b.into(),
                                    complement.into(),
                                    int_ann,
                                    Origin::synthetic(),
                                ),
                                true,
                            )
                        } else {
                            (
                                self.builder.shl(
                                    a.into(),
                                    complement.into(),
                                    int_ann,
                                    Origin::synthetic(),
                                ),
                                self.builder
                                    .shr(b.into(), c.into(), int_ann, Origin::synthetic()),
                                false,
                            )
                        };
                        let c_is_zero = self.builder.icmp(
                            tuffy_ir::instruction::ICmpOp::Eq,
                            c.into(),
                            zero.into(),
                            Origin::synthetic(),
                        );
                        let ann64 = Some(Annotation::Int(I64));
                        let (final_hi, final_lo) = if is_shl {
                            let lo_fixed = self.builder.select(
                                c_is_zero.into(),
                                zero.into(),
                                lo.raw().into(),
                                Type::Int,
                                ann64,
                                Origin::synthetic(),
                            );
                            (hi.raw(), lo_fixed)
                        } else {
                            let hi_fixed = self.builder.select(
                                c_is_zero.into(),
                                zero.into(),
                                hi.raw().into(),
                                Type::Int,
                                ann64,
                                Origin::synthetic(),
                            );
                            (hi_fixed, lo.raw())
                        };
                        let result = self.builder.or(
                            final_hi.into(),
                            final_lo.into(),
                            I64,
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result.raw());
                    } else {
                        // 128-bit funnel shift: use 128-bit IR ops, store
                        // result in a stack slot.
                        let int_ann = IntAnnotation {
                            bit_width: 128,
                            signedness: IntSignedness::Unsigned,
                        };
                        let bits_val = self.builder.iconst(
                            128,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let complement =
                            self.builder
                                .sub(bits_val.into(), c.into(), I64, Origin::synthetic());
                        let zero = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let (hi, lo, is_shl) = if name == "unchecked_funnel_shl" {
                            (
                                self.builder
                                    .shl(a.into(), c.into(), int_ann, Origin::synthetic()),
                                self.builder.shr(
                                    b.into(),
                                    complement.into(),
                                    int_ann,
                                    Origin::synthetic(),
                                ),
                                true,
                            )
                        } else {
                            (
                                self.builder.shl(
                                    a.into(),
                                    complement.into(),
                                    int_ann,
                                    Origin::synthetic(),
                                ),
                                self.builder
                                    .shr(b.into(), c.into(), int_ann, Origin::synthetic()),
                                false,
                            )
                        };
                        let c_is_zero = self.builder.icmp(
                            tuffy_ir::instruction::ICmpOp::Eq,
                            c.into(),
                            zero.into(),
                            Origin::synthetic(),
                        );
                        let ann128 = Some(Annotation::Int(int_ann));
                        let (final_hi, final_lo) = if is_shl {
                            let lo_fixed = self.builder.select(
                                c_is_zero.into(),
                                zero.into(),
                                lo.raw().into(),
                                Type::Int,
                                ann128,
                                Origin::synthetic(),
                            );
                            (hi.raw(), lo_fixed)
                        } else {
                            let hi_fixed = self.builder.select(
                                c_is_zero.into(),
                                zero.into(),
                                hi.raw().into(),
                                Type::Int,
                                ann128,
                                Origin::synthetic(),
                            );
                            (hi_fixed, lo.raw())
                        };
                        let result = self.builder.or(
                            final_hi.into(),
                            final_lo.into(),
                            int_ann,
                            Origin::synthetic(),
                        );
                        let slot = self.builder.stack_slot(16, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                result.raw().into(),
                                slot.into(),
                                16,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        self.locals.set(destination_local, slot);
                        self.stack_locals.mark(destination_local);
                    }
                }
                true
            }
            _ => return None,
        })
    }

    fn translate_float_intrinsic(
        &mut self,
        name: &str,
        _substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<bool> {
        Some(match name {
            "fadd_algebraic" | "fsub_algebraic" | "fmul_algebraic" | "fdiv_algebraic"
            | "frem_algebraic" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let flags = FpRewriteFlags {
                    reassoc: true,
                    contract: true,
                };
                let o = Origin::synthetic();
                let result = match name {
                    "fadd_algebraic" => self.builder.fadd(a.into(), b.into(), flags, ty, o),
                    "fsub_algebraic" => self.builder.fsub(a.into(), b.into(), flags, ty, o),
                    "fmul_algebraic" => self.builder.fmul(a.into(), b.into(), flags, ty, o),
                    "fdiv_algebraic" => self.builder.fdiv(a.into(), b.into(), flags, ty, o),
                    "frem_algebraic" => self.builder.frem(a.into(), b.into(), flags, ty, o),
                    _ => unreachable!(),
                };
                self.locals.set(destination_local, result.raw());
                true
            }

            // Float min/max intrinsics.
            // minnumf32/minnumf64: legacy IEEE 754-2008 minNum.
            // minimumf32/minimumf64: IEEE 754-2019 minimum (NaN-propagating, -0 < +0).
            "minimumf32" | "minimumf64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let o = || Origin::synthetic();
                let int_bits = match &ty {
                    Type::Float(FloatType::F32) => 32u32,
                    _ => 64u32,
                };
                let iann = IntAnnotation {
                    bit_width: int_bits,
                    signedness: IntSignedness::Unsigned,
                };
                let int_ann = Some(Annotation::Int(iann));
                let fp_flags = tuffy_ir::types::FpRewriteFlags {
                    reassoc: false,
                    contract: false,
                };
                // NaN check
                let a_nan = self.builder.fcmp(FCmpOp::Uno, a.into(), a.into(), o());
                let b_nan = self.builder.fcmp(FCmpOp::Uno, b.into(), b.into(), o());
                let either_nan = self.builder.bor(a_nan.into(), b_nan.into(), o());
                let nan_val = self
                    .builder
                    .fadd(a.into(), b.into(), fp_flags, ty.clone(), o());
                // Ordered comparison
                let a_lt = self.builder.fcmp(FCmpOp::OLt, a.into(), b.into(), o());
                let a_gt = self.builder.fcmp(FCmpOp::OGt, a.into(), b.into(), o());
                // Tie-break for ±0: minimum → pick -0 → OR of bit patterns
                let a_bits = self.builder.bitcast(a.into(), Type::Int, int_ann, o());
                let b_bits = self.builder.bitcast(b.into(), Type::Int, int_ann, o());
                let or_bits = self.builder.or(a_bits.into(), b_bits.into(), iann, o());
                let tie = self
                    .builder
                    .bitcast(or_bits.raw().into(), ty.clone(), None, o());
                let r1 =
                    self.builder
                        .select(a_gt.into(), b.into(), tie.into(), ty.clone(), None, o());
                let r2 =
                    self.builder
                        .select(a_lt.into(), a.into(), r1.into(), ty.clone(), None, o());
                let result = self.builder.select(
                    either_nan.into(),
                    nan_val.raw().into(),
                    r2.into(),
                    ty,
                    None,
                    o(),
                );
                self.locals.set(destination_local, result);
                true
            }
            // minnumf32/minnumf64: legacy IEEE 754-2008 minNum (NaN-suppressing).
            // minimum_number_nsz: like minNum (no signed zero → ±0 equal).
            "minnumf32" | "minnumf64" | "minimum_number_nsz_f32" | "minimum_number_nsz_f64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let result = self
                    .builder
                    .fminnum(a.into(), b.into(), ty, Origin::synthetic());
                self.locals.set(destination_local, result.raw());
                true
            }
            // maximumf32/maximumf64: IEEE 754-2019 maximum (NaN-propagating, -0 < +0).
            "maximumf32" | "maximumf64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let o = || Origin::synthetic();
                let int_bits = match &ty {
                    Type::Float(FloatType::F32) => 32u32,
                    _ => 64u32,
                };
                let iann = IntAnnotation {
                    bit_width: int_bits,
                    signedness: IntSignedness::Unsigned,
                };
                let int_ann = Some(Annotation::Int(iann));
                let fp_flags = tuffy_ir::types::FpRewriteFlags {
                    reassoc: false,
                    contract: false,
                };
                // NaN check
                let a_nan = self.builder.fcmp(FCmpOp::Uno, a.into(), a.into(), o());
                let b_nan = self.builder.fcmp(FCmpOp::Uno, b.into(), b.into(), o());
                let either_nan = self.builder.bor(a_nan.into(), b_nan.into(), o());
                let nan_val = self
                    .builder
                    .fadd(a.into(), b.into(), fp_flags, ty.clone(), o());
                // Ordered comparison
                let a_gt = self.builder.fcmp(FCmpOp::OGt, a.into(), b.into(), o());
                let a_lt = self.builder.fcmp(FCmpOp::OLt, a.into(), b.into(), o());
                // Tie-break for ±0: maximum → pick +0 → AND of bit patterns
                let a_bits = self.builder.bitcast(a.into(), Type::Int, int_ann, o());
                let b_bits = self.builder.bitcast(b.into(), Type::Int, int_ann, o());
                let and_bits = self.builder.and(a_bits.into(), b_bits.into(), iann, o());
                let tie = self
                    .builder
                    .bitcast(and_bits.raw().into(), ty.clone(), None, o());
                let r1 =
                    self.builder
                        .select(a_lt.into(), b.into(), tie.into(), ty.clone(), None, o());
                let r2 =
                    self.builder
                        .select(a_gt.into(), a.into(), r1.into(), ty.clone(), None, o());
                let result = self.builder.select(
                    either_nan.into(),
                    nan_val.raw().into(),
                    r2.into(),
                    ty,
                    None,
                    o(),
                );
                self.locals.set(destination_local, result);
                true
            }
            // maxnumf32/maxnumf64: legacy IEEE 754-2008 maxNum (NaN-suppressing).
            // maximum_number_nsz: like maxNum (no signed zero → ±0 equal).
            "maxnumf32" | "maxnumf64" | "maximum_number_nsz_f32" | "maximum_number_nsz_f64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let result = self
                    .builder
                    .fmaxnum(a.into(), b.into(), ty, Origin::synthetic());
                self.locals.set(destination_local, result.raw());
                true
            }
            _ => return None,
        })
    }

    pub(super) fn detect_intrinsic(
        &self,
        func_op: &Operand<'tcx>,
    ) -> Option<(String, &'tcx ty::List<ty::GenericArg<'tcx>>)> {
        let ty = match func_op {
            Operand::Constant(c) => c.ty(),
            _ => return None,
        };
        let ty = self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        );
        if let ty::FnDef(def_id, args) = ty.kind()
            && let Some(intrinsic) = self.tcx.intrinsic(*def_id)
        {
            return Some((intrinsic.name.as_str().to_string(), args));
        }
        None
    }
}

pub(super) fn intrinsic_to_libc(name: &str) -> Option<&'static str> {
    match name {
        // compare_bytes(left, right, count) -> i32 maps directly to memcmp.
        "compare_bytes" => Some("memcmp"),

        // Fused multiply-add: fma(a, b, c) = a * b + c (single rounding).
        "fmaf32" => Some("fmaf"),
        "fmaf64" => Some("fma"),

        // Square root.
        "sqrtf32" => Some("sqrtf"),
        "sqrtf64" => Some("sqrt"),

        // Trigonometric functions.
        "sinf32" => Some("sinf"),
        "sinf64" => Some("sin"),
        "cosf32" => Some("cosf"),
        "cosf64" => Some("cos"),

        // Exponential / logarithmic functions.
        "expf32" => Some("expf"),
        "expf64" => Some("exp"),
        "exp2f32" => Some("exp2f"),
        "exp2f64" => Some("exp2"),
        "logf32" => Some("logf"),
        "logf64" => Some("log"),
        "log2f32" => Some("log2f"),
        "log2f64" => Some("log2"),
        "log10f32" => Some("log10f"),
        "log10f64" => Some("log10"),

        // Power functions.
        "powf32" => Some("powf"),
        "powf64" => Some("pow"),
        "powif32" => Some("__powisf2"),
        "powif64" => Some("__powidf2"),

        // Rounding functions.
        "ceilf32" => Some("ceilf"),
        "ceilf64" => Some("ceil"),
        "floorf32" => Some("floorf"),
        "floorf64" => Some("floor"),
        "truncf32" => Some("truncf"),
        "truncf64" => Some("trunc"),
        "roundf32" => Some("roundf"),
        "roundf64" => Some("round"),
        "round_ties_even_f32" => Some("rintf"),
        "round_ties_even_f64" => Some("rint"),

        // Absolute value and sign manipulation.
        "fabsf32" => Some("fabsf"),
        "fabsf64" => Some("fabs"),
        "copysignf32" => Some("copysignf"),
        "copysignf64" => Some("copysign"),

        _ => None,
    }
}
