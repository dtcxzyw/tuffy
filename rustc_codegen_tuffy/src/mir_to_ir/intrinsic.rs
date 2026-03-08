//! Intrinsic handling for MIR → IR translation.

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty;

use tuffy_ir::instruction::{AtomicRmwOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, MemoryOrdering, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::int_annotation_for_bytes;
use super::types::{
    default_int_annotation, default_int_type, translate_annotation, type_align, type_size,
};

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
        let current_mem = self.current_mem;
        let tcx = self.tcx;

        match name {
            // black_box: identity function, prevents optimizations.
            // Just copy the argument to the destination.
            "black_box" => {
                if let Some(&v) = ir_args.first() {
                    self.locals.set(destination_local, v);
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
                    let result = self.builder.count_ones(v.into(), 64, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
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
                    let result =
                        self.builder
                            .count_leading_zeros(v.into(), bits, bits, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // cttz / cttz_nonzero: count trailing zeros.
            "cttz" | "cttz_nonzero" => {
                if let Some(&v) = ir_args.first() {
                    let result =
                        self.builder
                            .count_trailing_zeros(v.into(), 64, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
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
                            } else {
                                // dyn Trait: read size from vtable (fallback to 0 for now).
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

            // arith_offset<T>(ptr, offset) → ptr + offset * sizeof(T)
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

            // ptr_offset_from_unsigned<T>(ptr1, ptr2) → (ptr1 - ptr2) / sizeof(T)
            "ptr_offset_from_unsigned" | "ptr_offset_from" => {
                if ir_args.len() >= 2 {
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
                        let sz = self.builder.iconst(
                            elem_size as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .div(diff.into(), sz.into(), I64, Origin::synthetic())
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
            "unchecked_shl" => {
                if ir_args.len() >= 2 {
                    let result = self.builder.shl(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        None,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }
            "unchecked_shr" => {
                if ir_args.len() >= 2 {
                    let result = self.builder.shr(
                        ir_args[0].into(),
                        ir_args[1].into(),
                        None,
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // Funnel shifts: fshl(a, b, c) = (a << c) | (b >> (bits - c))
            //                fshr(a, b, c) = (a << (bits - c)) | (b >> c)
            "unchecked_funnel_shl" | "unchecked_funnel_shr" => {
                if ir_args.len() >= 3 {
                    let a = ir_args[0];
                    let b = ir_args[1];
                    let c = ir_args[2];
                    let ty = substs.first().and_then(|arg| arg.as_type());
                    let bits = ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as i64)
                        .unwrap_or(64);
                    let ann = ty.and_then(translate_annotation);
                    let bits_val =
                        self.builder
                            .iconst(bits, 64, IntSignedness::DontCare, Origin::synthetic());
                    let complement =
                        self.builder
                            .sub(bits_val.into(), c.into(), I64, Origin::synthetic());
                    let (hi, lo) = if name == "unchecked_funnel_shl" {
                        (
                            self.builder
                                .shl(a.into(), c.into(), ann, Origin::synthetic()),
                            self.builder
                                .shr(b.into(), complement.into(), ann, Origin::synthetic()),
                        )
                    } else {
                        (
                            self.builder
                                .shl(a.into(), complement.into(), ann, Origin::synthetic()),
                            self.builder
                                .shr(b.into(), c.into(), ann, Origin::synthetic()),
                        )
                    };
                    let result = self
                        .builder
                        .or(hi.into(), lo.into(), I64, Origin::synthetic());
                    self.locals.set(destination_local, result.raw());
                }
                true
            }

            // minnumf32/minnumf64/maxnumf32/maxnumf64: IEEE 754 minNum/maxNum.
            "minnumf32" | "minnumf64" => {
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
            "maxnumf32" | "maxnumf64" => {
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
                let byte_count = if elem_size == 1 {
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
                let byte_count = if elem_size == 1 {
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
                let byte_count = if elem_size == 1 {
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
                    default_int_type(),
                    current_mem.into(),
                    None,
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
                        default_int_type(),
                        mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    let vy = self.builder.load(
                        ya.into(),
                        chunk,
                        default_int_type(),
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
                    default_int_type(),
                    ordering,
                    current_mem.into(),
                    default_int_annotation(),
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
                let expected = ir_args[1];
                let new_val = ir_args[2];
                let ordering = parse_atomic_ordering(name);

                let (new_mem, actual_old) = self.builder.atomic_cmpxchg(
                    ptr.into(),
                    expected.into(),
                    new_val.into(),
                    default_int_type(),
                    ordering,
                    ordering,
                    current_mem.into(),
                    default_int_annotation(),
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
                    default_int_type(),
                    ordering,
                    current_mem.into(),
                    default_int_annotation(),
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
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xsub") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Sub,
                        ptr.into(),
                        operand.into(),
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_and") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::And,
                        ptr.into(),
                        operand.into(),
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_or") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Or,
                        ptr.into(),
                        operand.into(),
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xor") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Xor,
                        ptr.into(),
                        operand.into(),
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else {
                    // Unsupported ops: nand, max, min, umax, umin — use atomic load/store.
                    let (mem1, old) = self.builder.load_atomic(
                        ptr.into(),
                        default_int_type(),
                        ordering,
                        current_mem.into(),
                        default_int_annotation(),
                        Origin::synthetic(),
                    );

                    let new_val = if name.starts_with("atomic_nand") {
                        let a =
                            self.builder
                                .and(old.into(), operand.into(), I64, Origin::synthetic());
                        let all_ones = self.builder.iconst(
                            -1,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .xor(a.into(), all_ones.into(), I64, Origin::synthetic())
                            .raw()
                    } else if name.starts_with("atomic_umax") {
                        let _bits = (elem_size * 8) as u32;
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
                            default_int_type(),
                            default_int_annotation(),
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_umin") {
                        let _bits = (elem_size * 8) as u32;
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
                            default_int_type(),
                            default_int_annotation(),
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_max") {
                        let _bits = (elem_size * 8) as u32;
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
                            default_int_type(),
                            default_int_annotation(),
                            Origin::synthetic(),
                        )
                    } else {
                        // atomic_min
                        let _bits = (elem_size * 8) as u32;
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
                            default_int_type(),
                            default_int_annotation(),
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

            _ => None,
        }
    }

    /// Check if the given function operand is a compiler intrinsic.
    /// Returns the intrinsic name and generic args (for extracting type parameters).
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

/// Map compiler intrinsics to libc/compiler-rt symbol names.
/// Returns None for intrinsics that need inline handling or aren't supported.
pub(super) fn intrinsic_to_libc(name: &str) -> Option<&'static str> {
    match name {
        // compare_bytes(left, right, count) -> i32 maps directly to memcmp.
        "compare_bytes" => Some("memcmp"),
        _ => None,
    }
}
