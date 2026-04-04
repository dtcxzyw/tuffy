//! Intrinsic handling for MIR → IR translation.

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty;

use tuffy_ir::instruction::{AtomicRmwOp, FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::typed::IntOperand;
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
        let current_mem = self.current_mem;
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

            // assume: optimizer hint, no runtime effect. Treat as no-op.
            "assume" => true,

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

            // Algebraic float intrinsics: same as regular ops but compiler may reassociate.
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

            // ── SIMD platform intrinsics ──────────────────────────────────
            // Lower simd_* intrinsics to scalar IR.  We handle variable-width
            // SIMD types by normalizing all args to stack pointers.
            n if n.starts_with("simd_") && ir_args.is_empty() => {
                eprintln!(
                    "WARNING: simd intrinsic {n} has 0 ir_args in {:?}",
                    self.instance,
                );
                false
            }

            "simd_bitmask" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let u64_opt = Some(Annotation::Int(u64_int));
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let src = self.ensure_simd_on_stack(ir_args[0], simd_bytes);

                let n_words = simd_bytes.div_ceil(8);
                let mask_c = self.builder.iconst(
                    0x8080_8080_8080_8080u64 as i64,
                    64,
                    IntSignedness::Unsigned,
                    o!(),
                );
                let magic = self.builder.iconst(
                    0x0002_0408_1020_4081u64 as i64,
                    64,
                    IntSignedness::Unsigned,
                    o!(),
                );
                let sh56 = self
                    .builder
                    .iconst(56i64, 64, IntSignedness::Unsigned, o!());

                let mut result = self
                    .builder
                    .iconst(0i64, 64, IntSignedness::Unsigned, o!())
                    .raw();
                for w in 0..n_words {
                    let word_ptr: ValueRef = if w == 0 {
                        src
                    } else {
                        let off =
                            self.builder
                                .iconst(w as i64 * 8, 64, IntSignedness::Unsigned, o!());
                        self.builder.ptradd(src.into(), off.into(), 0, o!()).raw()
                    };
                    let word = self.builder.load(
                        word_ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        u64_opt,
                        o!(),
                    );
                    let masked = self.builder.and(word.into(), mask_c.into(), u64_int, o!());
                    let prod = self.builder.mul(masked.into(), magic.into(), u64_int, o!());
                    let bits = self.builder.shr(prod.into(), sh56.into(), u64_int, o!());
                    if w == 0 {
                        result = bits.raw();
                    } else {
                        let shift =
                            self.builder
                                .iconst(w as i64 * 8, 64, IntSignedness::Unsigned, o!());
                        let shifted = self.builder.shl(bits.into(), shift.into(), u64_int, o!());
                        result = self
                            .builder
                            .or(result.into(), shifted.into(), u64_int, o!())
                            .raw();
                    }
                }
                self.locals.set(destination_local, result);
                true
            }

            "simd_eq" | "simd_ne" | "simd_gt" | "simd_lt" | "simd_ge" | "simd_le" => {
                let cmp_op = match name {
                    "simd_eq" => ICmpOp::Eq,
                    "simd_ne" => ICmpOp::Ne,
                    "simd_gt" => ICmpOp::Gt,
                    "simd_lt" => ICmpOp::Lt,
                    "simd_ge" => ICmpOp::Ge,
                    _ => ICmpOp::Le,
                };
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                self.emit_simd_cmp_byte(ir_args, destination_local, cmp_op, simd_bytes);
                true
            }

            "simd_or" | "simd_and" | "simd_xor" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                self.emit_simd_binop_qword(ir_args, destination_local, name, simd_bytes);
                true
            }

            "simd_add" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                self.emit_simd_add(ir_args, destination_local, simd_bytes);
                true
            }

            "simd_mul" | "simd_sub" | "simd_div" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let elem_info = self.simd_elem_info_from_substs(substs);
                self.emit_simd_elementwise_binop(
                    ir_args,
                    destination_local,
                    name,
                    simd_bytes,
                    elem_info,
                );
                true
            }

            "simd_neg" | "simd_fabs" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let elem_info = self.simd_elem_info_from_substs(substs);
                self.emit_simd_unary_op(ir_args, destination_local, name, simd_bytes, elem_info);
                true
            }

            "simd_reduce_or" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let u64_opt = Some(Annotation::Int(u64_int));
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let src = self.ensure_simd_on_stack(ir_args[0], simd_bytes);

                let n_words = simd_bytes.div_ceil(8);
                let first = self.builder.load(
                    src.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    u64_opt,
                    o!(),
                );
                let mut acc: ValueRef = first;
                for w in 1..n_words {
                    let off = self
                        .builder
                        .iconst(w as i64 * 8, 64, IntSignedness::Unsigned, o!());
                    let ptr = self.builder.ptradd(src.into(), off.into(), 0, o!());
                    let word = self.builder.load(
                        ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        u64_opt,
                        o!(),
                    );
                    acc = self
                        .builder
                        .or(acc.into(), word.into(), u64_int, o!())
                        .raw();
                }
                let sh32 = self
                    .builder
                    .iconst(32i64, 64, IntSignedness::Unsigned, o!());
                let f1 = self.builder.shr(acc.into(), sh32.into(), u64_int, o!());
                let acc2 = self.builder.or(acc.into(), f1.into(), u64_int, o!());
                let sh16 = self
                    .builder
                    .iconst(16i64, 64, IntSignedness::Unsigned, o!());
                let f2 = self.builder.shr(acc2.into(), sh16.into(), u64_int, o!());
                let acc3 = self.builder.or(acc2.into(), f2.into(), u64_int, o!());
                let sh8 = self.builder.iconst(8i64, 64, IntSignedness::Unsigned, o!());
                let f3 = self.builder.shr(acc3.into(), sh8.into(), u64_int, o!());
                let result = self.builder.or(acc3.into(), f3.into(), u64_int, o!());
                let mask_ff = self
                    .builder
                    .iconst(0xFFi64, 64, IntSignedness::Unsigned, o!());
                let byte_result = self
                    .builder
                    .and(result.into(), mask_ff.into(), u64_int, o!());

                self.locals.set(destination_local, byte_result.raw());
                true
            }

            "simd_splat" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let elem_val = ir_args[0];
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);

                // Determine per-element store size from the IR value type.
                let elem_size: u32 = match self.builder.value_type(elem_val) {
                    Some(Type::Float(FloatType::F32)) => 4,
                    Some(Type::Float(FloatType::F64)) => 8,
                    Some(Type::Float(FloatType::F16 | FloatType::BF16)) => 2,
                    Some(Type::Float(FloatType::F128)) => 16,
                    _ => 1, // integer — use byte-splat
                };

                if elem_size == 1 {
                    // Byte-splat: mask to 8 bits, then broadcast via multiply.
                    let mask_ff = self
                        .builder
                        .iconst(0xFFi64, 64, IntSignedness::Unsigned, o!());
                    let masked = self
                        .builder
                        .and(elem_val.into(), mask_ff.into(), u64_int, o!());
                    let rep = self.builder.iconst(
                        0x0101_0101_0101_0101u64 as i64,
                        64,
                        IntSignedness::Unsigned,
                        o!(),
                    );
                    let splat_word = self.builder.mul(masked.into(), rep.into(), u64_int, o!());

                    if simd_bytes <= 8 {
                        self.locals.set(destination_local, splat_word.raw());
                    } else {
                        let slot = self.builder.stack_slot(simd_bytes, 0, o!());
                        let n_words = simd_bytes.div_ceil(8);
                        for w in 0..n_words {
                            let dst: ValueRef = if w == 0 {
                                slot
                            } else {
                                let off = self.builder.iconst(
                                    w as i64 * 8,
                                    64,
                                    IntSignedness::Unsigned,
                                    o!(),
                                );
                                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
                            };
                            self.current_mem = self
                                .builder
                                .store(
                                    splat_word.raw().into(),
                                    dst.into(),
                                    8,
                                    self.current_mem.into(),
                                    o!(),
                                )
                                .raw();
                        }
                        self.locals.set(destination_local, slot);
                    }
                } else {
                    // Non-byte element (f32, f64, etc.): store element at each
                    // lane position.
                    let slot = self.builder.stack_slot(simd_bytes, 0, o!());
                    let n_lanes = simd_bytes / elem_size;
                    for i in 0..n_lanes {
                        let dst: ValueRef = if i == 0 {
                            slot
                        } else {
                            let off = self.builder.iconst(
                                (i * elem_size) as i64,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                elem_val.into(),
                                dst.into(),
                                elem_size,
                                self.current_mem.into(),
                                o!(),
                            )
                            .raw();
                    }
                    self.locals.set(destination_local, slot);
                }
                true
            }

            "simd_reduce_all" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let u64_opt = Some(Annotation::Int(u64_int));
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let src = self.ensure_simd_on_stack(ir_args[0], simd_bytes);

                // AND all qwords together.
                let n_words = simd_bytes.div_ceil(8);
                let first = self.builder.load(
                    src.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    u64_opt,
                    o!(),
                );
                let mut acc: ValueRef = first;
                for w in 1..n_words {
                    let off = self
                        .builder
                        .iconst(w as i64 * 8, 64, IntSignedness::Unsigned, o!());
                    let ptr = self.builder.ptradd(src.into(), off.into(), 0, o!());
                    let word = self.builder.load(
                        ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        u64_opt,
                        o!(),
                    );
                    acc = self
                        .builder
                        .and(acc.into(), word.into(), u64_int, o!())
                        .raw();
                }
                // Fold qword down to a single byte via AND.
                let sh32 = self
                    .builder
                    .iconst(32i64, 64, IntSignedness::Unsigned, o!());
                let f1 = self.builder.shr(acc.into(), sh32.into(), u64_int, o!());
                let acc2 = self.builder.and(acc.into(), f1.into(), u64_int, o!());
                let sh16 = self
                    .builder
                    .iconst(16i64, 64, IntSignedness::Unsigned, o!());
                let f2 = self.builder.shr(acc2.into(), sh16.into(), u64_int, o!());
                let acc3 = self.builder.and(acc2.into(), f2.into(), u64_int, o!());
                let sh8 = self.builder.iconst(8i64, 64, IntSignedness::Unsigned, o!());
                let f3 = self.builder.shr(acc3.into(), sh8.into(), u64_int, o!());
                let result = self.builder.and(acc3.into(), f3.into(), u64_int, o!());
                // Mask and test lowest byte (0xFF = all-true for i8 masks).
                let mask_ff = self
                    .builder
                    .iconst(0xFFi64, 64, IntSignedness::Unsigned, o!());
                let byte_result = self
                    .builder
                    .and(result.into(), mask_ff.into(), u64_int, o!());

                self.locals.set(destination_local, byte_result.raw());
                true
            }

            "simd_reduce_any" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let u64_opt = Some(Annotation::Int(u64_int));
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let src = self.ensure_simd_on_stack(ir_args[0], simd_bytes);

                let n_words = simd_bytes.div_ceil(8);
                let first = self.builder.load(
                    src.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    u64_opt,
                    o!(),
                );
                let mut acc: ValueRef = first;
                for w in 1..n_words {
                    let off = self
                        .builder
                        .iconst(w as i64 * 8, 64, IntSignedness::Unsigned, o!());
                    let ptr = self.builder.ptradd(src.into(), off.into(), 0, o!());
                    let word = self.builder.load(
                        ptr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        u64_opt,
                        o!(),
                    );
                    acc = self
                        .builder
                        .or(acc.into(), word.into(), u64_int, o!())
                        .raw();
                }
                let sh32 = self
                    .builder
                    .iconst(32i64, 64, IntSignedness::Unsigned, o!());
                let f1 = self.builder.shr(acc.into(), sh32.into(), u64_int, o!());
                let acc2 = self.builder.or(acc.into(), f1.into(), u64_int, o!());
                let sh16 = self
                    .builder
                    .iconst(16i64, 64, IntSignedness::Unsigned, o!());
                let f2 = self.builder.shr(acc2.into(), sh16.into(), u64_int, o!());
                let acc3 = self.builder.or(acc2.into(), f2.into(), u64_int, o!());
                let sh8 = self.builder.iconst(8i64, 64, IntSignedness::Unsigned, o!());
                let f3 = self.builder.shr(acc3.into(), sh8.into(), u64_int, o!());
                let result = self.builder.or(acc3.into(), f3.into(), u64_int, o!());
                let mask_ff = self
                    .builder
                    .iconst(0xFFi64, 64, IntSignedness::Unsigned, o!());
                let byte_result = self
                    .builder
                    .and(result.into(), mask_ff.into(), u64_int, o!());

                self.locals.set(destination_local, byte_result.raw());
                true
            }

            "simd_shuffle" => {
                macro_rules! o {
                    () => {
                        Origin::synthetic()
                    };
                }
                let u64_int = IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                };
                let u64_opt = Some(Annotation::Int(u64_int));

                // Determine element size from the first generic arg (element type).
                let elem_size: u32 = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(self.tcx, t))
                    .unwrap_or(1) as u32;

                // Input vector size from the first arg's type.
                let input_simd_bytes = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|_| {
                        // Element count from second generic arg.
                        substs
                            .get(1)
                            .and_then(|c| c.as_const())
                            .and_then(|c| c.try_to_target_usize(self.tcx))
                    })
                    .map(|n| (n as u32) * elem_size)
                    .unwrap_or(16);

                // The third argument is the index array.
                // For simd_shuffle, args are: (vec_a, vec_b, indices).
                // indices is a [u32; N] constant array.
                let n_input_lanes = input_simd_bytes / elem_size;
                let output_lanes = if ir_args.len() >= 3 {
                    // Determine output lanes from the index array type via substs.
                    // The index array length IS the output lane count.
                    // We'll infer it from the return type.
                    let ret_ty = self.monomorphize(self.mir.local_decls[destination_local].ty);
                    type_size(self.tcx, ret_ty).unwrap_or(input_simd_bytes as u64) as u32
                        / elem_size
                } else {
                    n_input_lanes
                };

                let output_bytes = output_lanes * elem_size;

                // Place both input vectors on the stack contiguously.
                let concat_bytes = input_simd_bytes * 2;
                let concat_slot = self.builder.stack_slot(concat_bytes, 0, o!());
                if ir_args.len() >= 2 {
                    let a_ptr = self.ensure_simd_on_stack(ir_args[0], input_simd_bytes);
                    let b_ptr = self.ensure_simd_on_stack(ir_args[1], input_simd_bytes);
                    // Copy a to concat_slot[0..input_simd_bytes]
                    for w in 0..input_simd_bytes.div_ceil(8) {
                        let load_size = 8.min(input_simd_bytes - w * 8);
                        let src_off = if w == 0 {
                            a_ptr
                        } else {
                            let off = self.builder.iconst(
                                w as i64 * 8,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
                        };
                        let val = self.builder.load(
                            src_off.into(),
                            load_size,
                            Type::Int,
                            self.current_mem.into(),
                            u64_opt,
                            o!(),
                        );
                        let dst_off = if w == 0 {
                            concat_slot
                        } else {
                            let off = self.builder.iconst(
                                w as i64 * 8,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder
                                .ptradd(concat_slot.into(), off.into(), 0, o!())
                                .raw()
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                dst_off.into(),
                                load_size,
                                self.current_mem.into(),
                                o!(),
                            )
                            .raw();
                    }
                    // Copy b to concat_slot[input_simd_bytes..]
                    for w in 0..input_simd_bytes.div_ceil(8) {
                        let load_size = 8.min(input_simd_bytes - w * 8);
                        let src_off = if w == 0 {
                            b_ptr
                        } else {
                            let off = self.builder.iconst(
                                w as i64 * 8,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
                        };
                        let val = self.builder.load(
                            src_off.into(),
                            load_size,
                            Type::Int,
                            self.current_mem.into(),
                            u64_opt,
                            o!(),
                        );
                        let dest_byte_off = input_simd_bytes + w * 8;
                        let off = self.builder.iconst(
                            dest_byte_off as i64,
                            64,
                            IntSignedness::Unsigned,
                            o!(),
                        );
                        let dst = self
                            .builder
                            .ptradd(concat_slot.into(), off.into(), 0, o!())
                            .raw();
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                dst.into(),
                                load_size,
                                self.current_mem.into(),
                                o!(),
                            )
                            .raw();
                    }
                }

                // Read indices from the third argument and build output.
                let out_slot = self.builder.stack_slot(output_bytes.max(8), 0, o!());
                if ir_args.len() >= 3 {
                    let idx_ptr = self.ensure_simd_on_stack(ir_args[2], output_lanes * 4);
                    for i in 0..output_lanes {
                        // Load index as u32.
                        let idx_off = if i == 0 {
                            idx_ptr
                        } else {
                            let off = self.builder.iconst(
                                i as i64 * 4,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder
                                .ptradd(idx_ptr.into(), off.into(), 0, o!())
                                .raw()
                        };
                        let idx_val = self.builder.load(
                            idx_off.into(),
                            4,
                            Type::Int,
                            self.current_mem.into(),
                            Some(Annotation::Int(IntAnnotation {
                                bit_width: 32,
                                signedness: IntSignedness::Unsigned,
                            })),
                            o!(),
                        );
                        // Compute source byte offset: idx * elem_size.
                        let byte_off = if elem_size == 1 {
                            idx_val
                        } else {
                            let es = self.builder.iconst(
                                elem_size as i64,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder
                                .mul(idx_val.into(), es.into(), u64_int, o!())
                                .raw()
                        };
                        let src_elem = self
                            .builder
                            .ptradd(concat_slot.into(), byte_off.into(), 0, o!())
                            .raw();
                        let elem_val = self.builder.load(
                            src_elem.into(),
                            elem_size,
                            Type::Int,
                            self.current_mem.into(),
                            u64_opt,
                            o!(),
                        );
                        let dst_elem = if i == 0 {
                            out_slot
                        } else {
                            let off = self.builder.iconst(
                                (i * elem_size) as i64,
                                64,
                                IntSignedness::Unsigned,
                                o!(),
                            );
                            self.builder
                                .ptradd(out_slot.into(), off.into(), 0, o!())
                                .raw()
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                elem_val.into(),
                                dst_elem.into(),
                                elem_size,
                                self.current_mem.into(),
                                o!(),
                            )
                            .raw();
                    }
                }

                let result = self.simd_result_from_stack(out_slot, output_bytes);
                self.locals.set(destination_local, result);
                true
            }

            // Not handled here — fall through to translate_memory_intrinsic.
            other => {
                if other.starts_with("simd_") {
                    eprintln!(
                        "WARNING: unhandled simd intrinsic: {other} in {:?}",
                        self.instance
                    );
                }
                false
            }
        }
    }

    // ── SIMD helper methods ──────────────────────────────────────────

    /// Get the SIMD type size in bytes from the first generic arg.
    fn simd_size_from_substs(&self, substs: &'tcx ty::List<ty::GenericArg<'tcx>>) -> Option<u32> {
        substs
            .first()
            .and_then(|a| a.as_type())
            .and_then(|t| type_size(self.tcx, t))
            .map(|sz| sz as u32)
    }

    /// Extract SIMD element info: (elem_size_bytes, Option<FloatType>).
    /// Returns None if the element type cannot be determined.
    fn simd_elem_info_from_substs(
        &self,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> (u32, Option<FloatType>) {
        let simd_ty = substs.first().and_then(|a| a.as_type());
        if let Some(simd_ty) = simd_ty
            && let ty::Adt(def, adt_substs) = simd_ty.kind()
        {
            // Simd<T, N> — the element type is the first generic arg.
            if let Some(elem_ty) = adt_substs.first().and_then(|a| a.as_type()) {
                let elem_size = type_size(self.tcx, elem_ty).unwrap_or(1) as u32;
                let float_ty = match elem_ty.kind() {
                    ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
                    ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
                    ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
                    ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
                    _ => None,
                };
                return (elem_size, float_ty);
            }
            // Fallback: look at the first field (may be [T; N]).
            let variant = def.non_enum_variant();
            if let Some(field) = variant.fields.iter().next() {
                let field_ty = field.ty(self.tcx, adt_substs);
                let inner_ty = match field_ty.kind() {
                    ty::Array(elem, _) => *elem,
                    _ => field_ty,
                };
                let elem_size = type_size(self.tcx, inner_ty).unwrap_or(1) as u32;
                let float_ty = match inner_ty.kind() {
                    ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
                    ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
                    ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
                    ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
                    _ => None,
                };
                return (elem_size, float_ty);
            }
        }
        (1, None) // default: byte-sized integer
    }

    /// Ensure a SIMD value is on the stack.  If the value is already
    /// a Ptr (16-byte SIMD), return it.  If it's an Int (≤8 byte SIMD),
    /// spill to a temporary stack slot.
    fn ensure_simd_on_stack(&mut self, val: ValueRef, size: u32) -> ValueRef {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        if matches!(self.builder.value_type(val), Some(Type::Ptr(_))) {
            val
        } else {
            let store_size = if size <= 8 { 8 } else { size };
            let slot = self.builder.stack_slot(store_size, 0, o!());
            self.current_mem = self
                .builder
                .store(
                    val.into(),
                    slot.into(),
                    store_size.min(8),
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
            slot
        }
    }

    /// Load the result from a stack slot as Int if the SIMD type fits in
    /// a register (≤8 bytes), otherwise leave as a stack pointer.
    fn simd_result_from_stack(&mut self, slot: ValueRef, size: u32) -> ValueRef {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        if size <= 8 {
            let u64_opt = Some(Annotation::Int(IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Unsigned,
            }));
            self.builder.load(
                slot.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt,
                o!(),
            )
        } else {
            slot
        }
    }

    /// Emit a per-byte comparison of two SIMD vectors.
    fn emit_simd_cmp_byte(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op: ICmpOp,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let s8_int = IntAnnotation {
            bit_width: 8,
            signedness: IntSignedness::Signed,
        };
        let s8_opt = Some(Annotation::Int(s8_int));
        let s8_annotation = Annotation::Int(s8_int);
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());

        for i in 0..simd_bytes {
            let a_addr: ValueRef = if i == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if i == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_byte = self.builder.load(
                a_addr.into(),
                1,
                Type::Int,
                self.current_mem.into(),
                s8_opt,
                o!(),
            );
            let b_byte = self.builder.load(
                b_addr.into(),
                1,
                Type::Int,
                self.current_mem.into(),
                s8_opt,
                o!(),
            );
            let a_op = IntOperand::from(IrOperand::annotated(a_byte, s8_annotation));
            let b_op = IntOperand::from(IrOperand::annotated(b_byte, s8_annotation));
            let cmp = self.builder.icmp(op, a_op, b_op, o!());
            let ff = self.builder.iconst(-1i64, 8, IntSignedness::Signed, o!());
            let zero_byte = self.builder.iconst(0i64, 8, IntSignedness::Signed, o!());
            let res_byte = self.builder.select(
                cmp.into(),
                ff.raw().into(),
                zero_byte.raw().into(),
                Type::Int,
                s8_opt,
                o!(),
            );

            let dst_addr: ValueRef = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    res_byte.into(),
                    dst_addr.into(),
                    1,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit a qword-level bitwise operation on two SIMD vectors.
    fn emit_simd_binop_qword(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op: &str,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let u64_int = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let u64_opt = Some(Annotation::Int(u64_int));
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_words = simd_bytes.div_ceil(8);

        for half in 0..n_words {
            let offset_val = half as i64 * 8;
            let a_addr: ValueRef = if half == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if half == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_val = self.builder.load(
                a_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt,
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt,
                o!(),
            );

            let result = match op {
                "simd_or" => self.builder.or(a_val.into(), b_val.into(), u64_int, o!()),
                "simd_and" => self.builder.and(a_val.into(), b_val.into(), u64_int, o!()),
                "simd_xor" => self.builder.xor(a_val.into(), b_val.into(), u64_int, o!()),
                _ => unreachable!(),
            };

            let dst_addr: ValueRef = if half == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    result.raw().into(),
                    dst_addr.into(),
                    8,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit per-byte addition of two SIMD vectors using SWAR trick.
    fn emit_simd_add(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let u64_int = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let u64_opt = Some(Annotation::Int(u64_int));
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_words = simd_bytes.div_ceil(8);
        let mask_7f = self.builder.iconst(
            0x7F7F_7F7F_7F7F_7F7Fu64 as i64,
            64,
            IntSignedness::Unsigned,
            o!(),
        );
        let mask_80 = self.builder.iconst(
            0x8080_8080_8080_8080u64 as i64,
            64,
            IntSignedness::Unsigned,
            o!(),
        );

        for w in 0..n_words {
            let offset_val = w as i64 * 8;
            let a_addr: ValueRef = if w == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if w == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_val = self.builder.load(
                a_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt,
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt,
                o!(),
            );

            // SWAR per-byte add: ((a & 0x7F...) + (b & 0x7F...)) ^ ((a ^ b) & 0x80...)
            let a_lo = self
                .builder
                .and(a_val.into(), mask_7f.into(), u64_int, o!());
            let b_lo = self
                .builder
                .and(b_val.into(), mask_7f.into(), u64_int, o!());
            let sum_lo = self.builder.add(a_lo.into(), b_lo.into(), u64_int, o!());
            let axb = self.builder.xor(a_val.into(), b_val.into(), u64_int, o!());
            let carry = self.builder.and(axb.into(), mask_80.into(), u64_int, o!());
            let result = self.builder.xor(sum_lo.into(), carry.into(), u64_int, o!());

            let dst_addr: ValueRef = if w == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    result.raw().into(),
                    dst_addr.into(),
                    8,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit a per-element binary operation (mul, sub, div) on two SIMD vectors.
    fn emit_simd_elementwise_binop(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op_name: &str,
        simd_bytes: u32,
        elem_info: (u32, Option<FloatType>),
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let (elem_size, float_ty) = elem_info;
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;

        for i in 0..n_lanes {
            let byte_off = (i * elem_size) as i64;
            let a_addr = if i == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr = if i == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let dst_addr = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };

            if let Some(fty) = float_ty {
                let load_ty = Type::Float(fty);
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    load_ty.clone(),
                    self.current_mem.into(),
                    None,
                    o!(),
                );
                let b_val = self.builder.load(
                    b_addr.into(),
                    elem_size,
                    load_ty.clone(),
                    self.current_mem.into(),
                    None,
                    o!(),
                );
                let flags = FpRewriteFlags::default();
                let result = match op_name {
                    "simd_mul" => {
                        self.builder
                            .fmul(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    "simd_sub" => {
                        self.builder
                            .fsub(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    "simd_div" => {
                        self.builder
                            .fdiv(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    _ => {
                        self.builder
                            .fmul(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                };
                self.current_mem = self
                    .builder
                    .store(
                        result.raw().into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            } else {
                // Integer element
                let int_ann = IntAnnotation {
                    bit_width: (elem_size * 8),
                    signedness: IntSignedness::DontCare,
                };
                let ann_opt = Some(Annotation::Int(int_ann));
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    Type::Int,
                    self.current_mem.into(),
                    ann_opt,
                    o!(),
                );
                let b_val = self.builder.load(
                    b_addr.into(),
                    elem_size,
                    Type::Int,
                    self.current_mem.into(),
                    ann_opt,
                    o!(),
                );
                let result = match op_name {
                    "simd_mul" => self.builder.mul(a_val.into(), b_val.into(), int_ann, o!()),
                    "simd_sub" => self.builder.sub(a_val.into(), b_val.into(), int_ann, o!()),
                    _ => self.builder.mul(a_val.into(), b_val.into(), int_ann, o!()),
                };
                self.current_mem = self
                    .builder
                    .store(
                        result.raw().into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            }
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit a per-element unary operation (neg, fabs) on a SIMD vector.
    fn emit_simd_unary_op(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op_name: &str,
        simd_bytes: u32,
        elem_info: (u32, Option<FloatType>),
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let (elem_size, float_ty) = elem_info;
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;

        for i in 0..n_lanes {
            let byte_off = (i * elem_size) as i64;
            let a_addr = if i == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let dst_addr = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };

            if let Some(fty) = float_ty {
                let load_ty = Type::Float(fty);
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    load_ty.clone(),
                    self.current_mem.into(),
                    None,
                    o!(),
                );
                let result = match op_name {
                    "simd_neg" => self.builder.fneg(a_val.into(), load_ty.clone(), o!()).raw(),
                    "simd_fabs" => {
                        // fabs via: bitcast to int, clear sign bit, bitcast back
                        let int_ann = IntAnnotation {
                            bit_width: (elem_size * 8),
                            signedness: IntSignedness::Unsigned,
                        };
                        let mask = match elem_size {
                            4 => 0x7FFF_FFFFi64,
                            8 => 0x7FFF_FFFF_FFFF_FFFFi64,
                            2 => 0x7FFFi64,
                            _ => 0x7FFF_FFFFi64,
                        };
                        let mask_val =
                            self.builder
                                .iconst(mask, elem_size * 8, IntSignedness::Unsigned, o!());
                        let as_int = self.builder.bitcast(
                            a_val.into(),
                            Type::Int,
                            Some(Annotation::Int(int_ann)),
                            o!(),
                        );
                        let cleared =
                            self.builder
                                .and(as_int.into(), mask_val.into(), int_ann, o!());
                        self.builder
                            .bitcast(cleared.raw().into(), load_ty.clone(), None, o!())
                    }
                    _ => self.builder.fneg(a_val.into(), load_ty.clone(), o!()).raw(),
                };
                self.current_mem = self
                    .builder
                    .store(
                        result.into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            } else {
                // Integer neg: 0 - x
                let int_ann = IntAnnotation {
                    bit_width: (elem_size * 8),
                    signedness: IntSignedness::DontCare,
                };
                let ann_opt = Some(Annotation::Int(int_ann));
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    Type::Int,
                    self.current_mem.into(),
                    ann_opt,
                    o!(),
                );
                let zero = self
                    .builder
                    .iconst(0, elem_size * 8, IntSignedness::DontCare, o!());
                let result = self.builder.sub(zero.into(), a_val.into(), int_ann, o!());
                self.current_mem = self
                    .builder
                    .store(
                        result.raw().into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            }
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
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

    /// 128-bit carrying_mul_add: computes a*b + carry + add as (lo_128, hi_128).
    /// Uses 64-bit partial products since 256-bit arithmetic isn't available.
    fn emit_carrying_mul_add_128(
        &mut self,
        ir_args: &[tuffy_ir::value::ValueRef],
        destination_local: rustc_middle::mir::Local,
        is_signed: bool,
    ) {
        use tuffy_ir::instruction::Origin;
        use tuffy_ir::types::{IntAnnotation, IntSignedness};
        use tuffy_ir::value::ValueRef;

        let o = || Origin::synthetic();
        let i64_ann = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let _i128_ann = IntAnnotation {
            bit_width: 128,
            signedness: IntSignedness::Unsigned,
        };

        // Split each 128-bit arg into (lo64, hi64) via stack
        let split_128 = |this: &mut Self, val: ValueRef| -> (ValueRef, ValueRef) {
            let slot = this.builder.stack_slot(16, 0, o());
            this.current_mem = this
                .builder
                .store(val.into(), slot.into(), 16, this.current_mem.into(), o())
                .raw();
            let lo = this.builder.load(
                slot.into(),
                8,
                Type::Int,
                this.current_mem.into(),
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let off8 = this.builder.iconst(8, 64, IntSignedness::Unsigned, o());
            let hi_ptr = this.builder.ptradd(slot.into(), off8.into(), 0, o());
            let hi = this.builder.load(
                hi_ptr.raw().into(),
                8,
                Type::Int,
                this.current_mem.into(),
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            (lo, hi)
        };

        let (a_lo, a_hi) = split_128(self, ir_args[0]);
        let (b_lo, b_hi) = split_128(self, ir_args[1]);
        let (c_lo, c_hi) = split_128(self, ir_args[2]);
        let (d_lo, d_hi) = split_128(self, ir_args[3]);

        // 4 partial products: a*b = (a_lo + a_hi*2^64) * (b_lo + b_hi*2^64)
        // Each uses 32-bit schoolbook multiply to get full 128-bit result (lo64, hi64).
        let (ll_lo, ll_hi) = self.emit_widening_mul_u64(a_lo, b_lo);
        let (lh_lo, lh_hi) = self.emit_widening_mul_u64(a_lo, b_hi);
        let (hl_lo, hl_hi) = self.emit_widening_mul_u64(a_hi, b_lo);
        let (hh_lo, hh_hi) = self.emit_widening_mul_u64(a_hi, b_hi);

        // Accumulate 256-bit product: [w0, w1, w2, w3] (each 64 bits)
        // w0 = ll_lo
        let w0 = ll_lo;

        // w1 = ll_hi + lh_lo + hl_lo (with carries into w2)
        let w1_a = self.builder.add(ll_hi.into(), lh_lo.into(), i64_ann, o());
        let c1_a = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w1_a.into(),
            ll_hi.into(),
            o(),
        );
        let w1 = self.builder.add(w1_a.into(), hl_lo.into(), i64_ann, o());
        let c1_b = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w1.into(),
            w1_a.into(),
            o(),
        );
        let c1_a_int = self.bool_to_u64(c1_a);
        let c1_b_int = self.bool_to_u64(c1_b);
        let c1 = self
            .builder
            .add(c1_a_int.into(), c1_b_int.into(), i64_ann, o());

        // w2 = lh_hi + hl_hi + hh_lo + c1
        let w2_a = self.builder.add(lh_hi.into(), hl_hi.into(), i64_ann, o());
        let c2_a = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2_a.into(),
            lh_hi.into(),
            o(),
        );
        let w2_b = self.builder.add(w2_a.into(), hh_lo.into(), i64_ann, o());
        let c2_b = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2_b.into(),
            w2_a.into(),
            o(),
        );
        let w2 = self.builder.add(w2_b.into(), c1.into(), i64_ann, o());
        let c2_c = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2.into(),
            w2_b.into(),
            o(),
        );
        let c2_a_int = self.bool_to_u64(c2_a);
        let c2_b_int = self.bool_to_u64(c2_b);
        let c2_c_int = self.bool_to_u64(c2_c);
        let c2_ab = self
            .builder
            .add(c2_a_int.into(), c2_b_int.into(), i64_ann, o());
        let c2 = self
            .builder
            .add(c2_ab.into(), c2_c_int.into(), i64_ann, o());

        // w3 = hh_hi + c2
        let w3 = self.builder.add(hh_hi.into(), c2.into(), i64_ann, o());

        // For signed: adjust high 128 bits
        // If a is negative (a_hi < 0 as signed), subtract b from high half
        // If b is negative (b_hi < 0 as signed), subtract a from high half
        let (w2_final, w3_final) = if is_signed {
            let zero = self.builder.iconst(0, 64, IntSignedness::Unsigned, o());
            let signed_ann = IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Signed,
            };
            // a negative?
            let a_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    a_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            // b negative?
            let b_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    b_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );

            // If a_neg, subtract b from (w2,w3)
            let sub_b_lo = self.builder.sub(w2.into(), b_lo.into(), i64_ann, o());
            let borrow1 = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                w2.into(),
                b_lo.into(),
                o(),
            );
            let borrow1_int = self.bool_to_u64(borrow1);
            let sub_b_hi_tmp = self.builder.sub(w3.into(), b_hi.into(), i64_ann, o());
            let sub_b_hi = self
                .builder
                .sub(sub_b_hi_tmp.into(), borrow1_int.into(), i64_ann, o());
            let w2_adj1 = self.builder.select(
                a_neg.into(),
                sub_b_lo.raw().into(),
                w2.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let w3_adj1 = self.builder.select(
                a_neg.into(),
                sub_b_hi.raw().into(),
                w3.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );

            // If b_neg, subtract a from (w2_adj1, w3_adj1)
            let sub_a_lo = self.builder.sub(w2_adj1.into(), a_lo.into(), i64_ann, o());
            let borrow2 = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                w2_adj1.into(),
                a_lo.into(),
                o(),
            );
            let borrow2_int = self.bool_to_u64(borrow2);
            let sub_a_hi_tmp = self.builder.sub(w3_adj1.into(), a_hi.into(), i64_ann, o());
            let sub_a_hi = self
                .builder
                .sub(sub_a_hi_tmp.into(), borrow2_int.into(), i64_ann, o());
            let w2_adj2 = self.builder.select(
                b_neg.into(),
                sub_a_lo.raw().into(),
                w2_adj1.into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let w3_adj2 = self.builder.select(
                b_neg.into(),
                sub_a_hi.raw().into(),
                w3_adj1.into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            (w2_adj2, w3_adj2)
        } else {
            (w2.raw(), w3.raw())
        };

        // Now add carry (c_lo, c_hi) and add (d_lo, d_hi) to the 256-bit product
        // Add carry to low 128 bits first, propagate carry into high 128 bits
        let add_to_256 = |this: &mut Self,
                          w0: ValueRef,
                          w1: ValueRef,
                          w2: ValueRef,
                          w3: ValueRef,
                          x_lo: ValueRef,
                          x_hi: ValueRef|
         -> (ValueRef, ValueRef, ValueRef, ValueRef) {
            let r0 = this.builder.add(w0.into(), x_lo.into(), i64_ann, o());
            let c0 =
                this.builder
                    .icmp(tuffy_ir::instruction::ICmpOp::Lt, r0.into(), w0.into(), o());
            let c0_int = this.bool_to_u64(c0);
            let r1_tmp = this.builder.add(w1.into(), x_hi.into(), i64_ann, o());
            let c1_tmp = this.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r1_tmp.into(),
                w1.into(),
                o(),
            );
            let r1 = this.builder.add(r1_tmp.into(), c0_int.into(), i64_ann, o());
            let c1_tmp2 = this.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r1.into(),
                r1_tmp.into(),
                o(),
            );
            let c1_a = this.bool_to_u64(c1_tmp);
            let c1_b = this.bool_to_u64(c1_tmp2);
            let c1_total = this.builder.add(c1_a.into(), c1_b.into(), i64_ann, o());
            let r2 = this.builder.add(w2.into(), c1_total.into(), i64_ann, o());
            let c2 =
                this.builder
                    .icmp(tuffy_ir::instruction::ICmpOp::Lt, r2.into(), w2.into(), o());
            let c2_int = this.bool_to_u64(c2);
            let r3 = this.builder.add(w3.into(), c2_int.into(), i64_ann, o());
            (r0.raw(), r1.raw(), r2.raw(), r3.raw())
        };

        let (r0, r1, r2, r3) = add_to_256(self, w0, w1.raw(), w2_final, w3_final, c_lo, c_hi);
        let (r0, r1, r2, r3) = add_to_256(self, r0, r1, r2, r3, d_lo, d_hi);

        // For signed types, unsigned add_to_256 doesn't sign-extend the 128-bit
        // carry/add values into the upper 128 bits. If the value was negative,
        // its unsigned representation is 2^128 too large, so subtract 1 from (r2,r3).
        let (r2, r3) = if is_signed {
            let signed_ann = IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Signed,
            };
            let zero_s = self.builder.iconst(0, 64, IntSignedness::Unsigned, o());
            let one_s = self.builder.iconst(1, 64, IntSignedness::Unsigned, o());

            // Sign extension for carry value (c_lo, c_hi)
            let c_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    c_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero_s.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            let c_adj = self.builder.select(
                c_neg.into(),
                one_s.raw().into(),
                zero_s.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let r2a = self.builder.sub(r2.into(), c_adj.into(), i64_ann, o());
            let c_borrow = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r2.into(),
                c_adj.into(),
                o(),
            );
            let c_borrow_int = self.bool_to_u64(c_borrow);
            let r3a = self
                .builder
                .sub(r3.into(), c_borrow_int.into(), i64_ann, o());

            // Sign extension for add value (d_lo, d_hi)
            let d_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    d_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero_s.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            let d_adj = self.builder.select(
                d_neg.into(),
                one_s.raw().into(),
                zero_s.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let r2b = self.builder.sub(r2a.into(), d_adj.into(), i64_ann, o());
            let d_borrow = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r2a.raw().into(),
                d_adj.into(),
                o(),
            );
            let d_borrow_int = self.bool_to_u64(d_borrow);
            let r3b = self
                .builder
                .sub(r3a.into(), d_borrow_int.into(), i64_ann, o());

            (r2b.raw(), r3b.raw())
        } else {
            (r2, r3)
        };

        // Store result: lo_128 = (r0, r1), hi_128 = (r2, r3)
        let slot = self.builder.stack_slot(32, 0, o());
        self.current_mem = self
            .builder
            .store(r0.into(), slot.into(), 8, self.current_mem.into(), o())
            .raw();
        let off8 = self.builder.iconst(8, 64, IntSignedness::Unsigned, o());
        let addr1 = self.builder.ptradd(slot.into(), off8.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r1.into(),
                addr1.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        let off16 = self.builder.iconst(16, 64, IntSignedness::Unsigned, o());
        let addr2 = self.builder.ptradd(slot.into(), off16.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r2.into(),
                addr2.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        let off24 = self.builder.iconst(24, 64, IntSignedness::Unsigned, o());
        let addr3 = self.builder.ptradd(slot.into(), off24.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r3.into(),
                addr3.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        self.locals.set(destination_local, slot);
        self.stack_locals.mark(destination_local);
    }

    /// Compute the full 128-bit unsigned product of two 64-bit values,
    /// returning (lo64, hi64). Uses schoolbook 32-bit partial products
    /// (same algorithm as `widening_mul_u64` in legalize.rs).
    fn emit_widening_mul_u64(
        &mut self,
        x: tuffy_ir::value::ValueRef,
        y: tuffy_ir::value::ValueRef,
    ) -> (tuffy_ir::value::ValueRef, tuffy_ir::value::ValueRef) {
        use tuffy_ir::instruction::{ICmpOp, Origin};
        use tuffy_ir::types::IntSignedness;

        let o = || Origin::synthetic();
        let i64_ann = tuffy_ir::types::IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };

        let c32 = self.builder.iconst(32, 64, IntSignedness::Unsigned, o());
        let mask32 = self
            .builder
            .iconst(0xFFFF_FFFF_i64, 64, IntSignedness::Unsigned, o());

        let x0 = self.builder.and(x.into(), mask32.into(), i64_ann, o());
        let x1 = self.builder.shr(x.into(), c32.into(), i64_ann, o());
        let y0 = self.builder.and(y.into(), mask32.into(), i64_ann, o());
        let y1 = self.builder.shr(y.into(), c32.into(), i64_ann, o());

        let p0 = self.builder.mul(x0.into(), y0.into(), i64_ann, o());
        let p1 = self.builder.mul(x0.into(), y1.into(), i64_ann, o());
        let p2 = self.builder.mul(x1.into(), y0.into(), i64_ann, o());
        let p3 = self.builder.mul(x1.into(), y1.into(), i64_ann, o());

        let p0_hi = self.builder.shr(p0.into(), c32.into(), i64_ann, o());
        let mid1 = self.builder.add(p0_hi.into(), p1.into(), i64_ann, o());
        let cmp = self.builder.icmp(ICmpOp::Lt, mid1.into(), p1.into(), o());
        let c1 = self.bool_to_u64(cmp);
        let mid = self.builder.add(mid1.into(), p2.into(), i64_ann, o());
        let cmp = self.builder.icmp(ICmpOp::Lt, mid.into(), p2.into(), o());
        let c2 = self.bool_to_u64(cmp);
        let total_carry = self.builder.add(c1.into(), c2.into(), i64_ann, o());

        let mid_shifted = self.builder.shl(mid.into(), c32.into(), i64_ann, o());
        let p0_lo = self.builder.and(p0.into(), mask32.into(), i64_ann, o());
        let lo = self
            .builder
            .or(mid_shifted.into(), p0_lo.into(), i64_ann, o());

        let mid_hi = self.builder.shr(mid.into(), c32.into(), i64_ann, o());
        let carry_shifted = self
            .builder
            .shl(total_carry.into(), c32.into(), i64_ann, o());
        let hi = self
            .builder
            .add(mid_hi.into(), carry_shifted.into(), i64_ann, o());
        let hi = self.builder.add(hi.into(), p3.into(), i64_ann, o());

        (lo.raw(), hi.raw())
    }

    fn bool_to_u64(&mut self, val: tuffy_ir::typed::BoolValue) -> tuffy_ir::typed::IntValue {
        self.builder.zext(val.raw().into(), 64, Origin::synthetic())
    }
}

/// Map compiler intrinsics to libc/compiler-rt symbol names.
/// Returns None for intrinsics that need inline handling or aren't supported.
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
