//! Intrinsic handling for MIR → IR translation.

mod arith;
mod atomic;
mod bit;
mod float;
mod memory;

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty;

use tuffy_ir::instruction::{AtomicRmwOp, FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::int_annotation_for_bytes;
use super::types::{int_ann_for_bytes, is_signed_int, translate_annotation, type_align, type_size};

/// Shared 64-bit unsigned annotation used by several intrinsic lowering paths.
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

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
                        ann.clone(),
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
            | "float_to_int_unchecked"
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
            | "fadd_fast"
            | "fsub_fast"
            | "fmul_fast"
            | "fdiv_fast"
            | "frem_fast"
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

    /// Resolves the intrinsic name and generic arguments for a call operand.
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

/// Maps rustc intrinsic names that are lowered as libc calls to their symbol names.
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
