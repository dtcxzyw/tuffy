//! SIMD intrinsic handling for MIR → IR translation.

use rustc_middle::mir;
use rustc_middle::ty;

use tuffy_ir::instruction::{ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::typed::IntOperand;
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::type_size;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Translate a SIMD intrinsic to scalar IR.
    ///
    /// Returns `Some(true)` if the intrinsic was handled successfully,
    /// `Some(false)` if handling failed (e.g. missing args), or `None`
    /// if the intrinsic name is not a SIMD intrinsic.
    pub(super) fn translate_simd_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<bool> {
        if !name.starts_with("simd_") {
            return None;
        }
        Some(self.translate_simd_intrinsic_inner(name, substs, ir_args, destination_local))
    }

    fn translate_simd_intrinsic_inner(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> bool {
        match name {
            _ if ir_args.is_empty() => {
                eprintln!(
                    "WARNING: simd intrinsic {name} has 0 ir_args in {:?}",
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
            // Not a recognized SIMD intrinsic.
            _ => {
                eprintln!(
                    "WARNING: unhandled simd intrinsic: {name} in {:?}",
                    self.instance
                );
                false
            }
        }
    }

    // ── SIMD helper methods ──────────────────────────────────────────

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
}
