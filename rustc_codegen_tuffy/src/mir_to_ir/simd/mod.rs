//! SIMD intrinsic handling for MIR → IR translation.

mod binop;
mod cast;
mod float;
mod info;
mod lane;
mod storage;
mod unary;

use rustc_middle::mir;
use rustc_middle::ty;

use tuffy_ir::instruction::{ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::typed::IntOperand;
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::intrinsic::intrinsic_to_libc;
use super::types::{int_ann_for_bytes, int_annotation_for_bytes, translate_annotation, type_size};

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Translate a SIMD intrinsic to scalar IR.
    ///
    /// Returns `Some(true)` if the intrinsic was handled successfully, or
    /// `None` if the intrinsic name is not a SIMD intrinsic.
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

    /// Lowers the body of a recognized `simd_*` intrinsic.
    fn translate_simd_intrinsic_inner(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> bool {
        match name {
            _ if ir_args.is_empty() => {
                self.tcx.dcx().fatal(format!(
                    "SIMD intrinsic {name} in {:?} has no translated arguments",
                    self.instance
                ));
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
                        u64_opt.clone(),
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

            "simd_shl" | "simd_shr" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                self.emit_simd_shift(ir_args, destination_local, name, substs, simd_bytes);
                true
            }

            "simd_cast" => {
                self.emit_simd_cast(ir_args, destination_local, substs);
                true
            }

            "simd_extract" => {
                self.emit_simd_extract(ir_args, destination_local, substs);
                true
            }

            "simd_insert" => {
                self.emit_simd_insert(ir_args, destination_local, substs);
                true
            }

            "simd_fma" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let elem_info = self.simd_elem_info_from_substs(substs);
                self.emit_simd_fma(ir_args, destination_local, simd_bytes, elem_info);
                true
            }

            "simd_relaxed_fma" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let elem_info = self.simd_elem_info_from_substs(substs);
                self.emit_simd_fma(ir_args, destination_local, simd_bytes, elem_info);
                true
            }

            "simd_ceil"
            | "simd_floor"
            | "simd_round"
            | "simd_round_ties_even"
            | "simd_trunc"
            | "simd_fsqrt"
            | "simd_fsin"
            | "simd_fcos"
            | "simd_fexp"
            | "simd_fexp2"
            | "simd_flog10"
            | "simd_flog2"
            | "simd_flog" => {
                let simd_bytes = self.simd_size_from_substs(substs).unwrap_or(16);
                let elem_info = self.simd_elem_info_from_substs(substs);
                self.emit_simd_float_unary_libcall(
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
                    u64_opt.clone(),
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
                        u64_opt.clone(),
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
                    u64_opt.clone(),
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
                        u64_opt.clone(),
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
                    u64_opt.clone(),
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
                        u64_opt.clone(),
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
                            u64_opt.clone(),
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
                            u64_opt.clone(),
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
                            u64_opt.clone(),
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
                self.tcx.dcx().fatal(format!(
                    "unhandled SIMD intrinsic {name} in {:?}",
                    self.instance
                ));
            }
        }
    }

    // ── SIMD helper methods ──────────────────────────────────────────
}
