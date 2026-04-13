//! Arithmetic intrinsic helpers for MIR to IR lowering.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers integer arithmetic intrinsics such as saturating and overflowing ops.
    pub(crate) fn translate_arithmetic_intrinsic(
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
            "float_to_int_unchecked" => {
                if let Some(&val) = ir_args.first() {
                    let src_ft = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| match t.kind() {
                            ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
                            ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
                            ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
                            ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
                            _ => None,
                        })
                        .unwrap_or(FloatType::F64);
                    let dst_ty = substs.get(1).and_then(|a| a.as_type());
                    let signed = dst_ty.is_some_and(|t| matches!(t.kind(), ty::Int(_)));
                    let bit_width = dst_ty
                        .and_then(|t| type_size(tcx, t))
                        .map(|s| (s * 8) as u32)
                        .unwrap_or(64);
                    let float_val = if matches!(self.builder.value_type(val), Some(Type::Float(_)))
                    {
                        val
                    } else {
                        self.builder.bitcast(
                            val.into(),
                            Type::Float(src_ft),
                            None,
                            Origin::synthetic(),
                        )
                    };
                    let raw = if signed {
                        self.builder.fp_to_si(
                            float_val.into(),
                            bit_width.min(64),
                            Origin::synthetic(),
                        )
                    } else {
                        self.builder.fp_to_ui(
                            float_val.into(),
                            bit_width.min(64),
                            Origin::synthetic(),
                        )
                    };
                    let result = if bit_width > 64 {
                        if signed {
                            self.builder
                                .sext(raw.into(), bit_width, Origin::synthetic())
                                .raw()
                        } else {
                            self.builder
                                .zext(raw.into(), bit_width, Origin::synthetic())
                                .raw()
                        }
                    } else {
                        raw.raw()
                    };
                    self.locals.set(destination_local, result);
                }
                true
            }
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
            "abort" => {
                let sym_id = self.symbols.intern("abort");
                let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                self.builder.call(
                    callee.into(),
                    vec![],
                    Type::Unit,
                    current_mem.into(),
                    None,
                    None,
                    Origin::synthetic(),
                );
                true
            }
            "catch_unwind" | "r#try" | "try" => {
                if ir_args.len() >= 3 {
                    let sym_id = self.symbols.intern("__rust_try");
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                    let (mem_out, data) = self.builder.call(
                        callee.into(),
                        vec![ir_args[0].into(), ir_args[1].into(), ir_args[2].into()],
                        Type::Int,
                        current_mem.into(),
                        None,
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
            "carrying_mul_add" => {
                if ir_args.len() >= 4 {
                    let elem_ty = substs.first().and_then(|a| a.as_type());
                    let elem_bytes = elem_ty.and_then(|t| type_size(tcx, t)).unwrap_or(8) as u32;
                    let is_signed = elem_ty.is_some_and(|t| is_signed_int(t));
                    let narrow_bits = elem_bytes * 8;
                    let (lo, hi) = if is_signed {
                        self.builder.s_carrying_mul_add(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            ir_args[2].into(),
                            ir_args[3].into(),
                            narrow_bits,
                            Origin::synthetic(),
                        )
                    } else {
                        self.builder.u_carrying_mul_add(
                            ir_args[0].into(),
                            ir_args[1].into(),
                            ir_args[2].into(),
                            ir_args[3].into(),
                            narrow_bits,
                            Origin::synthetic(),
                        )
                    };

                    let slot = self
                        .builder
                        .stack_slot(elem_bytes * 2, 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            lo.raw().into(),
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
                    let hi_addr =
                        self.builder
                            .ptradd(slot.into(), hi_offset.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            hi.raw().into(),
                            hi_addr.raw().into(),
                            elem_bytes,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                    self.locals.set(destination_local, slot);
                    self.stack_locals.mark(destination_local);
                }
                true
            }
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
                    let full_ann = Annotation::Int(ann);
                    let a_op =
                        tuffy_ir::instruction::Operand::annotated(ir_args[0], full_ann.clone());
                    let b_op =
                        tuffy_ir::instruction::Operand::annotated(ir_args[1], full_ann.clone());
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
                        let int_ann = IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::Unsigned,
                        };
                        let bits_val = self.builder.iconst(
                            bits as i64,
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
                                ann128.clone(),
                                Origin::synthetic(),
                            );
                            (hi.raw(), lo_fixed)
                        } else {
                            let hi_fixed = self.builder.select(
                                c_is_zero.into(),
                                zero.into(),
                                hi.raw().into(),
                                Type::Int,
                                ann128.clone(),
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
}
