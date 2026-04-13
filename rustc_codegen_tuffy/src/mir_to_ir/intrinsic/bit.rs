//! Bit intrinsic helpers for MIR to IR lowering.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers integer bit-manipulation intrinsics such as `ctpop` and rotates.
    pub(crate) fn translate_bit_intrinsic(
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

            "ctlz" | "ctlz_nonzero" => {
                if let Some(&v) = ir_args.first() {
                    let bits = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    if bits <= 64 {
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
                    } else if bits == self.target_direct_abi_bits() {
                        let part_bytes = self.target_part_bytes() as u32;
                        let slot = self.builder.stack_slot(bits / 8, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                IrOperand::annotated(
                                    v,
                                    Annotation::Int(IntAnnotation {
                                        bit_width: bits,
                                        signedness: IntSignedness::Unsigned,
                                    }),
                                ),
                                slot.into(),
                                bits / 8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        let lo = self.builder.load(
                            slot.into(),
                            part_bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(part_bytes),
                            Origin::synthetic(),
                        );
                        let off = self.builder.iconst(
                            part_bytes as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let hi_addr =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        let hi = self.builder.load(
                            hi_addr.into(),
                            part_bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(part_bytes),
                            Origin::synthetic(),
                        );
                        let clz_hi = self.builder.count_leading_zeros(
                            hi.into(),
                            self.target_max_int_width,
                            64,
                            Origin::synthetic(),
                        );
                        let clz_lo = self.builder.count_leading_zeros(
                            lo.into(),
                            self.target_max_int_width,
                            64,
                            Origin::synthetic(),
                        );
                        let part_bits = self.builder.iconst(
                            self.target_max_int_width as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let zero = self.builder.iconst(
                            0,
                            self.target_max_int_width,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let hi_is_zero = self.builder.icmp(
                            tuffy_ir::instruction::ICmpOp::Eq,
                            hi.into(),
                            zero.into(),
                            Origin::synthetic(),
                        );
                        let adjusted = self.builder.add(
                            clz_lo.into(),
                            part_bits.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::Unsigned,
                            },
                            Origin::synthetic(),
                        );
                        let result = self.builder.select(
                            hi_is_zero.into(),
                            adjusted.into(),
                            clz_hi.into(),
                            Type::Int,
                            Some(Annotation::Int(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::Unsigned,
                            })),
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result);
                    } else {
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

            "cttz" | "cttz_nonzero" => {
                if let Some(&v) = ir_args.first() {
                    let bits = substs
                        .first()
                        .and_then(|a| a.as_type())
                        .and_then(|t| type_size(tcx, t))
                        .map(|sz| (sz * 8) as u32)
                        .unwrap_or(64);
                    if bits < 64 {
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
                    } else if bits == self.target_direct_abi_bits() {
                        let part_bytes = self.target_part_bytes() as u32;
                        let slot = self.builder.stack_slot(bits / 8, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                IrOperand::annotated(
                                    v,
                                    Annotation::Int(IntAnnotation {
                                        bit_width: bits,
                                        signedness: IntSignedness::Unsigned,
                                    }),
                                ),
                                slot.into(),
                                bits / 8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        let lo = self.builder.load(
                            slot.into(),
                            part_bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(part_bytes),
                            Origin::synthetic(),
                        );
                        let off = self.builder.iconst(
                            part_bytes as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let hi_addr =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        let hi = self.builder.load(
                            hi_addr.into(),
                            part_bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(part_bytes),
                            Origin::synthetic(),
                        );
                        let ctz_lo =
                            self.builder
                                .count_trailing_zeros(lo.into(), 64, Origin::synthetic());
                        let ctz_hi =
                            self.builder
                                .count_trailing_zeros(hi.into(), 64, Origin::synthetic());
                        let part_bits = self.builder.iconst(
                            self.target_max_int_width as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let zero = self.builder.iconst(
                            0,
                            self.target_max_int_width,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let lo_is_zero = self.builder.icmp(
                            tuffy_ir::instruction::ICmpOp::Eq,
                            lo.into(),
                            zero.into(),
                            Origin::synthetic(),
                        );
                        let adjusted = self.builder.add(
                            ctz_hi.into(),
                            part_bits.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::Unsigned,
                            },
                            Origin::synthetic(),
                        );
                        let result = self.builder.select(
                            lo_is_zero.into(),
                            adjusted.into(),
                            ctz_lo.into(),
                            Type::Int,
                            Some(Annotation::Int(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::Unsigned,
                            })),
                            Origin::synthetic(),
                        );
                        self.locals.set(destination_local, result);
                    } else {
                        let result =
                            self.builder
                                .count_trailing_zeros(v.into(), 64, Origin::synthetic());
                        self.locals.set(destination_local, result.raw());
                    }
                }
                true
            }

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
}
