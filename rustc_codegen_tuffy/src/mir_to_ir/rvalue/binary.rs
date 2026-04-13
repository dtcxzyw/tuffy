use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers MIR binary operations, comparisons, and pointer offsets.
    pub(super) fn translate_binary_op(
        &mut self,
        op: &BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
        dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        let l_raw = self.translate_operand(lhs)?;
        let r_raw = self.translate_operand(rhs)?;
        let l_ann = operand_annotation(lhs, self.mir);
        let r_ann = operand_annotation(rhs, self.mir);

        // Detect float operands for arithmetic dispatch.
        let float_ty = {
            let mir_ty = operand_ty_projected(lhs, self.mir, self.tcx)
                .map(|ty| self.monomorphize(ty))
                .unwrap_or(self.tcx.types.i32);
            match mir_ty.kind() {
                ty::Float(ty::FloatTy::F16) => Some(Type::Float(FloatType::F16)),
                ty::Float(ty::FloatTy::F32) => Some(Type::Float(FloatType::F32)),
                ty::Float(ty::FloatTy::F64) => Some(Type::Float(FloatType::F64)),
                ty::Float(ty::FloatTy::F128) => Some(Type::Float(FloatType::F128)),
                _ => None,
            }
        };

        // Float arithmetic: dispatch directly to fadd/fsub/fmul/fdiv.
        // Operands are always Float-typed at this point.
        // Floats have no "unchecked" variants — only the plain ops.
        if let Some(ref fty) = float_ty
            && matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
            )
        {
            let flags = FpRewriteFlags::default();
            let l_f = l_raw;
            let r_f = r_raw;
            let res = match op {
                BinOp::Add => self.builder.fadd(
                    l_f.into(),
                    r_f.into(),
                    flags,
                    fty.clone(),
                    Origin::synthetic(),
                ),
                BinOp::Sub => self.builder.fsub(
                    l_f.into(),
                    r_f.into(),
                    flags,
                    fty.clone(),
                    Origin::synthetic(),
                ),
                BinOp::Mul => self.builder.fmul(
                    l_f.into(),
                    r_f.into(),
                    flags,
                    fty.clone(),
                    Origin::synthetic(),
                ),
                BinOp::Rem => self.builder.frem(
                    l_f.into(),
                    r_f.into(),
                    flags,
                    fty.clone(),
                    Origin::synthetic(),
                ),
                _ => self.builder.fdiv(
                    l_f.into(),
                    r_f.into(),
                    flags,
                    fty.clone(),
                    Origin::synthetic(),
                ),
            };
            return Some(res.raw());
        }

        // Unsupported operand types produce Unit or
        // typeless values — emit a dummy zero so the IR stays well-typed.
        // Float operands are allowed here because float comparisons
        // (Ge, Le, etc.) are handled further below via fcmp.
        if !matches!(
            self.builder.value_type(l_raw),
            Some(Type::Int | Type::Ptr(_) | Type::Bool | Type::Float(_))
        ) || !matches!(
            self.builder.value_type(r_raw),
            Some(Type::Int | Type::Ptr(_) | Type::Bool | Type::Float(_))
        ) {
            return Some(
                self.builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            );
        }

        // Resolve projected MIR types for accurate annotations.
        let lhs_mir_ty = operand_ty_projected(lhs, self.mir, self.tcx)
            .map(|ty| self.monomorphize(ty))
            .unwrap_or(self.tcx.types.i32);
        let rhs_mir_ty = operand_ty_projected(rhs, self.mir, self.tcx)
            .map(|ty| self.monomorphize(ty))
            .unwrap_or(self.tcx.types.i32);

        // Recompute annotations from the fully-resolved MIR types.
        // `operand_annotation` uses the local's type which misses
        // projections (e.g. `RET.fld1` where RET is a struct but
        // fld1 is i128).  The MIR types computed above resolve
        // through projections correctly.
        let l_ann = translate_annotation(lhs_mir_ty).or(l_ann.clone());
        let r_ann = translate_annotation(rhs_mir_ty).or(r_ann.clone());

        // Coerce pointer operands to integers — needed for both
        // arithmetic/bitwise ops and comparisons.
        let l = self.coerce_to_int(l_raw);
        let r = self.coerce_to_int(r_raw);
        let l_op = IrOperand {
            value: l,
            annotation: l_ann.clone(),
        };
        let r_op = IrOperand {
            value: r,
            annotation: r_ann.clone(),
        };
        let res_ann = Some(
            l_ann
                .clone()
                .and_then(|a| IntAnn::from_annotation(&a))
                .or_else(|| r_ann.clone().and_then(|a| IntAnn::from_annotation(&a)))
                .or_else(|| {
                    // Fallback: use destination type
                    let dest_ty = dest_place.ty(&self.mir.local_decls, self.tcx).ty;
                    translate_annotation(dest_ty).and_then(|a| IntAnn::from_annotation(&a))
                })
                .unwrap_or(IntAnn::Unsigned(64)),
        );

        // Detect float operands for comparison fixup.
        let is_float_cmp = matches!(
            op,
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne | BinOp::Cmp
        ) && float_ty.is_some();

        let val = match op {
            // Wrapping integer arithmetic: use DontCare signedness at target bit width,
            // then extend to proper signedness.
            BinOp::Add => {
                let bits = self.extract_result_bits(res_ann);
                let sum = self
                    .builder
                    .add(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(sum, res_ann, bits)
            }
            BinOp::Sub => {
                let bits = self.extract_result_bits(res_ann);
                let diff = self
                    .builder
                    .sub(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(diff, res_ann, bits)
            }
            BinOp::Mul => {
                let bits = self.extract_result_bits(res_ann);
                let prod = self
                    .builder
                    .mul(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(prod, res_ann, bits)
            }
            // Unchecked variants: the caller guarantees no overflow so the
            // result can carry a full Signed/Unsigned annotation directly.
            BinOp::AddUnchecked => {
                let ann = res_ann
                    .map(|a| match a {
                        IntAnn::Signed(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Signed,
                        },
                        IntAnn::Unsigned(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Unsigned,
                        },
                        IntAnn::DontCare(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::DontCare,
                        },
                    })
                    .unwrap_or(IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    });
                self.builder
                    .add(l_op.into(), r_op.into(), ann, Origin::synthetic())
                    .raw()
            }
            BinOp::SubUnchecked => {
                let ann = res_ann
                    .map(|a| match a {
                        IntAnn::Signed(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Signed,
                        },
                        IntAnn::Unsigned(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Unsigned,
                        },
                        IntAnn::DontCare(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::DontCare,
                        },
                    })
                    .unwrap_or(IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    });
                self.builder
                    .sub(l_op.into(), r_op.into(), ann, Origin::synthetic())
                    .raw()
            }
            BinOp::MulUnchecked => {
                let ann = res_ann
                    .map(|a| match a {
                        IntAnn::Signed(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Signed,
                        },
                        IntAnn::Unsigned(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Unsigned,
                        },
                        IntAnn::DontCare(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::DontCare,
                        },
                    })
                    .unwrap_or(IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    });
                self.builder
                    .mul(l_op.into(), r_op.into(), ann, Origin::synthetic())
                    .raw()
            }
            // Checked arithmetic: emit a multi-result IR intrinsic that
            // produces (wrapping_result: Int, overflow: Bool).  The primary
            // result is returned here and stored in `locals`; the secondary
            // overflow flag is saved in `overflow_locals` for Field(1) access.
            BinOp::AddWithOverflow => {
                let bits = match res_ann {
                    Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => n,
                    None => 64,
                };
                let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                    self.builder.sadd_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                } else {
                    self.builder.uadd_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                };
                self.overflow_locals.set(dest_place.local, overflow.raw());
                primary.raw()
            }
            BinOp::SubWithOverflow => {
                let bits = match res_ann {
                    Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => n,
                    None => 64,
                };
                let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                    self.builder.ssub_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                } else {
                    self.builder.usub_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                };
                self.overflow_locals.set(dest_place.local, overflow.raw());
                primary.raw()
            }
            BinOp::MulWithOverflow => {
                let bits = match res_ann {
                    Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => n,
                    None => 64,
                };
                let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                    self.builder.smul_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                } else {
                    self.builder.umul_with_overflow(
                        l_op.into(),
                        r_op.into(),
                        bits,
                        Origin::synthetic(),
                    )
                };
                self.overflow_locals.set(dest_place.local, overflow.raw());
                primary.raw()
            }
            BinOp::Eq => {
                if is_float_cmp {
                    self.builder
                        .fcmp(FCmpOp::OEq, l_raw.into(), r_raw.into(), Origin::synthetic())
                        .raw()
                } else if is_fat_ptr(self.tcx, lhs_mir_ty) {
                    // Fat pointer equality: compare data AND metadata.
                    // For stack-local fat pointers, l_raw/r_raw hold
                    // slot addresses — load the actual data pointers.
                    let l_data = self.load_fat_data_for_operand(lhs, l_raw);
                    let l_data = self.coerce_to_int(l_data);
                    let r_data = self.load_fat_data_for_operand(rhs, r_raw);
                    let r_data = self.coerce_to_int(r_data);
                    let data_eq = self.builder.icmp(
                        ICmpOp::Eq,
                        IrOperand {
                            value: l_data,
                            annotation: int_annotation_for_bytes(8),
                        }
                        .into(),
                        IrOperand {
                            value: r_data,
                            annotation: int_annotation_for_bytes(8),
                        }
                        .into(),
                        Origin::synthetic(),
                    );
                    let l_meta = self.find_fat_metadata_for_operand(lhs);
                    let r_meta = self.find_fat_metadata_for_operand(rhs);
                    if let (Some(lm), Some(rm)) = (l_meta, r_meta) {
                        let lm_int = self.coerce_to_int(lm);
                        let rm_int = self.coerce_to_int(rm);
                        let meta_eq = self.builder.icmp(
                            ICmpOp::Eq,
                            IrOperand {
                                value: lm_int,
                                annotation: int_annotation_for_bytes(8),
                            }
                            .into(),
                            IrOperand {
                                value: rm_int,
                                annotation: int_annotation_for_bytes(8),
                            }
                            .into(),
                            Origin::synthetic(),
                        );
                        let d = self.coerce_to_int(data_eq.raw());
                        let m = self.coerce_to_int(meta_eq.raw());
                        self.builder
                            .and(
                                d.into(),
                                m.into(),
                                IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::Unsigned,
                                },
                                Origin::synthetic(),
                            )
                            .raw()
                    } else {
                        data_eq.raw()
                    }
                } else {
                    self.builder
                        .icmp(ICmpOp::Eq, l_op.into(), r_op.into(), Origin::synthetic())
                        .raw()
                }
            }
            BinOp::Ne => {
                if is_float_cmp {
                    self.builder
                        .fcmp(FCmpOp::UNe, l_raw.into(), r_raw.into(), Origin::synthetic())
                        .raw()
                } else if is_fat_ptr(self.tcx, lhs_mir_ty) {
                    // Fat pointer inequality: data OR metadata differs.
                    let l_data = self.load_fat_data_for_operand(lhs, l_raw);
                    let l_data = self.coerce_to_int(l_data);
                    let r_data = self.load_fat_data_for_operand(rhs, r_raw);
                    let r_data = self.coerce_to_int(r_data);
                    let data_ne = self.builder.icmp(
                        ICmpOp::Ne,
                        IrOperand {
                            value: l_data,
                            annotation: int_annotation_for_bytes(8),
                        }
                        .into(),
                        IrOperand {
                            value: r_data,
                            annotation: int_annotation_for_bytes(8),
                        }
                        .into(),
                        Origin::synthetic(),
                    );
                    let l_meta = self.find_fat_metadata_for_operand(lhs);
                    let r_meta = self.find_fat_metadata_for_operand(rhs);
                    if let (Some(lm), Some(rm)) = (l_meta, r_meta) {
                        let lm_int = self.coerce_to_int(lm);
                        let rm_int = self.coerce_to_int(rm);
                        let meta_ne = self.builder.icmp(
                            ICmpOp::Ne,
                            IrOperand {
                                value: lm_int,
                                annotation: int_annotation_for_bytes(8),
                            }
                            .into(),
                            IrOperand {
                                value: rm_int,
                                annotation: int_annotation_for_bytes(8),
                            }
                            .into(),
                            Origin::synthetic(),
                        );
                        let d = self.coerce_to_int(data_ne.raw());
                        let m = self.coerce_to_int(meta_ne.raw());
                        self.builder
                            .or(
                                d.into(),
                                m.into(),
                                IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::Unsigned,
                                },
                                Origin::synthetic(),
                            )
                            .raw()
                    } else {
                        data_ne.raw()
                    }
                } else {
                    self.builder
                        .icmp(ICmpOp::Ne, l_op.into(), r_op.into(), Origin::synthetic())
                        .raw()
                }
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                if is_float_cmp {
                    let fcmp_op = match op {
                        BinOp::Lt => FCmpOp::OLt,
                        BinOp::Le => FCmpOp::OLe,
                        BinOp::Gt => FCmpOp::OGt,
                        _ => FCmpOp::OGe,
                    };
                    self.builder
                        .fcmp(fcmp_op, l_raw.into(), r_raw.into(), Origin::synthetic())
                        .raw()
                } else {
                    let icmp_op = match op {
                        BinOp::Lt => ICmpOp::Lt,
                        BinOp::Le => ICmpOp::Le,
                        BinOp::Gt => ICmpOp::Gt,
                        _ => ICmpOp::Ge,
                    };
                    self.builder
                        .icmp(icmp_op, l_op.into(), r_op.into(), Origin::synthetic())
                        .raw()
                }
            }
            BinOp::Cmp => {
                // Three-way comparison returning Ordering (-1/0/1).
                // Result = (l > r) as i8 - (l < r) as i8
                if is_float_cmp {
                    let fty = float_ty.unwrap();
                    let l_f =
                        self.builder
                            .bitcast(l.into(), fty.clone(), None, Origin::synthetic());
                    let r_f = self
                        .builder
                        .bitcast(r.into(), fty, None, Origin::synthetic());
                    let lt =
                        self.builder
                            .fcmp(FCmpOp::OLt, l_f.into(), r_f.into(), Origin::synthetic());
                    let one = self
                        .builder
                        .iconst(1, 8, IntSignedness::Signed, Origin::synthetic());
                    let zero =
                        self.builder
                            .iconst(0, 8, IntSignedness::Signed, Origin::synthetic());
                    let lt_int = self.builder.select(
                        lt.into(),
                        one.into(),
                        zero.into(),
                        Type::Int,
                        Some(Annotation::Int(IntAnnotation {
                            bit_width: 8,
                            signedness: IntSignedness::Signed,
                        })),
                        Origin::synthetic(),
                    );
                    let gt =
                        self.builder
                            .fcmp(FCmpOp::OGt, l_f.into(), r_f.into(), Origin::synthetic());
                    let gt_int = self.builder.select(
                        gt.into(),
                        one.into(),
                        zero.into(),
                        Type::Int,
                        Some(Annotation::Int(IntAnnotation {
                            bit_width: 8,
                            signedness: IntSignedness::Signed,
                        })),
                        Origin::synthetic(),
                    );
                    self.builder
                        .sub(
                            gt_int.into(),
                            lt_int.into(),
                            IntAnnotation {
                                bit_width: 8,
                                signedness: IntSignedness::Signed,
                            },
                            Origin::synthetic(),
                        )
                        .raw()
                } else {
                    let lt = self.builder.icmp(
                        ICmpOp::Lt,
                        l_op.clone().into(),
                        r_op.clone().into(),
                        Origin::synthetic(),
                    );
                    let one = self
                        .builder
                        .iconst(1, 8, IntSignedness::Signed, Origin::synthetic());
                    let zero =
                        self.builder
                            .iconst(0, 8, IntSignedness::Signed, Origin::synthetic());
                    let lt_int = self.builder.select(
                        lt.into(),
                        one.into(),
                        zero.into(),
                        Type::Int,
                        Some(Annotation::Int(IntAnnotation {
                            bit_width: 8,
                            signedness: IntSignedness::Signed,
                        })),
                        Origin::synthetic(),
                    );
                    let gt = self.builder.icmp(
                        ICmpOp::Gt,
                        l_op.into(),
                        r_op.into(),
                        Origin::synthetic(),
                    );
                    let gt_int = self.builder.select(
                        gt.into(),
                        one.into(),
                        zero.into(),
                        Type::Int,
                        Some(Annotation::Int(IntAnnotation {
                            bit_width: 8,
                            signedness: IntSignedness::Signed,
                        })),
                        Origin::synthetic(),
                    );
                    self.builder
                        .sub(
                            gt_int.into(),
                            lt_int.into(),
                            IntAnnotation {
                                bit_width: 8,
                                signedness: IntSignedness::Signed,
                            },
                            Origin::synthetic(),
                        )
                        .raw()
                }
            }
            BinOp::Shl | BinOp::ShlUnchecked => {
                let bits = self.extract_result_bits(res_ann);
                let shift_val = r_op.value;
                let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                let mask_val = self.builder.iconst(
                    lhs_bits - 1,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let masked = self.builder.and(
                    shift_val.into(),
                    mask_val.into(),
                    IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    },
                    Origin::synthetic(),
                );
                let masked_op = IrOperand {
                    value: masked.raw(),
                    annotation: None,
                };
                let shifted = self
                    .builder
                    .shl(
                        l_op.into(),
                        masked_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(shifted, res_ann, bits)
            }
            BinOp::BitOr => {
                let bits = self.extract_result_bits(res_ann);
                let result = self
                    .builder
                    .or(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(result, res_ann, bits)
            }
            BinOp::BitAnd => {
                let bits = self.extract_result_bits(res_ann);
                let result = self
                    .builder
                    .and(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(result, res_ann, bits)
            }
            BinOp::BitXor => {
                let bits = self.extract_result_bits(res_ann);
                let result = self
                    .builder
                    .xor(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    )
                    .raw();
                self.apply_int_extension(result, res_ann, bits)
            }
            BinOp::Shr | BinOp::ShrUnchecked => {
                let shift_val = r_op.value;
                let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                let mask_val = self.builder.iconst(
                    lhs_bits - 1,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let masked = self.builder.and(
                    shift_val.into(),
                    mask_val.into(),
                    IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    },
                    Origin::synthetic(),
                );
                let masked_op = IrOperand {
                    value: masked.raw(),
                    annotation: None,
                };
                let int_ann = res_ann
                    .map(|ia| match ia {
                        IntAnn::Signed(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Signed,
                        },
                        IntAnn::Unsigned(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::Unsigned,
                        },
                        IntAnn::DontCare(n) => IntAnnotation {
                            bit_width: n,
                            signedness: IntSignedness::DontCare,
                        },
                    })
                    .unwrap_or(IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::DontCare,
                    });
                self.builder
                    .shr(l_op.into(), masked_op.into(), int_ann, Origin::synthetic())
                    .raw()
            }
            BinOp::Div => {
                let bits = self.extract_result_bits(res_ann);
                let signedness = match res_ann {
                    Some(IntAnn::Signed(_)) => IntSignedness::Signed,
                    Some(IntAnn::Unsigned(_)) => IntSignedness::Unsigned,
                    _ => IntSignedness::DontCare,
                };
                self.builder
                    .div(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness,
                        },
                        Origin::synthetic(),
                    )
                    .raw()
            }
            BinOp::Rem => {
                let bits = self.extract_result_bits(res_ann);
                let signedness = match res_ann {
                    Some(IntAnn::Signed(_)) => IntSignedness::Signed,
                    Some(IntAnn::Unsigned(_)) => IntSignedness::Unsigned,
                    _ => IntSignedness::DontCare,
                };
                self.builder
                    .rem(
                        l_op.into(),
                        r_op.into(),
                        IntAnnotation {
                            bit_width: bits,
                            signedness,
                        },
                        Origin::synthetic(),
                    )
                    .raw()
            }
            BinOp::Offset => {
                // ptr.wrapping_offset(count) = ptr + count * sizeof(T).
                let l_raw = self.translate_operand(lhs)?;
                let r = self.translate_operand(rhs)?;
                let pointee_ty = operand_ty_projected(lhs, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                    .and_then(|ty| match ty.kind() {
                        ty::RawPtr(inner, _) => Some(*inner),
                        _ => None,
                    });
                let elem_size = pointee_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(1);
                let byte_offset = if elem_size == 1 {
                    r
                } else {
                    let size_val = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(
                            r.into(),
                            size_val.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            },
                            Origin::synthetic(),
                        )
                        .raw()
                };
                let ptr = self.coerce_to_ptr(l_raw);
                self.builder
                    .ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic())
                    .raw()
            }
        };
        Some(val)
    }
}
