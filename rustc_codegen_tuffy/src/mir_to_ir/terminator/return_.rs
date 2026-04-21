use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers MIR `Return`, including SRET and fat-pointer conventions.
    pub(super) fn translate_return(&mut self) {
        // SRET: copy the constructed return value from local stack slot
        // to the SRET pointer, then return the pointer.
        if let Some(sret) = self.sret_ptr {
            let ret_local = mir::Local::from_usize(0);
            let local_slot = self.locals.get(ret_local).expect("sret local must be set");

            // Safety check: if _0 already IS sret, skip the copy.
            if local_slot == sret {
                self.builder.ret(
                    Some(sret.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                return;
            }

            let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
            let ret_size = type_size(self.tcx, ret_mir_ty).unwrap_or(0);

            // Copy from local slot to SRET pointer
            let size_val = self.builder.iconst(
                ret_size as i64,
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            let align = type_align(self.tcx, ret_mir_ty).unwrap_or(8) as u32;
            let sret_annotated =
                tuffy_ir::instruction::Operand::annotated(sret, Annotation::Align(align));
            let local_annotated =
                tuffy_ir::instruction::Operand::annotated(local_slot, Annotation::Align(align));
            let new_mem = self.builder.mem_copy(
                sret_annotated.into(),
                local_annotated.into(),
                size_val.into(),
                self.current_mem.into(),
                Origin::synthetic(),
            );

            self.builder
                .ret(Some(sret.into()), None, new_mem.into(), Origin::synthetic());
            return;
        }

        let ret_local = mir::Local::from_usize(0);
        let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
        let ret_size = type_size(self.tcx, ret_mir_ty).unwrap_or(0);

        if matches!(translate_ty(self.tcx, ret_mir_ty), Some(Type::Unit))
            || (translate_ty(self.tcx, ret_mir_ty).is_none() && ret_size == 0)
        {
            // Unit-returning or zero-sized untranslatable return type: bare ret, no value.
            self.builder
                .ret(None, None, self.current_mem.into(), Origin::synthetic());
        } else if ret_size == 0 {
            // Zero-sized return type: return a dummy value to satisfy the
            // function signature (translate_ty maps ADTs to Int).
            let dummy = self
                .builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
            self.builder.ret(
                Some(dummy.into()),
                None,
                self.current_mem.into(),
                Origin::synthetic(),
            );
        } else if self.stack_locals.is_stack(ret_local)
            && matches!(
                self.locals
                    .get(ret_local)
                    .and_then(|v| self.builder.value_type(v).cloned()),
                Some(Type::Ptr(_))
            )
        {
            // Stack-allocated return (e.g., 16-byte struct built via Aggregate).
            // Load the actual data from the stack slot instead of returning
            // the slot address (which would be a dangling pointer).
            let slot = self
                .locals
                .get(ret_local)
                .expect("return local _0 must be set");
            let ret_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
            let size = type_size(self.tcx, ret_ty).unwrap_or(8);
            let ret_repr = repr_kind(self.tcx, ret_ty);
            let is_scalar_pair = matches!(ret_repr, ReprKind::ScalarPair);

            // Load size: for Scalar returns load the full type width
            // (legalizer splits wide loads); for ScalarPair load only
            // the first scalar.
            let sp_info = if is_scalar_pair {
                scalar_pair_info(self.tcx, ret_ty)
            } else {
                None
            };
            let load_size = if let Some((a_sz, _, _)) = sp_info {
                a_sz as u32
            } else {
                size as u32
            };
            let load_ty = translate_ty(self.tcx, ret_mir_ty).unwrap_or(Type::Int);
            // For ScalarPair returns (e.g. fat pointers), use a
            // register-width annotation for the low-half load — but
            // only when the type is Int (not Ptr).
            let ann = if is_scalar_pair {
                if matches!(load_ty, Type::Ptr(_)) {
                    None
                } else {
                    int_annotation_for_bytes(load_size)
                }
            } else {
                translate_annotation(ret_mir_ty).or_else(|| {
                    if matches!(load_ty, Type::Int) {
                        int_annotation_for_bytes(load_size)
                    } else {
                        None
                    }
                })
            };
            let word0 = self.builder.load(
                slot.into(),
                load_size,
                load_ty,
                self.current_mem.into(),
                ann,
                Origin::synthetic(),
            );

            // Coerce to match declared return type (e.g., Ptr for &T returns).
            let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty);
            let coerced_word0 = match ret_ir_ty {
                Some(Type::Ptr(_)) => self.coerce_to_ptr(word0),
                _ => word0,
            };

            if is_scalar_pair {
                // Two-register return (ScalarPair): load second scalar
                // and mark it for RDX via ABI metadata.
                let (_, b_sz, b_off) = sp_info.unwrap_or((size.min(8), size.saturating_sub(8), 8));
                let off_val = self.builder.iconst(
                    b_off as i64,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let hi_addr =
                    self.builder
                        .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic());
                let word1 = self.builder.load(
                    hi_addr.into(),
                    b_sz as u32,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(b_sz as u32),
                    Origin::synthetic(),
                );
                self.builder.ret(
                    Some(coerced_word0.into()),
                    Some(word1.into()),
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            } else {
                self.builder.ret(
                    Some(coerced_word0.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            }
        } else if let Some(fat_meta) = self.fat_locals.get(ret_local)
            && is_fat_ptr(self.tcx, ret_mir_ty)
        {
            // Non-stack fat pointer return (e.g. from an intrinsic
            // that set both locals and fat_locals directly).  Return
            // the data pointer in RAX and the metadata in RDX.
            let v = self
                .locals
                .get(ret_local)
                .expect("fat pointer return must have data_ptr");
            let coerced = self.coerce_to_ptr(v);
            self.builder.ret(
                Some(coerced.into()),
                Some(fat_meta.into()),
                self.current_mem.into(),
                Origin::synthetic(),
            );
        } else {
            // Normal scalar return.
            let val = self.locals.values[ret_local.as_usize()];
            if let Some(v) = val {
                // Coerce to match the declared return type.
                // Fall back to Type::Int for small aggregates (e.g.
                // [i8; 1]) that translate_ty maps to None — this
                // matches the function-signature logic in mod.rs.
                let part_bytes = self.target_part_bytes();
                let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty).or(
                    if ret_size > 0 && ret_size <= part_bytes {
                        Some(Type::Int)
                    } else {
                        None
                    },
                );
                let coerced = match (ret_ir_ty, self.builder.value_type(v).cloned()) {
                    (Some(Type::Int), Some(Type::Ptr(_))) if self.builder.is_memory_address(v) => {
                        // v is a pointer to data (e.g. symbol_addr for an
                        // indirect constant).  Load the actual value instead
                        // of converting the address to an integer.
                        let ret_size = type_size(self.tcx, ret_mir_ty)
                            .unwrap_or(part_bytes)
                            .min(part_bytes) as u32;

                        self.builder.load(
                            v.into(),
                            ret_size,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(ret_size),
                            Origin::synthetic(),
                        )
                    }
                    // Aggregate type (tuple/struct) that translate_ty
                    // maps to None but fits in one ABI part. The function
                    // signature declares Int return; load the value from
                    // the constant/stack pointer.
                    (None, Some(Type::Ptr(_)))
                        if self.builder.is_memory_address(v)
                            && ret_size > 0
                            && ret_size <= part_bytes =>
                    {
                        let sz = ret_size.min(part_bytes) as u32;
                        self.builder.load(
                            v.into(),
                            sz,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(sz),
                            Origin::synthetic(),
                        )
                    }
                    (Some(Type::Int), Some(Type::Float(_))) => {
                        // Float returned as integer bits (e.g. to_le_bytes).
                        let sz = ret_size.min(8) as u32;
                        self.builder.bitcast(
                            v.into(),
                            Type::Int,
                            int_annotation_for_bytes(sz),
                            Origin::synthetic(),
                        )
                    }
                    (Some(Type::Int), _) => self.coerce_to_int(v),
                    (Some(Type::Ptr(_)), _) => self.coerce_to_ptr(v),
                    (Some(Type::Bool), Some(Type::Int)) => {
                        let zero = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .icmp(ICmpOp::Ne, v.into(), zero.into(), Origin::synthetic())
                            .raw()
                    }
                    (Some(Type::Float(ft)), Some(Type::Int)) => {
                        // Float value was carried as Int bits — reinterpret.
                        self.builder
                            .bitcast(v.into(), Type::Float(ft), None, Origin::synthetic())
                    }
                    _ => v,
                };
                self.builder.ret(
                    Some(coerced.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            } else {
                // Return local was never assigned — return a dummy
                // value.  This can happen in custom MIR where the
                // return place is left uninitialised (the value is
                // garbage but the function must still return).
                let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty);
                let dummy = if matches!(ret_ir_ty, Some(Type::Ptr(_))) {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.builder
                        .inttoptr(zero.into(), 0, Origin::synthetic())
                        .raw()
                } else if let Some(Type::Float(ft)) = ret_ir_ty {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.builder
                        .bitcast(zero.into(), Type::Float(ft), None, Origin::synthetic())
                } else if matches!(ret_ir_ty, Some(Type::Bool)) {
                    self.builder.bconst(false, Origin::synthetic()).raw()
                } else {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                };
                self.builder.ret(
                    Some(dummy.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            }
        }
    }
}
