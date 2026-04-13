use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers MIR casts, including pointer coercions and integer reannotations.
    pub(super) fn translate_cast(
        &mut self,
        kind: &CastKind,
        operand: &Operand<'tcx>,
        target_ty: &ty::Ty<'tcx>,
        _dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        let val = self.translate_operand(operand)?;
        match kind {
            CastKind::IntToInt => {
                // Use projected type so field accesses like
                // _struct.field resolve to the field type, not
                // the struct type.
                let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx) else {
                    return Some(val);
                };
                let src_ty = self.monomorphize(src_ty);
                // `translate_place_to_value` returns the *address* of the
                // field (as a Ptr) for >8-byte types so the assignment
                // handler can do a word-by-word copy.  When this address
                // is used as the source of an IntToInt cast we must load
                // the actual integer value from memory first; otherwise
                // `coerce_to_int` below would convert the address itself
                // to an integer (ptrtoaddr), producing the wrong result.
                // This only applies when the target type fits in 64 bits;
                // Wide → wide casts go through the wide path.
                let target_ty_m = self.monomorphize(*target_ty);
                let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                let dst_size = type_size(self.tcx, target_ty_m).unwrap_or(0);
                if src_size > 8
                    && dst_size > 8
                    && src_ty.is_integral()
                    && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                {
                    // Both source and target are >8-byte integers (e.g.
                    // i128 → u128).  Load the full value now to capture
                    // the correct memory state.  Returning the Ptr would
                    // defer the load to use-time, reading stale data if
                    // the source memory is overwritten in between.
                    let ann = translate_annotation(src_ty)
                        .or_else(|| int_annotation_for_bytes(src_size as u32));
                    let loaded = self.builder.load(
                        val.into(),
                        src_size as u32,
                        Type::Int,
                        self.current_mem.into(),
                        ann.clone(),
                        Origin::synthetic(),
                    );
                    return Some(loaded);
                }
                let val = if src_size > 8
                    && src_ty.is_integral()
                    && dst_size <= 8
                    && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                {
                    // Load the low 8 bytes (little-endian) which hold
                    // the low machine word of the wide integer — sufficient
                    // for any narrowing cast to ≤64-bit targets.
                    self.builder.load(
                        val.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(8),
                        Origin::synthetic(),
                    )
                } else {
                    val
                };
                // Bool is Type::Bool in IR but IntToInt casts need Int operands.
                let val = self.coerce_to_int(val);
                translate_int_to_int_cast(src_ty, *target_ty, val, &mut self.builder)
            }
            CastKind::PointerCoercion(..) => {
                // Convert a zero-sized function item / closure to a function pointer.
                let Some(src_ty) = operand_ty(operand, self.mir) else {
                    return Some(val);
                };
                let src_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                    self.instance.args,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(src_ty),
                );
                let resolved = match src_ty.kind() {
                    ty::FnDef(def_id, args) => ty::Instance::try_resolve(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        *def_id,
                        args,
                    )
                    .ok()
                    .flatten(),
                    ty::Closure(def_id, args) => Some(Instance::resolve_closure(
                        self.tcx,
                        *def_id,
                        args,
                        ty::ClosureKind::FnOnce,
                    )),
                    _ => None,
                };
                if let Some(resolved) = resolved {
                    let sym_name = self.tcx.symbol_name(resolved).name.to_string();
                    self.referenced_instances.push(resolved);
                    let sym_id = self.symbols.intern(&sym_name);
                    Some(self.builder.symbol_addr(sym_id, Origin::synthetic()).raw())
                } else {
                    Some(val)
                }
            }
            CastKind::FloatToInt => {
                let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                else {
                    return Some(val);
                };
                let ft = match src_ty.kind() {
                    ty::Float(ty::FloatTy::F32) => FloatType::F32,
                    ty::Float(ty::FloatTy::F64) => FloatType::F64,
                    _ => return Some(val),
                };
                let target_ty_m = self.monomorphize(*target_ty);
                let signed = matches!(target_ty_m.kind(), ty::Int(_));
                let bit_width = type_size(self.tcx, target_ty_m)
                    .map(|s| s * 8)
                    .unwrap_or(64);

                // `val` may be Float (when loaded from a struct field) or Int
                // (the bit-pattern convention used for scalars). Normalise to
                // both forms so we can use the right one below.
                let val_is_float = matches!(self.builder.value_type(val), Some(Type::Float(_)));
                let float_val = if val_is_float {
                    val
                } else {
                    self.builder
                        .bitcast(val.into(), Type::Float(ft), None, Origin::synthetic())
                };
                let int_bits_val = if val_is_float {
                    let bits = match ft {
                        FloatType::F16 | FloatType::BF16 => 16,
                        FloatType::F32 => 32,
                        FloatType::F64 => 64,
                        FloatType::F128 => 128,
                    };
                    self.builder.bitcast(
                        val.into(),
                        Type::Int,
                        int_annotation_for_bytes(bits / 8),
                        Origin::synthetic(),
                    )
                } else {
                    val
                };
                // For wide integer targets, fp_to_ui/fp_to_si only produce one-part results.
                // Convert to 64-bit first, then extend.
                let needs_extend = bit_width > 64;
                let raw = if signed {
                    self.builder
                        .fp_to_si(float_val.into(), 64, Origin::synthetic())
                } else {
                    self.builder
                        .fp_to_ui(float_val.into(), 64, Origin::synthetic())
                };

                // Float constants for saturation checks.
                // cvttss2si returns INT64_MIN for out-of-range and NaN, so we must
                // detect these cases using float comparisons and apply correct Rust
                // saturating semantics:
                //   NaN → 0, positive overflow → MAX, negative overflow → MIN (or 0 for unsigned)
                let (two63_bits, two64_bits) = match ft {
                    FloatType::F32 => (0x5F00_0000_i64, 0x5F80_0000_i64),
                    // F64/others: 2^63 and 2^64 as f64 bit patterns
                    _ => (0x43E0_0000_0000_0000_i64, 0x43F0_0000_0000_0000_i64),
                };
                let two63_int = self.builder.iconst(
                    two63_bits,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let two63_float = self.builder.bitcast(
                    two63_int.into(),
                    Type::Float(ft),
                    None,
                    Origin::synthetic(),
                );

                // Rust's FloatToInt is saturating: clamp to target range.
                let result = if needs_extend {
                    // For wide integer types, fp_to_ui/fp_to_si produce one-part results.
                    // Explicitly extend to the full destination width.
                    if signed {
                        self.builder
                            .sext(raw.into(), bit_width as u32, Origin::synthetic())
                            .raw()
                    } else {
                        self.builder
                            .zext(raw.into(), bit_width as u32, Origin::synthetic())
                            .raw()
                    }
                } else if signed {
                    // Signed: fix cvttss2si sentinel for NaN and positive overflow.
                    // For negative overflow, cvttss2si returns i64::MIN which is correct.
                    let is_nan = self.builder.fcmp(
                        FCmpOp::Uno,
                        float_val.into(),
                        float_val.into(),
                        Origin::synthetic(),
                    );
                    let is_large = self.builder.fcmp(
                        FCmpOp::OGe,
                        float_val.into(),
                        two63_float.into(),
                        Origin::synthetic(),
                    );
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    let i64_max = self.builder.iconst(
                        i64::MAX,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    // Apply corrections: NaN → 0, then positive overflow → i64::MAX
                    let corrected = self.builder.select(
                        is_nan.into(),
                        zero.into(),
                        raw.into(),
                        Type::Int,
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    let corrected = self.builder.select(
                        is_large.into(),
                        i64_max.into(),
                        corrected.into(),
                        Type::Int,
                        default_int_annotation(),
                        Origin::synthetic(),
                    );
                    if bit_width < 64 {
                        // Clamp to [INT_MIN_of_width, INT_MAX_of_width].
                        // After corrections, corrected ∈ {0, i64::MAX, or cvttss2si result
                        // which is in [-2^63, 2^63-1]}.  Signed min/max works correctly.
                        let lo = -(1i64 << (bit_width - 1));
                        let hi = (1i64 << (bit_width - 1)) - 1;
                        let lo_c = self.builder.iconst(
                            lo,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let hi_c = self.builder.iconst(
                            hi,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let clamped_hi = self.builder.min(
                            corrected.into(),
                            hi_c.into(),
                            signed_int_ann_for_bytes(8),
                            Origin::synthetic(),
                        );
                        self.builder
                            .max(
                                clamped_hi.into(),
                                lo_c.into(),
                                signed_int_ann_for_bytes(8),
                                Origin::synthetic(),
                            )
                            .raw()
                    } else {
                        corrected
                    }
                } else {
                    // Unsigned: full saturating conversion.
                    // NaN → 0, negative → 0, [0, 2^63) → direct, [2^63, 2^64) → two-range,
                    // >= 2^64 → UINT64_MAX (for 64-bit) or UINT_MAX_of_width (for narrower).
                    let is_nan = self.builder.fcmp(
                        FCmpOp::Uno,
                        float_val.into(),
                        float_val.into(),
                        Origin::synthetic(),
                    );
                    // Detect float >= 2^63 (overflow for u32/u16/u8 and start of large range
                    // for u64).
                    let is_large = self.builder.fcmp(
                        FCmpOp::OGe,
                        float_val.into(),
                        two63_float.into(),
                        Origin::synthetic(),
                    );
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    if bit_width < 64 {
                        // For u32/u16/u8: float >= 2^63 is always an overflow (> UINT_MAX).
                        // cvttss2si is correct for float in [-2^63, 2^63): negative → negative
                        // i64, clamped to 0; in-range → correct; overflow beyond hi → large
                        // positive i64, clamped to hi.
                        let hi = (1i64 << bit_width) - 1;
                        let hi_c = self.builder.iconst(
                            hi,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let clamped = self.builder.min(
                            raw.into(),
                            hi_c.into(),
                            signed_int_ann_for_bytes(8),
                            Origin::synthetic(),
                        );
                        let clamped = self.builder.max(
                            clamped.into(),
                            zero.into(),
                            signed_int_ann_for_bytes(8),
                            Origin::synthetic(),
                        );
                        // Override: float >= 2^63 → hi (overflow), NaN → 0.
                        let clamped = self.builder.select(
                            is_large.into(),
                            hi_c.into(),
                            clamped.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            is_nan.into(),
                            zero.into(),
                            clamped.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        )
                    } else {
                        // u64: two-range implementation.
                        // [0, 2^63):   cvttss2si gives correct result.
                        // [2^63, 2^64): subtract 2^63, convert, add 2^63 via bitwise OR.
                        // >= 2^64:      saturate to UINT64_MAX.
                        let two64_int = self.builder.iconst(
                            two64_bits,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let two64_float = self.builder.bitcast(
                            two64_int.into(),
                            Type::Float(ft),
                            None,
                            Origin::synthetic(),
                        );
                        let is_huge = self.builder.fcmp(
                            FCmpOp::OGe,
                            float_val.into(),
                            two64_float.into(),
                            Origin::synthetic(),
                        );
                        // Large range [2^63, 2^64): shift float down, convert, shift back.
                        let flags = FpRewriteFlags::default();
                        let float_shifted = self.builder.fsub(
                            float_val.into(),
                            two63_float.into(),
                            flags,
                            Type::Float(ft),
                            Origin::synthetic(),
                        );
                        let raw_shifted =
                            self.builder
                                .fp_to_ui(float_shifted.into(), 64, Origin::synthetic());
                        let sign_bit = self.builder.iconst(
                            i64::MIN,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let result_large = self.builder.or(
                            raw_shifted.into(),
                            sign_bit.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            },
                            Origin::synthetic(),
                        );
                        let max_u64 = self.builder.iconst(
                            -1_i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        // Select in order: normal → large → huge → nan_or_neg
                        let tentative = self.builder.select(
                            is_large.into(),
                            result_large.into(),
                            raw.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        );
                        let tentative = self.builder.select(
                            is_huge.into(),
                            max_u64.into(),
                            tentative.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        );
                        // NaN or negative → 0 (NaN check must come after is_huge
                        // so that positive NaN doesn't get UINT64_MAX).
                        let sign_bit_pos: u32 = match ft {
                            FloatType::F32 => 31,
                            _ => 63,
                        };
                        let shift_c = self.builder.iconst(
                            sign_bit_pos as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let sign = self.builder.shr(
                            int_bits_val.into(),
                            shift_c.into(),
                            int_ann_for_bytes(8),
                            Origin::synthetic(),
                        );
                        let one = self.builder.iconst(
                            1,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let sign_masked = self.builder.and(
                            sign.into(),
                            one.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            },
                            Origin::synthetic(),
                        );
                        let zero_cmp = self.builder.iconst(
                            0,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let is_neg = self.builder.icmp(
                            ICmpOp::Ne,
                            sign_masked.into(),
                            zero_cmp.into(),
                            Origin::synthetic(),
                        );
                        let tentative = self.builder.select(
                            is_neg.into(),
                            zero.into(),
                            tentative.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            is_nan.into(),
                            zero.into(),
                            tentative.into(),
                            Type::Int,
                            default_int_annotation(),
                            Origin::synthetic(),
                        )
                    }
                };
                Some(result)
            }
            CastKind::IntToFloat => {
                let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                else {
                    return Some(val);
                };
                let signed = matches!(src_ty.kind(), ty::Int(_));
                let target_ty_m = self.monomorphize(*target_ty);
                let ft = match target_ty_m.kind() {
                    ty::Float(ty::FloatTy::F32) => FloatType::F32,
                    ty::Float(ty::FloatTy::F64) => FloatType::F64,
                    _ => return Some(val),
                };

                let src_size = type_size(self.tcx, src_ty).unwrap_or(8);
                // When val is a Ptr (address of a >8-byte int like
                // wide integer), load the full value so the legalizer can
                // split it.  Without this, coerce_to_int would convert
                // the address itself into an integer via ptrtoaddr.
                let int_val =
                    if src_size > 8 && matches!(self.builder.value_type(val), Some(Type::Ptr(_))) {
                        let ann = if signed {
                            signed_int_annotation_for_bytes(src_size as u32)
                        } else {
                            int_annotation_for_bytes(src_size as u32)
                        };
                        self.builder.load(
                            val.into(),
                            src_size as u32,
                            Type::Int,
                            self.current_mem.into(),
                            ann.clone(),
                            Origin::synthetic(),
                        )
                    } else {
                        self.coerce_to_int(val)
                    };

                // Set annotation so the isel can sign/zero-extend narrow
                // integers before cvtsi2ss/cvtsi2sd.  The x86 instruction
                // operates on a full 64-bit value; without sign-extension
                // a byte like 0xDA (-38 as i8) would be seen as 218.
                let annotation = if src_size > 0 {
                    let bits = (src_size * 8) as u32;
                    Some(if signed {
                        IntAnn::Signed(bits)
                    } else {
                        IntAnn::Unsigned(bits)
                    })
                } else {
                    None
                };

                let operand = if let Some(ann) = annotation {
                    tuffy_ir::instruction::Operand::annotated(int_val, ann.to_annotation())
                } else {
                    int_val.into()
                };
                let float_res = if signed {
                    self.builder
                        .si_to_fp(operand.into(), ft, Origin::synthetic())
                } else {
                    self.builder
                        .ui_to_fp(operand.into(), ft, Origin::synthetic())
                };
                Some(float_res.raw())
            }
            CastKind::FloatToFloat => {
                let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                else {
                    return Some(val);
                };
                let src_ft = match src_ty.kind() {
                    ty::Float(ty::FloatTy::F32) => FloatType::F32,
                    ty::Float(ty::FloatTy::F64) => FloatType::F64,
                    _ => return Some(val),
                };
                let target_ty_m = self.monomorphize(*target_ty);
                let dst_ft = match target_ty_m.kind() {
                    ty::Float(ty::FloatTy::F32) => FloatType::F32,
                    ty::Float(ty::FloatTy::F64) => FloatType::F64,
                    _ => return Some(val),
                };
                if src_ft == dst_ft {
                    return Some(val);
                }
                // Convert between float formats; val is already Float(src_ft).
                let converted = self
                    .builder
                    .fp_convert(val.into(), dst_ft, Origin::synthetic());
                Some(converted.raw())
            }
            // Pointer casts and transmutes are bitwise moves.
            _ => {
                let target_ty_mono = self.monomorphize(*target_ty);
                if is_fat_ptr(self.tcx, target_ty_mono)
                    && let Operand::Copy(src) | Operand::Move(src) = operand
                    && !src.projection.is_empty()
                {
                    let src_ty = src.ty(&self.mir.local_decls, self.tcx).ty;
                    let src_ty = self.monomorphize(src_ty);
                    let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                    if src_size > 8 && !is_fat_ptr(self.tcx, src_ty) {
                        // val is an address; load the data pointer.
                        let ptr_val = self.coerce_to_ptr(val);
                        let data = self.builder.load(
                            ptr_val.into(),
                            8,
                            Type::Ptr(0),
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        return Some(data);
                    }
                }
                // PtrToPtr from a large stack local
                if matches!(kind, CastKind::PtrToPtr) {
                    let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                    if target_size > 0
                        && target_size <= 8
                        && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                        && let Operand::Copy(src) | Operand::Move(src) = operand
                        && src.projection.is_empty()
                        && self.stack_locals.is_stack(src.local)
                    {
                        let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                        let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                        if src_size > 8 {
                            let ir_ty = translate_ty(self.tcx, target_ty_mono).unwrap_or(Type::Int);
                            let ann = if matches!(ir_ty, Type::Int) {
                                int_annotation_for_bytes(target_size as u32)
                            } else {
                                None
                            };
                            let data = self.builder.load(
                                val.into(),
                                target_size as u32,
                                ir_ty,
                                self.current_mem.into(),
                                ann.clone(),
                                Origin::synthetic(),
                            );
                            return Some(data);
                        }
                    }
                }
                // Transmute from a stack local into an integral type.
                // Load the target-sized value directly from the source slot
                // instead of returning the pointer.  Returning the pointer
                // would make the destination alias the source slot, causing
                // later independent writes to both locals to corrupt each other.
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                    && let Operand::Copy(src) | Operand::Move(src) = operand
                    && src.projection.is_empty()
                    && self.stack_locals.is_stack(src.local)
                {
                    let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                    // If the source local's MIR type is a pointer,
                    // translate_operand already loaded the pointer
                    // value from the stack slot.  Use ptrtoaddr to
                    // convert the address to an integer instead of
                    // dereferencing through it.
                    if matches!(src_ty.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                        && target_ty_mono.is_integral()
                    {
                        return Some(
                            self.builder
                                .ptrtoaddr(val.into(), 64, Origin::synthetic())
                                .raw(),
                        );
                    }
                    let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                    let target_ir_ty = translate_ty(self.tcx, target_ty_mono);
                    if target_size > 0 && matches!(target_ir_ty, Some(Type::Int | Type::Float(_))) {
                        let load_ty = target_ir_ty.unwrap();
                        let ann = if matches!(load_ty, Type::Int) {
                            int_annotation_for_bytes(target_size as u32)
                        } else {
                            None
                        };
                        let loaded = self.builder.load(
                            val.into(),
                            target_size as u32,
                            load_ty,
                            self.current_mem.into(),
                            ann.clone(),
                            Origin::synthetic(),
                        );
                        return Some(loaded);
                    }
                }
                // Transmute from a projected address (e.g. _3.0.0 where
                // the projected type is a fat-pointer-sized ADT wrapper
                // like NonNull<[T]>) to a fat raw pointer.  Val is a
                // memory address; load only the data pointer (first 8
                // bytes).  The metadata (second 8 bytes) is handled by
                // extract_fat_component in the statement handler.
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                    && self.builder.is_memory_address(val)
                    && is_fat_ptr(self.tcx, target_ty_mono)
                    && let Operand::Copy(src) | Operand::Move(src) = operand
                    && !src.projection.is_empty()
                {
                    let data_ptr = self.builder.load(
                        val.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    return Some(data_ptr);
                }
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Int | Type::Bool))
                    && let Some(Type::Float(ft)) = translate_ty(self.tcx, target_ty_mono)
                {
                    let size = type_size(self.tcx, target_ty_mono).unwrap_or(0) as u32;
                    if size > 0 && size <= self.target_direct_abi_bytes() as u32 {
                        let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        let loaded = self.builder.load(
                            slot.into(),
                            size,
                            Type::Float(ft),
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        return Some(loaded);
                    }
                }
                // Transmute from a Float register value to an Int type:
                // reinterpret via a temporary stack slot.
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Float(_)))
                    && matches!(translate_ty(self.tcx, target_ty_mono), Some(Type::Int))
                {
                    let size = type_size(self.tcx, target_ty_mono).unwrap_or(0) as u32;
                    if size > 0 && size <= self.target_direct_abi_bytes() as u32 {
                        let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        let ann = int_annotation_for_bytes(size);
                        let loaded = self.builder.load(
                            slot.into(),
                            size,
                            Type::Int,
                            self.current_mem.into(),
                            ann.clone(),
                            Origin::synthetic(),
                        );
                        return Some(loaded);
                    }
                }
                // Transmute / PtrToPtr from a pointer-typed source
                // to a non-pointer target (integer type only).
                if matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                    && target_ty_mono.is_integral()
                {
                    let src_ty = operand_ty_projected(operand, self.mir, self.tcx)
                        .map(|ty| self.monomorphize(ty));
                    if let Some(st) = src_ty
                        && matches!(st.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                    {
                        // If val is still a memory address (e.g. fat
                        // pointer in a stack slot), load the thin
                        // pointer first.  Skip the load for non-stack
                        // simple locals whose value is a stack_slot from
                        // `&raw mut` aliasing — val IS the pointer, not a
                        // location storing a pointer.
                        let is_aliased_ptr = matches!(
                            operand,
                            Operand::Copy(src) | Operand::Move(src)
                                if src.projection.is_empty()
                                    && !self.stack_locals.is_stack(src.local)
                        );
                        let ptr_val = if self.builder.is_memory_address(val) && !is_aliased_ptr {
                            self.builder.load(
                                val.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            )
                        } else {
                            val
                        };
                        return Some(
                            self.builder
                                .ptrtoaddr(ptr_val.into(), 64, Origin::synthetic())
                                .raw(),
                        );
                    }
                }
                // Transmute from Bool to an integer type: materialize
                // the 0/1 integer value so downstream integer ops
                // (bitwise NOT, shifts, etc.) see Type::Int, not Bool.
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Bool))
                    && target_ty_mono.is_integral()
                {
                    return Some(self.coerce_to_int(val));
                }
                // Transmute / cast from a memory address (e.g. projected
                // field like RET.fld0) into an integral type.  Load the
                // value now to avoid deferred-load aliasing bugs: if the
                // source memory is overwritten before the local is used,
                // the lazy load would read stale data.
                if matches!(kind, CastKind::Transmute)
                    && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                    && target_ty_mono.is_integral()
                {
                    let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                    if target_size > 0 {
                        let ann = int_annotation_for_bytes(target_size as u32);
                        let loaded = self.builder.load(
                            val.into(),
                            target_size as u32,
                            Type::Int,
                            self.current_mem.into(),
                            ann.clone(),
                            Origin::synthetic(),
                        );
                        return Some(loaded);
                    }
                }
                Some(val)
            }
        }
    }
}
