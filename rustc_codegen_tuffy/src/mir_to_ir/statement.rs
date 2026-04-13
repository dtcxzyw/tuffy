use super::ctx::TranslationCtx;
use super::types::*;
use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, Rvalue, StatementKind};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

/// Shared 64-bit unsigned annotation used for synthesized integer temporaries.
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Returns whether `rvalue` is a scalar constant that can stay in registers.
    fn rvalue_is_scalar_const(&self, rvalue: &Rvalue<'tcx>, dest_ty: ty::Ty<'tcx>) -> bool {
        matches!(
            rvalue,
            Rvalue::Use(Operand::Constant(_)) | Rvalue::Cast(_, Operand::Constant(_), _)
        ) && matches!(repr_kind(self.tcx, dest_ty), ReprKind::Scalar)
    }

    /// Lowers one MIR statement into Tuffy IR state updates and instructions.
    pub(super) fn translate_statement(&mut self, stmt: &mir::Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let rval_result = self.translate_rvalue(rvalue, place);
                if let Some(val) = rval_result {
                    // Handle stores through pointer dereference (e.g. *ptr = val).
                    // Other non-empty projections (Field, Index) on non-stack
                    // locals were previously no-ops; keep them that way to avoid
                    // generating ill-formed IR for patterns handled elsewhere.
                    let has_deref = !place.projection.is_empty()
                        && place
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, rustc_middle::mir::PlaceElem::Deref));
                    if has_deref {
                        self.assign_through_deref(val, place, rvalue);
                    } else if place.projection.is_empty() {
                        if self.stack_locals.is_stack(place.local) {
                            self.assign_to_stack_local(val, place, rvalue);
                        } else {
                            self.assign_to_register_local(val, place, rvalue);
                        }
                    } else {
                        self.assign_to_projected(val, place, rvalue);
                    }
                }
                // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
                // Only propagate fat metadata for direct local assignments (no
                // projection).  For deref / field stores we are writing THROUGH
                // the local, not TO it, so the rvalue's metadata must not be
                // associated with the base local (that would clobber unrelated
                // stack slots).
                if place.projection.is_empty()
                    && let Some(fat_val) = self.extract_fat_component(rvalue)
                {
                    self.fat_locals.set(place.local, fat_val);
                    // For stack-allocated locals, also store the metadata to
                    // the stack slot at offset `target_part_bytes()` so that
                    // code loading the full
                    // fat pointer from the slot (e.g. the Return terminator's
                    // stack-allocated path) sees both words.
                    if self.stack_locals.is_stack(place.local)
                        && let Some(slot) = self.locals.get(place.local)
                    {
                        let off = self.builder.iconst(
                            self.target_part_bytes() as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let addr =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                fat_val.into(),
                                addr.into(),
                                self.target_part_bytes() as u32,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }
                // Cast from a projected non-fat type to a fat pointer
                // (e.g. `NonNull<[T]> as *const [T]` in into_vec):
                // load the metadata from the source address + 8 and
                // store it in cast_fat_meta so PtrMetadata can find it.
                // This is kept separate from fat_locals to avoid
                // propagation through Use/Copy chains.
                if let Rvalue::Cast(_, op, target_ty) = rvalue {
                    let target_ty_mono = self.monomorphize(*target_ty);
                    if is_fat_ptr(self.tcx, target_ty_mono)
                        && let Operand::Copy(src) | Operand::Move(src) = op
                        && !src.projection.is_empty()
                    {
                        let src_ty = src.ty(&self.mir.local_decls, self.tcx).ty;
                        let src_ty = self.monomorphize(src_ty);
                        let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                        if src_size >= 16
                            && !is_fat_ptr(self.tcx, src_ty)
                            && let Some((addr, _)) = self.translate_place_to_addr(src)
                        {
                            let addr = self.coerce_to_ptr(addr);
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let meta_addr = self.builder.ptradd(
                                addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let meta = self.builder.load(
                                meta_addr.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            self.cast_fat_meta.set(place.local, meta);
                        }
                    }
                }
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            StatementKind::SetDiscriminant {
                box place,
                variant_index,
            } => {
                self.translate_set_discriminant(place, *variant_index);
            }
            StatementKind::Intrinsic(intrinsic) => {
                use rustc_middle::mir::NonDivergingIntrinsic;
                match &**intrinsic {
                    NonDivergingIntrinsic::CopyNonOverlapping(copy_info) => {
                        // copy_nonoverlapping(src, dst, count) → memcpy(dst, src, count * sizeof(T))
                        // count is in elements; we must multiply by the pointee size.
                        let src = self.translate_operand(&copy_info.src);
                        let dst = self.translate_operand(&copy_info.dst);
                        let count = self.translate_operand(&copy_info.count);
                        if let (Some(src_v), Some(dst_v), Some(count_v)) = (src, dst, count) {
                            let src_ty = self
                                .monomorphize(copy_info.src.ty(&self.mir.local_decls, self.tcx));
                            let pointee_size = src_ty
                                .builtin_deref(true)
                                .and_then(|t| type_size(self.tcx, t))
                                .unwrap_or(1);
                            let byte_count = if pointee_size == 0 {
                                // ZST: no bytes to copy regardless of count.
                                self.builder
                                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                                    .raw()
                            } else if pointee_size == 1 {
                                count_v
                            } else {
                                let sz = self.builder.iconst(
                                    pointee_size as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .mul(count_v.into(), sz.into(), I64, Origin::synthetic())
                                    .raw()
                            };
                            let sym_id = self.symbols.intern("memcpy");
                            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                            let (mem_out, _) = self.builder.call(
                                callee.into(),
                                vec![dst_v.into(), src_v.into(), byte_count.into()],
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Some(Annotation::Int(I64)),
                                Origin::synthetic(),
                            );
                            self.current_mem = mem_out.raw();
                        }
                    }
                    NonDivergingIntrinsic::Assume(_) => {
                        // Runtime assumption — no codegen needed.
                    }
                }
            }
            _ => {
                unimplemented!("MIR statement: {:?}", stmt.kind);
            }
        }
    }

    /// Stores a lowered value through a dereferenced place.
    fn assign_through_deref(&mut self, val: ValueRef, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        if let Some((addr, projected_ty)) = self.translate_place_to_addr(place) {
            let addr = self.coerce_to_ptr(addr);
            let dest_ty = self.monomorphize(projected_ty);
            let bytes = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
            if bytes == 0 {
                // ZST: nothing to store.
            } else if matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                && bytes > 8
                && is_fat_ptr(self.tcx, dest_ty)
                && let Some(fat_val) = self.extract_fat_component(rvalue)
            {
                // Fat pointer value (e.g. &[u8]): val is the data
                // pointer, metadata lives in fat_locals / extract_fat_component.
                // Store both halves directly.
                let data_ptr = if self.builder.is_local_memory_address(val)
                    && self.builder.stack_slot_size(val).is_some()
                {
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
                self.current_mem = self
                    .builder
                    .store(
                        data_ptr.into(),
                        addr.into(),
                        8,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                let off = self
                    .builder
                    .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                let meta_addr =
                    self.builder
                        .ptradd(addr.into(), off.into(), 0, Origin::synthetic());
                self.current_mem = self
                    .builder
                    .store(
                        fat_val.into(),
                        meta_addr.into(),
                        8,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            } else if matches!(self.builder.value_type(val), Some(Type::Ptr(_))) && bytes > 8 {
                // Large aggregate: copy word by word
                let words = bytes.div_ceil(8);
                for w in 0..words {
                    let off_val = w as i64 * 8;
                    let src_ptr = if w == 0 {
                        val
                    } else {
                        let off = self.builder.iconst(
                            off_val,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(val.into(), off.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    let load_sz = if w == words - 1 && !bytes.is_multiple_of(8) {
                        bytes % 8
                    } else {
                        8
                    };
                    let word = self.builder.load(
                        src_ptr.into(),
                        load_sz,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(load_sz),
                        Origin::synthetic(),
                    );
                    let dst_ptr = if w == 0 {
                        addr
                    } else {
                        let off = self.builder.iconst(
                            off_val,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(addr.into(), off.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    self.current_mem = self
                        .builder
                        .store(
                            word.into(),
                            dst_ptr.into(),
                            load_sz,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else if matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                && self.builder.is_local_memory_address(val)
            {
                // Small aggregate in a stack slot (≤8 bytes):
                // load the data from the source and store to dest.
                // Use is_local_memory_address (not is_memory_address)
                // so that computed pointers (e.g. PtrAdd from Offset)
                // are stored directly as pointer values, not loaded from.
                let data = self.builder.load(
                    val.into(),
                    bytes,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(bytes),
                    Origin::synthetic(),
                );
                self.current_mem = self
                    .builder
                    .store(
                        data.into(),
                        addr.into(),
                        bytes,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            } else {
                // Scalar or small: store directly.
                // Coerce the value to match the store type.
                let store_val = if matches!(self.builder.value_type(val), Some(Type::Bool)) {
                    self.coerce_to_int(val)
                } else if matches!(self.builder.value_type(val), Some(Type::Ptr(_))) && bytes <= 8 {
                    // Pointer value stored to a pointer-sized
                    // field: pass through (store handles Ptr).
                    val
                } else {
                    val
                };
                // For wide integers, store the
                // full 16 bytes; the legalizer splits into two
                // 64-bit stores.  Other scalars cap at 8.
                let store_bytes =
                    if matches!(self.builder.value_type(store_val), Some(Type::Int)) && bytes > 8 {
                        bytes.min(16)
                    } else {
                        bytes.min(8)
                    };
                self.current_mem = self
                    .builder
                    .store(
                        store_val.into(),
                        addr.into(),
                        store_bytes,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
        }
    }

    /// Writes an assignment into a destination local that already lives on the stack.
    fn assign_to_stack_local(&mut self, val: ValueRef, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        if let Some(slot) = self.locals.get(place.local) {
            if matches!(self.builder.value_type(slot), Some(Type::Ptr(_))) {
                let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                let bytes = type_size(self.tcx, ty).unwrap_or(8) as u32;
                // If val is also a pointer (e.g. stack slot from
                // Aggregate) and the type is larger than 8 bytes,
                // do a word-by-word copy of the DATA instead of
                // storing the pointer value.
                let val_ty = self.builder.value_type(val).cloned();
                let is_ref_rvalue = matches!(rvalue, Rvalue::Ref(..) | Rvalue::RawPtr(..));
                // When the destination MIR type is a thin
                // reference/pointer, val IS the pointer value
                // (not an address pointing to data).  Store it
                // directly instead of doing a word-by-word copy.
                // Fat pointers (references to unsized types like
                // &dyn Trait, &[T], &str, or &Struct<[T]>) need
                // the fat-component assembly path, so exclude them.
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let dest_is_ptr_ty = matches!(ty.kind(),
                    ty::Ref(_, inner, _) if inner.is_sized(self.tcx, typing_env)
                ) || matches!(ty.kind(),
                    ty::RawPtr(inner, _) if inner.is_sized(self.tcx, typing_env)
                ) || matches!(ty.kind(), ty::FnPtr(..));
                let scalar_const_symbol = matches!(val_ty.as_ref(), Some(Type::Ptr(_)))
                    && bytes <= 8
                    && self.builder.is_symbol_addr(val)
                    && self.rvalue_is_scalar_const(rvalue, ty);
                if matches!(val_ty.as_ref(), Some(Type::Ptr(_)))
                    && bytes > 0
                    && !is_ref_rvalue
                    && !dest_is_ptr_ty
                {
                    if scalar_const_symbol {
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        return;
                    }
                    // When the Aggregate rvalue reused the
                    // destination slot, val == slot and the
                    // data is already in place — skip the copy.
                    if val == slot {
                        // already stored by translate_rvalue
                    } else {
                        // Check if the source is a non-stack fat pointer
                        // local (e.g. a &[T] function parameter). In that
                        // case `val` is the data pointer VALUE, not an
                        // address to load from. Store the two components
                        // (data ptr + metadata) directly into the slot.
                        let fat_src = match rvalue {
                            Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place))
                                if src_place.projection.is_empty()
                                    && !self.stack_locals.is_stack(src_place.local) =>
                            {
                                self.fat_locals.get(src_place.local)
                            }
                            // Constant fat pointer (e.g. &str literal,
                            // &[T] associated constant).  translate_const
                            // already loaded the data pointer; extract the
                            // length from the constant so we can store both
                            // components into the stack slot.
                            Rvalue::Use(Operand::Constant(c)) => {
                                let mono_const =
                                    self.tcx.instantiate_and_normalize_erasing_regions(
                                        self.instance.args,
                                        ty::TypingEnv::fully_monomorphized(),
                                        ty::EarlyBinder::bind(c.const_),
                                    );
                                let resolved = match mono_const {
                                    mir::Const::Val(v, _) => Some(v),
                                    _ => {
                                        let typing_env = ty::TypingEnv::fully_monomorphized();
                                        mono_const.eval(self.tcx, typing_env, c.span).ok()
                                    }
                                };
                                if let Some(mir::ConstValue::Slice { meta, .. }) = resolved {
                                    Some(
                                        self.builder
                                            .iconst(
                                                meta as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    )
                                } else if let Some(mir::ConstValue::Indirect { alloc_id, offset }) =
                                    resolved
                                {
                                    let const_ty = mono_const.ty();
                                    if is_fat_ptr(self.tcx, const_ty) {
                                        let alloc = self.tcx.global_alloc(alloc_id);
                                        if let rustc_middle::mir::interpret::GlobalAlloc::Memory(
                                            mem_alloc,
                                        ) = alloc
                                        {
                                            let inner = mem_alloc.inner();
                                            let byte_offset = offset.bytes() as usize + 8;
                                            let len_bytes = inner
                                                .inspect_with_uninit_and_ptr_outside_interpreter(
                                                    byte_offset..byte_offset + 8,
                                                );
                                            let len = u64::from_le_bytes(
                                                len_bytes.try_into().unwrap_or([0u8; 8]),
                                            );
                                            Some(
                                                self.builder
                                                    .iconst(
                                                        len as i64,
                                                        64,
                                                        IntSignedness::DontCare,
                                                        Origin::synthetic(),
                                                    )
                                                    .raw(),
                                            )
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }
                            // Cast (e.g. PtrToPtr) of a non-stack
                            // fat pointer local: propagate the fat
                            // component so we store (data_ptr, len)
                            // instead of doing a word-by-word copy
                            // from the data pointer address.
                            Rvalue::Cast(
                                _,
                                Operand::Copy(src_place) | Operand::Move(src_place),
                                _,
                            ) if src_place.projection.is_empty()
                                && !self.stack_locals.is_stack(src_place.local) =>
                            {
                                self.fat_locals.get(src_place.local)
                            }
                            // &raw const (*local) / &(*local) on a
                            // non-stack fat pointer local: the fat
                            // component lives in fat_locals.
                            Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place)
                                if !self.stack_locals.is_stack(src_place.local) =>
                            {
                                self.fat_locals.get(src_place.local)
                            }
                            _ => None,
                        };
                        // Fallback: for Unsize coercions the source is a
                        // thin pointer but extract_fat_component can
                        // generate the vtable/length for the destination.
                        // Skip the fallback when the source is a stack
                        // local — val is a slot address, not a data
                        // pointer, so the word-by-word copy path must
                        // handle it instead.
                        let src_is_stack = matches!(rvalue,
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.projection.is_empty()
                                    && self.stack_locals.is_stack(p.local)
                        );
                        let fat_src = if src_is_stack {
                            None
                        } else {
                            fat_src.or_else(|| self.extract_fat_component(rvalue))
                        };
                        if let Some(fat_val) = fat_src {
                            // Stack locals are split here:
                            // - thin pointer locals: translate_operand already loaded the
                            //   pointer value from the slot, so reloading would dereference
                            //   through the pointee and corrupt the fat-pointer data word.
                            // - fat / aggregate locals: translate_operand still returns the
                            //   slot address, so we must load the first word from the slot.
                            let operand_is_stack_local = match rvalue {
                                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => {
                                    p.projection.is_empty() && self.stack_locals.is_stack(p.local)
                                }
                                _ => false,
                            };
                            let operand_uses_stack_slot =
                                operand_is_stack_local && self.builder.is_local_memory_address(val);
                            let data_ptr = if operand_uses_stack_slot {
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
                            // Store data pointer into slot[0..8].
                            self.current_mem = self
                                .builder
                                .store(
                                    data_ptr.into(),
                                    slot.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            // Store fat component (length/vtable) into slot[8..16].
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let hi_addr = self.builder.ptradd(
                                slot.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            self.current_mem = self
                                .builder
                                .store(
                                    fat_val.into(),
                                    hi_addr.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            // For ADT Unsize casts (e.g. RefMut<[T; N]> →
                            // RefMut<[T]>), the first field grows from 8→16
                            // bytes (thin→fat pointer), shifting subsequent
                            // fields. Copy remaining bytes from the source
                            // after the first 8 bytes to dest after 16 bytes.
                            if operand_is_stack_local {
                                let src_place = match rvalue {
                                    Rvalue::Cast(
                                        mir::CastKind::PointerCoercion(
                                            ty::adjustment::PointerCoercion::Unsize,
                                            _,
                                        ),
                                        Operand::Copy(p) | Operand::Move(p),
                                        _,
                                    ) => Some(p),
                                    _ => None,
                                };
                                if let Some(src_place) = src_place {
                                    let src_ty =
                                        self.monomorphize(self.mir.local_decls[src_place.local].ty);
                                    let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                                    // If source > 8, there are trailing fields
                                    // after the first pointer that must move.
                                    if src_size > 8 {
                                        let trailing = src_size - 8;
                                        let src_slot =
                                            self.locals.get(src_place.local).unwrap_or(val);
                                        let num_words = trailing.div_ceil(8);
                                        for i in 0..num_words {
                                            let chunk = std::cmp::min(8, trailing - i * 8) as u32;
                                            let src_off = (8 + i * 8) as i64;
                                            let dst_off = (16 + i * 8) as i64;
                                            let soff = self.builder.iconst(
                                                src_off,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            );
                                            let sa = self.builder.ptradd(
                                                src_slot.into(),
                                                soff.into(),
                                                0,
                                                Origin::synthetic(),
                                            );
                                            let word = self.builder.load(
                                                sa.into(),
                                                chunk,
                                                Type::Int,
                                                self.current_mem.into(),
                                                int_annotation_for_bytes(chunk),
                                                Origin::synthetic(),
                                            );
                                            let doff = self.builder.iconst(
                                                dst_off,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            );
                                            let da = self.builder.ptradd(
                                                slot.into(),
                                                doff.into(),
                                                0,
                                                Origin::synthetic(),
                                            );
                                            self.current_mem = self
                                                .builder
                                                .store(
                                                    word.into(),
                                                    da.into(),
                                                    chunk,
                                                    self.current_mem.into(),
                                                    Origin::synthetic(),
                                                )
                                                .raw();
                                        }
                                    }
                                }
                            }
                        } else {
                            // For word-by-word copy we need a SOURCE ADDRESS
                            // to load from. When the rvalue is Use(Copy/Move)
                            // of a place with projections (e.g. a fat pointer
                            // field like &str), `val` is the LOADED value (the
                            // data pointer), not a pointer to the multi-word
                            // data. Use translate_place_to_addr to get the
                            // actual source address in memory.
                            let src_base = match rvalue {
                                Rvalue::Use(
                                    Operand::Copy(src_place) | Operand::Move(src_place),
                                ) if !src_place.projection.is_empty() => self
                                    .translate_place_to_addr(src_place)
                                    .map(|(a, _)| self.coerce_to_ptr(a)),
                                // Stack locals: val is the loaded first
                                // word, not the slot address.  Use the
                                // slot address so the word-by-word copy
                                // reads from the correct location.
                                Rvalue::Use(
                                    Operand::Copy(src_place) | Operand::Move(src_place),
                                ) if src_place.projection.is_empty()
                                    && self.stack_locals.is_stack(src_place.local) =>
                                {
                                    self.locals.get(src_place.local)
                                }
                                _ => None,
                            };
                            // When no explicit source address was found
                            // and val is a computed register value
                            // (e.g. ptradd from Offset, transmuted into
                            // an ADT like NonNull<T>), val is the VALUE
                            // to store, not a memory address to load from.
                            if src_base.is_none()
                                && bytes <= 8
                                && !self.builder.is_local_memory_address(val)
                            {
                                self.current_mem = self
                                    .builder
                                    .store(
                                        val.into(),
                                        slot.into(),
                                        bytes,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                            } else {
                                let src_base = src_base.unwrap_or(val);
                                let num_words = (bytes as u64).div_ceil(8);
                                for i in 0..num_words {
                                    let byte_off = i * 8;
                                    let chunk = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                                    let src_addr = if byte_off == 0 {
                                        src_base
                                    } else {
                                        let off = self.builder.iconst(
                                            byte_off as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        );
                                        self.builder
                                            .ptradd(
                                                src_base.into(),
                                                off.into(),
                                                0,
                                                Origin::synthetic(),
                                            )
                                            .raw()
                                    };
                                    let word = self.builder.load(
                                        src_addr.into(),
                                        chunk,
                                        Type::Int,
                                        self.current_mem.into(),
                                        int_annotation_for_bytes(chunk),
                                        Origin::synthetic(),
                                    );
                                    let dst_addr = if byte_off == 0 {
                                        slot
                                    } else {
                                        let off = self.builder.iconst(
                                            byte_off as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        );
                                        self.builder
                                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                                            .raw()
                                    };
                                    self.current_mem = self
                                        .builder
                                        .store(
                                            word.into(),
                                            dst_addr.into(),
                                            chunk,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        )
                                        .raw();
                                }
                            }
                        }
                    }
                } else if bytes > 8 {
                    // Value is not a Ptr but the destination is
                    // wider than 8 bytes (e.g. a fat pointer stored
                    // as Int via repr(transparent)).  Try to find
                    // the source stack-slot pointer so we can do a
                    // word-by-word copy of the full width.
                    //
                    // First, check if this is a Ref/RawPtr on a
                    // non-stack fat pointer local.  In that case the
                    // data pointer and metadata live in separate IR
                    // values (locals + fat_locals), so we store them
                    // directly instead of doing a word-by-word copy.
                    let ref_fat_src = match rvalue {
                        Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place)
                            if (!self.stack_locals.is_stack(src_place.local)
                                    || src_place.projection.len() > 1)
                                    // When the Ref handler already built
                                    // a complete fat-pointer stack slot
                                    // (e.g. for Subslice), val already
                                    // contains {data_ptr, adjusted_meta}.
                                    // Don't override with stale fat_locals.
                                    && !self
                                        .builder
                                        .is_local_memory_address(val) =>
                        {
                            self.fat_locals.get(src_place.local)
                        }
                        _ => None,
                    };
                    if let Some(fat_val) = ref_fat_src {
                        // When val is a stack slot from the
                        // Ref/RawPtr handler (containing a fat
                        // pointer), load the data pointer from
                        // it instead of storing the raw slot
                        // address.
                        let data_ptr = if self.builder.is_local_memory_address(val) {
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
                        // Store data pointer into slot[0..8].
                        self.current_mem = self
                            .builder
                            .store(
                                data_ptr.into(),
                                slot.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        // Store metadata (length/vtable) into slot[8..16].
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let hi_addr =
                            self.builder
                                .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                fat_val.into(),
                                hi_addr.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    } else {
                        let src_slot = match rvalue {
                            Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place))
                                if src_place.projection.is_empty()
                                    && self.stack_locals.is_stack(src_place.local) =>
                            {
                                self.locals.get(src_place.local)
                            }
                            // &(*local) / &raw (*local) on a fat-pointer
                            // stack local: the slot holds the full fat
                            // pointer (data ptr + metadata) which must be
                            // copied word-by-word to the destination.
                            // Only apply when the place has at most one
                            // projection (Deref); deeper projections
                            // (e.g. &(*_1).field) are handled above via
                            // ref_fat_src with the pre-computed `val`.
                            Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place)
                                if self.stack_locals.is_stack(src_place.local)
                                    && src_place.projection.len() <= 1 =>
                            {
                                self.locals.get(src_place.local)
                            }
                            _ => None,
                        };
                        if let Some(src_base) = src_slot {
                            let src_base = self.coerce_to_ptr(src_base);
                            let num_words = (bytes as u64).div_ceil(8);
                            for i in 0..num_words {
                                let byte_off = i * 8;
                                let chunk = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                                let src_addr = if byte_off == 0 {
                                    src_base
                                } else {
                                    let off = self.builder.iconst(
                                        byte_off as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    self.builder
                                        .ptradd(src_base.into(), off.into(), 0, Origin::synthetic())
                                        .raw()
                                };
                                let word = self.builder.load(
                                    src_addr.into(),
                                    chunk,
                                    Type::Int,
                                    self.current_mem.into(),
                                    int_annotation_for_bytes(chunk),
                                    Origin::synthetic(),
                                );
                                let dst_addr = if byte_off == 0 {
                                    slot
                                } else {
                                    let off = self.builder.iconst(
                                        byte_off as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    self.builder
                                        .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                                        .raw()
                                };
                                self.current_mem = self
                                    .builder
                                    .store(
                                        word.into(),
                                        dst_addr.into(),
                                        chunk,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                            }
                        } else {
                            // CheckedBinaryOp stores (result, bool)
                            // but translate_rvalue only returns the
                            // arithmetic result.  For (T, bool) tuples
                            // where T is > 8 bytes (e.g. i128), only
                            // store size_of(T) bytes, and place the
                            // overflow flag at offset size_of(T).
                            let checked_rvalue = match rvalue {
                                Rvalue::BinaryOp(
                                    BinOp::AddWithOverflow
                                    | BinOp::SubWithOverflow
                                    | BinOp::MulWithOverflow,
                                    box (lhs, _),
                                ) => {
                                    let lhs_ty = lhs.ty(&self.mir.local_decls, self.tcx);
                                    let lhs_ty = self.monomorphize(lhs_ty);
                                    let arith_bytes =
                                        type_size(self.tcx, lhs_ty).unwrap_or(8) as u32;
                                    Some(arith_bytes)
                                }
                                _ => None,
                            };
                            // When val is a memory address (stack slot from
                            // Ref/RawPtr handler) and not a CheckedBinaryOp,
                            // do a word-by-word copy instead of a direct
                            // store (which would store the address, not the
                            // contents).
                            if checked_rvalue.is_none() && self.builder.is_memory_address(val) {
                                let num_words = (bytes as u64).div_ceil(8);
                                for i in 0..num_words {
                                    let byte_off = i * 8;
                                    let chunk = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                                    let src_addr = if byte_off == 0 {
                                        val
                                    } else {
                                        let off = self.builder.iconst(
                                            byte_off as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        );
                                        self.builder
                                            .ptradd(val.into(), off.into(), 0, Origin::synthetic())
                                            .raw()
                                    };
                                    let word = self.builder.load(
                                        src_addr.into(),
                                        chunk,
                                        Type::Int,
                                        self.current_mem.into(),
                                        int_annotation_for_bytes(chunk),
                                        Origin::synthetic(),
                                    );
                                    let dst_addr = if byte_off == 0 {
                                        slot
                                    } else {
                                        let off = self.builder.iconst(
                                            byte_off as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        );
                                        self.builder
                                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                                            .raw()
                                    };
                                    self.current_mem = self
                                        .builder
                                        .store(
                                            word.into(),
                                            dst_addr.into(),
                                            chunk,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        )
                                        .raw();
                                }
                            } else {
                                let store_bytes = checked_rvalue.unwrap_or(bytes);
                                self.current_mem = self
                                    .builder
                                    .store(
                                        val.into(),
                                        slot.into(),
                                        store_bytes,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                if let Some(arith_bytes) = checked_rvalue {
                                    let off = self.builder.iconst(
                                        arith_bytes as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    let flag_addr = self.builder.ptradd(
                                        slot.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    // Store the actual overflow flag
                                    // from the WithOverflow result.
                                    let flag_val = self
                                        .overflow_locals
                                        .get(place.local)
                                        .unwrap_or_else(|| {
                                            self.builder
                                                .iconst(
                                                    0,
                                                    64,
                                                    IntSignedness::DontCare,
                                                    Origin::synthetic(),
                                                )
                                                .raw()
                                        });
                                    self.current_mem = self
                                        .builder
                                        .store(
                                            flag_val.into(),
                                            flag_addr.into(),
                                            1,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        )
                                        .raw();
                                }
                            } // close is_memory_address else
                        }
                    } // close ref_fat_src else
                } else {
                    // When the Aggregate rvalue reused the
                    // destination slot, val == slot and the
                    // data is already in place — skip the copy.
                    if val != slot {
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                    // For checked ops (AddWithOverflow etc.), the
                    // primary result was stored but the overflow
                    // flag must also be written to its field offset
                    // inside the (T, bool) tuple.
                    if let Rvalue::BinaryOp(
                        BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow,
                        box (lhs, _),
                    ) = rvalue
                        && let Some(overflow_flag) = self.overflow_locals.get(place.local)
                    {
                        let lhs_ty = lhs.ty(&self.mir.local_decls, self.tcx);
                        let lhs_ty = self.monomorphize(lhs_ty);
                        let flag_offset = type_size(self.tcx, lhs_ty).unwrap_or(8) as i64;
                        let off = self.builder.iconst(
                            flag_offset,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let flag_addr =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                overflow_flag.into(),
                                flag_addr.into(),
                                1,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }
            } else {
                self.locals.set(place.local, val);
            }
        } else {
            self.locals.set(place.local, val);
        }
    }

    /// Writes an assignment into a destination local that currently lives in registers.
    fn assign_to_register_local(
        &mut self,
        val: ValueRef,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) {
        self.locals.set(place.local, val);
        // Propagate stack-local status when the source is a
        // stack local (e.g. `_6 = move _4` where _4 is sret,
        // or `_5 = _1 as T (Transmute)` where _1 is a two-reg
        // struct parameter, or `_5 = move ((_1 as Some).0: T)`
        // where the projected field is > 8 bytes).
        // Without this, later uses treat the slot pointer as
        // a data value instead of an address.
        // Only mark dest as a stack local when val is actually
        // a Ptr (a stack slot address).  When translate_operand
        // loaded the value from a slot for an integral type > 8
        // bytes (e.g. u128), val is an Int, not a Ptr — marking
        // the dest as stack in that case corrupts later uses that
        // call coerce_to_ptr on a non-pointer Int.
        let mark_as_stack = matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
            && match rvalue {
                // Direct copy/move from a stack local (no projections).
                // Only propagate when the source type is > 8 bytes,
                // because translate_operand loads small (≤8 byte)
                // values from the slot — the returned value is data,
                // not a slot pointer.
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if src.projection.is_empty() && self.stack_locals.is_stack(src.local) =>
                {
                    let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                    type_size(self.tcx, src_ty).unwrap_or(8) > 8
                }
                // Cast/Transmute from a stack local.
                // Exclude PtrToPtr from a large stack local: the
                // PtrToPtr handler in translate_rvalue already
                // loads the actual value from the slot, so val is
                // data (not a slot address) and the destination
                // must NOT be marked as stack.
                Rvalue::Cast(kind, Operand::Copy(src) | Operand::Move(src), cast_ty)
                    if src.projection.is_empty() && self.stack_locals.is_stack(src.local) =>
                {
                    let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                    let src_size = type_size(self.tcx, src_ty).unwrap_or(8);
                    if src_size > 8 {
                        // PtrToPtr with target ≤ 8 bytes already
                        // loaded the value — don't propagate.
                        let target_ty = self.monomorphize(*cast_ty);
                        let target_size = type_size(self.tcx, target_ty).unwrap_or(0);
                        !(matches!(kind, CastKind::PtrToPtr) && target_size <= 8)
                    } else {
                        false
                    }
                }
                // Projected place where the projected type is
                // > 8 bytes.  translate_operand returns an
                // address for large projected types (either a
                // pointer into a stack slot, or a dereferenced
                // pointer), so the destination must also be
                // treated as a stack local.
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if !src.projection.is_empty() =>
                {
                    let projected_ty = src.ty(&self.mir.local_decls, self.tcx).ty;
                    let projected_ty = self.monomorphize(projected_ty);
                    type_size(self.tcx, projected_ty).unwrap_or(8) > 8
                        && !is_fat_ptr(self.tcx, projected_ty)
                }
                // Ref/RawPtr producing a fat pointer: the
                // rvalue handler builds a 16-byte stack slot
                // containing (data_ptr, metadata).
                Rvalue::Ref(..) | Rvalue::RawPtr(..) => {
                    let dest_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                    is_fat_ptr(self.tcx, dest_ty)
                }
                _ => false,
            };
        if mark_as_stack {
            self.stack_locals.mark(place.local);
            // When the source is a projected field (e.g.
            // `_6 = _5.1`), val is a pointer INTO another
            // local's stack slot.  If that field is later
            // overwritten, _6 would see the new value
            // instead of the copied one.  Allocate a
            // private slot and copy the data.
            //
            // The same aliasing problem occurs for plain
            // copy/move of stack locals without projections:
            // `_8 = _6` where both are >8-byte stack types.
            // Without a copy, writing to _6's slot later
            // (e.g. `_6.0 = 3`) would corrupt _8.
            let needs_copy = matches!(rvalue,
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if !src.projection.is_empty()
            ) || matches!(rvalue,
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if src.projection.is_empty()
                        && self.stack_locals.is_stack(src.local)
            );
            if needs_copy {
                let dest_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                let sz = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                let new_slot =
                    self.builder
                        .stack_slot(std::cmp::max(sz, 1), 0, Origin::synthetic());
                let num_words = (sz as u64).div_ceil(8);
                for i in 0..num_words {
                    let off = i * 8;
                    let chunk = std::cmp::min(8, sz as u64 - off) as u32;
                    let src_addr = if off == 0 {
                        val
                    } else {
                        let o = self.builder.iconst(
                            off as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(val.into(), o.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    let word = self.builder.load(
                        src_addr.into(),
                        chunk,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    let dst_addr = if off == 0 {
                        new_slot
                    } else {
                        let o = self.builder.iconst(
                            off as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(new_slot.into(), o.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    self.current_mem = self
                        .builder
                        .store(
                            word.into(),
                            dst_addr.into(),
                            chunk,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
                self.locals.set(place.local, new_slot);
            }
        }
    }

    /// Writes an assignment into a projected destination place.
    fn assign_to_projected(&mut self, val: ValueRef, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        // Projected destination: compute address and emit Store.
        // persist_spill=true: if the base local was a register
        // that got spilled to a stack slot for field access,
        // make the spill permanent so later reads see the mutation.
        let addr_result = self.translate_place_to_addr_inner(place, true);
        if let Some((addr, projected_ty)) = addr_result {
            let addr = self.coerce_to_ptr(addr);
            let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
            let val_ty = self.builder.value_type(val).cloned();
            if matches!(val_ty.as_ref(), Some(Type::Ptr(_))) && bytes > 0 {
                let fat_src = match rvalue {
                    Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place))
                        if src_place.projection.is_empty()
                            && !self.stack_locals.is_stack(src_place.local) =>
                    {
                        self.fat_locals.get(src_place.local)
                    }
                    _ => None,
                };
                if is_fat_ptr(self.tcx, projected_ty)
                    && bytes >= 16
                    && let Some(fat_val) = self.extract_fat_component(rvalue)
                {
                    let data_ptr = if self.builder.is_local_memory_address(val)
                        && self.builder.stack_slot_size(val).is_some()
                    {
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
                    self.current_mem = self
                        .builder
                        .store(
                            data_ptr.into(),
                            addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let hi_addr =
                        self.builder
                            .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            fat_val.into(),
                            hi_addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                } else if let Some(fat_val) = fat_src.filter(|_| bytes >= 16) {
                    // Store data pointer into dst[0..8].
                    self.current_mem = self
                        .builder
                        .store(
                            val.into(),
                            addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                    // Store fat component into dst[8..16].
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let hi_addr =
                        self.builder
                            .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            fat_val.into(),
                            hi_addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                } else if bytes > 8 || matches!(rvalue, Rvalue::Aggregate(..)) || {
                    // When the destination is a non-pointer type
                    // (e.g. an ADT like NonNull<T>) and val is a
                    // Ptr, we need to decide whether val is a
                    // memory address to copy FROM, or a pointer
                    // VALUE to store directly.
                    //
                    // For Use(Move/Copy) of a non-stack local with
                    // no projections, translate_operand returns the
                    // register value.  Even if it's a Ptr (e.g. a
                    // ptradd from Offset), it's the VALUE, not an
                    // address pointing to data.  Store it directly.
                    let src_is_register = matches!(rvalue,
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            if src.projection.is_empty()
                                && !self.stack_locals.is_stack(src.local)
                    );
                    !matches!(
                        projected_ty.kind(),
                        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..)
                    ) && !src_is_register
                } {
                    // val is a pointer to multi-word data (e.g.
                    // symbol_addr of an Indirect constant like a
                    // slice reference, or a stack slot from an
                    // Aggregate rvalue).  Also applies to 8-byte
                    // non-pointer types (e.g. (char, bool)) where
                    // the pointer points to the actual data bytes.
                    // Copy word-by-word from the source address.
                    let src_base = match rvalue {
                        Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place))
                            if !src_place.projection.is_empty() =>
                        {
                            self.translate_place_to_addr(src_place)
                                .map(|(a, _)| self.coerce_to_ptr(a))
                        }
                        _ => None,
                    };
                    let src_base = src_base.unwrap_or(val);
                    let num_words = (bytes as u64).div_ceil(8);
                    for i in 0..num_words {
                        let byte_off = i * 8;
                        let chunk = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                        let src_addr = if byte_off == 0 {
                            src_base
                        } else {
                            let off = self.builder.iconst(
                                byte_off as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .ptradd(src_base.into(), off.into(), 0, Origin::synthetic())
                                .raw()
                        };
                        let word = self.builder.load(
                            src_addr.into(),
                            chunk,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(chunk),
                            Origin::synthetic(),
                        );
                        let dst_addr = if byte_off == 0 {
                            addr
                        } else {
                            let off = self.builder.iconst(
                                byte_off as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .ptradd(addr.into(), off.into(), 0, Origin::synthetic())
                                .raw()
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                word.into(),
                                dst_addr.into(),
                                chunk,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                } else {
                    // Scalar pointer value (≤8 bytes, e.g. &u32,
                    // *const T): store the value directly instead
                    // of treating it as an address to load from.
                    self.current_mem = self
                        .builder
                        .store(
                            val.into(),
                            addr.into(),
                            bytes,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else if bytes > 8 {
                // Wide value (e.g. i128 arithmetic result or
                // constant). Store full width — the legalizer
                // lowers wide integer stores into legal-width chunks.
                // For checked ops, store only the primary
                // result width, not the full tuple size.
                let store_bytes = if let Rvalue::BinaryOp(
                    BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow,
                    box (lhs, _),
                ) = rvalue
                {
                    let lhs_ty = lhs.ty(&self.mir.local_decls, self.tcx);
                    let lhs_ty = self.monomorphize(lhs_ty);
                    type_size(self.tcx, lhs_ty).unwrap_or(16) as u32
                } else {
                    bytes
                };
                self.current_mem = self
                    .builder
                    .store(
                        val.into(),
                        addr.into(),
                        store_bytes,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            } else if bytes > 0 {
                // For checked ops, only store primary result
                // bytes (not the full tuple including overflow
                // flag). The overflow flag is stored separately
                // below.
                let store_bytes = if let Rvalue::BinaryOp(
                    BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow,
                    box (lhs, _),
                ) = rvalue
                {
                    let lhs_ty = lhs.ty(&self.mir.local_decls, self.tcx);
                    let lhs_ty = self.monomorphize(lhs_ty);
                    type_size(self.tcx, lhs_ty).unwrap_or(8) as u32
                } else {
                    bytes
                };
                self.current_mem = self
                    .builder
                    .store(
                        val.into(),
                        addr.into(),
                        store_bytes,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
            // For checked ops (AddWithOverflow etc.) into a
            // projected destination, the overflow flag must be
            // stored at the end of the primary result.
            if let Rvalue::BinaryOp(
                BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow,
                box (lhs, _),
            ) = rvalue
                && let Some(overflow_flag) = self.overflow_locals.get(place.local)
            {
                let lhs_ty = lhs.ty(&self.mir.local_decls, self.tcx);
                let lhs_ty = self.monomorphize(lhs_ty);
                let flag_offset = type_size(self.tcx, lhs_ty).unwrap_or(8) as i64;
                let off = self.builder.iconst(
                    flag_offset,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let flag_addr =
                    self.builder
                        .ptradd(addr.into(), off.into(), 0, Origin::synthetic());
                let one = self
                    .builder
                    .iconst(1, 64, IntSignedness::DontCare, Origin::synthetic());
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                let flag_int = self.builder.select(
                    overflow_flag.into(),
                    one.into(),
                    zero.into(),
                    Type::Int,
                    Some(Annotation::Int(IntAnnotation {
                        bit_width: 8,
                        signedness: IntSignedness::Unsigned,
                    })),
                    Origin::synthetic(),
                );
                self.current_mem = self
                    .builder
                    .store(
                        flag_int.into(),
                        flag_addr.into(),
                        1,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
        }
    }
}
