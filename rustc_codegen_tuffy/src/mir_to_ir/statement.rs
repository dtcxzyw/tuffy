use super::ctx::TranslationCtx;
use super::types::*;
use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, Rvalue, StatementKind};
use rustc_middle::ty;
use tuffy_ir::instruction::{Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::ValueRef;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    pub(super) fn translate_statement(&mut self, stmt: &mir::Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let rval_result = self.translate_rvalue(rvalue, place);
                if let Some(val) = rval_result {
                    if place.projection.is_empty() {
                        // For stack-allocated locals, store the value into the
                        // existing stack slot instead of overwriting the pointer.
                        // This preserves the slot address for later loads (e.g.,
                        // sret return copy, field access).
                        if self.stack_locals.is_stack(place.local) {
                            if let Some(slot) = self.locals.get(place.local) {
                                if matches!(self.builder.value_type(slot), Some(Type::Ptr(_))) {
                                    let ty =
                                        self.monomorphize(self.mir.local_decls[place.local].ty);
                                    let bytes = type_size(self.tcx, ty).unwrap_or(8) as u32;
                                    // If val is also a pointer (e.g. stack slot from
                                    // Aggregate) and the type is larger than 8 bytes,
                                    // do a word-by-word copy of the DATA instead of
                                    // storing the pointer value.
                                    let val_ty = self.builder.value_type(val).cloned();
                                    let is_ref_rvalue =
                                        matches!(rvalue, Rvalue::Ref(..) | Rvalue::RawPtr(..));
                                    // When the destination MIR type is a thin
                                    // reference/pointer, val IS the pointer value
                                    // (not an address pointing to data).  Store it
                                    // directly instead of doing a word-by-word copy.
                                    let dest_is_ptr_ty = matches!(ty.kind(),
                                        ty::Ref(_, inner, _) if !matches!(inner.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
                                    ) || matches!(ty.kind(),
                                        ty::RawPtr(inner, _) if !matches!(inner.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
                                    ) || matches!(ty.kind(), ty::FnPtr(..));
                                    if matches!(val_ty.as_ref(), Some(Type::Ptr(_)))
                                        && bytes > 0
                                        && !is_ref_rvalue
                                        && !dest_is_ptr_ty
                                    {
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
                                                Rvalue::Use(
                                                    Operand::Copy(src_place)
                                                    | Operand::Move(src_place),
                                                ) if src_place.projection.is_empty()
                                                    && !self
                                                        .stack_locals
                                                        .is_stack(src_place.local) =>
                                                {
                                                    self.fat_locals.get(src_place.local)
                                                }
                                                // Constant fat pointer (e.g. &str literal,
                                                // &[T] associated constant).  translate_const
                                                // already loaded the data pointer; extract the
                                                // length from the constant so we can store both
                                                // components into the stack slot.
                                                Rvalue::Use(Operand::Constant(c)) => {
                                                    let mono_const = self
                                                        .tcx
                                                        .instantiate_and_normalize_erasing_regions(
                                                            self.instance.args,
                                                            ty::TypingEnv::fully_monomorphized(),
                                                            ty::EarlyBinder::bind(c.const_),
                                                        );
                                                    let resolved = match mono_const {
                                                        mir::Const::Val(v, _) => Some(v),
                                                        _ => {
                                                            let typing_env =
                                                                ty::TypingEnv::fully_monomorphized(
                                                                );
                                                            mono_const
                                                                .eval(self.tcx, typing_env, c.span)
                                                                .ok()
                                                        }
                                                    };
                                                    if let Some(mir::ConstValue::Slice {
                                                        meta,
                                                        ..
                                                    }) = resolved
                                                    {
                                                        Some(self.builder.iconst(
                                                            meta as i64,
                                                            Origin::synthetic(),
                                                        ))
                                                    } else if let Some(
                                                        mir::ConstValue::Indirect {
                                                            alloc_id,
                                                            offset,
                                                        },
                                                    ) = resolved
                                                    {
                                                        let const_ty = mono_const.ty();
                                                        if is_fat_ptr(self.tcx, const_ty) {
                                                            let alloc =
                                                                self.tcx.global_alloc(alloc_id);
                                                            if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) = alloc {
                                                            let inner = mem_alloc.inner();
                                                            let byte_offset = offset.bytes() as usize + 8;
                                                            let len_bytes = inner.inspect_with_uninit_and_ptr_outside_interpreter(
                                                                byte_offset..byte_offset + 8,
                                                            );
                                                            let len = u64::from_le_bytes(
                                                                len_bytes.try_into().unwrap_or([0u8; 8]),
                                                            );
                                                            Some(self.builder.iconst(len as i64, Origin::synthetic()))
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
                                                    Operand::Copy(src_place)
                                                    | Operand::Move(src_place),
                                                    _,
                                                ) if src_place.projection.is_empty()
                                                    && !self
                                                        .stack_locals
                                                        .is_stack(src_place.local) =>
                                                {
                                                    self.fat_locals.get(src_place.local)
                                                }
                                                // &raw const (*local) / &(*local) on a
                                                // non-stack fat pointer local: the fat
                                                // component lives in fat_locals.
                                                Rvalue::Ref(_, _, src_place)
                                                | Rvalue::RawPtr(_, src_place)
                                                    if !self
                                                        .stack_locals
                                                        .is_stack(src_place.local) =>
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
                                                fat_src
                                                    .or_else(|| self.extract_fat_component(rvalue))
                                            };
                                            if let Some(fat_val) = fat_src {
                                                // Store data pointer into slot[0..8].
                                                self.current_mem = self.builder.store(
                                                    val.into(),
                                                    slot.into(),
                                                    8,
                                                    self.current_mem.into(),
                                                    Origin::synthetic(),
                                                );
                                                // Store fat component (length/vtable) into slot[8..16].
                                                let off8 =
                                                    self.builder.iconst(8, Origin::synthetic());
                                                let hi_addr = self.builder.ptradd(
                                                    slot.into(),
                                                    off8.into(),
                                                    0,
                                                    Origin::synthetic(),
                                                );
                                                self.current_mem = self.builder.store(
                                                    fat_val.into(),
                                                    hi_addr.into(),
                                                    8,
                                                    self.current_mem.into(),
                                                    Origin::synthetic(),
                                                );
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
                                                        Operand::Copy(src_place)
                                                        | Operand::Move(src_place),
                                                    ) if !src_place.projection.is_empty() => self
                                                        .translate_place_to_addr(src_place)
                                                        .map(|(a, _)| self.coerce_to_ptr(a)),
                                                    _ => None,
                                                };
                                                let src_base = src_base.unwrap_or(val);
                                                let num_words = (bytes as u64).div_ceil(8);
                                                for i in 0..num_words {
                                                    let byte_off = i * 8;
                                                    let chunk =
                                                        std::cmp::min(8, bytes as u64 - byte_off)
                                                            as u32;
                                                    let src_addr = if byte_off == 0 {
                                                        src_base
                                                    } else {
                                                        let off = self.builder.iconst(
                                                            byte_off as i64,
                                                            Origin::synthetic(),
                                                        );
                                                        self.builder.ptradd(
                                                            src_base.into(),
                                                            off.into(),
                                                            0,
                                                            Origin::synthetic(),
                                                        )
                                                    };
                                                    let word = self.builder.load(
                                                        src_addr.into(),
                                                        chunk,
                                                        Type::Int,
                                                        self.current_mem.into(),
                                                        None,
                                                        Origin::synthetic(),
                                                    );
                                                    let dst_addr = if byte_off == 0 {
                                                        slot
                                                    } else {
                                                        let off = self.builder.iconst(
                                                            byte_off as i64,
                                                            Origin::synthetic(),
                                                        );
                                                        self.builder.ptradd(
                                                            slot.into(),
                                                            off.into(),
                                                            0,
                                                            Origin::synthetic(),
                                                        )
                                                    };
                                                    self.current_mem = self.builder.store(
                                                        word.into(),
                                                        dst_addr.into(),
                                                        chunk,
                                                        self.current_mem.into(),
                                                        Origin::synthetic(),
                                                    );
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
                                            Rvalue::Ref(_, _, src_place)
                                            | Rvalue::RawPtr(_, src_place)
                                                if !self.stack_locals.is_stack(src_place.local) =>
                                            {
                                                self.fat_locals.get(src_place.local)
                                            }
                                            _ => None,
                                        };
                                        if let Some(fat_val) = ref_fat_src {
                                            // Store data pointer into slot[0..8].
                                            self.current_mem = self.builder.store(
                                                val.into(),
                                                slot.into(),
                                                8,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            );
                                            // Store metadata (length/vtable) into slot[8..16].
                                            let off8 = self.builder.iconst(8, Origin::synthetic());
                                            let hi_addr = self.builder.ptradd(
                                                slot.into(),
                                                off8.into(),
                                                0,
                                                Origin::synthetic(),
                                            );
                                            self.current_mem = self.builder.store(
                                                fat_val.into(),
                                                hi_addr.into(),
                                                8,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            );
                                        } else {
                                            let src_slot = match rvalue {
                                                Rvalue::Use(
                                                    Operand::Copy(src_place)
                                                    | Operand::Move(src_place),
                                                ) if src_place.projection.is_empty()
                                                    && self
                                                        .stack_locals
                                                        .is_stack(src_place.local) =>
                                                {
                                                    self.locals.get(src_place.local)
                                                }
                                                // &(*local) / &raw (*local) on a fat-pointer
                                                // stack local: the slot holds the full fat
                                                // pointer (data ptr + metadata) which must be
                                                // copied word-by-word to the destination.
                                                Rvalue::Ref(_, _, src_place)
                                                | Rvalue::RawPtr(_, src_place)
                                                    if self
                                                        .stack_locals
                                                        .is_stack(src_place.local) =>
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
                                                    let chunk =
                                                        std::cmp::min(8, bytes as u64 - byte_off)
                                                            as u32;
                                                    let src_addr = if byte_off == 0 {
                                                        src_base
                                                    } else {
                                                        let off = self.builder.iconst(
                                                            byte_off as i64,
                                                            Origin::synthetic(),
                                                        );
                                                        self.builder.ptradd(
                                                            src_base.into(),
                                                            off.into(),
                                                            0,
                                                            Origin::synthetic(),
                                                        )
                                                    };
                                                    let word = self.builder.load(
                                                        src_addr.into(),
                                                        chunk,
                                                        Type::Int,
                                                        self.current_mem.into(),
                                                        None,
                                                        Origin::synthetic(),
                                                    );
                                                    let dst_addr = if byte_off == 0 {
                                                        slot
                                                    } else {
                                                        let off = self.builder.iconst(
                                                            byte_off as i64,
                                                            Origin::synthetic(),
                                                        );
                                                        self.builder.ptradd(
                                                            slot.into(),
                                                            off.into(),
                                                            0,
                                                            Origin::synthetic(),
                                                        )
                                                    };
                                                    self.current_mem = self.builder.store(
                                                        word.into(),
                                                        dst_addr.into(),
                                                        chunk,
                                                        self.current_mem.into(),
                                                        Origin::synthetic(),
                                                    );
                                                }
                                            } else {
                                                // No source slot — store only the bytes
                                                // we actually have (8 for an Int value).
                                                self.current_mem = self.builder.store(
                                                    val.into(),
                                                    slot.into(),
                                                    std::cmp::min(bytes, 8),
                                                    self.current_mem.into(),
                                                    Origin::synthetic(),
                                                );
                                                // CheckedBinaryOp stores (result, bool)
                                                // but translate_rvalue only returns the
                                                // arithmetic result.  Zero the overflow
                                                // flag so later reads don't see garbage.
                                                let is_checked = matches!(
                                                    rvalue,
                                                    Rvalue::BinaryOp(
                                                        BinOp::AddWithOverflow
                                                            | BinOp::SubWithOverflow
                                                            | BinOp::MulWithOverflow,
                                                        _
                                                    )
                                                );
                                                if is_checked && bytes > 8 {
                                                    let off =
                                                        self.builder.iconst(8, Origin::synthetic());
                                                    let flag_addr = self.builder.ptradd(
                                                        slot.into(),
                                                        off.into(),
                                                        0,
                                                        Origin::synthetic(),
                                                    );
                                                    let zero =
                                                        self.builder.iconst(0, Origin::synthetic());
                                                    self.current_mem = self.builder.store(
                                                        zero.into(),
                                                        flag_addr.into(),
                                                        1,
                                                        self.current_mem.into(),
                                                        Origin::synthetic(),
                                                    );
                                                }
                                            }
                                        } // close ref_fat_src else
                                    } else {
                                        self.current_mem = self.builder.store(
                                            val.into(),
                                            slot.into(),
                                            bytes,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        );
                                    }
                                } else {
                                    self.locals.set(place.local, val);
                                }
                            } else {
                                self.locals.set(place.local, val);
                            }
                        } else {
                            self.locals.set(place.local, val);
                            // Propagate stack-local status when the source is a
                            // stack local (e.g. `_6 = move _4` where _4 is sret,
                            // or `_5 = _1 as T (Transmute)` where _1 is a two-reg
                            // struct parameter, or `_5 = move ((_1 as Some).0: T)`
                            // where the projected field is > 8 bytes).
                            // Without this, later uses treat the slot pointer as
                            // a data value instead of an address.
                            let mark_as_stack = match rvalue {
                                // Direct copy/move from a stack local (no projections).
                                // Only propagate when the source type is > 8 bytes,
                                // because translate_operand loads small (≤8 byte)
                                // values from the slot — the returned value is data,
                                // not a slot pointer.
                                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                                    if src.projection.is_empty()
                                        && self.stack_locals.is_stack(src.local) =>
                                {
                                    let src_ty =
                                        self.monomorphize(self.mir.local_decls[src.local].ty);
                                    type_size(self.tcx, src_ty).unwrap_or(8) > 8
                                }
                                // Cast/Transmute from a stack local.
                                // Exclude PtrToPtr from a large stack local: the
                                // PtrToPtr handler in translate_rvalue already
                                // loads the actual value from the slot, so val is
                                // data (not a slot address) and the destination
                                // must NOT be marked as stack.
                                Rvalue::Cast(
                                    kind,
                                    Operand::Copy(src) | Operand::Move(src),
                                    cast_ty,
                                ) if src.projection.is_empty()
                                    && self.stack_locals.is_stack(src.local) =>
                                {
                                    let src_ty =
                                        self.monomorphize(self.mir.local_decls[src.local].ty);
                                    let src_size = type_size(self.tcx, src_ty).unwrap_or(8);
                                    if src_size > 8 {
                                        // PtrToPtr with target ≤ 8 bytes already
                                        // loaded the value — don't propagate.
                                        let target_ty = self.monomorphize(*cast_ty);
                                        let target_size =
                                            type_size(self.tcx, target_ty).unwrap_or(0);
                                        if matches!(kind, CastKind::PtrToPtr) && target_size <= 8 {
                                            false
                                        } else {
                                            true
                                        }
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
                                _ => false,
                            };
                            if mark_as_stack {
                                self.stack_locals.mark(place.local);
                            }
                        }
                    } else {
                        // Projected destination: compute address and emit Store.
                        // persist_spill=true: if the base local was a register
                        // that got spilled to a stack slot for field access,
                        // make the spill permanent so later reads see the mutation.
                        if let Some((addr, projected_ty)) =
                            self.translate_place_to_addr_inner(place, true)
                        {
                            let addr = self.coerce_to_ptr(addr);
                            let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
                            let val_ty = self.builder.value_type(val).cloned();
                            if matches!(val_ty.as_ref(), Some(Type::Ptr(_))) && bytes > 0 {
                                // Check if source is a non-stack fat pointer local.
                                let fat_src = match rvalue {
                                    Rvalue::Use(
                                        Operand::Copy(src_place) | Operand::Move(src_place),
                                    ) if src_place.projection.is_empty()
                                        && !self.stack_locals.is_stack(src_place.local) =>
                                    {
                                        self.fat_locals.get(src_place.local)
                                    }
                                    _ => None,
                                };
                                if let Some(fat_val) = fat_src.filter(|_| bytes >= 16) {
                                    // Store data pointer into dst[0..8].
                                    self.current_mem = self.builder.store(
                                        val.into(),
                                        addr.into(),
                                        8,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                    // Store fat component into dst[8..16].
                                    let off8 = self.builder.iconst(8, Origin::synthetic());
                                    let hi_addr = self.builder.ptradd(
                                        addr.into(),
                                        off8.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    self.current_mem = self.builder.store(
                                        fat_val.into(),
                                        hi_addr.into(),
                                        8,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                } else if bytes > 8 || matches!(rvalue, Rvalue::Aggregate(..)) {
                                    // val is a pointer to multi-word data (e.g.
                                    // symbol_addr of an Indirect constant like a
                                    // slice reference, or a stack slot from an
                                    // Aggregate rvalue).  Copy word-by-word from
                                    // the source address.
                                    let src_base = match rvalue {
                                        Rvalue::Use(
                                            Operand::Copy(src_place) | Operand::Move(src_place),
                                        ) if !src_place.projection.is_empty() => self
                                            .translate_place_to_addr(src_place)
                                            .map(|(a, _)| self.coerce_to_ptr(a)),
                                        _ => None,
                                    };
                                    let src_base = src_base.unwrap_or(val);
                                    let num_words = (bytes as u64).div_ceil(8);
                                    for i in 0..num_words {
                                        let byte_off = i * 8;
                                        let chunk =
                                            std::cmp::min(8, bytes as u64 - byte_off) as u32;
                                        let src_addr = if byte_off == 0 {
                                            src_base
                                        } else {
                                            let off = self
                                                .builder
                                                .iconst(byte_off as i64, Origin::synthetic());
                                            self.builder.ptradd(
                                                src_base.into(),
                                                off.into(),
                                                0,
                                                Origin::synthetic(),
                                            )
                                        };
                                        let word = self.builder.load(
                                            src_addr.into(),
                                            chunk,
                                            Type::Int,
                                            self.current_mem.into(),
                                            None,
                                            Origin::synthetic(),
                                        );
                                        let dst_addr = if byte_off == 0 {
                                            addr
                                        } else {
                                            let off = self
                                                .builder
                                                .iconst(byte_off as i64, Origin::synthetic());
                                            self.builder.ptradd(
                                                addr.into(),
                                                off.into(),
                                                0,
                                                Origin::synthetic(),
                                            )
                                        };
                                        self.current_mem = self.builder.store(
                                            word.into(),
                                            dst_addr.into(),
                                            chunk,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        );
                                    }
                                } else {
                                    // Scalar pointer value (≤8 bytes, e.g. &u32,
                                    // *const T): store the value directly instead
                                    // of treating it as an address to load from.
                                    self.current_mem = self.builder.store(
                                        val.into(),
                                        addr.into(),
                                        bytes,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                }
                            } else if bytes > 8 {
                                // Scalar Int value being stored to a >8-byte
                                // projected field (e.g. u16 as u128 → _2.0).
                                // Store low word, then compute and store high word.
                                self.current_mem = self.builder.store(
                                    val.into(),
                                    addr.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                );
                                let src_is_signed = match rvalue {
                                    Rvalue::Cast(CastKind::IntToInt, op, _) => {
                                        let src_ty = match op {
                                            Operand::Copy(p) | Operand::Move(p) => self
                                                .monomorphize(
                                                    p.ty(&self.mir.local_decls, self.tcx).ty,
                                                ),
                                            Operand::Constant(c) => self.monomorphize(c.ty()),
                                            _ => projected_ty,
                                        };
                                        is_signed_int(src_ty)
                                    }
                                    _ => matches!(projected_ty.kind(), ty::Int(ty::IntTy::I128)),
                                };
                                let hi_word = if src_is_signed {
                                    let c63 = self.builder.iconst(63, Origin::synthetic());
                                    let signed_op =
                                        IrOperand::annotated(val, Annotation::Signed(64));
                                    self.builder.shr(
                                        signed_op,
                                        c63.into(),
                                        None,
                                        Origin::synthetic(),
                                    )
                                } else {
                                    self.builder.iconst(0, Origin::synthetic())
                                };
                                let off8 = self.builder.iconst(8, Origin::synthetic());
                                let hi_addr = self.builder.ptradd(
                                    addr.into(),
                                    off8.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                self.current_mem = self.builder.store(
                                    hi_word.into(),
                                    hi_addr.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                );
                            } else if bytes > 0 {
                                self.current_mem = self.builder.store(
                                    val.into(),
                                    addr.into(),
                                    bytes,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                );
                            }
                        }
                    }
                }
                // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
                if let Some(fat_val) = self.extract_fat_component(rvalue) {
                    self.fat_locals.set(place.local, fat_val);
                    // For stack-allocated locals, also store the metadata to
                    // the stack slot at offset 8 so that code loading the full
                    // fat pointer from the slot (e.g. the Return terminator's
                    // stack-allocated path) sees both words.
                    if self.stack_locals.is_stack(place.local) {
                        if let Some(slot) = self.locals.get(place.local) {
                            let off = self.builder.iconst(8, Origin::synthetic());
                            let addr = self.builder.ptradd(
                                slot.into(),
                                off.into(),
                                0,
                                Origin::synthetic(),
                            );
                            self.current_mem = self.builder.store(
                                fat_val.into(),
                                addr.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
                        }
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
                            let off8 = self.builder.iconst(8, Origin::synthetic());
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
                                None,
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
                            let byte_count = if pointee_size <= 1 {
                                count_v
                            } else {
                                let sz = self
                                    .builder
                                    .iconst(pointee_size as i64, Origin::synthetic());
                                self.builder.mul(
                                    count_v.into(),
                                    sz.into(),
                                    None,
                                    Origin::synthetic(),
                                )
                            };
                            let sym_id = self.symbols.intern("memcpy");
                            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                            let (mem_out, _) = self.builder.call(
                                callee.into(),
                                vec![dst_v.into(), src_v.into(), byte_count.into()],
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            self.current_mem = mem_out;
                        }
                    }
                    NonDivergingIntrinsic::Assume(_) => {
                        // Runtime assumption — no codegen needed.
                    }
                }
            }
            _ => {}
        }
    }

    /// Write the discriminant tag for an enum variant.
    ///
    /// Handles both `TagEncoding::Direct` (write the discriminant value) and
    /// `TagEncoding::Niche` (compute niche_start + offset and write to the
    /// niche field).  For niche encoding, the untagged variant is a no-op
    /// because the payload already distinguishes it.
    pub(super) fn translate_set_discriminant(
        &mut self,
        place: &Place<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(place_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        // Compute the tag value to store.
        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match place_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    // The payload already encodes this variant — nothing to write.
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

        // Resolve the base address of the enum.
        let base_addr = if place.projection.is_empty() {
            if self.stack_locals.is_stack(place.local) {
                match self.locals.get(place.local) {
                    Some(v) => v,
                    None => return,
                }
            } else {
                return;
            }
        } else {
            match self.translate_place_to_addr(place) {
                Some((addr, _)) => self.coerce_to_ptr(addr),
                None => return,
            }
        };

        // Tag field offset and store size.
        let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
        let tag_size = match tag.primitive() {
            rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
            rustc_abi::Primitive::Pointer(_) => 8,
            _ => 8,
        };

        let tag_addr = if tag_offset != 0 {
            let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
            self.builder
                .ptradd(base_addr.into(), off.into(), 0, Origin::synthetic())
        } else {
            base_addr
        };

        let tag_const = self.builder.iconst(tag_val, Origin::synthetic());
        self.current_mem = self.builder.store(
            tag_const.into(),
            tag_addr.into(),
            tag_size,
            self.current_mem.into(),
            Origin::synthetic(),
        );
    }

    /// Write the discriminant tag for an enum variant into a slot pointer.
    ///
    /// Called from the `Rvalue::Aggregate` handler to set the correct
    /// discriminant after storing variant fields.
    pub(super) fn write_enum_tag(
        &mut self,
        slot: ValueRef,
        enum_ty: ty::Ty<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(enum_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match enum_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

        let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
        let tag_size = match tag.primitive() {
            rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
            rustc_abi::Primitive::Pointer(_) => 8,
            _ => 8,
        };

        let tag_addr = if tag_offset != 0 {
            let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
            self.builder
                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
        } else {
            slot
        };

        let tag_const = self.builder.iconst(tag_val, Origin::synthetic());
        self.current_mem = self.builder.store(
            tag_const.into(),
            tag_addr.into(),
            tag_size,
            self.current_mem.into(),
            Origin::synthetic(),
        );
    }
}
