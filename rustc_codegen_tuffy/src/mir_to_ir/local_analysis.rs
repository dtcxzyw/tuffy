//! Local variable analysis: determine which MIR locals need stack slots.
//!
//! This pre-scan runs before the main translation loop.  It marks locals
//! that cannot be kept in SSA registers (e.g. multi-block assignments,
//! composite types, address-taken locals) for stack promotion.

use rustc_middle::mir::{self, BasicBlock, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::IntSignedness;

use super::ctx::TranslationCtx;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Analyse MIR locals and promote those that cannot live in SSA
    /// registers to stack slots.  Also allocates the exception-pointer
    /// stack slot when unwind cleanup blocks are present.
    pub(super) fn promote_locals_to_stack(&mut self) {
        // Pre-scan: find scalar locals assigned in more than one basic block.
        // These need stack slots so that mutations in loop bodies are visible
        // at loop headers (SSA values can't be mutated in place).
        {
            let mut assign_bb: Vec<Option<BasicBlock>> = vec![None; self.mir.local_decls.len()];
            // Function parameters are effectively assigned in the entry block
            // by translate_params.  Seed assign_bb so that any MIR assignment
            // to a parameter in a different block triggers stack promotion.
            let entry_bb = mir::BasicBlock::from_u32(0);
            for i in 0..self.mir.arg_count {
                let local = mir::Local::from_usize(i + 1);
                // Only seed non-stack params (large structs / two-reg structs
                // are already stack locals from translate_params).
                if !self.stack_locals.is_stack(local) {
                    assign_bb[local.as_usize()] = Some(entry_bb);
                }
            }
            for (bb, bb_data) in self.mir.basic_blocks.iter_enumerated() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (place, _)) = &stmt.kind
                        && place.projection.is_empty()
                    {
                        let local = place.local;
                        // _0 (return place) is only skipped when it already has
                        // a stack slot (sret); otherwise it may need promotion
                        // when assigned in multiple BBs.
                        if local.as_usize() == 0 && self.stack_locals.is_stack(local) {
                            continue;
                        }
                        let ty = self.monomorphize(self.mir.local_decls[local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(0);
                        if size == 0 {
                            continue;
                        }
                        if let Some(prev_bb) = assign_bb[local.as_usize()] {
                            if prev_bb != bb && !self.stack_locals.is_stack(local) {
                                let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                                self.promote_local_to_stack(local, size, align);
                            }
                        } else {
                            assign_bb[local.as_usize()] = Some(bb);
                        }
                    }
                }
                // Also check call terminators — they assign to a destination local.
                if let Some(terminator) = &bb_data.terminator
                    && let TerminatorKind::Call { destination, .. } = &terminator.kind
                    && destination.projection.is_empty()
                {
                    let local = destination.local;
                    if local.as_usize() == 0 && self.stack_locals.is_stack(local) {
                        // _0 with sret already has a stack slot — skip.
                    } else {
                        let ty = self.monomorphize(self.mir.local_decls[local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(0);
                        if size > 0 {
                            if let Some(prev_bb) = assign_bb[local.as_usize()] {
                                if prev_bb != bb && !self.stack_locals.is_stack(local) {
                                    let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                                    self.promote_local_to_stack(local, size, align);
                                }
                            } else {
                                assign_bb[local.as_usize()] = Some(bb);
                            }
                        }
                    }
                }
            }

            // Locals assigned via projections (e.g. `_0.0 = ...`) need stack
            // slots unconditionally — partial field writes require addressable memory.
            for bb_data in self.mir.basic_blocks.iter() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                        self.promote_projected_place(place);
                    }
                }
                // Also check Call terminators — they can assign to projected
                // destinations like `(_5.0: u64) = bswap(...)`.
                if let Some(terminator) = &bb_data.terminator
                    && let TerminatorKind::Call { destination, .. } = &terminator.kind
                {
                    self.promote_projected_place(destination);
                }
            }

            // Allocate stack slots for all >8 byte composite locals (arrays, structs).
            // These must be stored in memory for proper argument decomposition.
            for local in self.mir.local_decls.indices() {
                if !self.stack_locals.is_stack(local) {
                    let ty = self.monomorphize(self.mir.local_decls[local].ty);
                    let size = type_size(self.tcx, ty).unwrap_or(0);
                    if size > 8 && matches!(ty.kind(), ty::Array(..) | ty::Adt(..)) {
                        let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                        self.promote_local_to_stack(local, size, align);
                    }
                }
            }

            // Promote locals used in a block that precedes their assignment
            // block in declaration order.
            let collect_used_locals = |op: &Operand<'tcx>| -> Option<mir::Local> {
                match op {
                    Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                    _ => None,
                }
            };
            for (bb, bb_data) in self.mir.basic_blocks.iter_enumerated() {
                let mut used_locals = Vec::new();
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                        // When the LHS has a leading Deref (e.g. `(*_7) = ...`),
                        // the base local is read to obtain the pointer address.
                        // It must be promoted if defined in a later block.
                        if !place.projection.is_empty()
                            && matches!(place.projection.first(), Some(mir::PlaceElem::Deref))
                        {
                            used_locals.push(place.local);
                        }
                        match rvalue {
                            Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => {
                                used_locals.extend(collect_used_locals(op));
                            }
                            Rvalue::BinaryOp(_, box (a, b)) => {
                                used_locals.extend(collect_used_locals(a));
                                used_locals.extend(collect_used_locals(b));
                            }
                            Rvalue::Aggregate(_, ops) => {
                                for op in ops.iter() {
                                    used_locals.extend(collect_used_locals(op));
                                }
                            }
                            Rvalue::Discriminant(place)
                            | Rvalue::Ref(_, _, place)
                            | Rvalue::RawPtr(_, place)
                            | Rvalue::CopyForDeref(place) => {
                                used_locals.push(place.local);
                            }
                            _ => {}
                        }
                    }
                }
                if let Some(terminator) = &bb_data.terminator {
                    match &terminator.kind {
                        TerminatorKind::SwitchInt { discr, .. } => {
                            used_locals.extend(collect_used_locals(discr));
                        }
                        TerminatorKind::Call { func, args, .. } => {
                            used_locals.extend(collect_used_locals(func));
                            for arg in args {
                                used_locals.extend(collect_used_locals(&arg.node));
                            }
                        }
                        TerminatorKind::Return => {
                            used_locals.push(mir::Local::from_usize(0));
                        }
                        _ => {}
                    }
                }
                for local in used_locals {
                    if local.as_usize() > 0 && local.as_usize() <= self.mir.arg_count {
                        continue;
                    }
                    if self.stack_locals.is_stack(local) {
                        continue;
                    }
                    if let Some(def_bb) = assign_bb[local.as_usize()]
                        && bb < def_bb
                    {
                        let ty = self.monomorphize(self.mir.local_decls[local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(0);
                        if size > 0 {
                            let slot_size = (size as u32).max(1);
                            let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                            let slot =
                                self.builder
                                    .stack_slot(slot_size, align, Origin::synthetic());
                            self.locals.set(local, slot);
                            self.stack_locals.mark(local);
                        }
                    }
                }
            }
        }

        // Pre-scan: promote locals whose address is taken (Ref / RawPtr) to
        // stack locals.  Without this, `&mut x` inside a loop body would spill
        // the current value into a *new* temporary each iteration, losing
        // mutations made through the reference on previous iterations.
        {
            for bb_data in self.mir.basic_blocks.iter() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                        let referenced_local = match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                                Some(place.local)
                            }
                            _ => None,
                        };
                        if let Some(local) = referenced_local {
                            if self.stack_locals.is_stack(local) {
                                continue;
                            }
                            let ty = self.monomorphize(self.mir.local_decls[local].ty);
                            let size = type_size(self.tcx, ty).unwrap_or(0);
                            let ty_align = type_align(self.tcx, ty).unwrap_or(1);
                            if size == 0 && ty_align <= 1 {
                                continue;
                            }
                            // ZSTs with alignment > 1 (e.g. #[repr(align(64))])
                            // need a stack slot so &val produces an aligned address.
                            if size == 0 {
                                let slot = self.builder.stack_slot(
                                    0,
                                    ty_align as u32,
                                    Origin::synthetic(),
                                );
                                self.locals.set(local, slot);
                                self.stack_locals.mark(local);
                                continue;
                            }
                            // Large params (size > 16 bytes) are passed by hidden pointer in
                            // the SysV ABI — regardless of whether rustc classifies them as
                            // Memory, ScalarPair, or Scalar.  The received value IS already
                            // the pointer to the data in the caller's stack frame.  Creating
                            // a new slot and only copying 8 bytes (the pointer itself) would
                            // lose the indirection, so just mark the local as stack-allocated
                            // without allocating a new slot.
                            // This optimization only applies to parameters, not to local
                            // variables — locals with size > 16 bytes need a real slot.
                            if size > 16 && local.as_usize() <= self.mir.arg_count {
                                self.stack_locals.mark(local);
                                continue;
                            }
                            let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                            let slot = self.builder.stack_slot(
                                (size as u32).max(1),
                                align,
                                Origin::synthetic(),
                            );
                            if let Some(prev) = self.locals.get(local) {
                                // For fat pointer ScalarPairs (&str, &[T], &dyn Trait), only
                                // store the first word (data pointer); the second word
                                // (metadata) is handled below via fat_locals.
                                // For non-fat-ptr ScalarPairs (e.g. (char, i64)), store the
                                // full size so the legalizer can emit both lo and hi stores.
                                // Scalar and Memory types store the full size.
                                let store_bytes = if is_fat_ptr(self.tcx, ty) {
                                    8
                                } else {
                                    size as u32
                                };
                                self.current_mem = self
                                    .builder
                                    .store(
                                        prev.into(),
                                        slot.into(),
                                        store_bytes,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                if let Some(meta) = self.fat_locals.get(local) {
                                    let off8 = self.builder.iconst(
                                        8,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    let meta_addr = self.builder.ptradd(
                                        slot.into(),
                                        off8.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    self.current_mem = self
                                        .builder
                                        .store(
                                            meta.into(),
                                            meta_addr.into(),
                                            8,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        )
                                        .raw();
                                }
                            }
                            self.locals.set(local, slot);
                            self.stack_locals.mark(local);
                        }
                    }
                }
            }
        }

        // Pre-assign reference holders: when `_5 = &mut _2` (or &, &raw)
        // and `_2` is now a stack local, pre-assign `_5` to `_2`'s slot.
        // MIR passes (e.g. CheckAlignment) can reorder basic blocks so the
        // `_5 = &mut _2` definition may appear in a later-indexed block than
        // a use like `(*_5) = ...`.  Since the flat LocalMap has no per-block
        // scoping, pre-assigning the reference holder here ensures it is
        // visible in all blocks regardless of index order.
        {
            // Collect which locals have their address taken (via &_X or
            // &mut _X where _X has no projections).  These locals need
            // to be backed by stack slots so the address is stable.
            let mut addr_taken: std::collections::HashSet<mir::Local> =
                std::collections::HashSet::new();
            for bb_data in self.mir.basic_blocks.iter() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                        && place.projection.is_empty()
                    {
                        addr_taken.insert(place.local);
                    }
                }
            }
            for bb_data in self.mir.basic_blocks.iter() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind {
                        let ref_place = match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(place),
                            _ => None,
                        };
                        if let Some(place) = ref_place
                            && place.projection.is_empty()
                            && dest.projection.is_empty()
                            && self.stack_locals.is_stack(place.local)
                            && self.locals.get(dest.local).is_none()
                            && let Some(slot) = self.locals.get(place.local)
                        {
                            // If this local's address is also taken (e.g.
                            // `_5 = &mut _0` where `_0 = &raw const _4`,
                            // then later `_7 = &mut _0`), we need to
                            // store the value in a proper stack slot
                            // so that the spill slot is initialized at
                            // function entry rather than lazily in a
                            // later block.
                            if addr_taken.contains(&dest.local) {
                                let dest_ty =
                                    self.monomorphize(self.mir.local_decls[dest.local].ty);
                                let dest_sz = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                                let new_slot =
                                    self.builder
                                        .stack_slot(dest_sz.max(8), 0, Origin::synthetic());
                                self.current_mem = self
                                    .builder
                                    .store(
                                        slot.into(),
                                        new_slot.into(),
                                        8,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                self.locals.set(dest.local, new_slot);
                                self.stack_locals.mark(dest.local);
                            } else {
                                self.locals.set(dest.local, slot);
                            }
                        }
                    }
                }
            }
            // Second pass: handle `_X = &(mut) (*_Y)` where _Y was
            // pre-assigned above (it points to a stack local). Since
            // `*_Y` dereferences to the same stack slot, _X gets the
            // same address.
            for bb_data in self.mir.basic_blocks.iter() {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind {
                        let ref_place = match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(place),
                            _ => None,
                        };
                        if let Some(place) = ref_place
                            && place.projection.len() == 1
                            && matches!(place.projection[0], mir::PlaceElem::Deref)
                            && dest.projection.is_empty()
                            && self.locals.get(dest.local).is_none()
                            && let Some(slot) = self.locals.get(place.local)
                        {
                            self.locals.set(dest.local, slot);
                        }
                    }
                }
            }
        }

        // Pre-allocate a stack slot for the return place (_0) when it is a
        // multi-word type (9-16 bytes, e.g. &str, &[T]) or a ScalarPair
        // (e.g. Option<u8>).  ScalarPair returns are always two-register
        // (RAX + RDX), so the return handler needs a stack slot to load
        // both scalars from.
        {
            let ret_local = mir::Local::from_usize(0);
            let ret_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
            let ret_size = type_size(self.tcx, ret_ty).unwrap_or(0);
            let ret_repr = repr_kind(self.tcx, ret_ty);
            let needs_slot = (ret_size > 8
                && ret_size <= 16
                && !matches!(ret_repr, ReprKind::Scalar if ret_size <= 8))
                || (matches!(ret_repr, ReprKind::ScalarPair) && ret_size > 0 && ret_size <= 8);
            if needs_slot && !self.stack_locals.is_stack(ret_local) {
                let ret_align = type_align(self.tcx, ret_ty).unwrap_or(8) as u32;
                let slot = self
                    .builder
                    .stack_slot(ret_size as u32, ret_align, Origin::synthetic());
                self.locals.set(ret_local, slot);
                self.stack_locals.mark(ret_local);
            }
        }

        // Pre-scan: if any block has an unwind cleanup action, allocate an
        // exception-pointer stack slot in the entry block.  This must happen
        // before the main translation loop so that the slot is available when
        // cleanup terminators are processed.
        {
            use mir::UnwindAction;
            let has_cleanup = self.mir.basic_blocks.iter().any(|bb| {
                if let Some(ref term) = bb.terminator {
                    match &term.kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. } => {
                            matches!(unwind, UnwindAction::Cleanup(_))
                        }
                        _ => false,
                    }
                } else {
                    false
                }
            });
            if has_cleanup {
                let slot = self.builder.stack_slot(8, 0, Origin::synthetic());
                self.exc_ptr_slot = Some(slot);
            }
        }
    }

    /// Promote a projected place's base local to a stack slot.
    fn promote_projected_place(&mut self, place: &mir::Place<'tcx>) {
        if !place.projection.is_empty()
            // A leading Deref means we write *through* the local (e.g.
            // `(*_0).1 = ...`).  The local itself is a pointer — it must
            // NOT be turned into a stack slot; doing so would create a
            // fresh 8-byte slot while the pointer value is never stored.
            && !matches!(
                place.projection.first(),
                Some(mir::PlaceElem::Deref)
            )
            && !self.stack_locals.is_stack(place.local)
        {
            let local = place.local;
            let ty = self.monomorphize(self.mir.local_decls[local].ty);
            let size = type_size(self.tcx, ty).unwrap_or(0);
            if size > 0 {
                let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                self.promote_local_to_stack(local, size, align);
            }
        }
    }
}
