use rustc_middle::mir::{self, Operand};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::constant::translate_const;
use super::ctx::TranslationCtx;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Returns true when `op` is a `Constant` whose resolved value is
    /// `ConstValue::Indirect` and whose type is NOT a reference/pointer.
    ///
    /// In `translate_const`, `Indirect` non-ref constants produce a
    /// `symbol_addr` pointing to the constant data rather than the data
    /// itself.  Callers that need the *value* (like the Aggregate handler)
    /// must load from this address first.
    pub(super) fn is_indirect_nonref_const(&self, op: &Operand<'tcx>) -> bool {
        let Operand::Constant(c) = op else {
            return false;
        };
        let mono_const = self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(c.const_),
        );
        let const_ty = mono_const.ty();
        if matches!(
            const_ty.kind(),
            ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..)
        ) {
            return false;
        }
        let resolved = match mono_const {
            mir::Const::Val(v, _) => Some(v),
            _ => {
                let typing_env = ty::TypingEnv::fully_monomorphized();
                mono_const.eval(self.tcx, typing_env, c.span).ok()
            }
        };
        matches!(resolved, Some(mir::ConstValue::Indirect { .. }))
    }

    /// Lowers a MIR operand into the IR value currently representing it.
    pub(super) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    let val = self
                        .locals
                        .get(place.local)
                        .or_else(|| self.materialize_split_pair_local(place.local));
                    // For scalar locals promoted to stack slots (multi-BB
                    // mutation), load the current value from the slot.
                    if self.stack_locals.is_stack(place.local)
                        && let Some(slot) = val
                    {
                        let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(8) as u32;
                        let slot_size = self.builder.stack_slot_size(slot);
                        let is_slot_ptr =
                            matches!(self.builder.value_type(slot), Some(Type::Ptr(_)));
                        if is_slot_ptr
                            && let Some((load_ty, load_bytes, ann)) =
                                scalar_value_info(self.tcx, ty)
                            && slot_size.is_some_and(|sz| sz >= load_bytes)
                        {
                            let loaded = self.builder.load(
                                slot.into(),
                                load_bytes,
                                load_ty,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                        if is_slot_ptr
                            && size > 0
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= size)
                            && translate_ty(self.tcx, ty).is_none()
                        {
                            let loaded = self.builder.load(
                                slot.into(),
                                size,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(size),
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                    }
                    // Non-stack local holding a memory address (e.g. symbol_addr
                    // for an indirect constant like `const S: Point = ...`).
                    // For Int-typed locals stored at a memory address (symbol or
                    // PtrAdd), load the actual value instead of returning the
                    // raw pointer.  This covers both small scalars (≤8 bytes)
                    // and large integers such as i128/u128 (16 bytes).
                    if !self.stack_locals.is_stack(place.local)
                        && let Some(v) = val
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                        && self.builder.is_memory_address(v)
                    {
                        let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        if let Some((load_ty, load_bytes, ann)) = scalar_value_info(self.tcx, ty)
                            && !matches!(load_ty, Type::Ptr(_))
                        {
                            let loaded = self.builder.load(
                                v.into(),
                                load_bytes,
                                load_ty,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                    }
                    val
                } else {
                    self.translate_place_to_value(place)
                }
            }
            Operand::Constant(constant) => translate_const(
                self.tcx,
                self.instance,
                constant,
                &mut self.builder,
                &mut self.symbols,
                &mut self.static_data,
                &mut self.current_mem,
                &mut self.referenced_instances,
                self.data_counter,
                &mut self.weak_undefined_symbols,
                self.vtable_cache,
                self.alloc_cache,
                self.content_cache,
            ),
            Operand::RuntimeChecks(_) => {
                // UbChecks / ContractChecks / OverflowChecks: emit false (0)
                // to skip runtime checks, matching release-mode behaviour.
                Some(
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw(),
                )
            }
        }
    }
}
