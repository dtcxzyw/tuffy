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
                        let size = type_size(self.tcx, ty).unwrap_or(8);
                        let slot_size = self.builder.stack_slot_size(slot);
                        let ir_ty = translate_ty(self.tcx, ty);
                        let is_slot_ptr =
                            matches!(self.builder.value_type(slot), Some(Type::Ptr(_)));
                        let should_load_stack_int = matches!(ir_ty, Some(Type::Int))
                            && is_slot_ptr
                            && ((size <= 8 && slot_size.is_some_and(|sz| sz <= 8))
                                || (size > 8
                                    && ty.is_integral()
                                    && slot_size.is_some_and(|sz| u64::from(sz) >= size)));
                        let should_load_stack_ptr = matches!(ir_ty, Some(Type::Ptr(_)))
                            && is_slot_ptr
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= 8);
                        let should_load_stack_scalar = is_slot_ptr
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= 8)
                            && matches!(ir_ty, Some(Type::Bool | Type::Float(_)));
                        // Small aggregate types (closures, tuples, ADTs) where
                        // translate_ty returns None but the value fits in a
                        // register.  Without this, the stack slot address is
                        // returned instead of the contained value.
                        let should_load_stack_aggregate = ir_ty.is_none()
                            && is_slot_ptr
                            && size > 0
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= 8);
                        if should_load_stack_int
                            || should_load_stack_ptr
                            || should_load_stack_scalar
                            || should_load_stack_aggregate
                        {
                            let load_ty = if should_load_stack_ptr {
                                Type::Ptr(0)
                            } else {
                                ir_ty.unwrap_or(Type::Int)
                            };
                            let ann = translate_annotation(ty).or_else(|| {
                                // Aggregate types have no annotation from
                                // translate_annotation.  When we load them as
                                // Type::Int, supply a width annotation to
                                // satisfy the IR verifier.
                                if should_load_stack_aggregate {
                                    int_annotation_for_bytes(size as u32)
                                } else {
                                    None
                                }
                            });
                            let loaded = self.builder.load(
                                slot.into(),
                                size as u32,
                                load_ty,
                                self.current_mem.into(),
                                ann,
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
                        let size = type_size(self.tcx, ty).unwrap_or(8);
                        if matches!(translate_ty(self.tcx, ty), Some(Type::Int))
                            && (size <= 8 || ty.is_integral())
                        {
                            let ann = translate_annotation(ty);
                            let loaded = self.builder.load(
                                v.into(),
                                size as u32,
                                Type::Int,
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
