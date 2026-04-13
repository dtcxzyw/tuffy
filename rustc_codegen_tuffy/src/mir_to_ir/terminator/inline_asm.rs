use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Handles recognized `InlineAsm` patterns without emitting raw assembly.
    pub(super) fn translate_inline_asm(
        &mut self,
        template: &[rustc_ast::InlineAsmTemplatePiece],
        operands: &[InlineAsmOperand<'tcx>],
        targets: &[mir::BasicBlock],
    ) {
        // Concatenate template strings for pattern matching.
        let template_str: String = template
            .iter()
            .filter_map(|piece| match piece {
                rustc_ast::InlineAsmTemplatePiece::String(s) => Some(s.as_ref()),
                _ => None,
            })
            .collect();

        // Collect In values and Out places by operand index.
        let mut in_vals: Vec<ValueRef> = Vec::new();
        let mut out_places: Vec<Option<&mir::Place<'tcx>>> = Vec::new();
        let mut inout_pairs: Vec<(ValueRef, Option<&mir::Place<'tcx>>)> = Vec::new();

        for op in operands {
            match op {
                InlineAsmOperand::In { value, .. } => {
                    if let Some(v) = self.translate_operand(value) {
                        in_vals.push(v);
                    }
                }
                InlineAsmOperand::Out { place, .. } => {
                    out_places.push(place.as_ref());
                }
                InlineAsmOperand::InOut {
                    in_value,
                    out_place,
                    ..
                } => {
                    let v = self.translate_operand(in_value);
                    if let Some(v) = v {
                        inout_pairs.push((v, out_place.as_ref()));
                    }
                }
                // Const, SymFn, SymStatic, Label — not relevant here.
                _ => {}
            }
        }

        // Pattern: select_unpredictable — "test" + "cmovnz" + "cmovz"
        // Operands: In(cond), In(true_val), In(false_val), Out(result)
        let is_select = (template_str.contains("cmovnz") || template_str.contains("cmovne"))
            && (template_str.contains("cmovz") || template_str.contains("cmove"))
            && in_vals.len() >= 3
            && !out_places.is_empty();

        if is_select {
            let cond = in_vals[0];
            let true_val = in_vals[1];
            let false_val = in_vals[2];

            // cond is a byte — compare != 0 to get a Bool.
            let cond_int = self.coerce_to_int(cond);
            let zero = self
                .builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
            let cond_bool = self.builder.icmp(
                ICmpOp::Ne,
                cond_int.into(),
                zero.into(),
                Origin::synthetic(),
            );

            // select(cond, true_val, false_val)
            let result_ty = self
                .builder
                .value_type(true_val)
                .cloned()
                .unwrap_or(Type::Ptr(0));
            let result = self.builder.select(
                cond_bool.into(),
                true_val.into(),
                false_val.into(),
                result_ty.clone(),
                None,
                Origin::synthetic(),
            );

            // Store result to each Out place.
            for place in out_places.iter().flatten() {
                self.store_val_to_place(result, place, &result_ty);
            }
        } else {
            // Handle InOut operands: copy input to output.
            for (in_val, out_place) in &inout_pairs {
                if let Some(place) = out_place {
                    let ty = self
                        .builder
                        .value_type(*in_val)
                        .cloned()
                        .unwrap_or(Type::Int);
                    self.store_val_to_place(*in_val, place, &ty);
                }
            }

            // For unrecognised Out-only operands, store zero to prevent UB.
            for place in out_places.iter().flatten() {
                let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
                let _sz = type_size(self.tcx, place_ty).unwrap_or(8);
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                self.store_val_to_place(zero.raw(), place, &Type::Int);
            }
        }

        // Branch to the normal destination (first target).
        if let Some(&target) = targets.first() {
            let target_block = self.block_map.get(target);
            self.builder.br(
                target_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else {
            self.builder.trap(Origin::synthetic());
        }
    }

    /// Store an IR value to a MIR place (handles both register and stack locals).
    fn store_val_to_place(&mut self, val: ValueRef, place: &mir::Place<'tcx>, _ir_ty: &Type) {
        if place.projection.is_empty() {
            // Simple local — either set the register or store to the stack slot.
            if self.stack_locals.is_stack(place.local) {
                if let Some(slot) = self.locals.get(place.local) {
                    let place_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                    let bytes = type_size(self.tcx, place_ty).unwrap_or(8) as u32;
                    if bytes > 0 {
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                bytes.min(8),
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }
            } else {
                self.locals.set(place.local, val);
            }
        } else if let Some((addr, projected_ty)) = self.translate_place_to_addr(place) {
            let addr = self.coerce_to_ptr(addr);
            let dest_ty = self.monomorphize(projected_ty);
            let bytes = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
            if bytes > 0 {
                self.current_mem = self
                    .builder
                    .store(
                        val.into(),
                        addr.into(),
                        bytes.min(8),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
        }
    }
}
