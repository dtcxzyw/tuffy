use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers MIR `SwitchInt` into chained integer comparisons and branches.
    pub(super) fn translate_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
    ) {
        // Get the discriminant type's byte size so we can truncate switch
        // target values to the correct bit width.  MIR stores switch values
        // as u128, but the runtime discriminant is stored in a sized slot
        // (e.g. 32-bit for i32) and zero-extended on load.
        // Use projected type so that e.g. `_x.1` where `_x: (u64, u128)`
        // yields `u128` rather than the whole tuple type.
        let discr_ty =
            operand_ty_projected(discr, self.mir, self.tcx).map(|t| self.monomorphize(t));
        let discr_bits = discr_ty
            .and_then(|t| type_size(self.tcx, t))
            .map(|sz| sz * 8)
            .unwrap_or(64);

        // Basic blocks are translated in reverse post-order and mutated locals
        // are stack-promoted before block translation, so a SwitchInt operand
        // should always have a materialized runtime value by the time we lower
        // the terminator.
        let mut discr_val = self
            .translate_operand(discr)
            .expect("SwitchInt discriminant should be available before lowering");

        // If the discriminant is a pointer, it may be:
        // (a) an integer type > 8 bytes whose address was returned by
        //     translate_place_to_value — load the actual integer value, or
        // (b) a nullable-pointer-optimised discriminant — convert to integer.
        // Bool discriminants need BoolToInt for icmp.
        if matches!(self.builder.value_type(discr_val), Some(Type::Ptr(_))) {
            let is_integer_discr = discr_ty.is_some_and(|t| t.is_integral());
            if is_integer_discr {
                let byte_size = discr_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(8) as u32;
                discr_val = self.builder.load(
                    discr_val.into(),
                    byte_size,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(byte_size),
                    Origin::synthetic(),
                );
            } else {
                discr_val = self
                    .builder
                    .ptrtoaddr(discr_val.into(), 64, Origin::synthetic())
                    .raw();
            }
        } else if matches!(self.builder.value_type(discr_val), Some(Type::Bool)) {
            let one = self
                .builder
                .iconst(1, 64, IntSignedness::Unsigned, Origin::synthetic());
            let zero = self
                .builder
                .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic());
            discr_val = self.builder.select(
                discr_val.into(),
                one.into(),
                zero.into(),
                Type::Int,
                Some(Annotation::Int(IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                })),
                Origin::synthetic(),
            );
        }

        // Mask the discriminant to its type's bit width so that a sign-extended
        // 64-bit register value matches the zero-extended switch target constants.
        if discr_bits < 64 {
            let mask_val = self.builder.iconst(
                (1i64 << discr_bits) - 1,
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            discr_val = self
                .builder
                .and(discr_val.into(), mask_val.into(), I64, Origin::synthetic())
                .raw();
        }

        let all_targets: Vec<_> = targets.iter().collect();
        let otherwise = targets.otherwise();

        if all_targets.is_empty() {
            // No explicit value-target pairs — unconditionally jump to otherwise.
            // This happens for single-variant enums where the discriminant check
            // is optimised away.
            let otherwise_block = self.block_map.get(otherwise);
            self.builder.br(
                otherwise_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else if all_targets.len() == 1 {
            // Two-way branch: compare discriminant with the single value.
            let (test_val, target_bb) = all_targets[0];
            // Truncate u128 switch value to discriminant bit width so it
            // matches the zero-extended runtime value loaded from a sized slot.
            let truncated = if discr_bits < 128 {
                test_val & ((1u128 << discr_bits) - 1)
            } else {
                test_val
            };
            let const_val = self.builder.iconst(
                BigInt::from(truncated),
                (discr_bits as u32).min(128),
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            let cmp = self.builder.icmp(
                ICmpOp::Eq,
                discr_val.into(),
                const_val.into(),
                Origin::synthetic(),
            );
            let then_block = self.block_map.get(target_bb);
            let else_block = self.block_map.get(otherwise);
            self.builder.brif(
                cmp.into(),
                then_block,
                vec![self.current_mem.into()],
                else_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else {
            // Multi-way: chain of brif comparisons with fallthrough blocks.
            let otherwise_block = self.block_map.get(otherwise);
            for (i, (test_val, target_bb)) in all_targets.iter().enumerate() {
                let truncated = if discr_bits < 128 {
                    *test_val & ((1u128 << discr_bits) - 1)
                } else {
                    *test_val
                };
                let const_val = self.builder.iconst(
                    BigInt::from(truncated),
                    (discr_bits as u32).min(128),
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let cmp = self.builder.icmp(
                    ICmpOp::Eq,
                    discr_val.into(),
                    const_val.into(),
                    Origin::synthetic(),
                );
                let then_block = self.block_map.get(*target_bb);

                if i == all_targets.len() - 1 {
                    // Last comparison: else goes to otherwise.
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        otherwise_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                } else {
                    // Not last: else falls through to a new comparison block.
                    let next_block = self.builder.create_block();
                    let next_mem = self.builder.add_block_arg(next_block, Type::Mem, None);
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        next_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                    self.builder.switch_to_block(next_block);
                    self.current_mem = next_mem;
                }
            }
        }
    }
}
