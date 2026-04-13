//! Unary SIMD operation helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Emit a per-element unary operation (neg, fabs) on a SIMD vector.
    pub(crate) fn emit_simd_unary_op(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op_name: &str,
        simd_bytes: u32,
        elem_info: (u32, Option<FloatType>),
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let (elem_size, float_ty) = elem_info;
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;

        for i in 0..n_lanes {
            let byte_off = (i * elem_size) as i64;
            let a_addr = if i == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let dst_addr = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };

            if let Some(fty) = float_ty {
                let load_ty = Type::Float(fty);
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    load_ty.clone(),
                    self.current_mem.into(),
                    None,
                    o!(),
                );
                let result = match op_name {
                    "simd_neg" => self.builder.fneg(a_val.into(), load_ty.clone(), o!()).raw(),
                    "simd_fabs" => {
                        let int_ann = IntAnnotation {
                            bit_width: (elem_size * 8),
                            signedness: IntSignedness::Unsigned,
                        };
                        let mask = match elem_size {
                            4 => 0x7FFF_FFFFi64,
                            8 => 0x7FFF_FFFF_FFFF_FFFFi64,
                            2 => 0x7FFFi64,
                            _ => 0x7FFF_FFFFi64,
                        };
                        let mask_val =
                            self.builder
                                .iconst(mask, elem_size * 8, IntSignedness::Unsigned, o!());
                        let as_int = self.builder.bitcast(
                            a_val.into(),
                            Type::Int,
                            Some(Annotation::Int(int_ann)),
                            o!(),
                        );
                        let cleared =
                            self.builder
                                .and(as_int.into(), mask_val.into(), int_ann, o!());
                        self.builder
                            .bitcast(cleared.raw().into(), load_ty.clone(), None, o!())
                    }
                    _ => self.builder.fneg(a_val.into(), load_ty.clone(), o!()).raw(),
                };
                self.current_mem = self
                    .builder
                    .store(
                        result.into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            } else {
                let int_ann = IntAnnotation {
                    bit_width: (elem_size * 8),
                    signedness: IntSignedness::DontCare,
                };
                let ann_opt = Some(Annotation::Int(int_ann));
                let a_val = self.builder.load(
                    a_addr.into(),
                    elem_size,
                    Type::Int,
                    self.current_mem.into(),
                    ann_opt.clone(),
                    o!(),
                );
                let zero = self
                    .builder
                    .iconst(0, elem_size * 8, IntSignedness::DontCare, o!());
                let result = self.builder.sub(zero.into(), a_val.into(), int_ann, o!());
                self.current_mem = self
                    .builder
                    .store(
                        result.raw().into(),
                        dst_addr.into(),
                        elem_size,
                        self.current_mem.into(),
                        o!(),
                    )
                    .raw();
            }
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }
}
