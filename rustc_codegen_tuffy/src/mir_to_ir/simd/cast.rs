//! SIMD cast helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers SIMD cast intrinsics between integer and floating-point lane types.
    pub(crate) fn emit_simd_cast(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let src_ty = substs.first().and_then(|a| a.as_type()).unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "simd_cast missing source type in {:?}",
                self.instance
            ))
        });
        let dst_ty = substs.get(1).and_then(|a| a.as_type()).unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "simd_cast missing destination type in {:?}",
                self.instance
            ))
        });
        let src_info = self.simd_cast_info(src_ty).unwrap_or_else(|| {
            self.tcx
                .dcx()
                .fatal(format!("unsupported simd_cast source type {src_ty:?}"))
        });
        let dst_info = self.simd_cast_info(dst_ty).unwrap_or_else(|| {
            self.tcx
                .dcx()
                .fatal(format!("unsupported simd_cast destination type {dst_ty:?}"))
        });
        if src_info.lanes != dst_info.lanes {
            self.tcx.dcx().fatal(format!(
                "simd_cast requires equal lane counts, got {} and {} in {:?}",
                src_info.lanes, dst_info.lanes, self.instance
            ));
        }

        let src_bytes = type_size(self.tcx, src_ty).unwrap_or(16) as u32;
        let dst_bytes = type_size(self.tcx, dst_ty).unwrap_or(16) as u32;
        let src_ptr = self.ensure_simd_on_stack(ir_args[0], src_bytes);
        let dst_slot = self.builder.stack_slot(dst_bytes.max(8), 0, o!());
        let trunc_slot =
            self.builder
                .stack_slot(src_info.elem_size.max(dst_info.elem_size), 0, o!());

        for i in 0..src_info.lanes {
            let src_byte_off = (i * src_info.elem_size) as i64;
            let dst_byte_off = (i * dst_info.elem_size) as i64;
            let src_addr = if i == 0 {
                src_ptr
            } else {
                let off = self
                    .builder
                    .iconst(src_byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder
                    .ptradd(src_ptr.into(), off.into(), 0, o!())
                    .raw()
            };
            let dst_addr = if i == 0 {
                dst_slot
            } else {
                let off = self
                    .builder
                    .iconst(dst_byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder
                    .ptradd(dst_slot.into(), off.into(), 0, o!())
                    .raw()
            };

            let cast_result = match (
                src_info.int_ann,
                src_info.float_ty,
                dst_info.int_ann,
                dst_info.float_ty,
            ) {
                (Some(src_int), None, Some(dst_int), None) => {
                    let src_val = self.builder.load(
                        src_addr.into(),
                        src_info.elem_size,
                        Type::Int,
                        self.current_mem.into(),
                        Some(Annotation::Int(src_int)),
                        o!(),
                    );
                    if dst_int.bit_width > src_int.bit_width {
                        if matches!(src_int.signedness, IntSignedness::Signed) {
                            self.builder
                                .sext(src_val.into(), dst_int.bit_width, o!())
                                .raw()
                        } else {
                            self.builder
                                .zext(src_val.into(), dst_int.bit_width, o!())
                                .raw()
                        }
                    } else if dst_int.bit_width < src_int.bit_width {
                        self.current_mem = self
                            .builder
                            .store(
                                src_val.into(),
                                trunc_slot.into(),
                                src_info.elem_size,
                                self.current_mem.into(),
                                o!(),
                            )
                            .raw();
                        self.builder.load(
                            trunc_slot.into(),
                            dst_info.elem_size,
                            Type::Int,
                            self.current_mem.into(),
                            Some(Annotation::Int(dst_int)),
                            o!(),
                        )
                    } else {
                        src_val
                    }
                }
                (Some(src_int), None, None, Some(dst_float)) => {
                    let src_val = self.builder.load(
                        src_addr.into(),
                        src_info.elem_size,
                        Type::Int,
                        self.current_mem.into(),
                        Some(Annotation::Int(src_int)),
                        o!(),
                    );
                    if matches!(src_int.signedness, IntSignedness::Signed) {
                        self.builder.si_to_fp(src_val.into(), dst_float, o!()).raw()
                    } else {
                        self.builder.ui_to_fp(src_val.into(), dst_float, o!()).raw()
                    }
                }
                (None, Some(src_float), Some(dst_int), None) => {
                    let src_val = self.builder.load(
                        src_addr.into(),
                        src_info.elem_size,
                        Type::Float(src_float),
                        self.current_mem.into(),
                        None,
                        o!(),
                    );
                    if matches!(dst_int.signedness, IntSignedness::Signed) {
                        self.builder
                            .fp_to_si(src_val.into(), dst_int.bit_width, o!())
                            .raw()
                    } else {
                        self.builder
                            .fp_to_ui(src_val.into(), dst_int.bit_width, o!())
                            .raw()
                    }
                }
                (None, Some(src_float), None, Some(dst_float)) => {
                    let src_val = self.builder.load(
                        src_addr.into(),
                        src_info.elem_size,
                        Type::Float(src_float),
                        self.current_mem.into(),
                        None,
                        o!(),
                    );
                    if src_float == dst_float {
                        src_val
                    } else {
                        self.builder
                            .fp_convert(src_val.into(), dst_float, o!())
                            .raw()
                    }
                }
                _ => self.tcx.dcx().fatal(format!(
                    "unsupported simd_cast element conversion in {:?}",
                    self.instance
                )),
            };

            self.current_mem = self
                .builder
                .store(
                    cast_result.into(),
                    dst_addr.into(),
                    dst_info.elem_size,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(dst_slot, dst_bytes);
        self.locals.set(destination_local, result);
    }
}
