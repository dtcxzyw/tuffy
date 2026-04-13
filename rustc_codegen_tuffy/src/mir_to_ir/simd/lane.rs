//! SIMD lane extraction and insertion helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers `simd_extract` by loading the requested lane from the source vector.
    pub(crate) fn emit_simd_extract(
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
        let vec_ty = substs.first().and_then(|a| a.as_type()).unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "simd_extract missing vector type in {:?}",
                self.instance
            ))
        });
        let vec_info = self.simd_cast_info(vec_ty).unwrap_or_else(|| {
            self.tcx
                .dcx()
                .fatal(format!("unsupported simd_extract vector type {vec_ty:?}"))
        });
        let vec_bytes = type_size(self.tcx, vec_ty).unwrap_or(16) as u32;
        let vec_ptr = self.ensure_simd_on_stack(ir_args[0], vec_bytes);
        let idx = self.coerce_to_int(ir_args[1]);
        let byte_off = if vec_info.elem_size == 1 {
            idx
        } else {
            let elem_size =
                self.builder
                    .iconst(vec_info.elem_size as i64, 64, IntSignedness::Unsigned, o!());
            self.builder
                .mul(idx.into(), elem_size.into(), int_ann_for_bytes(8), o!())
                .raw()
        };
        let elem_addr = self
            .builder
            .ptradd(vec_ptr.into(), byte_off.into(), 0, o!())
            .raw();
        let result = match (vec_info.int_ann, vec_info.float_ty) {
            (Some(int_ann), None) => self.builder.load(
                elem_addr.into(),
                vec_info.elem_size,
                Type::Int,
                self.current_mem.into(),
                Some(Annotation::Int(int_ann)),
                o!(),
            ),
            (None, Some(float_ty)) => self.builder.load(
                elem_addr.into(),
                vec_info.elem_size,
                Type::Float(float_ty),
                self.current_mem.into(),
                None,
                o!(),
            ),
            _ => self.tcx.dcx().fatal(format!(
                "unsupported simd_extract element type in {:?}",
                self.instance
            )),
        };
        self.locals.set(destination_local, result);
    }

    /// Lowers `simd_insert` by writing one lane into a copied vector slot.
    pub(crate) fn emit_simd_insert(
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
        let vec_ty = substs.first().and_then(|a| a.as_type()).unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "simd_insert missing vector type in {:?}",
                self.instance
            ))
        });
        let vec_info = self.simd_cast_info(vec_ty).unwrap_or_else(|| {
            self.tcx
                .dcx()
                .fatal(format!("unsupported simd_insert vector type {vec_ty:?}"))
        });
        let vec_bytes = type_size(self.tcx, vec_ty).unwrap_or(16) as u32;
        let vec_ptr = self.ensure_simd_on_stack(ir_args[0], vec_bytes);
        let idx = self.coerce_to_int(ir_args[1]);
        let value = ir_args[2];
        let slot = self.builder.stack_slot(vec_bytes.max(8), 0, o!());

        for w in 0..vec_bytes.div_ceil(8) {
            let chunk = (vec_bytes - w * 8).min(8);
            let byte_off = (w * 8) as i64;
            let src_addr = if w == 0 {
                vec_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder
                    .ptradd(vec_ptr.into(), off.into(), 0, o!())
                    .raw()
            };
            let dst_addr = if w == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            let word = self.builder.load(
                src_addr.into(),
                chunk,
                Type::Int,
                self.current_mem.into(),
                int_annotation_for_bytes(chunk),
                o!(),
            );
            self.current_mem = self
                .builder
                .store(
                    word.into(),
                    dst_addr.into(),
                    chunk,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let byte_off = if vec_info.elem_size == 1 {
            idx
        } else {
            let elem_size =
                self.builder
                    .iconst(vec_info.elem_size as i64, 64, IntSignedness::Unsigned, o!());
            self.builder
                .mul(idx.into(), elem_size.into(), int_ann_for_bytes(8), o!())
                .raw()
        };
        let elem_addr = self
            .builder
            .ptradd(slot.into(), byte_off.into(), 0, o!())
            .raw();
        self.current_mem = self
            .builder
            .store(
                value.into(),
                elem_addr.into(),
                vec_info.elem_size,
                self.current_mem.into(),
                o!(),
            )
            .raw();

        let result = self.simd_result_from_stack(slot, vec_bytes);
        self.locals.set(destination_local, result);
    }
}
