//! Floating-point SIMD operation helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers fused multiply-add SIMD intrinsics lane by lane.
    pub(crate) fn emit_simd_fma(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        simd_bytes: u32,
        elem_info: (u32, Option<FloatType>),
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let (elem_size, float_ty) = elem_info;
        let float_ty = float_ty.unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "simd_fma requires floating-point lanes in {:?}",
                self.instance
            ))
        });
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let c_ptr = self.ensure_simd_on_stack(ir_args[2], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;
        let load_ty = Type::Float(float_ty);
        let flags = FpRewriteFlags::default();

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
            let b_addr = if i == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let c_addr = if i == 0 {
                c_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(c_ptr.into(), off.into(), 0, o!()).raw()
            };
            let dst_addr = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            let a_val = self.builder.load(
                a_addr.into(),
                elem_size,
                load_ty.clone(),
                self.current_mem.into(),
                None,
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                elem_size,
                load_ty.clone(),
                self.current_mem.into(),
                None,
                o!(),
            );
            let c_val = self.builder.load(
                c_addr.into(),
                elem_size,
                load_ty.clone(),
                self.current_mem.into(),
                None,
                o!(),
            );
            let product =
                self.builder
                    .fmul(a_val.into(), b_val.into(), flags, load_ty.clone(), o!());
            let result =
                self.builder
                    .fadd(product.into(), c_val.into(), flags, load_ty.clone(), o!());
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

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Lowers unary float SIMD intrinsics by calling a scalar libcall per lane.
    pub(crate) fn emit_simd_float_unary_libcall(
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
        let float_ty = float_ty.unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "{op_name} requires floating-point lanes in {:?}",
                self.instance
            ))
        });
        let scalar_intrinsic = match (op_name, float_ty) {
            ("simd_ceil", FloatType::F32) => "ceilf32",
            ("simd_ceil", FloatType::F64) => "ceilf64",
            ("simd_floor", FloatType::F32) => "floorf32",
            ("simd_floor", FloatType::F64) => "floorf64",
            ("simd_round", FloatType::F32) => "roundf32",
            ("simd_round", FloatType::F64) => "roundf64",
            ("simd_round_ties_even", FloatType::F32) => "round_ties_even_f32",
            ("simd_round_ties_even", FloatType::F64) => "round_ties_even_f64",
            ("simd_trunc", FloatType::F32) => "truncf32",
            ("simd_trunc", FloatType::F64) => "truncf64",
            ("simd_fsqrt", FloatType::F32) => "sqrtf32",
            ("simd_fsqrt", FloatType::F64) => "sqrtf64",
            ("simd_fsin", FloatType::F32) => "sinf32",
            ("simd_fsin", FloatType::F64) => "sinf64",
            ("simd_fcos", FloatType::F32) => "cosf32",
            ("simd_fcos", FloatType::F64) => "cosf64",
            ("simd_fexp", FloatType::F32) => "expf32",
            ("simd_fexp", FloatType::F64) => "expf64",
            ("simd_fexp2", FloatType::F32) => "exp2f32",
            ("simd_fexp2", FloatType::F64) => "exp2f64",
            ("simd_flog10", FloatType::F32) => "log10f32",
            ("simd_flog10", FloatType::F64) => "log10f64",
            ("simd_flog2", FloatType::F32) => "log2f32",
            ("simd_flog2", FloatType::F64) => "log2f64",
            ("simd_flog", FloatType::F32) => "logf32",
            ("simd_flog", FloatType::F64) => "logf64",
            _ => self.tcx.dcx().fatal(format!(
                "unsupported {op_name} float type {float_ty:?} in {:?}",
                self.instance
            )),
        };
        let libc_sym = intrinsic_to_libc(scalar_intrinsic).unwrap_or_else(|| {
            self.tcx.dcx().fatal(format!(
                "missing libc mapping for {scalar_intrinsic} in {:?}",
                self.instance
            ))
        });
        let sym_id = self.symbols.intern(libc_sym);
        let callee = self.builder.symbol_addr(sym_id, o!());
        let src_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;
        let load_ty = Type::Float(float_ty);

        for i in 0..n_lanes {
            let byte_off = (i * elem_size) as i64;
            let src_addr = if i == 0 {
                src_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder
                    .ptradd(src_ptr.into(), off.into(), 0, o!())
                    .raw()
            };
            let dst_addr = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            let arg = self.builder.load(
                src_addr.into(),
                elem_size,
                load_ty.clone(),
                self.current_mem.into(),
                None,
                o!(),
            );
            let (call_mem, data) = self.builder.call(
                callee.into(),
                vec![arg.into()],
                load_ty.clone(),
                self.current_mem.into(),
                None,
                None,
                o!(),
            );
            let data = data.unwrap_or_else(|| {
                self.tcx.dcx().fatal(format!(
                    "{op_name} libcall returned no value in {:?}",
                    self.instance
                ))
            });
            self.current_mem = self
                .builder
                .store(
                    data.into(),
                    dst_addr.into(),
                    elem_size,
                    call_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }
}
