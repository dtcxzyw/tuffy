//! SIMD binary operation helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Emit a per-byte comparison of two SIMD vectors.
    pub(crate) fn emit_simd_cmp_byte(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op: ICmpOp,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let s8_int = IntAnnotation {
            bit_width: 8,
            signedness: IntSignedness::Signed,
        };
        let s8_opt = Some(Annotation::Int(s8_int));
        let s8_annotation = Annotation::Int(s8_int);
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());

        for i in 0..simd_bytes {
            let a_addr: ValueRef = if i == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if i == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_byte = self.builder.load(
                a_addr.into(),
                1,
                Type::Int,
                self.current_mem.into(),
                s8_opt.clone(),
                o!(),
            );
            let b_byte = self.builder.load(
                b_addr.into(),
                1,
                Type::Int,
                self.current_mem.into(),
                s8_opt.clone(),
                o!(),
            );
            let a_op = IntOperand::from(IrOperand::annotated(a_byte, s8_annotation.clone()));
            let b_op = IntOperand::from(IrOperand::annotated(b_byte, s8_annotation.clone()));
            let cmp = self.builder.icmp(op, a_op, b_op, o!());
            let ff = self.builder.iconst(-1i64, 8, IntSignedness::Signed, o!());
            let zero_byte = self.builder.iconst(0i64, 8, IntSignedness::Signed, o!());
            let res_byte = self.builder.select(
                cmp.into(),
                ff.raw().into(),
                zero_byte.raw().into(),
                Type::Int,
                s8_opt.clone(),
                o!(),
            );

            let dst_addr: ValueRef = if i == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(i as i64, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    res_byte.into(),
                    dst_addr.into(),
                    1,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit a qword-level bitwise operation on two SIMD vectors.
    pub(crate) fn emit_simd_binop_qword(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op: &str,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let u64_int = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let u64_opt = Some(Annotation::Int(u64_int));
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_words = simd_bytes.div_ceil(8);

        for half in 0..n_words {
            let offset_val = half as i64 * 8;
            let a_addr: ValueRef = if half == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if half == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_val = self.builder.load(
                a_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt.clone(),
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt.clone(),
                o!(),
            );

            let result = match op {
                "simd_or" => self.builder.or(a_val.into(), b_val.into(), u64_int, o!()),
                "simd_and" => self.builder.and(a_val.into(), b_val.into(), u64_int, o!()),
                "simd_xor" => self.builder.xor(a_val.into(), b_val.into(), u64_int, o!()),
                _ => unreachable!(),
            };

            let dst_addr: ValueRef = if half == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    result.raw().into(),
                    dst_addr.into(),
                    8,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit per-byte addition of two SIMD vectors using SWAR trick.
    pub(crate) fn emit_simd_add(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        simd_bytes: u32,
    ) {
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let u64_int = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let u64_opt = Some(Annotation::Int(u64_int));
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }

        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_words = simd_bytes.div_ceil(8);
        let mask_7f = self.builder.iconst(
            0x7F7F_7F7F_7F7F_7F7Fu64 as i64,
            64,
            IntSignedness::Unsigned,
            o!(),
        );
        let mask_80 = self.builder.iconst(
            0x8080_8080_8080_8080u64 as i64,
            64,
            IntSignedness::Unsigned,
            o!(),
        );

        for w in 0..n_words {
            let offset_val = w as i64 * 8;
            let a_addr: ValueRef = if w == 0 {
                a_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(a_ptr.into(), off.into(), 0, o!()).raw()
            };
            let b_addr: ValueRef = if w == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
            };
            let a_val = self.builder.load(
                a_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt.clone(),
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt.clone(),
                o!(),
            );
            let a_lo = self
                .builder
                .and(a_val.into(), mask_7f.into(), u64_int, o!());
            let b_lo = self
                .builder
                .and(b_val.into(), mask_7f.into(), u64_int, o!());
            let sum_lo = self.builder.add(a_lo.into(), b_lo.into(), u64_int, o!());
            let axb = self.builder.xor(a_val.into(), b_val.into(), u64_int, o!());
            let carry = self.builder.and(axb.into(), mask_80.into(), u64_int, o!());
            let result = self.builder.xor(sum_lo.into(), carry.into(), u64_int, o!());

            let dst_addr: ValueRef = if w == 0 {
                slot
            } else {
                let off = self
                    .builder
                    .iconst(offset_val, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(slot.into(), off.into(), 0, o!()).raw()
            };
            self.current_mem = self
                .builder
                .store(
                    result.raw().into(),
                    dst_addr.into(),
                    8,
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
        }

        let result = self.simd_result_from_stack(slot, simd_bytes);
        self.locals.set(destination_local, result);
    }

    /// Emit a per-element binary operation (mul, sub, div) on two SIMD vectors.
    pub(crate) fn emit_simd_elementwise_binop(
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
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
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
            let b_addr = if i == 0 {
                b_ptr
            } else {
                let off = self
                    .builder
                    .iconst(byte_off, 64, IntSignedness::Unsigned, o!());
                self.builder.ptradd(b_ptr.into(), off.into(), 0, o!()).raw()
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
                let b_val = self.builder.load(
                    b_addr.into(),
                    elem_size,
                    load_ty.clone(),
                    self.current_mem.into(),
                    None,
                    o!(),
                );
                let flags = FpRewriteFlags::default();
                let result = match op_name {
                    "simd_mul" => {
                        self.builder
                            .fmul(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    "simd_sub" => {
                        self.builder
                            .fsub(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    "simd_div" => {
                        self.builder
                            .fdiv(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                    _ => {
                        self.builder
                            .fmul(a_val.into(), b_val.into(), flags, load_ty.clone(), o!())
                    }
                };
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
            } else {
                let int_ann = IntAnnotation {
                    bit_width: elem_size * 8,
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
                let b_val = self.builder.load(
                    b_addr.into(),
                    elem_size,
                    Type::Int,
                    self.current_mem.into(),
                    ann_opt.clone(),
                    o!(),
                );
                let result = match op_name {
                    "simd_mul" => self.builder.mul(a_val.into(), b_val.into(), int_ann, o!()),
                    "simd_sub" => self.builder.sub(a_val.into(), b_val.into(), int_ann, o!()),
                    _ => self.builder.mul(a_val.into(), b_val.into(), int_ann, o!()),
                };
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

    /// Lowers SIMD lane-wise shift intrinsics.
    pub(crate) fn emit_simd_shift(
        &mut self,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
        op_name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        simd_bytes: u32,
    ) {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        let elem_ann = self
            .simd_elem_int_ann_from_substs(substs)
            .unwrap_or_else(|| {
                self.tcx.dcx().fatal(format!(
                    "{op_name} requires an integer SIMD element type in {:?}",
                    self.instance
                ))
            });
        let elem_size = elem_ann.bit_width / 8;
        let a_ptr = self.ensure_simd_on_stack(ir_args[0], simd_bytes);
        let b_ptr = self.ensure_simd_on_stack(ir_args[1], simd_bytes);
        let slot = self.builder.stack_slot(simd_bytes.max(8), 0, o!());
        let n_lanes = simd_bytes / elem_size;
        let lane_ann = Some(Annotation::Int(elem_ann));

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
                Type::Int,
                self.current_mem.into(),
                lane_ann.clone(),
                o!(),
            );
            let b_val = self.builder.load(
                b_addr.into(),
                elem_size,
                Type::Int,
                self.current_mem.into(),
                lane_ann.clone(),
                o!(),
            );
            let a_op = IntOperand::from(IrOperand::annotated(a_val, Annotation::Int(elem_ann)));
            let b_op = IntOperand::from(IrOperand::annotated(b_val, Annotation::Int(elem_ann)));
            let result = match op_name {
                "simd_shl" => self.builder.shl(a_op, b_op, elem_ann, o!()),
                "simd_shr" => self.builder.shr(a_op, b_op, elem_ann, o!()),
                _ => unreachable!(),
            };
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
}
