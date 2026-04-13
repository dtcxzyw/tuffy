//! Floating-point intrinsic helpers for MIR to IR lowering.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers floating-point arithmetic intrinsics and their libcall fallbacks.
    pub(crate) fn translate_float_intrinsic(
        &mut self,
        name: &str,
        _substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<bool> {
        Some(match name {
            "fadd_algebraic" | "fsub_algebraic" | "fmul_algebraic" | "fdiv_algebraic"
            | "frem_algebraic" | "fadd_fast" | "fsub_fast" | "fmul_fast" | "fdiv_fast"
            | "frem_fast" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let flags = FpRewriteFlags {
                    reassoc: true,
                    contract: true,
                };
                let o = Origin::synthetic();
                let result = match name {
                    "fadd_algebraic" | "fadd_fast" => {
                        self.builder.fadd(a.into(), b.into(), flags, ty, o)
                    }
                    "fsub_algebraic" | "fsub_fast" => {
                        self.builder.fsub(a.into(), b.into(), flags, ty, o)
                    }
                    "fmul_algebraic" | "fmul_fast" => {
                        self.builder.fmul(a.into(), b.into(), flags, ty, o)
                    }
                    "fdiv_algebraic" | "fdiv_fast" => {
                        self.builder.fdiv(a.into(), b.into(), flags, ty, o)
                    }
                    "frem_algebraic" | "frem_fast" => {
                        self.builder.frem(a.into(), b.into(), flags, ty, o)
                    }
                    _ => unreachable!(),
                };
                self.locals.set(destination_local, result.raw());
                true
            }
            "minimumf32" | "minimumf64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let o = || Origin::synthetic();
                let int_bits = match &ty {
                    Type::Float(FloatType::F32) => 32u32,
                    _ => 64u32,
                };
                let iann = IntAnnotation {
                    bit_width: int_bits,
                    signedness: IntSignedness::Unsigned,
                };
                let int_ann = Some(Annotation::Int(iann));
                let fp_flags = tuffy_ir::types::FpRewriteFlags {
                    reassoc: false,
                    contract: false,
                };
                let a_nan = self.builder.fcmp(FCmpOp::Uno, a.into(), a.into(), o());
                let b_nan = self.builder.fcmp(FCmpOp::Uno, b.into(), b.into(), o());
                let either_nan = self.builder.bor(a_nan.into(), b_nan.into(), o());
                let nan_val = self
                    .builder
                    .fadd(a.into(), b.into(), fp_flags, ty.clone(), o());
                let a_lt = self.builder.fcmp(FCmpOp::OLt, a.into(), b.into(), o());
                let a_gt = self.builder.fcmp(FCmpOp::OGt, a.into(), b.into(), o());
                let a_bits = self
                    .builder
                    .bitcast(a.into(), Type::Int, int_ann.clone(), o());
                let b_bits = self
                    .builder
                    .bitcast(b.into(), Type::Int, int_ann.clone(), o());
                let or_bits = self.builder.or(a_bits.into(), b_bits.into(), iann, o());
                let tie = self
                    .builder
                    .bitcast(or_bits.raw().into(), ty.clone(), None, o());
                let r1 =
                    self.builder
                        .select(a_gt.into(), b.into(), tie.into(), ty.clone(), None, o());
                let r2 =
                    self.builder
                        .select(a_lt.into(), a.into(), r1.into(), ty.clone(), None, o());
                let result = self.builder.select(
                    either_nan.into(),
                    nan_val.raw().into(),
                    r2.into(),
                    ty,
                    None,
                    o(),
                );
                self.locals.set(destination_local, result);
                true
            }
            "minnumf32" | "minnumf64" | "minimum_number_nsz_f32" | "minimum_number_nsz_f64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let result = self
                    .builder
                    .fminnum(a.into(), b.into(), ty, Origin::synthetic());
                self.locals.set(destination_local, result.raw());
                true
            }
            "maximumf32" | "maximumf64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let o = || Origin::synthetic();
                let int_bits = match &ty {
                    Type::Float(FloatType::F32) => 32u32,
                    _ => 64u32,
                };
                let iann = IntAnnotation {
                    bit_width: int_bits,
                    signedness: IntSignedness::Unsigned,
                };
                let int_ann = Some(Annotation::Int(iann));
                let fp_flags = tuffy_ir::types::FpRewriteFlags {
                    reassoc: false,
                    contract: false,
                };
                let a_nan = self.builder.fcmp(FCmpOp::Uno, a.into(), a.into(), o());
                let b_nan = self.builder.fcmp(FCmpOp::Uno, b.into(), b.into(), o());
                let either_nan = self.builder.bor(a_nan.into(), b_nan.into(), o());
                let nan_val = self
                    .builder
                    .fadd(a.into(), b.into(), fp_flags, ty.clone(), o());
                let a_gt = self.builder.fcmp(FCmpOp::OGt, a.into(), b.into(), o());
                let a_lt = self.builder.fcmp(FCmpOp::OLt, a.into(), b.into(), o());
                let a_bits = self
                    .builder
                    .bitcast(a.into(), Type::Int, int_ann.clone(), o());
                let b_bits = self
                    .builder
                    .bitcast(b.into(), Type::Int, int_ann.clone(), o());
                let and_bits = self.builder.and(a_bits.into(), b_bits.into(), iann, o());
                let tie = self
                    .builder
                    .bitcast(and_bits.raw().into(), ty.clone(), None, o());
                let r1 =
                    self.builder
                        .select(a_lt.into(), b.into(), tie.into(), ty.clone(), None, o());
                let r2 =
                    self.builder
                        .select(a_gt.into(), a.into(), r1.into(), ty.clone(), None, o());
                let result = self.builder.select(
                    either_nan.into(),
                    nan_val.raw().into(),
                    r2.into(),
                    ty,
                    None,
                    o(),
                );
                self.locals.set(destination_local, result);
                true
            }
            "maxnumf32" | "maxnumf64" | "maximum_number_nsz_f32" | "maximum_number_nsz_f64" => {
                let a = ir_args[0];
                let b = ir_args[1];
                let ty = self
                    .builder
                    .value_type(a)
                    .cloned()
                    .unwrap_or(Type::Float(FloatType::F64));
                let result = self
                    .builder
                    .fmaxnum(a.into(), b.into(), ty, Origin::synthetic());
                self.locals.set(destination_local, result.raw());
                true
            }
            _ => return None,
        })
    }
}
