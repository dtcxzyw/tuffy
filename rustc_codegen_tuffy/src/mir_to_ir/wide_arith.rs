//! 128-bit wide arithmetic intrinsic handling.

use tuffy_ir::instruction::Origin;
use tuffy_ir::types::Type;

use super::ctx::TranslationCtx;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// 128-bit carrying_mul_add: computes a*b + carry + add as (lo_128, hi_128).
    /// Uses 64-bit partial products since 256-bit arithmetic isn't available.
    pub(super) fn emit_carrying_mul_add_128(
        &mut self,
        ir_args: &[tuffy_ir::value::ValueRef],
        destination_local: rustc_middle::mir::Local,
        is_signed: bool,
    ) {
        use tuffy_ir::instruction::Origin;
        use tuffy_ir::types::{IntAnnotation, IntSignedness};
        use tuffy_ir::value::ValueRef;

        let o = || Origin::synthetic();
        let i64_ann = IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };
        let _i128_ann = IntAnnotation {
            bit_width: 128,
            signedness: IntSignedness::Unsigned,
        };

        // Split each 128-bit arg into (lo64, hi64) via stack
        let split_128 = |this: &mut Self, val: ValueRef| -> (ValueRef, ValueRef) {
            let slot = this.builder.stack_slot(16, 0, o());
            this.current_mem = this
                .builder
                .store(val.into(), slot.into(), 16, this.current_mem.into(), o())
                .raw();
            let lo = this.builder.load(
                slot.into(),
                8,
                Type::Int,
                this.current_mem.into(),
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let off8 = this.builder.iconst(8, 64, IntSignedness::Unsigned, o());
            let hi_ptr = this.builder.ptradd(slot.into(), off8.into(), 0, o());
            let hi = this.builder.load(
                hi_ptr.raw().into(),
                8,
                Type::Int,
                this.current_mem.into(),
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            (lo, hi)
        };

        let (a_lo, a_hi) = split_128(self, ir_args[0]);
        let (b_lo, b_hi) = split_128(self, ir_args[1]);
        let (c_lo, c_hi) = split_128(self, ir_args[2]);
        let (d_lo, d_hi) = split_128(self, ir_args[3]);

        // 4 partial products: a*b = (a_lo + a_hi*2^64) * (b_lo + b_hi*2^64)
        // Each uses 32-bit schoolbook multiply to get full 128-bit result (lo64, hi64).
        let (ll_lo, ll_hi) = self.emit_widening_mul_u64(a_lo, b_lo);
        let (lh_lo, lh_hi) = self.emit_widening_mul_u64(a_lo, b_hi);
        let (hl_lo, hl_hi) = self.emit_widening_mul_u64(a_hi, b_lo);
        let (hh_lo, hh_hi) = self.emit_widening_mul_u64(a_hi, b_hi);

        // Accumulate 256-bit product: [w0, w1, w2, w3] (each 64 bits)
        // w0 = ll_lo
        let w0 = ll_lo;

        // w1 = ll_hi + lh_lo + hl_lo (with carries into w2)
        let w1_a = self.builder.add(ll_hi.into(), lh_lo.into(), i64_ann, o());
        let c1_a = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w1_a.into(),
            ll_hi.into(),
            o(),
        );
        let w1 = self.builder.add(w1_a.into(), hl_lo.into(), i64_ann, o());
        let c1_b = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w1.into(),
            w1_a.into(),
            o(),
        );
        let c1_a_int = self.bool_to_u64(c1_a);
        let c1_b_int = self.bool_to_u64(c1_b);
        let c1 = self
            .builder
            .add(c1_a_int.into(), c1_b_int.into(), i64_ann, o());

        // w2 = lh_hi + hl_hi + hh_lo + c1
        let w2_a = self.builder.add(lh_hi.into(), hl_hi.into(), i64_ann, o());
        let c2_a = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2_a.into(),
            lh_hi.into(),
            o(),
        );
        let w2_b = self.builder.add(w2_a.into(), hh_lo.into(), i64_ann, o());
        let c2_b = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2_b.into(),
            w2_a.into(),
            o(),
        );
        let w2 = self.builder.add(w2_b.into(), c1.into(), i64_ann, o());
        let c2_c = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            w2.into(),
            w2_b.into(),
            o(),
        );
        let c2_a_int = self.bool_to_u64(c2_a);
        let c2_b_int = self.bool_to_u64(c2_b);
        let c2_c_int = self.bool_to_u64(c2_c);
        let c2_ab = self
            .builder
            .add(c2_a_int.into(), c2_b_int.into(), i64_ann, o());
        let c2 = self
            .builder
            .add(c2_ab.into(), c2_c_int.into(), i64_ann, o());

        // w3 = hh_hi + c2
        let w3 = self.builder.add(hh_hi.into(), c2.into(), i64_ann, o());

        // For signed: adjust high 128 bits
        // If a is negative (a_hi < 0 as signed), subtract b from high half
        // If b is negative (b_hi < 0 as signed), subtract a from high half
        let (w2_final, w3_final) = if is_signed {
            let zero = self.builder.iconst(0, 64, IntSignedness::Unsigned, o());
            let signed_ann = IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Signed,
            };
            // a negative?
            let a_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    a_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            // b negative?
            let b_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    b_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );

            // If a_neg, subtract b from (w2,w3)
            let sub_b_lo = self.builder.sub(w2.into(), b_lo.into(), i64_ann, o());
            let borrow1 = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                w2.into(),
                b_lo.into(),
                o(),
            );
            let borrow1_int = self.bool_to_u64(borrow1);
            let sub_b_hi_tmp = self.builder.sub(w3.into(), b_hi.into(), i64_ann, o());
            let sub_b_hi = self
                .builder
                .sub(sub_b_hi_tmp.into(), borrow1_int.into(), i64_ann, o());
            let w2_adj1 = self.builder.select(
                a_neg.into(),
                sub_b_lo.raw().into(),
                w2.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let w3_adj1 = self.builder.select(
                a_neg.into(),
                sub_b_hi.raw().into(),
                w3.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );

            // If b_neg, subtract a from (w2_adj1, w3_adj1)
            let sub_a_lo = self.builder.sub(w2_adj1.into(), a_lo.into(), i64_ann, o());
            let borrow2 = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                w2_adj1.into(),
                a_lo.into(),
                o(),
            );
            let borrow2_int = self.bool_to_u64(borrow2);
            let sub_a_hi_tmp = self.builder.sub(w3_adj1.into(), a_hi.into(), i64_ann, o());
            let sub_a_hi = self
                .builder
                .sub(sub_a_hi_tmp.into(), borrow2_int.into(), i64_ann, o());
            let w2_adj2 = self.builder.select(
                b_neg.into(),
                sub_a_lo.raw().into(),
                w2_adj1.into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let w3_adj2 = self.builder.select(
                b_neg.into(),
                sub_a_hi.raw().into(),
                w3_adj1.into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            (w2_adj2, w3_adj2)
        } else {
            (w2.raw(), w3.raw())
        };

        // Now add carry (c_lo, c_hi) and add (d_lo, d_hi) to the 256-bit product
        // Add carry to low 128 bits first, propagate carry into high 128 bits
        let add_to_256 = |this: &mut Self,
                          w0: ValueRef,
                          w1: ValueRef,
                          w2: ValueRef,
                          w3: ValueRef,
                          x_lo: ValueRef,
                          x_hi: ValueRef|
         -> (ValueRef, ValueRef, ValueRef, ValueRef) {
            let r0 = this.builder.add(w0.into(), x_lo.into(), i64_ann, o());
            let c0 =
                this.builder
                    .icmp(tuffy_ir::instruction::ICmpOp::Lt, r0.into(), w0.into(), o());
            let c0_int = this.bool_to_u64(c0);
            let r1_tmp = this.builder.add(w1.into(), x_hi.into(), i64_ann, o());
            let c1_tmp = this.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r1_tmp.into(),
                w1.into(),
                o(),
            );
            let r1 = this.builder.add(r1_tmp.into(), c0_int.into(), i64_ann, o());
            let c1_tmp2 = this.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r1.into(),
                r1_tmp.into(),
                o(),
            );
            let c1_a = this.bool_to_u64(c1_tmp);
            let c1_b = this.bool_to_u64(c1_tmp2);
            let c1_total = this.builder.add(c1_a.into(), c1_b.into(), i64_ann, o());
            let r2 = this.builder.add(w2.into(), c1_total.into(), i64_ann, o());
            let c2 =
                this.builder
                    .icmp(tuffy_ir::instruction::ICmpOp::Lt, r2.into(), w2.into(), o());
            let c2_int = this.bool_to_u64(c2);
            let r3 = this.builder.add(w3.into(), c2_int.into(), i64_ann, o());
            (r0.raw(), r1.raw(), r2.raw(), r3.raw())
        };

        let (r0, r1, r2, r3) = add_to_256(self, w0, w1.raw(), w2_final, w3_final, c_lo, c_hi);
        let (r0, r1, r2, r3) = add_to_256(self, r0, r1, r2, r3, d_lo, d_hi);

        // For signed types, unsigned add_to_256 doesn't sign-extend the 128-bit
        // carry/add values into the upper 128 bits. If the value was negative,
        // its unsigned representation is 2^128 too large, so subtract 1 from (r2,r3).
        let (r2, r3) = if is_signed {
            let signed_ann = IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Signed,
            };
            let zero_s = self.builder.iconst(0, 64, IntSignedness::Unsigned, o());
            let one_s = self.builder.iconst(1, 64, IntSignedness::Unsigned, o());

            // Sign extension for carry value (c_lo, c_hi)
            let c_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    c_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero_s.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            let c_adj = self.builder.select(
                c_neg.into(),
                one_s.raw().into(),
                zero_s.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let r2a = self.builder.sub(r2.into(), c_adj.into(), i64_ann, o());
            let c_borrow = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r2.into(),
                c_adj.into(),
                o(),
            );
            let c_borrow_int = self.bool_to_u64(c_borrow);
            let r3a = self
                .builder
                .sub(r3.into(), c_borrow_int.into(), i64_ann, o());

            // Sign extension for add value (d_lo, d_hi)
            let d_neg = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                tuffy_ir::instruction::Operand::annotated(
                    d_hi,
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                tuffy_ir::instruction::Operand::annotated(
                    zero_s.raw(),
                    tuffy_ir::types::Annotation::Int(signed_ann),
                )
                .into(),
                o(),
            );
            let d_adj = self.builder.select(
                d_neg.into(),
                one_s.raw().into(),
                zero_s.raw().into(),
                Type::Int,
                Some(tuffy_ir::types::Annotation::Int(i64_ann)),
                o(),
            );
            let r2b = self.builder.sub(r2a.into(), d_adj.into(), i64_ann, o());
            let d_borrow = self.builder.icmp(
                tuffy_ir::instruction::ICmpOp::Lt,
                r2a.raw().into(),
                d_adj.into(),
                o(),
            );
            let d_borrow_int = self.bool_to_u64(d_borrow);
            let r3b = self
                .builder
                .sub(r3a.into(), d_borrow_int.into(), i64_ann, o());

            (r2b.raw(), r3b.raw())
        } else {
            (r2, r3)
        };

        // Store result: lo_128 = (r0, r1), hi_128 = (r2, r3)
        let slot = self.builder.stack_slot(32, 0, o());
        self.current_mem = self
            .builder
            .store(r0.into(), slot.into(), 8, self.current_mem.into(), o())
            .raw();
        let off8 = self.builder.iconst(8, 64, IntSignedness::Unsigned, o());
        let addr1 = self.builder.ptradd(slot.into(), off8.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r1.into(),
                addr1.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        let off16 = self.builder.iconst(16, 64, IntSignedness::Unsigned, o());
        let addr2 = self.builder.ptradd(slot.into(), off16.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r2.into(),
                addr2.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        let off24 = self.builder.iconst(24, 64, IntSignedness::Unsigned, o());
        let addr3 = self.builder.ptradd(slot.into(), off24.into(), 0, o());
        self.current_mem = self
            .builder
            .store(
                r3.into(),
                addr3.raw().into(),
                8,
                self.current_mem.into(),
                o(),
            )
            .raw();
        self.locals.set(destination_local, slot);
        self.stack_locals.mark(destination_local);
    }

    /// Compute the full 128-bit unsigned product of two 64-bit values,
    /// returning (lo64, hi64). Uses schoolbook 32-bit partial products
    /// (same algorithm as `widening_mul_u64` in legalize.rs).
    fn emit_widening_mul_u64(
        &mut self,
        x: tuffy_ir::value::ValueRef,
        y: tuffy_ir::value::ValueRef,
    ) -> (tuffy_ir::value::ValueRef, tuffy_ir::value::ValueRef) {
        use tuffy_ir::instruction::{ICmpOp, Origin};
        use tuffy_ir::types::IntSignedness;

        let o = || Origin::synthetic();
        let i64_ann = tuffy_ir::types::IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        };

        let c32 = self.builder.iconst(32, 64, IntSignedness::Unsigned, o());
        let mask32 = self
            .builder
            .iconst(0xFFFF_FFFF_i64, 64, IntSignedness::Unsigned, o());

        let x0 = self.builder.and(x.into(), mask32.into(), i64_ann, o());
        let x1 = self.builder.shr(x.into(), c32.into(), i64_ann, o());
        let y0 = self.builder.and(y.into(), mask32.into(), i64_ann, o());
        let y1 = self.builder.shr(y.into(), c32.into(), i64_ann, o());

        let p0 = self.builder.mul(x0.into(), y0.into(), i64_ann, o());
        let p1 = self.builder.mul(x0.into(), y1.into(), i64_ann, o());
        let p2 = self.builder.mul(x1.into(), y0.into(), i64_ann, o());
        let p3 = self.builder.mul(x1.into(), y1.into(), i64_ann, o());

        let p0_hi = self.builder.shr(p0.into(), c32.into(), i64_ann, o());
        let mid1 = self.builder.add(p0_hi.into(), p1.into(), i64_ann, o());
        let cmp = self.builder.icmp(ICmpOp::Lt, mid1.into(), p1.into(), o());
        let c1 = self.bool_to_u64(cmp);
        let mid = self.builder.add(mid1.into(), p2.into(), i64_ann, o());
        let cmp = self.builder.icmp(ICmpOp::Lt, mid.into(), p2.into(), o());
        let c2 = self.bool_to_u64(cmp);
        let total_carry = self.builder.add(c1.into(), c2.into(), i64_ann, o());

        let mid_shifted = self.builder.shl(mid.into(), c32.into(), i64_ann, o());
        let p0_lo = self.builder.and(p0.into(), mask32.into(), i64_ann, o());
        let lo = self
            .builder
            .or(mid_shifted.into(), p0_lo.into(), i64_ann, o());

        let mid_hi = self.builder.shr(mid.into(), c32.into(), i64_ann, o());
        let carry_shifted = self
            .builder
            .shl(total_carry.into(), c32.into(), i64_ann, o());
        let hi = self
            .builder
            .add(mid_hi.into(), carry_shifted.into(), i64_ann, o());
        let hi = self.builder.add(hi.into(), p3.into(), i64_ann, o());

        (lo.raw(), hi.raw())
    }

    fn bool_to_u64(&mut self, val: tuffy_ir::typed::BoolValue) -> tuffy_ir::typed::IntValue {
        self.builder.zext(val.raw().into(), 64, Origin::synthetic())
    }
}
