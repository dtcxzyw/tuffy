//! Memory and atomic intrinsic helpers for MIR to IR lowering.

use super::atomic::parse_atomic_ordering;
use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lower memory intrinsics to IR memory operations.
    /// Handles write_bytes, copy_nonoverlapping, copy, and raw_eq.
    /// Returns `Some(new_mem)` if the intrinsic was handled, `None` to fall through.
    pub(crate) fn translate_memory_intrinsic(
        &mut self,
        name: &str,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
        ir_args: &[ValueRef],
        destination_local: mir::Local,
    ) -> Option<ValueRef> {
        let current_mem = self.current_mem;
        let tcx = self.tcx;
        if name.starts_with("atomic_fence") || name.starts_with("atomic_singlethreadfence") {
            let ordering = parse_atomic_ordering(name);
            let new_mem = self
                .builder
                .fence(ordering, current_mem.into(), Origin::synthetic());
            return Some(new_mem.raw());
        }
        // Extract the type parameter T and compute its size and alignment.
        let (elem_size, elem_align) = match substs.first().and_then(|a| a.as_type()) {
            Some(t) => (
                type_size(tcx, t).unwrap_or(0),
                type_align(tcx, t).unwrap_or(1),
            ),
            None => return None,
        };

        match name {
            // write_bytes<T>(dst, val, count) → MemSet(dst, val, count * sizeof(T), align)
            "write_bytes" | "volatile_set_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let dst = ir_args[0];
                let val = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_set(
                    dst_annotated.into(),
                    val.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // copy_nonoverlapping<T>(src, dst, count) → MemCopy(dst, src, count * sizeof(T), align)
            "copy_nonoverlapping" | "volatile_copy_nonoverlapping_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let src = ir_args[0];
                let dst = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let src_annotated = IrOperand::annotated(src, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_copy(
                    dst_annotated.into(),
                    src_annotated.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // copy<T>(src, dst, count) → MemMove(dst, src, count * sizeof(T), align)
            "copy" | "volatile_copy_memory" => {
                if ir_args.len() < 3 {
                    return None;
                }
                let src = ir_args[0];
                let dst = ir_args[1];
                let count = ir_args[2];
                let byte_count = if elem_size == 0 {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                } else if elem_size == 1 {
                    count
                } else {
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .mul(count.into(), sz.into(), I64, Origin::synthetic())
                        .raw()
                };
                let dst_annotated = IrOperand::annotated(dst, Annotation::Align(elem_align as u32));
                let src_annotated = IrOperand::annotated(src, Annotation::Align(elem_align as u32));
                let mem_out = self.builder.mem_move(
                    dst_annotated.into(),
                    src_annotated.into(),
                    byte_count.into(),
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(mem_out.raw())
            }

            // raw_eq<T>(a, b) → memcmp(a, b, sizeof(T)) == 0
            "raw_eq" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let a = ir_args[0];
                let b = ir_args[1];
                let sz = self.builder.iconst(
                    elem_size as i64,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let sym_id = self.symbols.intern("memcmp");
                let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                let (mem_out, data) = self.builder.call(
                    callee.into(),
                    vec![a.into(), b.into(), sz.into()],
                    Type::Int,
                    current_mem.into(),
                    None,
                    int_annotation_for_bytes(4),
                    Origin::synthetic(),
                );
                let cmp_result = data.unwrap_or_else(|| {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                });
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw();
                let eq = self.builder.icmp(
                    tuffy_ir::instruction::ICmpOp::Eq,
                    cmp_result.into(),
                    zero.into(),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, eq.raw());
                Some(mem_out.raw())
            }

            // typed_swap_nonoverlapping<T>(x, y) — swap values at two pointers.
            "typed_swap_nonoverlapping" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let x = self.coerce_to_ptr(ir_args[0]);
                let y = self.coerce_to_ptr(ir_args[1]);
                let mut mem = current_mem;
                let num_words = elem_size.div_ceil(8);
                for i in 0..num_words {
                    let off = i * 8;
                    let chunk = std::cmp::min(8, elem_size - off) as u32;
                    let (xa, ya) = if off == 0 {
                        (x, y)
                    } else {
                        let o = self.builder.iconst(
                            off as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        (
                            self.builder
                                .ptradd(x.into(), o.into(), 0, Origin::synthetic())
                                .raw(),
                            self.builder
                                .ptradd(y.into(), o.into(), 0, Origin::synthetic())
                                .raw(),
                        )
                    };
                    let vx = self.builder.load(
                        xa.into(),
                        chunk,
                        Type::Int,
                        mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    let vy = self.builder.load(
                        ya.into(),
                        chunk,
                        Type::Int,
                        mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
                    mem = self
                        .builder
                        .store(vy.into(), xa.into(), chunk, mem.into(), Origin::synthetic())
                        .raw();
                    mem = self
                        .builder
                        .store(vx.into(), ya.into(), chunk, mem.into(), Origin::synthetic())
                        .raw();
                }
                Some(mem)
            }

            _ if name.starts_with("atomic_load") => {
                if ir_args.is_empty() {
                    return None;
                }
                let ptr = ir_args[0];
                let ordering = parse_atomic_ordering(name);
                let (new_mem, val) = self.builder.load_atomic(
                    ptr.into(),
                    Type::Int,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, val);
                Some(new_mem.raw())
            }

            _ if name.starts_with("atomic_store") => {
                if ir_args.len() < 2 {
                    return None;
                }
                let ptr = ir_args[0];
                let val = ir_args[1];
                let ordering = parse_atomic_ordering(name);
                let new_mem = self.builder.store_atomic(
                    val.into(),
                    ptr.into(),
                    ordering,
                    current_mem.into(),
                    Origin::synthetic(),
                );
                Some(new_mem.raw())
            }

            _ if name.starts_with("atomic_cxchg") => {
                if ir_args.len() < 3 {
                    return None;
                }
                let ptr = ir_args[0];
                let expected = self.coerce_to_int(ir_args[1]);
                let new_val = self.coerce_to_int(ir_args[2]);
                let ordering = parse_atomic_ordering(name);

                let (new_mem, actual_old) = self.builder.atomic_cmpxchg(
                    ptr.into(),
                    expected.into(),
                    new_val.into(),
                    Type::Int,
                    ordering,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );

                let eq = self.builder.icmp(
                    tuffy_ir::instruction::ICmpOp::Eq,
                    actual_old.into(),
                    expected.into(),
                    Origin::synthetic(),
                );

                if let Some(slot) = self.locals.get(destination_local) {
                    let size = elem_size as u32;
                    let mem2 = self.builder.store(
                        actual_old.into(),
                        slot.into(),
                        size,
                        new_mem.into(),
                        Origin::synthetic(),
                    );
                    let bool_off = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let bool_ptr =
                        self.builder
                            .ptradd(slot.into(), bool_off.into(), 0, Origin::synthetic());
                    let mem3 = self.builder.store(
                        eq.into(),
                        bool_ptr.into(),
                        1,
                        mem2.into(),
                        Origin::synthetic(),
                    );
                    Some(mem3.raw())
                } else {
                    self.locals.set(destination_local, actual_old);
                    Some(new_mem.raw())
                }
            }

            _ if name.starts_with("atomic_xchg") => {
                if ir_args.len() < 2 {
                    return None;
                }
                let ptr = ir_args[0];
                let new_val = ir_args[1];
                let ordering = parse_atomic_ordering(name);
                let (new_mem, old) = self.builder.atomic_rmw(
                    AtomicRmwOp::Xchg,
                    ptr.into(),
                    new_val.into(),
                    Type::Int,
                    ordering,
                    current_mem.into(),
                    int_annotation_for_bytes(elem_size as u32),
                    Origin::synthetic(),
                );
                self.locals.set(destination_local, old);
                Some(new_mem.raw())
            }

            _ if name.starts_with("atomic_and")
                || name.starts_with("atomic_or")
                || name.starts_with("atomic_xor")
                || name.starts_with("atomic_nand")
                || name.starts_with("atomic_xadd")
                || name.starts_with("atomic_xsub")
                || name.starts_with("atomic_max")
                || name.starts_with("atomic_min")
                || name.starts_with("atomic_umax")
                || name.starts_with("atomic_umin") =>
            {
                if ir_args.len() < 2 {
                    return None;
                }
                let ptr = ir_args[0];
                let operand = ir_args[1];
                let ordering = parse_atomic_ordering(name);

                if name.starts_with("atomic_xadd") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Add,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xsub") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Sub,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_and") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::And,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_or") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Or,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else if name.starts_with("atomic_xor") {
                    let (new_mem, old) = self.builder.atomic_rmw(
                        AtomicRmwOp::Xor,
                        ptr.into(),
                        operand.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        int_annotation_for_bytes(elem_size as u32),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                } else {
                    let elem_bytes = elem_size as u32;
                    let elem_bits = elem_bytes * 8;
                    let elem_ann = int_annotation_for_bytes(elem_bytes);
                    let int_ty = IntAnnotation {
                        bit_width: elem_bits,
                        signedness: IntSignedness::DontCare,
                    };

                    let (mem1, old) = self.builder.load_atomic(
                        ptr.into(),
                        Type::Int,
                        ordering,
                        current_mem.into(),
                        elem_ann.clone(),
                        Origin::synthetic(),
                    );

                    let new_val = if name.starts_with("atomic_nand") {
                        let a = self.builder.and(
                            old.into(),
                            operand.into(),
                            int_ty,
                            Origin::synthetic(),
                        );
                        let all_ones = self.builder.iconst(
                            -1,
                            elem_bits,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .xor(a.into(), all_ones.into(), int_ty, Origin::synthetic())
                            .raw()
                    } else if name.starts_with("atomic_umax") {
                        let gt = self.builder.icmp(
                            ICmpOp::Gt,
                            old.into(),
                            operand.into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            gt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann.clone(),
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_umin") {
                        let lt = self.builder.icmp(
                            ICmpOp::Lt,
                            old.into(),
                            operand.into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            lt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann.clone(),
                            Origin::synthetic(),
                        )
                    } else if name.starts_with("atomic_max") {
                        let signed_ann = Annotation::Int(IntAnnotation {
                            bit_width: elem_bits,
                            signedness: IntSignedness::Signed,
                        });
                        let gt = self.builder.icmp(
                            ICmpOp::Gt,
                            IrOperand::annotated(old, signed_ann.clone()).into(),
                            IrOperand::annotated(operand, signed_ann.clone()).into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            gt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann.clone(),
                            Origin::synthetic(),
                        )
                    } else {
                        let signed_ann = Annotation::Int(IntAnnotation {
                            bit_width: elem_bits,
                            signedness: IntSignedness::Signed,
                        });
                        let lt = self.builder.icmp(
                            ICmpOp::Lt,
                            IrOperand::annotated(old, signed_ann.clone()).into(),
                            IrOperand::annotated(operand, signed_ann.clone()).into(),
                            Origin::synthetic(),
                        );
                        self.builder.select(
                            lt.into(),
                            old.into(),
                            operand.into(),
                            Type::Int,
                            elem_ann.clone(),
                            Origin::synthetic(),
                        )
                    };

                    let new_mem = self.builder.store_atomic(
                        new_val.into(),
                        ptr.into(),
                        ordering,
                        mem1.into(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, old);
                    Some(new_mem.raw())
                }
            }

            "write_via_move" | "write_volatile" | "volatile_store" | "unaligned_volatile_store" => {
                if ir_args.len() < 2 {
                    return None;
                }
                let dst = self.coerce_to_ptr(ir_args[0]);
                let src = ir_args[1];
                if elem_size == 0 {
                    Some(current_mem)
                } else if self.builder.is_memory_address(src) {
                    let src_ptr = self.coerce_to_ptr(src);
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let mem_out = self.builder.mem_copy(
                        dst.into(),
                        src_ptr.into(),
                        sz.into(),
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    Some(mem_out.raw())
                } else {
                    let store_size = elem_size.min(8) as u32;
                    let mem_out = self.builder.store(
                        src.into(),
                        dst.into(),
                        store_size,
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    Some(mem_out.raw())
                }
            }

            "read_via_copy" | "read_volatile" | "volatile_load" | "unaligned_volatile_load" => {
                if ir_args.is_empty() {
                    return None;
                }
                let src = self.coerce_to_ptr(ir_args[0]);
                if elem_size == 0 {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.locals.set(destination_local, zero.raw());
                    Some(current_mem)
                } else if elem_size > 8 {
                    let slot =
                        self.builder
                            .stack_slot(elem_size.max(8) as u32, 0, Origin::synthetic());
                    let sz = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let mem_out = self.builder.mem_copy(
                        slot.into(),
                        src.into(),
                        sz.into(),
                        current_mem.into(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, slot);
                    self.stack_locals.mark(destination_local);
                    Some(mem_out.raw())
                } else {
                    let load_size = elem_size.min(8) as u32;
                    let ann = int_annotation_for_bytes(load_size);
                    let val = self.builder.load(
                        src.into(),
                        load_size,
                        Type::Int,
                        current_mem.into(),
                        ann.clone(),
                        Origin::synthetic(),
                    );
                    self.locals.set(destination_local, val);
                    Some(current_mem)
                }
            }

            _ => None,
        }
    }
}
