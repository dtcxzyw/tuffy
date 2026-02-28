use super::StaticDataVec;
use super::types::{int_bitwidth, is_signed_int};
use num_bigint::BigInt;
use rustc_middle::mir;
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::{Operand as IrOperand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::ValueRef;

pub(super) fn translate_int_to_int_cast(
    src_ty: ty::Ty<'_>,
    target_ty: ty::Ty<'_>,
    val: ValueRef,
    builder: &mut Builder<'_>,
) -> Option<ValueRef> {
    let src_bits = int_bitwidth(src_ty)?;
    let dst_bits = int_bitwidth(target_ty)?;

    if src_bits == dst_bits {
        // Same width: reinterpretation only.
        return Some(val);
    }

    if dst_bits > src_bits {
        // Widening cast.  Cap effective destination at 64 bits — the IR
        // operates on 64-bit registers, so shl/shr by ≥64 is undefined.
        // The high word for 128-bit targets is handled by the caller.
        let effective_dst = std::cmp::min(dst_bits, 64);
        if is_signed_int(src_ty) && src_bits < effective_dst {
            // Sign-extend: shl by (eff_dst - src), then arithmetic shr.
            let shift_amt = effective_dst - src_bits;
            let shift_val = builder.iconst(shift_amt as i64, Origin::synthetic());
            let shifted = builder.shl(val.into(), shift_val.into(), None, Origin::synthetic());
            let shift_val2 = builder.iconst(shift_amt as i64, Origin::synthetic());
            let shifted_op = IrOperand::annotated(shifted, Annotation::Signed(effective_dst));
            Some(builder.shr(shifted_op, shift_val2.into(), None, Origin::synthetic()))
        } else if !is_signed_int(src_ty) && src_bits < 64 {
            // Zero-extend: mask off high bits.
            let mask = (BigInt::from(1) << src_bits) - 1;
            let mask_val = builder.iconst(mask, Origin::synthetic());
            Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
        } else {
            // src_bits == 64 widening to 128, or signed 64→128:
            // low word is val as-is; caller stores the high word.
            Some(val)
        }
    } else {
        // Narrowing cast: mask to target width.
        let mask = (BigInt::from(1) << dst_bits) - 1;
        let mask_val = builder.iconst(mask, Origin::synthetic());
        Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
    }
}

pub(super) fn translate_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
    builder: &mut Builder<'_>,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
    current_mem: &mut ValueRef,
    referenced_instances: &mut Vec<Instance<'tcx>>,
    data_counter: &mut u64,
) -> Option<ValueRef> {
    // Monomorphize the constant using the instance's substitutions so that
    // associated type projections (e.g. <B as Flags>::Bits) are resolved
    // before evaluation.
    let mono_const = tcx.instantiate_and_normalize_erasing_regions(
        instance.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(constant.const_),
    );
    let ty = mono_const.ty();
    let val = match mono_const {
        mir::Const::Val(v, _) => v,
        _ => {
            // Const::Ty and Const::Unevaluated need evaluation first.
            let typing_env = ty::TypingEnv::fully_monomorphized();
            match mono_const.eval(tcx, typing_env, constant.span) {
                Ok(v) => v,
                Err(_) => return None,
            }
        }
    };
    match val {
        mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(ptr, _)) => {
            let (prov, ptr_offset) = ptr.into_raw_parts();
            let alloc_id = prov.alloc_id();
            match tcx.global_alloc(alloc_id) {
                rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) => {
                    let alloc = alloc.inner();
                    let offset = ptr_offset.bytes() as usize;
                    let size = alloc.len() - offset;
                    let bytes: Vec<u8> = alloc
                        .inspect_with_uninit_and_ptr_outside_interpreter(offset..offset + size)
                        .to_vec();
                    let sym = format!(".Lconst.{}", {
                        let id = *data_counter;
                        *data_counter += 1;
                        id
                    });
                    let sym_id = symbols.intern(&sym);
                    let relocs = extract_alloc_relocs(
                        tcx,
                        alloc,
                        offset,
                        size,
                        symbols,
                        static_data,
                        referenced_instances,
                        data_counter,
                    );
                    static_data.push((sym_id, bytes, relocs));
                    let base = builder.symbol_addr(sym_id, Origin::synthetic());
                    Some(base)
                }
                rustc_middle::mir::interpret::GlobalAlloc::Static(def_id) => {
                    let instance = Instance::mono(tcx, def_id);
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    let base = builder.symbol_addr(sym_id, Origin::synthetic());
                    if ptr_offset.bytes() > 0 {
                        let off = builder.iconst(ptr_offset.bytes() as i64, Origin::synthetic());
                        Some(builder.add(base.into(), off.into(), None, Origin::synthetic()))
                    } else {
                        Some(base)
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    referenced_instances.push(instance);
                    Some(builder.symbol_addr(sym_id, Origin::synthetic()))
                }
                rustc_middle::mir::interpret::GlobalAlloc::VTable(vtable_ty, vtable_trait_ref) => {
                    // Construct vtable as static data with function pointer relocations.
                    // Extract the principal trait ref from the existential predicates list.
                    let principal = vtable_trait_ref
                        .principal()
                        .map(|p| tcx.instantiate_bound_regions_with_erased(p));
                    let vtable_alloc_id = tcx.vtable_allocation((vtable_ty, principal));
                    let vtable_alloc = tcx.global_alloc(vtable_alloc_id);
                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) = vtable_alloc {
                        let inner = alloc.inner();
                        let size = inner.len();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..size)
                            .to_vec();
                        let sym = format!(".Lvtable.{}", {
                            let id = *data_counter;
                            *data_counter += 1;
                            id
                        });
                        let sym_id = symbols.intern(&sym);

                        let relocs = extract_alloc_relocs(
                            tcx,
                            inner,
                            0,
                            size,
                            symbols,
                            static_data,
                            referenced_instances,
                            data_counter,
                        );

                        static_data.push((sym_id, bytes, relocs));
                        let base = builder.symbol_addr(sym_id, Origin::synthetic());
                        Some(base)
                    } else {
                        Some(builder.iconst(0, Origin::synthetic()))
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::TypeId { .. } => {
                    Some(builder.iconst(0, Origin::synthetic()))
                }
            }
        }
        mir::ConstValue::Scalar(scalar) => {
            // For 128-bit integer constants, decompose into two 64-bit words
            // in a stack slot instead of emitting a single oversized iconst.
            if matches!(
                ty.kind(),
                ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128)
            ) {
                if let mir::interpret::Scalar::Int(int) = scalar {
                    let bits = int.to_bits(int.size());
                    let lo = (bits & u128::from(u64::MAX)) as u64;
                    let hi = (bits >> 64) as u64;
                    let slot = builder.stack_slot(16, Origin::synthetic());
                    let lo_val = builder.iconst(lo as i64, Origin::synthetic());
                    *current_mem = builder.store(
                        lo_val.into(),
                        slot.into(),
                        8,
                        (*current_mem).into(),
                        Origin::synthetic(),
                    );
                    let off8 = builder.iconst(8, Origin::synthetic());
                    let hi_addr = builder.ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                    let hi_val = builder.iconst(hi as i64, Origin::synthetic());
                    *current_mem = builder.store(
                        hi_val.into(),
                        hi_addr.into(),
                        8,
                        (*current_mem).into(),
                        Origin::synthetic(),
                    );
                    return Some(slot);
                }
            }
            translate_scalar(scalar, ty, builder)
        }
        mir::ConstValue::ZeroSized => Some(builder.iconst(0, Origin::synthetic())),
        mir::ConstValue::Slice { alloc_id, meta } => translate_const_slice(
            tcx,
            alloc_id,
            meta,
            builder,
            symbols,
            static_data,
            data_counter,
        ),
        mir::ConstValue::Indirect { alloc_id, offset } => {
            // Multi-byte constant stored in an allocation (e.g. Option::<&str>::None).
            // Emit the bytes as static data and return a pointer.
            let alloc = tcx.global_alloc(alloc_id);
            if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) = alloc {
                let inner = mem_alloc.inner();
                let byte_offset = offset.bytes() as usize;
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let size = tcx
                    .layout_of(typing_env.as_query_input(ty))
                    .map(|l| l.size.bytes() as usize)
                    .unwrap_or(inner.len() - byte_offset);
                let bytes: Vec<u8> = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(
                        byte_offset..byte_offset + size,
                    )
                    .to_vec();
                let sym = format!(".Lconst.{}", {
                    let id = *data_counter;
                    *data_counter += 1;
                    id
                });
                let sym_id = symbols.intern(&sym);
                let relocs = extract_alloc_relocs(
                    tcx,
                    inner,
                    byte_offset,
                    size,
                    symbols,
                    static_data,
                    referenced_instances,
                    data_counter,
                );
                static_data.push((sym_id, bytes, relocs));
                let base = builder.symbol_addr(sym_id, Origin::synthetic());

                // For reference/pointer types, the Indirect constant contains
                // the pointer value (or fat pointer data).  Load the actual
                // pointer from the emitted static data so the local holds the
                // pointer value, not a pointer-to-the-pointer.
                // For fat pointers (&[T], &str), this loads only the data
                // pointer (first 8 bytes); the length component is extracted
                // separately by extract_fat_component.
                if matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..)) {
                    let loaded = builder.load(
                        base.into(),
                        8,
                        Type::Ptr(0),
                        (*current_mem).into(),
                        None,
                        Origin::synthetic(),
                    );
                    Some(loaded)
                } else {
                    Some(base)
                }
            } else {
                None
            }
        }
    }
}

/// Extract relocations from an allocation's provenance table.
///
/// Walks the provenance entries in the given byte range and resolves each
/// pointer target to a symbol name. For `Memory` targets, the target
/// allocation is recursively emitted as static data.
pub(super) fn extract_alloc_relocs<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc: &rustc_middle::mir::interpret::Allocation,
    byte_offset: usize,
    byte_len: usize,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
    referenced_instances: &mut Vec<Instance<'tcx>>,
    data_counter: &mut u64,
) -> Vec<(usize, String)> {
    let mut relocs = Vec::new();
    for (offset, prov) in alloc.provenance().ptrs().iter() {
        let abs_offset = offset.bytes() as usize;
        if abs_offset < byte_offset || abs_offset >= byte_offset + byte_len {
            continue;
        }
        let rel_offset = abs_offset - byte_offset;
        let target_alloc_id = prov.alloc_id();
        let ga = tcx.global_alloc(target_alloc_id);
        match ga {
            rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                let fn_sym = tcx.symbol_name(instance).name.to_string();
                relocs.push((rel_offset, fn_sym));
                referenced_instances.push(instance);
            }
            rustc_middle::mir::interpret::GlobalAlloc::Static(def_id) => {
                let instance = Instance::mono(tcx, def_id);
                let sym_name = tcx.symbol_name(instance).name.to_string();
                relocs.push((rel_offset, sym_name));
            }
            rustc_middle::mir::interpret::GlobalAlloc::Memory(target_alloc) => {
                let inner = target_alloc.inner();
                let bytes = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                    .to_vec();
                let sym = format!(".Lconst.{}", {
                    let id = *data_counter;
                    *data_counter += 1;
                    id
                });
                let sym_id = symbols.intern(&sym);
                let nested_relocs = extract_alloc_relocs(
                    tcx,
                    inner,
                    0,
                    inner.len(),
                    symbols,
                    static_data,
                    referenced_instances,
                    data_counter,
                );
                static_data.push((sym_id, bytes, nested_relocs));
                relocs.push((rel_offset, symbols.resolve(sym_id).to_string()));
            }
            rustc_middle::mir::interpret::GlobalAlloc::VTable(vtable_ty, vtable_trait_ref) => {
                let principal = vtable_trait_ref
                    .principal()
                    .map(|p| tcx.instantiate_bound_regions_with_erased(p));
                let vtable_alloc_id = tcx.vtable_allocation((vtable_ty, principal));
                let vtable_alloc = tcx.global_alloc(vtable_alloc_id);
                if let rustc_middle::mir::interpret::GlobalAlloc::Memory(va) = vtable_alloc {
                    let inner = va.inner();
                    let bytes = inner
                        .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                        .to_vec();
                    let sym = format!(".Lvtable.{}", {
                        let id = *data_counter;
                        *data_counter += 1;
                        id
                    });
                    let sym_id = symbols.intern(&sym);
                    let nested_relocs = extract_alloc_relocs(
                        tcx,
                        inner,
                        0,
                        inner.len(),
                        symbols,
                        static_data,
                        referenced_instances,
                        data_counter,
                    );
                    static_data.push((sym_id, bytes, nested_relocs));
                    relocs.push((rel_offset, symbols.resolve(sym_id).to_string()));
                }
            }
            _ => {}
        }
    }
    relocs
}

pub(super) fn translate_scalar(
    scalar: mir::interpret::Scalar,
    ty: ty::Ty<'_>,
    builder: &mut Builder<'_>,
) -> Option<ValueRef> {
    let mir::interpret::Scalar::Int(int) = scalar else {
        return None;
    };
    let bits = int.to_bits(int.size());
    match ty.kind() {
        ty::Int(_) => {
            // Sign-extend: interpret as i128, then convert to BigInt.
            let size_bytes = int.size().bytes();
            let val = match size_bytes {
                1 => BigInt::from(bits as i8),
                2 => BigInt::from(bits as i16),
                4 => BigInt::from(bits as i32),
                8 => BigInt::from(bits as i64),
                16 => BigInt::from(bits as i128),
                _ => BigInt::from(bits as i128),
            };
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Uint(_) => {
            // Unsigned: convert u128 directly to BigInt (always non-negative).
            let val = BigInt::from(bits);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Bool => Some(builder.bconst(bits != 0, Origin::synthetic())),
        ty::Char => {
            let val = BigInt::from(bits as u32);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..) => {
            // Scalar::Int reference/pointer (e.g., null pointer constant)
            let val = bits as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Float(_) => {
            // Store IEEE 754 bit pattern as an integer (no XMM support).
            let val = BigInt::from(bits);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Adt(..) => {
            // Newtype structs (e.g., ExitCode(u8)) are represented as
            // scalars. Treat the raw bits as an unsigned integer.
            let val = BigInt::from(bits);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        _ => None,
    }
}

/// Translate a ConstValue::Slice (e.g., a string literal `&str`).
///
/// Emits the data bytes to .rodata and returns an IR constant whose index
/// is recorded in `symbols` so that isel emits a RIP-relative LEA.
pub(super) fn translate_const_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: rustc_middle::mir::interpret::AllocId,
    meta: u64,
    builder: &mut Builder<'_>,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
    data_counter: &mut u64,
) -> Option<ValueRef> {
    let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) = tcx.global_alloc(alloc_id)
    else {
        return None;
    };
    let alloc = alloc.inner();
    let bytes: Vec<u8> = alloc
        .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
        .to_vec();

    // Create a unique symbol name for this data blob.
    let sym = format!(".Lstr.{}", {
        let id = *data_counter;
        *data_counter += 1;
        id
    });
    let sym_id = symbols.intern(&sym);
    static_data.push((sym_id, bytes, vec![]));

    // Emit a SymbolAddr to reference this static data blob.
    let ptr_val = builder.symbol_addr(sym_id, Origin::synthetic());

    // Emit the length as a separate constant.
    let len_val = builder.iconst(meta as i64, Origin::synthetic());

    // Store both components. The "value" of this slice is the pointer;
    // the length is stored as the next local via the fat_locals mechanism.
    // For now, we return the pointer and rely on the caller to handle
    // the fat pointer decomposition.
    //
    // We use a convention: for a &str local, we store the pointer in
    // locals[local] and the length in fat_locals[local].
    let _ = len_val;

    // Return pointer; the caller must also retrieve the length.
    Some(ptr_val)
}
