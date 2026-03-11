use super::StaticDataVec;
use super::types::{int_bitwidth, is_signed_int};
use num_bigint::BigInt;
use rustc_middle::mir;
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::Origin;
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{FloatType, IntSignedness, Type};
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
        return Some(val);
    }

    if dst_bits > src_bits {
        // Widening cast. For sub-64-bit sources targeting 128 bits, first
        // extend to 64 bits so that leg_sext_128 / leg_zext_128 see a full
        // 64-bit lo value (their `val >> 63` assumes 64-bit input).
        let mut v = val;
        if src_bits < 64 && dst_bits > 64 {
            // Intermediate extension to 64 bits.
            if is_signed_int(src_ty) {
                v = builder.sext(v.into(), 64, Origin::synthetic()).raw();
            } else {
                v = builder.zext(v.into(), 64, Origin::synthetic()).raw();
            }
        }
        if is_signed_int(src_ty) {
            Some(builder.sext(v.into(), dst_bits, Origin::synthetic()).raw())
        } else {
            Some(builder.zext(v.into(), dst_bits, Origin::synthetic()).raw())
        }
    } else {
        // Narrowing: use sext/zext with dst_bits
        if is_signed_int(target_ty) {
            Some(
                builder
                    .sext(val.into(), dst_bits, Origin::synthetic())
                    .raw(),
            )
        } else {
            Some(
                builder
                    .zext(val.into(), dst_bits, Origin::synthetic())
                    .raw(),
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
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
                    Some(base.raw())
                }
                rustc_middle::mir::interpret::GlobalAlloc::Static(def_id) => {
                    let instance = Instance::mono(tcx, def_id);
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    let base = builder.symbol_addr(sym_id, Origin::synthetic());
                    if ptr_offset.bytes() > 0 {
                        let off = builder.iconst(
                            ptr_offset.bytes() as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        Some(
                            builder
                                .ptradd(base.raw().into(), off.into(), 0, Origin::synthetic())
                                .raw(),
                        )
                    } else {
                        Some(base.raw())
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    referenced_instances.push(instance);
                    Some(builder.symbol_addr(sym_id, Origin::synthetic()).raw())
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
                        Some(base.raw())
                    } else {
                        Some(
                            builder
                                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                                .raw(),
                        )
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::TypeId { .. } => Some(
                    builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw(),
                ),
            }
        }
        mir::ConstValue::Scalar(scalar) => translate_scalar(scalar, ty, builder),
        mir::ConstValue::ZeroSized => Some(
            builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                .raw(),
        ),
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
                        base.raw().into(),
                        8,
                        Type::Ptr(0),
                        (*current_mem).into(),
                        None,
                        Origin::synthetic(),
                    );
                    Some(loaded)
                } else {
                    Some(base.raw())
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
#[allow(clippy::too_many_arguments)]
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
            let bit_width = (size_bytes * 8).min(128) as u32;
            Some(
                builder
                    .iconst(val, bit_width, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
        }
        ty::Uint(_) => {
            // Unsigned: convert u128 directly to BigInt (always non-negative).
            let size_bytes = int.size().bytes();
            let val = BigInt::from(bits);
            let bit_width = (size_bytes * 8).min(128) as u32;
            Some(
                builder
                    .iconst(val, bit_width, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
        }
        ty::Bool => Some(builder.bconst(bits != 0, Origin::synthetic()).raw()),
        ty::Char => {
            let val = BigInt::from(bits as u32);
            Some(
                builder
                    .iconst(val, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
        }
        ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..) => {
            // Scalar::Int reference/pointer (e.g., null pointer constant)
            let val = bits as i64;
            Some(
                builder
                    .iconst(val, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
        }
        ty::Float(float_ty) => {
            let ft = match float_ty {
                ty::FloatTy::F16 => FloatType::F16,
                ty::FloatTy::F32 => FloatType::F32,
                ty::FloatTy::F64 => FloatType::F64,
                ty::FloatTy::F128 => FloatType::F128,
            };
            Some(builder.fconst(ft, bits, Origin::synthetic()).raw())
        }
        ty::Adt(..) => {
            // Newtype structs (e.g., ExitCode(u8)) are represented as
            // scalars. Treat the raw bits as an unsigned integer.
            let val = BigInt::from(bits);
            Some(
                builder
                    .iconst(val, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
        }
        ty::Tuple(_) => {
            // 1-tuples optimized to scalars by MIR (e.g., const (42_i32,)).
            // Treat the raw bits as an unsigned integer.
            let val = BigInt::from(bits);
            Some(
                builder
                    .iconst(val, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            )
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
    _meta: u64,
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

    let sym = format!(".Lstr.{}", {
        let id = *data_counter;
        *data_counter += 1;
        id
    });
    let sym_id = symbols.intern(&sym);
    static_data.push((sym_id, bytes, vec![]));

    let ptr_val = builder.symbol_addr(sym_id, Origin::synthetic());

    Some(ptr_val.raw())
}
