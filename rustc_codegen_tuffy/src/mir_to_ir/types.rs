//! Type translation utilities for MIR → IR conversion.

use rustc_abi::BackendRepr;
use rustc_middle::mir::{self, Operand};
use rustc_middle::ty::{self, TyCtxt};

use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};

/// Local helper for integer annotations during MIR translation.
#[derive(Debug, Clone, Copy)]
pub(super) enum IntAnn {
    Signed(u32),
    Unsigned(u32),
    DontCare(u32),
}

impl IntAnn {
    /// Convert from Annotation to IntAnn.
    pub(super) fn from_annotation(ann: &Annotation) -> Option<Self> {
        match ann {
            Annotation::Int(int_ann) => Some(match int_ann.signedness {
                IntSignedness::Signed => IntAnn::Signed(int_ann.bit_width),
                IntSignedness::Unsigned => IntAnn::Unsigned(int_ann.bit_width),
                IntSignedness::DontCare => IntAnn::DontCare(int_ann.bit_width),
            }),
            Annotation::Align(_) | Annotation::Byval(_) => None,
        }
    }

    /// Convert IntAnn to Annotation.
    pub(super) fn to_annotation(self) -> Annotation {
        match self {
            IntAnn::Signed(n) => Annotation::Int(IntAnnotation {
                bit_width: n,
                signedness: IntSignedness::Signed,
            }),
            IntAnn::Unsigned(n) => Annotation::Int(IntAnnotation {
                bit_width: n,
                signedness: IntSignedness::Unsigned,
            }),
            IntAnn::DontCare(n) => Annotation::Int(IntAnnotation {
                bit_width: n,
                signedness: IntSignedness::DontCare,
            }),
        }
    }
}

/// Helper to create a default Int annotation (64-bit, DontCare signedness).
pub(super) fn default_int_annotation() -> Option<Annotation> {
    Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::DontCare,
    }))
}

/// Helper to create an Int annotation for a given number of bytes.
pub(super) fn int_annotation_for_bytes(bytes: u32) -> Option<Annotation> {
    Some(Annotation::Int(IntAnnotation {
        bit_width: bytes * 8,
        signedness: IntSignedness::DontCare,
    }))
}

/// Helper to create a *signed* Int annotation for a given number of bytes.
pub(super) fn signed_int_annotation_for_bytes(bytes: u32) -> Option<Annotation> {
    Some(Annotation::Int(IntAnnotation {
        bit_width: bytes * 8,
        signedness: IntSignedness::Signed,
    }))
}

/// Helper to create an IntAnnotation (not wrapped in Option) for shift operations.
pub(super) fn int_ann_for_bytes(bytes: u32) -> IntAnnotation {
    IntAnnotation {
        bit_width: bytes * 8,
        signedness: IntSignedness::DontCare,
    }
}

/// Helper to create a signed IntAnnotation (not wrapped in Option) for shift operations.
pub(super) fn signed_int_ann_for_bytes(bytes: u32) -> IntAnnotation {
    IntAnnotation {
        bit_width: bytes * 8,
        signedness: IntSignedness::Signed,
    }
}

/// Look up the fully-monomorphized layout for a type, or return `None` on failure.
///
/// All layout queries in this module use fully-monomorphized types, so this
/// helper avoids repeating the same `TypingEnv::fully_monomorphized()` boilerplate.
#[inline]
fn mono_layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<rustc_abi::TyAndLayout<'tcx, ty::Ty<'tcx>>> {
    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()
}

/// Coarse-grained ABI representation of a Rust type, mirroring BackendRepr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReprKind {
    /// Zero-sized type — no data to pass or return.
    Zst,
    /// Single register (int, float, pointer, i128/u128).
    Scalar,
    /// Two registers (fat pointer: data ptr + length/vtable).
    ScalarPair,
    /// Passed via memory pointer (large structs, arrays, etc.).
    Memory,
}

pub(super) fn repr_kind<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ReprKind {
    let Some(layout) = mono_layout_of(tcx, ty) else {
        return ReprKind::Memory;
    };
    if layout.is_zst() {
        return ReprKind::Zst;
    }
    match layout.backend_repr {
        BackendRepr::Scalar(_) => ReprKind::Scalar,
        BackendRepr::ScalarPair(_, _) => ReprKind::ScalarPair,
        _ => ReprKind::Memory,
    }
}

pub(super) fn translate_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<Type> {
    match ty.kind() {
        ty::Bool => Some(Type::Bool),
        ty::Int(ty::IntTy::I8) => Some(Type::Int),
        ty::Uint(ty::UintTy::U8) => Some(Type::Int),
        ty::Int(ty::IntTy::I16) => Some(Type::Int),
        ty::Uint(ty::UintTy::U16) => Some(Type::Int),
        ty::Int(ty::IntTy::I32) => Some(Type::Int),
        ty::Uint(ty::UintTy::U32) => Some(Type::Int),
        ty::Char => Some(Type::Int),
        ty::Int(ty::IntTy::I64) => Some(Type::Int),
        ty::Uint(ty::UintTy::U64) => Some(Type::Int),
        ty::Int(ty::IntTy::I128) => Some(Type::Int),
        ty::Uint(ty::UintTy::U128) => Some(Type::Int),
        ty::Int(ty::IntTy::Isize) => Some(Type::Int),
        ty::Uint(ty::UintTy::Usize) => Some(Type::Int),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Type::Ptr(0)),
        ty::Tuple(fields) if fields.is_empty() => Some(Type::Unit),
        ty::FnDef(..) => None,
        ty::Never => None,
        ty::Float(ty::FloatTy::F16) => Some(Type::Float(FloatType::F16)),
        ty::Float(ty::FloatTy::F32) => Some(Type::Float(FloatType::F32)),
        ty::Float(ty::FloatTy::F64) => Some(Type::Float(FloatType::F64)),
        ty::Float(ty::FloatTy::F128) => Some(Type::Float(FloatType::F128)),
        ty::Adt(..) | ty::Tuple(..) => None,
        ty::Array(..) | ty::Slice(..) | ty::Str => None,
        ty::Closure(..) | ty::CoroutineClosure(..) => None,
        _ => None,
    }
}

pub(super) fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
    match ty.kind() {
        ty::Int(_) | ty::Uint(_) => int_bitwidth(ty).map(|bw| {
            Annotation::Int(IntAnnotation {
                bit_width: bw,
                signedness: if is_signed_int(ty) {
                    IntSignedness::Signed
                } else {
                    IntSignedness::Unsigned
                },
            })
        }),
        ty::Char => Some(Annotation::Int(IntAnnotation {
            bit_width: 32,
            signedness: IntSignedness::Unsigned,
        })),
        _ => None,
    }
}

/// Get the type of an operand (local type, not projected).
pub(super) fn operand_ty<'tcx>(
    operand: &Operand<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(mir.local_decls[place.local].ty),
        Operand::Constant(c) => Some(c.ty()),
        _ => None,
    }
}

/// Get the projected type of an operand.
pub(super) fn operand_ty_projected<'tcx>(
    operand: &Operand<'tcx>,
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place.ty(&mir.local_decls, tcx).ty),
        Operand::Constant(c) => Some(c.ty()),
        _ => None,
    }
}

/// Extract the type annotation from a MIR operand.
pub(super) fn operand_annotation<'tcx>(
    operand: &Operand<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Option<Annotation> {
    let ty = operand_ty(operand, mir)?;
    translate_annotation(ty)
}

/// Query the byte offset of field `field_idx` within type `ty`.
pub(super) fn field_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    field_idx: usize,
) -> Option<u64> {
    let layout = mono_layout_of(tcx, ty)?;
    if field_idx >= layout.fields.count() {
        return None;
    }
    Some(layout.fields.offset(field_idx).bytes())
}

/// Query the byte offset of field `field_idx` within a specific enum variant.
pub(super) fn variant_field_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    variant_idx: rustc_abi::VariantIdx,
    field_idx: usize,
) -> Option<u64> {
    let layout = mono_layout_of(tcx, ty)?;
    match &layout.variants {
        rustc_abi::Variants::Multiple { variants, .. } => {
            let variant_layout = &variants[variant_idx];
            if field_idx >= variant_layout.fields.count() {
                return None;
            }
            Some(variant_layout.fields.offset(field_idx).bytes())
        }
        rustc_abi::Variants::Single { .. } => {
            // Single-variant enum — field offsets are the same as the
            // top-level layout.
            if field_idx >= layout.fields.count() {
                return None;
            }
            Some(layout.fields.offset(field_idx).bytes())
        }
        rustc_abi::Variants::Empty => None,
    }
}

/// Query the total byte size of type `ty`.
pub(super) fn type_size<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    Some(mono_layout_of(tcx, ty)?.size.bytes())
}

/// Query the element count of a monomorphized array type.
pub(super) fn array_len<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    match ty.kind() {
        ty::Array(..) => Some(mono_layout_of(tcx, ty)?.fields.count() as u64),
        _ => None,
    }
}

/// For a ScalarPair type, return `(first_scalar_bytes, second_scalar_bytes, second_offset)`.
/// Returns `None` if `ty` is not a ScalarPair.
pub(super) fn scalar_pair_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<(u64, u64, u64)> {
    let layout = mono_layout_of(tcx, ty)?;
    if let BackendRepr::ScalarPair(a, b) = layout.backend_repr {
        let a_size = a.size(&tcx).bytes();
        let b_size = b.size(&tcx).bytes();
        let b_offset = a_size.max(b.align(&tcx).abi.bytes());
        Some((a_size, b_size, b_offset))
    } else {
        None
    }
}

/// Query the alignment of type `ty` in bytes.
#[allow(dead_code)]
pub(super) fn type_align<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    Some(mono_layout_of(tcx, ty)?.align.abi.bytes())
}

/// Check if a type is a signed integer type.
pub(super) fn is_signed_int(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Int(_))
}

/// Get the bitwidth of an integer type (for cast operations).
pub(super) fn int_bitwidth(ty: ty::Ty<'_>) -> Option<u32> {
    match ty.kind() {
        ty::Bool => Some(8),
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) => Some(8),
        ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => Some(16),
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) | ty::Char => Some(32),
        ty::Int(ty::IntTy::I64)
        | ty::Uint(ty::UintTy::U64)
        | ty::Int(ty::IntTy::Isize)
        | ty::Uint(ty::UintTy::Usize) => Some(64),
        ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128) => Some(128),
        _ => None,
    }
}

/// Check if a type is a fat pointer (e.g., &str, &[T], &dyn Trait) that uses two registers at ABI level.
pub(super) fn is_fat_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            let tail = tcx.struct_tail_for_codegen(*inner, ty::TypingEnv::fully_monomorphized());
            matches!(tail.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
        }
        _ => false,
    }
}
