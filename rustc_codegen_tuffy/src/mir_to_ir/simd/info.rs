//! Shared SIMD type-shape helpers.

use super::*;

#[derive(Clone, Copy)]
/// Precomputed shape information for a SIMD cast source or destination type.
pub(crate) struct SimdCastInfo {
    /// Element width in bytes.
    pub(crate) elem_size: u32,
    /// Number of lanes in the SIMD vector.
    pub(crate) lanes: u32,
    /// Integer annotation for integer-lane vectors.
    pub(crate) int_ann: Option<IntAnnotation>,
    /// Floating-point lane type for float vectors.
    pub(crate) float_ty: Option<FloatType>,
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Returns the total byte width of the SIMD type named by `substs`.
    pub(crate) fn simd_size_from_substs(
        &self,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> Option<u32> {
        substs
            .first()
            .and_then(|a| a.as_type())
            .and_then(|t| type_size(self.tcx, t))
            .map(|sz| sz as u32)
    }

    /// Extract SIMD element info: (elem_size_bytes, Option<FloatType>).
    /// Returns None if the element type cannot be determined.
    pub(crate) fn simd_elem_info_from_substs(
        &self,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> (u32, Option<FloatType>) {
        let simd_ty = substs.first().and_then(|a| a.as_type());
        if let Some(simd_ty) = simd_ty
            && let ty::Adt(def, adt_substs) = simd_ty.kind()
        {
            if let Some(elem_ty) = adt_substs.first().and_then(|a| a.as_type()) {
                let elem_size = type_size(self.tcx, elem_ty).unwrap_or(1) as u32;
                let float_ty = match elem_ty.kind() {
                    ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
                    ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
                    ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
                    ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
                    _ => None,
                };
                return (elem_size, float_ty);
            }
            let variant = def.non_enum_variant();
            if let Some(field) = variant.fields.iter().next() {
                let field_ty = field.ty(self.tcx, adt_substs);
                let inner_ty = match field_ty.kind() {
                    ty::Array(elem, _) => *elem,
                    _ => field_ty,
                };
                let elem_size = type_size(self.tcx, inner_ty).unwrap_or(1) as u32;
                let float_ty = match inner_ty.kind() {
                    ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
                    ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
                    ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
                    ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
                    _ => None,
                };
                return (elem_size, float_ty);
            }
        }
        (1, None)
    }

    /// Returns the integer lane annotation implied by the SIMD type in `substs`.
    pub(crate) fn simd_elem_int_ann_from_substs(
        &self,
        substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> Option<IntAnnotation> {
        let simd_ty = substs.first().and_then(|a| a.as_type())?;
        let elem_ty = self.simd_elem_ty(simd_ty)?;
        match translate_annotation(elem_ty) {
            Some(Annotation::Int(int_ann)) => Some(int_ann),
            _ => None,
        }
    }

    /// Returns the lane element type for a monomorphized SIMD type.
    pub(crate) fn simd_elem_ty(&self, simd_ty: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        if let ty::Adt(def, adt_substs) = simd_ty.kind() {
            if let Some(elem_ty) = adt_substs.first().and_then(|a| a.as_type()) {
                return Some(elem_ty);
            }
            let variant = def.non_enum_variant();
            if let Some(field) = variant.fields.iter().next() {
                let field_ty = field.ty(self.tcx, adt_substs);
                return Some(match field_ty.kind() {
                    ty::Array(elem, _) => *elem,
                    _ => field_ty,
                });
            }
        }
        None
    }

    /// Computes lane count and lane type data used by SIMD cast lowering.
    pub(crate) fn simd_cast_info(&self, simd_ty: ty::Ty<'tcx>) -> Option<SimdCastInfo> {
        let elem_ty = self.simd_elem_ty(simd_ty)?;
        let elem_size = type_size(self.tcx, elem_ty)? as u32;
        let total_size = type_size(self.tcx, simd_ty)? as u32;
        let lanes = total_size / elem_size.max(1);
        let int_ann = match translate_annotation(elem_ty) {
            Some(Annotation::Int(int_ann)) => Some(int_ann),
            _ => None,
        };
        let float_ty = match elem_ty.kind() {
            ty::Float(ty::FloatTy::F16) => Some(FloatType::F16),
            ty::Float(ty::FloatTy::F32) => Some(FloatType::F32),
            ty::Float(ty::FloatTy::F64) => Some(FloatType::F64),
            ty::Float(ty::FloatTy::F128) => Some(FloatType::F128),
            _ => None,
        };
        Some(SimdCastInfo {
            elem_size,
            lanes,
            int_ann,
            float_ty,
        })
    }
}
