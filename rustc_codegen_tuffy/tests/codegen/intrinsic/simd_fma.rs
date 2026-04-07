// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn fmadd_ps(_1: core::arch::x86_64::__m128, _2: core::arch::x86_64::__m128, _3: core::arch::x86_64::__m128) -> core::arch::x86_64::__m128 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug c => _3;
// CHECK:     let mut _0: core::arch::x86_64::__m128;
// CHECK:     scope 1 (inlined core::arch::x86_64::_mm_fmadd_ps) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::simd::simd_fma::<core::arch::x86_64::__m128>(move _1, move _2, move _3) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @fmadd_ps(ptr, ptr, ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: ptr = param 2
// CHECK:     v6: ptr = stack_slot 16 align 16
// CHECK:     v7: ptr = param 3
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: int:i64 = iconst 16
// CHECK:     v10: mem = memcopy v4:align8, v3:align8, v9, v0
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v6:align8, v5:align8, v11, v10
// CHECK:     v13: int:i64 = iconst 16
// CHECK:     v14: mem = memcopy v8:align8, v7:align8, v13, v12
// CHECK:     v15: ptr = stack_slot 16
// CHECK:     v16: f32 = load.4 v4, v14
// CHECK:     v17: f32 = load.4 v6, v14
// CHECK:     v18: f32 = load.4 v8, v14
// CHECK:     v19: f32 = fmul v16, v17
// CHECK:     v20: f32 = fadd v19, v18
// CHECK:     v21: mem = store.4 v20, v15, v14
// CHECK:     v22: int:u64 = iconst 4
// CHECK:     v23: ptr = ptradd v4, v22
// CHECK:     v24: int:u64 = iconst 4
// CHECK:     v25: ptr = ptradd v6, v24
// CHECK:     v26: int:u64 = iconst 4
// CHECK:     v27: ptr = ptradd v8, v26
// CHECK:     v28: int:u64 = iconst 4
// CHECK:     v29: ptr = ptradd v15, v28
// CHECK:     v30: f32 = load.4 v23, v21
// CHECK:     v31: f32 = load.4 v25, v21
// CHECK:     v32: f32 = load.4 v27, v21
// CHECK:     v33: f32 = fmul v30, v31
// CHECK:     v34: f32 = fadd v33, v32
// CHECK:     v35: mem = store.4 v34, v29, v21
// CHECK:     v36: int:u64 = iconst 8
// CHECK:     v37: ptr = ptradd v4, v36
// CHECK:     v38: int:u64 = iconst 8
// CHECK:     v39: ptr = ptradd v6, v38
// CHECK:     v40: int:u64 = iconst 8
// CHECK:     v41: ptr = ptradd v8, v40
// CHECK:     v42: int:u64 = iconst 8
// CHECK:     v43: ptr = ptradd v15, v42
// CHECK:     v44: f32 = load.4 v37, v35
// CHECK:     v45: f32 = load.4 v39, v35
// CHECK:     v46: f32 = load.4 v41, v35
// CHECK:     v47: f32 = fmul v44, v45
// CHECK:     v48: f32 = fadd v47, v46
// CHECK:     v49: mem = store.4 v48, v43, v35
// CHECK:     v50: int:u64 = iconst 12
// CHECK:     v51: ptr = ptradd v4, v50
// CHECK:     v52: int:u64 = iconst 12
// CHECK:     v53: ptr = ptradd v6, v52
// CHECK:     v54: int:u64 = iconst 12
// CHECK:     v55: ptr = ptradd v8, v54
// CHECK:     v56: int:u64 = iconst 12
// CHECK:     v57: ptr = ptradd v15, v56
// CHECK:     v58: f32 = load.4 v51, v49
// CHECK:     v59: f32 = load.4 v53, v49
// CHECK:     v60: f32 = load.4 v55, v49
// CHECK:     v61: f32 = fmul v58, v59
// CHECK:     v62: f32 = fadd v61, v60
// CHECK:     v63: mem = store.4 v62, v57, v49
// CHECK:     v64: int:i64 = load.8 v15, v63
// CHECK:     v65: mem = store.8 v64, v2, v63
// CHECK:     v66: int:i64 = iconst 8
// CHECK:     v67: ptr = ptradd v15, v66
// CHECK:     v68: int:i64 = load.8 v67, v65
// CHECK:     v69: int:i64 = iconst 8
// CHECK:     v70: ptr = ptradd v2, v69
// CHECK:     v71: mem = store.8 v68, v70, v65
// CHECK:     br bb1(v71)
// CHECK:
// CHECK:   bb1(v73: mem):
// CHECK:     v74: int:i64 = iconst 16
// CHECK:     v75: mem = memcopy v1:align8, v2:align8, v74, v73
// CHECK:     ret v1, v75
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::arch::x86_64::{__m128, _mm_fmadd_ps};

#[no_mangle]
#[target_feature(enable = "fma")]
pub unsafe fn fmadd_ps(a: __m128, b: __m128, c: __m128) -> __m128 {
    _mm_fmadd_ps(a, b, c)
}
