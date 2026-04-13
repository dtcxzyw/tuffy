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
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: ptr = param 2
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: ptr = param 3
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: int:i64 = iconst 16
// CHECK:     v9: mem = memcopy v3:align8, v2:align8, v8, v0
// CHECK:     v10: int:i64 = iconst 16
// CHECK:     v11: mem = memcopy v5:align8, v4:align8, v10, v9
// CHECK:     v12: int:i64 = iconst 16
// CHECK:     v13: mem = memcopy v7:align8, v6:align8, v12, v11
// CHECK:     v14: ptr = stack_slot 16
// CHECK:     v15: f32 = load.4 v3, v13
// CHECK:     v16: f32 = load.4 v5, v13
// CHECK:     v17: f32 = load.4 v7, v13
// CHECK:     v18: f32 = fmul v15, v16
// CHECK:     v19: f32 = fadd v18, v17
// CHECK:     v20: mem = store.4 v19, v14, v13
// CHECK:     v21: int:u64 = iconst 4
// CHECK:     v22: ptr = ptradd v3, v21
// CHECK:     v23: int:u64 = iconst 4
// CHECK:     v24: ptr = ptradd v5, v23
// CHECK:     v25: int:u64 = iconst 4
// CHECK:     v26: ptr = ptradd v7, v25
// CHECK:     v27: int:u64 = iconst 4
// CHECK:     v28: ptr = ptradd v14, v27
// CHECK:     v29: f32 = load.4 v22, v20
// CHECK:     v30: f32 = load.4 v24, v20
// CHECK:     v31: f32 = load.4 v26, v20
// CHECK:     v32: f32 = fmul v29, v30
// CHECK:     v33: f32 = fadd v32, v31
// CHECK:     v34: mem = store.4 v33, v28, v20
// CHECK:     v35: int:u64 = iconst 8
// CHECK:     v36: ptr = ptradd v3, v35
// CHECK:     v37: int:u64 = iconst 8
// CHECK:     v38: ptr = ptradd v5, v37
// CHECK:     v39: int:u64 = iconst 8
// CHECK:     v40: ptr = ptradd v7, v39
// CHECK:     v41: int:u64 = iconst 8
// CHECK:     v42: ptr = ptradd v14, v41
// CHECK:     v43: f32 = load.4 v36, v34
// CHECK:     v44: f32 = load.4 v38, v34
// CHECK:     v45: f32 = load.4 v40, v34
// CHECK:     v46: f32 = fmul v43, v44
// CHECK:     v47: f32 = fadd v46, v45
// CHECK:     v48: mem = store.4 v47, v42, v34
// CHECK:     v49: int:u64 = iconst 12
// CHECK:     v50: ptr = ptradd v3, v49
// CHECK:     v51: int:u64 = iconst 12
// CHECK:     v52: ptr = ptradd v5, v51
// CHECK:     v53: int:u64 = iconst 12
// CHECK:     v54: ptr = ptradd v7, v53
// CHECK:     v55: int:u64 = iconst 12
// CHECK:     v56: ptr = ptradd v14, v55
// CHECK:     v57: f32 = load.4 v50, v48
// CHECK:     v58: f32 = load.4 v52, v48
// CHECK:     v59: f32 = load.4 v54, v48
// CHECK:     v60: f32 = fmul v57, v58
// CHECK:     v61: f32 = fadd v60, v59
// CHECK:     v62: mem = store.4 v61, v56, v48
// CHECK:     v63: int:i64 = load.8 v14, v62
// CHECK:     v64: mem = store.8 v63, v1, v62
// CHECK:     v65: int:i64 = iconst 8
// CHECK:     v66: ptr = ptradd v14, v65
// CHECK:     v67: int:i64 = load.8 v66, v64
// CHECK:     v68: int:i64 = iconst 8
// CHECK:     v69: ptr = ptradd v1, v68
// CHECK:     v70: mem = store.8 v67, v69, v64
// CHECK:     br bb1(v70)
// CHECK:
// CHECK:   bb1(v72: mem):
// CHECK:     ret v1, v72
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
