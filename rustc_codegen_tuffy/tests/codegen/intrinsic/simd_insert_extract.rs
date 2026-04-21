// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn core::arch::x86_64::__m128i::as_i32x4(_1: core::arch::x86_64::__m128i) -> core::core_arch::simd::Simd<i32, 4> {
// CHECK:     debug self => _1;
// CHECK:     let mut _0: core::core_arch::simd::Simd<i32, 4>;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as core::core_arch::simd::Simd<i32, 4> (Transmute);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_i32x4C$HASH_19simd_insert_extract(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: mem = memcopy v3:align16, v2:align16, v4, v0
// CHECK:     v6: int:i64 = load.8 v3, v5
// CHECK:     v7: mem = store.8 v6, v1, v5
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v3, v8
// CHECK:     v10: int:i64 = load.8 v9, v7
// CHECK:     v11: int:i64 = iconst 8
// CHECK:     v12: ptr = ptradd v1, v11
// CHECK:     v13: mem = store.8 v10, v12, v7
// CHECK:     ret v1, v13
// CHECK: }
// CHECK:
// CHECK: fn extract_low_word(_1: core::arch::x86_64::__m128i) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i32;
// CHECK:     scope 1 (inlined core::arch::x86_64::_mm_cvtsi128_si32) {
// CHECK:         let mut _2: core::core_arch::simd::Simd<i32, 4>;
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _2 = core::arch::x86_64::__m128i::as_i32x4(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = core::intrinsics::simd::simd_extract::<core::core_arch::simd::Simd<i32, 4>, i32>(move _2, const 0_u32) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @extract_low_word(ptr) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i64 = iconst 16
// CHECK:     v4: mem = memcopy v2:align16, v1:align16, v3, v0
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: int:i64 = iconst 16
// CHECK:     v8: mem = memcopy v6:align16, v2:align16, v7, v4
// CHECK:     v9: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_i32x4C$HASH_19simd_insert_extract
// CHECK:     v10: mem, v11: int:i64 = call v9(v5, v6), v8 -> int:i64
// CHECK:     br bb1(v10)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: int:i32 = iconst 0
// CHECK:     v15: int:u64 = iconst 4
// CHECK:     v16: int:i64 = mul v14, v15
// CHECK:     v17: ptr = ptradd v5, v16
// CHECK:     v18: int:s32 = load.4 v17, v13
// CHECK:     br bb2(v13)
// CHECK:
// CHECK:   bb2(v20: mem):
// CHECK:     ret v18, v20
// CHECK: }
// CHECK:
// CHECK: fn insert_word(_1: core::arch::x86_64::__m128i, _2: i32) -> core::arch::x86_64::__m128i {
// CHECK:     debug a => _1;
// CHECK:     debug value => _2;
// CHECK:     let mut _0: core::arch::x86_64::__m128i;
// CHECK:     scope 1 (inlined core::arch::x86_64::_mm_insert_epi32::<0>) {
// CHECK:         let mut _3: core::core_arch::simd::Simd<i32, 4>;
// CHECK:         let mut _4: core::core_arch::simd::Simd<i32, 4>;
// CHECK:         scope 2 {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _4 = core::arch::x86_64::__m128i::as_i32x4(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = core::intrinsics::simd::simd_insert::<core::core_arch::simd::Simd<i32, 4>, i32>(move _4, const 0_u32, move _2) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = move _3 as core::arch::x86_64::__m128i (Transmute);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @insert_word(ptr, ptr, int:s32) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:s32 = param 2
// CHECK:     v5: int:i64 = iconst 16
// CHECK:     v6: mem = memcopy v3:align16, v2:align16, v5, v0
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: int:i64 = iconst 16
// CHECK:     v11: mem = memcopy v9:align16, v3:align16, v10, v6
// CHECK:     v12: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_i32x4C$HASH_19simd_insert_extract
// CHECK:     v13: mem, v14: int:i64 = call v12(v8, v9), v11 -> int:i64
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i32 = iconst 0
// CHECK:     v18: ptr = stack_slot 16
// CHECK:     v19: int:i64 = load.8 v8, v16
// CHECK:     v20: mem = store.8 v19, v18, v16
// CHECK:     v21: int:u64 = iconst 8
// CHECK:     v22: ptr = ptradd v8, v21
// CHECK:     v23: int:u64 = iconst 8
// CHECK:     v24: ptr = ptradd v18, v23
// CHECK:     v25: int:i64 = load.8 v22, v20
// CHECK:     v26: mem = store.8 v25, v24, v20
// CHECK:     v27: int:u64 = iconst 4
// CHECK:     v28: int:i64 = mul v17, v27
// CHECK:     v29: ptr = ptradd v18, v28
// CHECK:     v30: mem = store.4 v4, v29, v26
// CHECK:     v31: int:i64 = load.8 v18, v30
// CHECK:     v32: mem = store.8 v31, v7, v30
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v18, v33
// CHECK:     v35: int:i64 = load.8 v34, v32
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v7, v36
// CHECK:     v38: mem = store.8 v35, v37, v32
// CHECK:     br bb2(v38)
// CHECK:
// CHECK:   bb2(v40: mem):
// CHECK:     v41: int:i64 = load.8 v7, v40
// CHECK:     v42: mem = store.8 v41, v1, v40
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v7, v43
// CHECK:     v45: int:i64 = load.8 v44, v42
// CHECK:     v46: int:i64 = iconst 8
// CHECK:     v47: ptr = ptradd v1, v46
// CHECK:     v48: mem = store.8 v45, v47, v42
// CHECK:     ret v1, v48
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::arch::x86_64::{__m128i, _mm_cvtsi128_si32, _mm_insert_epi32};

#[no_mangle]
#[target_feature(enable = "sse4.1")]
pub unsafe fn insert_word(a: __m128i, value: i32) -> __m128i {
    _mm_insert_epi32::<0>(a, value)
}

#[no_mangle]
#[target_feature(enable = "sse2")]
pub unsafe fn extract_low_word(a: __m128i) -> i32 {
    _mm_cvtsi128_si32(a)
}
