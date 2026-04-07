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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:i64 = iconst 16
// CHECK:     v6: mem = memcopy v4:align8, v3:align8, v5, v0
// CHECK:     v7: int:i64 = load.8 v4, v6
// CHECK:     v8: mem = store.8 v7, v2, v6
// CHECK:     v9: int:i64 = iconst 8
// CHECK:     v10: ptr = ptradd v4, v9
// CHECK:     v11: int:i64 = load.8 v10, v8
// CHECK:     v12: int:i64 = iconst 8
// CHECK:     v13: ptr = ptradd v2, v12
// CHECK:     v14: mem = store.8 v11, v13, v8
// CHECK:     v15: int:i64 = iconst 16
// CHECK:     v16: mem = memcopy v1:align8, v2:align8, v15, v14
// CHECK:     ret v1, v16
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
// CHECK:     v4: mem = memcopy v2:align8, v1:align8, v3, v0
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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:s32 = param 2
// CHECK:     v6: int:i64 = iconst 16
// CHECK:     v7: mem = memcopy v4:align8, v3:align8, v6, v0
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16 align 16
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v10:align16, v4:align16, v11, v7
// CHECK:     v13: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_i32x4C$HASH_19simd_insert_extract
// CHECK:     v14: mem, v15: int:i64 = call v13(v9, v10), v12 -> int:i64
// CHECK:     br bb1(v14)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:i32 = iconst 0
// CHECK:     v19: ptr = stack_slot 16
// CHECK:     v20: int:i64 = load.8 v9, v17
// CHECK:     v21: mem = store.8 v20, v19, v17
// CHECK:     v22: int:u64 = iconst 8
// CHECK:     v23: ptr = ptradd v9, v22
// CHECK:     v24: int:u64 = iconst 8
// CHECK:     v25: ptr = ptradd v19, v24
// CHECK:     v26: int:i64 = load.8 v23, v21
// CHECK:     v27: mem = store.8 v26, v25, v21
// CHECK:     v28: int:u64 = iconst 4
// CHECK:     v29: int:i64 = mul v18, v28
// CHECK:     v30: ptr = ptradd v19, v29
// CHECK:     v31: mem = store.4 v5, v30, v27
// CHECK:     v32: int:i64 = load.8 v19, v31
// CHECK:     v33: mem = store.8 v32, v8, v31
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v19, v34
// CHECK:     v36: int:i64 = load.8 v35, v33
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v8, v37
// CHECK:     v39: mem = store.8 v36, v38, v33
// CHECK:     br bb2(v39)
// CHECK:
// CHECK:   bb2(v41: mem):
// CHECK:     v42: int:i64 = load.8 v8, v41
// CHECK:     v43: mem = store.8 v42, v2, v41
// CHECK:     v44: int:i64 = iconst 8
// CHECK:     v45: ptr = ptradd v8, v44
// CHECK:     v46: int:i64 = load.8 v45, v43
// CHECK:     v47: int:i64 = iconst 8
// CHECK:     v48: ptr = ptradd v2, v47
// CHECK:     v49: mem = store.8 v46, v48, v43
// CHECK:     v50: int:i64 = iconst 16
// CHECK:     v51: mem = memcopy v1:align8, v2:align8, v50, v49
// CHECK:     ret v1, v51
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
