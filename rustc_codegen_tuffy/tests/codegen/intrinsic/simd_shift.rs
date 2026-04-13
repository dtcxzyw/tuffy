// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn core::arch::x86_64::__m128i::as_u16x8(_1: core::arch::x86_64::__m128i) -> core::core_arch::simd::Simd<u16, 8> {
// CHECK:     debug self => _1;
// CHECK:     let mut _0: core::core_arch::simd::Simd<u16, 8>;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as core::core_arch::simd::Simd<u16, 8> (Transmute);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_10simd_shift(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: mem = memcopy v3:align8, v2:align8, v4, v0
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
// CHECK: fn core::core_arch::simd::Simd::<T, N>::splat(_1: T) -> core::core_arch::simd::Simd<T, N> {
// CHECK:     debug value => _1;
// CHECK:     let mut _0: core::core_arch::simd::Simd<T, N>;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::simd::simd_splat::<core::core_arch::simd::Simd<T, N>, T>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdtKj8_E5splatC$HASH_10simd_shift(ptr, int:u16) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u16 = param 1
// CHECK:     v3: int:u64 = iconst 255
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int:u64 = iconst 72340172838076673
// CHECK:     v6: int:u64 = mul v4, v5
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: mem = store.8 v6, v7, v0
// CHECK:     v9: int:u64 = iconst 8
// CHECK:     v10: ptr = ptradd v7, v9
// CHECK:     v11: mem = store.8 v6, v10, v8
// CHECK:     v12: int:i64 = load.8 v7, v11
// CHECK:     v13: mem = store.8 v12, v1, v11
// CHECK:     v14: int:i64 = iconst 8
// CHECK:     v15: ptr = ptradd v7, v14
// CHECK:     v16: int:i64 = load.8 v15, v13
// CHECK:     v17: int:i64 = iconst 8
// CHECK:     v18: ptr = ptradd v1, v17
// CHECK:     v19: mem = store.8 v16, v18, v13
// CHECK:     br bb1(v19)
// CHECK:
// CHECK:   bb1(v21: mem):
// CHECK:     ret v1, v21
// CHECK: }
// CHECK:
// CHECK: fn shift_left_words(_1: core::arch::x86_64::__m128i) -> core::arch::x86_64::__m128i {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: core::arch::x86_64::__m128i;
// CHECK:     scope 1 (inlined core::arch::x86_64::_mm_slli_epi16::<4>) {
// CHECK:         let mut _2: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         let mut _3: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         let mut _4: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         scope 2 {
// CHECK:         }
// CHECK:         scope 3 (inlined core::arch::x86_64::_mm_setzero_si128) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = core::arch::x86_64::__m128i::as_u16x8(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _4 = core::core_arch::simd::Simd::<u16, 8>::splat(const 4_u16) -> [return: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _2 = core::intrinsics::simd::simd_shl::<core::core_arch::simd::Simd<u16, 8>>(move _3, move _4) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = move _2 as core::arch::x86_64::__m128i (Transmute);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shift_left_words(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: mem = memcopy v3:align8, v2:align8, v4, v0
// CHECK:     v6: ptr = stack_slot 16 align 16
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: int:i64 = iconst 16
// CHECK:     v11: mem = memcopy v9:align16, v3:align16, v10, v5
// CHECK:     v12: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_10simd_shift
// CHECK:     v13: mem, v14: int:i64 = call v12(v7, v9), v11 -> int:i64
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i16 = iconst 4
// CHECK:     v18: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdtKj8_E5splatC$HASH_10simd_shift
// CHECK:     v19: mem, v20: int:i64 = call v18(v8, v17:u16), v16 -> int:i64
// CHECK:     br bb2(v19)
// CHECK:
// CHECK:   bb2(v22: mem):
// CHECK:     v23: ptr = stack_slot 16
// CHECK:     v24: int:u16 = load.2 v7, v22
// CHECK:     v25: int:u16 = load.2 v8, v22
// CHECK:     v26: int:u16 = shl v24, v25
// CHECK:     v27: mem = store.2 v26, v23, v22
// CHECK:     v28: int:u64 = iconst 2
// CHECK:     v29: ptr = ptradd v7, v28
// CHECK:     v30: int:u64 = iconst 2
// CHECK:     v31: ptr = ptradd v8, v30
// CHECK:     v32: int:u64 = iconst 2
// CHECK:     v33: ptr = ptradd v23, v32
// CHECK:     v34: int:u16 = load.2 v29, v27
// CHECK:     v35: int:u16 = load.2 v31, v27
// CHECK:     v36: int:u16 = shl v34, v35
// CHECK:     v37: mem = store.2 v36, v33, v27
// CHECK:     v38: int:u64 = iconst 4
// CHECK:     v39: ptr = ptradd v7, v38
// CHECK:     v40: int:u64 = iconst 4
// CHECK:     v41: ptr = ptradd v8, v40
// CHECK:     v42: int:u64 = iconst 4
// CHECK:     v43: ptr = ptradd v23, v42
// CHECK:     v44: int:u16 = load.2 v39, v37
// CHECK:     v45: int:u16 = load.2 v41, v37
// CHECK:     v46: int:u16 = shl v44, v45
// CHECK:     v47: mem = store.2 v46, v43, v37
// CHECK:     v48: int:u64 = iconst 6
// CHECK:     v49: ptr = ptradd v7, v48
// CHECK:     v50: int:u64 = iconst 6
// CHECK:     v51: ptr = ptradd v8, v50
// CHECK:     v52: int:u64 = iconst 6
// CHECK:     v53: ptr = ptradd v23, v52
// CHECK:     v54: int:u16 = load.2 v49, v47
// CHECK:     v55: int:u16 = load.2 v51, v47
// CHECK:     v56: int:u16 = shl v54, v55
// CHECK:     v57: mem = store.2 v56, v53, v47
// CHECK:     v58: int:u64 = iconst 8
// CHECK:     v59: ptr = ptradd v7, v58
// CHECK:     v60: int:u64 = iconst 8
// CHECK:     v61: ptr = ptradd v8, v60
// CHECK:     v62: int:u64 = iconst 8
// CHECK:     v63: ptr = ptradd v23, v62
// CHECK:     v64: int:u16 = load.2 v59, v57
// CHECK:     v65: int:u16 = load.2 v61, v57
// CHECK:     v66: int:u16 = shl v64, v65
// CHECK:     v67: mem = store.2 v66, v63, v57
// CHECK:     v68: int:u64 = iconst 10
// CHECK:     v69: ptr = ptradd v7, v68
// CHECK:     v70: int:u64 = iconst 10
// CHECK:     v71: ptr = ptradd v8, v70
// CHECK:     v72: int:u64 = iconst 10
// CHECK:     v73: ptr = ptradd v23, v72
// CHECK:     v74: int:u16 = load.2 v69, v67
// CHECK:     v75: int:u16 = load.2 v71, v67
// CHECK:     v76: int:u16 = shl v74, v75
// CHECK:     v77: mem = store.2 v76, v73, v67
// CHECK:     v78: int:u64 = iconst 12
// CHECK:     v79: ptr = ptradd v7, v78
// CHECK:     v80: int:u64 = iconst 12
// CHECK:     v81: ptr = ptradd v8, v80
// CHECK:     v82: int:u64 = iconst 12
// CHECK:     v83: ptr = ptradd v23, v82
// CHECK:     v84: int:u16 = load.2 v79, v77
// CHECK:     v85: int:u16 = load.2 v81, v77
// CHECK:     v86: int:u16 = shl v84, v85
// CHECK:     v87: mem = store.2 v86, v83, v77
// CHECK:     v88: int:u64 = iconst 14
// CHECK:     v89: ptr = ptradd v7, v88
// CHECK:     v90: int:u64 = iconst 14
// CHECK:     v91: ptr = ptradd v8, v90
// CHECK:     v92: int:u64 = iconst 14
// CHECK:     v93: ptr = ptradd v23, v92
// CHECK:     v94: int:u16 = load.2 v89, v87
// CHECK:     v95: int:u16 = load.2 v91, v87
// CHECK:     v96: int:u16 = shl v94, v95
// CHECK:     v97: mem = store.2 v96, v93, v87
// CHECK:     v98: int:i64 = load.8 v23, v97
// CHECK:     v99: mem = store.8 v98, v6, v97
// CHECK:     v100: int:i64 = iconst 8
// CHECK:     v101: ptr = ptradd v23, v100
// CHECK:     v102: int:i64 = load.8 v101, v99
// CHECK:     v103: int:i64 = iconst 8
// CHECK:     v104: ptr = ptradd v6, v103
// CHECK:     v105: mem = store.8 v102, v104, v99
// CHECK:     br bb3(v105)
// CHECK:
// CHECK:   bb3(v107: mem):
// CHECK:     v108: int:i64 = load.8 v6, v107
// CHECK:     v109: mem = store.8 v108, v1, v107
// CHECK:     v110: int:i64 = iconst 8
// CHECK:     v111: ptr = ptradd v6, v110
// CHECK:     v112: int:i64 = load.8 v111, v109
// CHECK:     v113: int:i64 = iconst 8
// CHECK:     v114: ptr = ptradd v1, v113
// CHECK:     v115: mem = store.8 v112, v114, v109
// CHECK:     ret v1, v115
// CHECK: }
// CHECK:
// CHECK: fn shift_right_words(_1: core::arch::x86_64::__m128i) -> core::arch::x86_64::__m128i {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: core::arch::x86_64::__m128i;
// CHECK:     scope 1 (inlined core::arch::x86_64::_mm_srli_epi16::<3>) {
// CHECK:         let mut _2: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         let mut _3: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         let mut _4: core::core_arch::simd::Simd<u16, 8>;
// CHECK:         scope 2 {
// CHECK:         }
// CHECK:         scope 3 (inlined core::arch::x86_64::_mm_setzero_si128) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = core::arch::x86_64::__m128i::as_u16x8(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _4 = core::core_arch::simd::Simd::<u16, 8>::splat(const 3_u16) -> [return: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _2 = core::intrinsics::simd::simd_shr::<core::core_arch::simd::Simd<u16, 8>>(move _3, move _4) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = move _2 as core::arch::x86_64::__m128i (Transmute);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shift_right_words(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: mem = memcopy v3:align8, v2:align8, v4, v0
// CHECK:     v6: ptr = stack_slot 16 align 16
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: int:i64 = iconst 16
// CHECK:     v11: mem = memcopy v9:align16, v3:align16, v10, v5
// CHECK:     v12: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_10simd_shift
// CHECK:     v13: mem, v14: int:i64 = call v12(v7, v9), v11 -> int:i64
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i16 = iconst 3
// CHECK:     v18: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdtKj8_E5splatC$HASH_10simd_shift
// CHECK:     v19: mem, v20: int:i64 = call v18(v8, v17:u16), v16 -> int:i64
// CHECK:     br bb2(v19)
// CHECK:
// CHECK:   bb2(v22: mem):
// CHECK:     v23: ptr = stack_slot 16
// CHECK:     v24: int:u16 = load.2 v7, v22
// CHECK:     v25: int:u16 = load.2 v8, v22
// CHECK:     v26: int:u16 = shr v24, v25
// CHECK:     v27: mem = store.2 v26, v23, v22
// CHECK:     v28: int:u64 = iconst 2
// CHECK:     v29: ptr = ptradd v7, v28
// CHECK:     v30: int:u64 = iconst 2
// CHECK:     v31: ptr = ptradd v8, v30
// CHECK:     v32: int:u64 = iconst 2
// CHECK:     v33: ptr = ptradd v23, v32
// CHECK:     v34: int:u16 = load.2 v29, v27
// CHECK:     v35: int:u16 = load.2 v31, v27
// CHECK:     v36: int:u16 = shr v34, v35
// CHECK:     v37: mem = store.2 v36, v33, v27
// CHECK:     v38: int:u64 = iconst 4
// CHECK:     v39: ptr = ptradd v7, v38
// CHECK:     v40: int:u64 = iconst 4
// CHECK:     v41: ptr = ptradd v8, v40
// CHECK:     v42: int:u64 = iconst 4
// CHECK:     v43: ptr = ptradd v23, v42
// CHECK:     v44: int:u16 = load.2 v39, v37
// CHECK:     v45: int:u16 = load.2 v41, v37
// CHECK:     v46: int:u16 = shr v44, v45
// CHECK:     v47: mem = store.2 v46, v43, v37
// CHECK:     v48: int:u64 = iconst 6
// CHECK:     v49: ptr = ptradd v7, v48
// CHECK:     v50: int:u64 = iconst 6
// CHECK:     v51: ptr = ptradd v8, v50
// CHECK:     v52: int:u64 = iconst 6
// CHECK:     v53: ptr = ptradd v23, v52
// CHECK:     v54: int:u16 = load.2 v49, v47
// CHECK:     v55: int:u16 = load.2 v51, v47
// CHECK:     v56: int:u16 = shr v54, v55
// CHECK:     v57: mem = store.2 v56, v53, v47
// CHECK:     v58: int:u64 = iconst 8
// CHECK:     v59: ptr = ptradd v7, v58
// CHECK:     v60: int:u64 = iconst 8
// CHECK:     v61: ptr = ptradd v8, v60
// CHECK:     v62: int:u64 = iconst 8
// CHECK:     v63: ptr = ptradd v23, v62
// CHECK:     v64: int:u16 = load.2 v59, v57
// CHECK:     v65: int:u16 = load.2 v61, v57
// CHECK:     v66: int:u16 = shr v64, v65
// CHECK:     v67: mem = store.2 v66, v63, v57
// CHECK:     v68: int:u64 = iconst 10
// CHECK:     v69: ptr = ptradd v7, v68
// CHECK:     v70: int:u64 = iconst 10
// CHECK:     v71: ptr = ptradd v8, v70
// CHECK:     v72: int:u64 = iconst 10
// CHECK:     v73: ptr = ptradd v23, v72
// CHECK:     v74: int:u16 = load.2 v69, v67
// CHECK:     v75: int:u16 = load.2 v71, v67
// CHECK:     v76: int:u16 = shr v74, v75
// CHECK:     v77: mem = store.2 v76, v73, v67
// CHECK:     v78: int:u64 = iconst 12
// CHECK:     v79: ptr = ptradd v7, v78
// CHECK:     v80: int:u64 = iconst 12
// CHECK:     v81: ptr = ptradd v8, v80
// CHECK:     v82: int:u64 = iconst 12
// CHECK:     v83: ptr = ptradd v23, v82
// CHECK:     v84: int:u16 = load.2 v79, v77
// CHECK:     v85: int:u16 = load.2 v81, v77
// CHECK:     v86: int:u16 = shr v84, v85
// CHECK:     v87: mem = store.2 v86, v83, v77
// CHECK:     v88: int:u64 = iconst 14
// CHECK:     v89: ptr = ptradd v7, v88
// CHECK:     v90: int:u64 = iconst 14
// CHECK:     v91: ptr = ptradd v8, v90
// CHECK:     v92: int:u64 = iconst 14
// CHECK:     v93: ptr = ptradd v23, v92
// CHECK:     v94: int:u16 = load.2 v89, v87
// CHECK:     v95: int:u16 = load.2 v91, v87
// CHECK:     v96: int:u16 = shr v94, v95
// CHECK:     v97: mem = store.2 v96, v93, v87
// CHECK:     v98: int:i64 = load.8 v23, v97
// CHECK:     v99: mem = store.8 v98, v6, v97
// CHECK:     v100: int:i64 = iconst 8
// CHECK:     v101: ptr = ptradd v23, v100
// CHECK:     v102: int:i64 = load.8 v101, v99
// CHECK:     v103: int:i64 = iconst 8
// CHECK:     v104: ptr = ptradd v6, v103
// CHECK:     v105: mem = store.8 v102, v104, v99
// CHECK:     br bb3(v105)
// CHECK:
// CHECK:   bb3(v107: mem):
// CHECK:     v108: int:i64 = load.8 v6, v107
// CHECK:     v109: mem = store.8 v108, v1, v107
// CHECK:     v110: int:i64 = iconst 8
// CHECK:     v111: ptr = ptradd v6, v110
// CHECK:     v112: int:i64 = load.8 v111, v109
// CHECK:     v113: int:i64 = iconst 8
// CHECK:     v114: ptr = ptradd v1, v113
// CHECK:     v115: mem = store.8 v112, v114, v109
// CHECK:     ret v1, v115
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::arch::x86_64::{__m128i, _mm_slli_epi16, _mm_srli_epi16};

#[no_mangle]
#[target_feature(enable = "sse2")]
pub unsafe fn shift_left_words(a: __m128i) -> __m128i {
    _mm_slli_epi16::<4>(a)
}

#[no_mangle]
#[target_feature(enable = "sse2")]
pub unsafe fn shift_right_words(a: __m128i) -> __m128i {
    _mm_srli_epi16::<3>(a)
}
