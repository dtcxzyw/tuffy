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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:u16 = param 1
// CHECK:     v4: int:u64 = iconst 255
// CHECK:     v5: int:u64 = and v3, v4
// CHECK:     v6: int:u64 = iconst 72340172838076673
// CHECK:     v7: int:u64 = mul v5, v6
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: mem = store.8 v7, v8, v0
// CHECK:     v10: int:u64 = iconst 8
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.8 v7, v11, v9
// CHECK:     v13: int:i64 = load.8 v8, v12
// CHECK:     v14: mem = store.8 v13, v2, v12
// CHECK:     v15: int:i64 = iconst 8
// CHECK:     v16: ptr = ptradd v8, v15
// CHECK:     v17: int:i64 = load.8 v16, v14
// CHECK:     v18: int:i64 = iconst 8
// CHECK:     v19: ptr = ptradd v2, v18
// CHECK:     v20: mem = store.8 v17, v19, v14
// CHECK:     br bb1(v20)
// CHECK:
// CHECK:   bb1(v22: mem):
// CHECK:     v23: int:i64 = iconst 16
// CHECK:     v24: mem = memcopy v1:align8, v2:align8, v23, v22
// CHECK:     ret v1, v24
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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:i64 = iconst 16
// CHECK:     v6: mem = memcopy v4:align8, v3:align8, v5, v0
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16 align 16
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v10:align16, v4:align16, v11, v6
// CHECK:     v13: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_10simd_shift
// CHECK:     v14: mem, v15: int:i64 = call v13(v8, v10), v12 -> int:i64
// CHECK:     br bb1(v14)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:i16 = iconst 4
// CHECK:     v19: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdtKj8_E5splatC$HASH_10simd_shift
// CHECK:     v20: mem, v21: int:i64 = call v19(v9, v18:u16), v17 -> int:i64
// CHECK:     br bb2(v20)
// CHECK:
// CHECK:   bb2(v23: mem):
// CHECK:     v24: ptr = stack_slot 16
// CHECK:     v25: int:u16 = load.2 v8, v23
// CHECK:     v26: int:u16 = load.2 v9, v23
// CHECK:     v27: int:u16 = shl v25, v26
// CHECK:     v28: mem = store.2 v27, v24, v23
// CHECK:     v29: int:u64 = iconst 2
// CHECK:     v30: ptr = ptradd v8, v29
// CHECK:     v31: int:u64 = iconst 2
// CHECK:     v32: ptr = ptradd v9, v31
// CHECK:     v33: int:u64 = iconst 2
// CHECK:     v34: ptr = ptradd v24, v33
// CHECK:     v35: int:u16 = load.2 v30, v28
// CHECK:     v36: int:u16 = load.2 v32, v28
// CHECK:     v37: int:u16 = shl v35, v36
// CHECK:     v38: mem = store.2 v37, v34, v28
// CHECK:     v39: int:u64 = iconst 4
// CHECK:     v40: ptr = ptradd v8, v39
// CHECK:     v41: int:u64 = iconst 4
// CHECK:     v42: ptr = ptradd v9, v41
// CHECK:     v43: int:u64 = iconst 4
// CHECK:     v44: ptr = ptradd v24, v43
// CHECK:     v45: int:u16 = load.2 v40, v38
// CHECK:     v46: int:u16 = load.2 v42, v38
// CHECK:     v47: int:u16 = shl v45, v46
// CHECK:     v48: mem = store.2 v47, v44, v38
// CHECK:     v49: int:u64 = iconst 6
// CHECK:     v50: ptr = ptradd v8, v49
// CHECK:     v51: int:u64 = iconst 6
// CHECK:     v52: ptr = ptradd v9, v51
// CHECK:     v53: int:u64 = iconst 6
// CHECK:     v54: ptr = ptradd v24, v53
// CHECK:     v55: int:u16 = load.2 v50, v48
// CHECK:     v56: int:u16 = load.2 v52, v48
// CHECK:     v57: int:u16 = shl v55, v56
// CHECK:     v58: mem = store.2 v57, v54, v48
// CHECK:     v59: int:u64 = iconst 8
// CHECK:     v60: ptr = ptradd v8, v59
// CHECK:     v61: int:u64 = iconst 8
// CHECK:     v62: ptr = ptradd v9, v61
// CHECK:     v63: int:u64 = iconst 8
// CHECK:     v64: ptr = ptradd v24, v63
// CHECK:     v65: int:u16 = load.2 v60, v58
// CHECK:     v66: int:u16 = load.2 v62, v58
// CHECK:     v67: int:u16 = shl v65, v66
// CHECK:     v68: mem = store.2 v67, v64, v58
// CHECK:     v69: int:u64 = iconst 10
// CHECK:     v70: ptr = ptradd v8, v69
// CHECK:     v71: int:u64 = iconst 10
// CHECK:     v72: ptr = ptradd v9, v71
// CHECK:     v73: int:u64 = iconst 10
// CHECK:     v74: ptr = ptradd v24, v73
// CHECK:     v75: int:u16 = load.2 v70, v68
// CHECK:     v76: int:u16 = load.2 v72, v68
// CHECK:     v77: int:u16 = shl v75, v76
// CHECK:     v78: mem = store.2 v77, v74, v68
// CHECK:     v79: int:u64 = iconst 12
// CHECK:     v80: ptr = ptradd v8, v79
// CHECK:     v81: int:u64 = iconst 12
// CHECK:     v82: ptr = ptradd v9, v81
// CHECK:     v83: int:u64 = iconst 12
// CHECK:     v84: ptr = ptradd v24, v83
// CHECK:     v85: int:u16 = load.2 v80, v78
// CHECK:     v86: int:u16 = load.2 v82, v78
// CHECK:     v87: int:u16 = shl v85, v86
// CHECK:     v88: mem = store.2 v87, v84, v78
// CHECK:     v89: int:u64 = iconst 14
// CHECK:     v90: ptr = ptradd v8, v89
// CHECK:     v91: int:u64 = iconst 14
// CHECK:     v92: ptr = ptradd v9, v91
// CHECK:     v93: int:u64 = iconst 14
// CHECK:     v94: ptr = ptradd v24, v93
// CHECK:     v95: int:u16 = load.2 v90, v88
// CHECK:     v96: int:u16 = load.2 v92, v88
// CHECK:     v97: int:u16 = shl v95, v96
// CHECK:     v98: mem = store.2 v97, v94, v88
// CHECK:     v99: int:i64 = load.8 v24, v98
// CHECK:     v100: mem = store.8 v99, v7, v98
// CHECK:     v101: int:i64 = iconst 8
// CHECK:     v102: ptr = ptradd v24, v101
// CHECK:     v103: int:i64 = load.8 v102, v100
// CHECK:     v104: int:i64 = iconst 8
// CHECK:     v105: ptr = ptradd v7, v104
// CHECK:     v106: mem = store.8 v103, v105, v100
// CHECK:     br bb3(v106)
// CHECK:
// CHECK:   bb3(v108: mem):
// CHECK:     v109: int:i64 = load.8 v7, v108
// CHECK:     v110: mem = store.8 v109, v2, v108
// CHECK:     v111: int:i64 = iconst 8
// CHECK:     v112: ptr = ptradd v7, v111
// CHECK:     v113: int:i64 = load.8 v112, v110
// CHECK:     v114: int:i64 = iconst 8
// CHECK:     v115: ptr = ptradd v2, v114
// CHECK:     v116: mem = store.8 v113, v115, v110
// CHECK:     v117: int:i64 = iconst 16
// CHECK:     v118: mem = memcopy v1:align8, v2:align8, v117, v116
// CHECK:     ret v1, v118
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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:i64 = iconst 16
// CHECK:     v6: mem = memcopy v4:align8, v3:align8, v5, v0
// CHECK:     v7: ptr = stack_slot 16 align 16
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: ptr = stack_slot 16 align 16
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v10:align16, v4:align16, v11, v6
// CHECK:     v13: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_10simd_shift
// CHECK:     v14: mem, v15: int:i64 = call v13(v8, v10), v12 -> int:i64
// CHECK:     br bb1(v14)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:i16 = iconst 3
// CHECK:     v19: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdtKj8_E5splatC$HASH_10simd_shift
// CHECK:     v20: mem, v21: int:i64 = call v19(v9, v18:u16), v17 -> int:i64
// CHECK:     br bb2(v20)
// CHECK:
// CHECK:   bb2(v23: mem):
// CHECK:     v24: ptr = stack_slot 16
// CHECK:     v25: int:u16 = load.2 v8, v23
// CHECK:     v26: int:u16 = load.2 v9, v23
// CHECK:     v27: int:u16 = shr v25, v26
// CHECK:     v28: mem = store.2 v27, v24, v23
// CHECK:     v29: int:u64 = iconst 2
// CHECK:     v30: ptr = ptradd v8, v29
// CHECK:     v31: int:u64 = iconst 2
// CHECK:     v32: ptr = ptradd v9, v31
// CHECK:     v33: int:u64 = iconst 2
// CHECK:     v34: ptr = ptradd v24, v33
// CHECK:     v35: int:u16 = load.2 v30, v28
// CHECK:     v36: int:u16 = load.2 v32, v28
// CHECK:     v37: int:u16 = shr v35, v36
// CHECK:     v38: mem = store.2 v37, v34, v28
// CHECK:     v39: int:u64 = iconst 4
// CHECK:     v40: ptr = ptradd v8, v39
// CHECK:     v41: int:u64 = iconst 4
// CHECK:     v42: ptr = ptradd v9, v41
// CHECK:     v43: int:u64 = iconst 4
// CHECK:     v44: ptr = ptradd v24, v43
// CHECK:     v45: int:u16 = load.2 v40, v38
// CHECK:     v46: int:u16 = load.2 v42, v38
// CHECK:     v47: int:u16 = shr v45, v46
// CHECK:     v48: mem = store.2 v47, v44, v38
// CHECK:     v49: int:u64 = iconst 6
// CHECK:     v50: ptr = ptradd v8, v49
// CHECK:     v51: int:u64 = iconst 6
// CHECK:     v52: ptr = ptradd v9, v51
// CHECK:     v53: int:u64 = iconst 6
// CHECK:     v54: ptr = ptradd v24, v53
// CHECK:     v55: int:u16 = load.2 v50, v48
// CHECK:     v56: int:u16 = load.2 v52, v48
// CHECK:     v57: int:u16 = shr v55, v56
// CHECK:     v58: mem = store.2 v57, v54, v48
// CHECK:     v59: int:u64 = iconst 8
// CHECK:     v60: ptr = ptradd v8, v59
// CHECK:     v61: int:u64 = iconst 8
// CHECK:     v62: ptr = ptradd v9, v61
// CHECK:     v63: int:u64 = iconst 8
// CHECK:     v64: ptr = ptradd v24, v63
// CHECK:     v65: int:u16 = load.2 v60, v58
// CHECK:     v66: int:u16 = load.2 v62, v58
// CHECK:     v67: int:u16 = shr v65, v66
// CHECK:     v68: mem = store.2 v67, v64, v58
// CHECK:     v69: int:u64 = iconst 10
// CHECK:     v70: ptr = ptradd v8, v69
// CHECK:     v71: int:u64 = iconst 10
// CHECK:     v72: ptr = ptradd v9, v71
// CHECK:     v73: int:u64 = iconst 10
// CHECK:     v74: ptr = ptradd v24, v73
// CHECK:     v75: int:u16 = load.2 v70, v68
// CHECK:     v76: int:u16 = load.2 v72, v68
// CHECK:     v77: int:u16 = shr v75, v76
// CHECK:     v78: mem = store.2 v77, v74, v68
// CHECK:     v79: int:u64 = iconst 12
// CHECK:     v80: ptr = ptradd v8, v79
// CHECK:     v81: int:u64 = iconst 12
// CHECK:     v82: ptr = ptradd v9, v81
// CHECK:     v83: int:u64 = iconst 12
// CHECK:     v84: ptr = ptradd v24, v83
// CHECK:     v85: int:u16 = load.2 v80, v78
// CHECK:     v86: int:u16 = load.2 v82, v78
// CHECK:     v87: int:u16 = shr v85, v86
// CHECK:     v88: mem = store.2 v87, v84, v78
// CHECK:     v89: int:u64 = iconst 14
// CHECK:     v90: ptr = ptradd v8, v89
// CHECK:     v91: int:u64 = iconst 14
// CHECK:     v92: ptr = ptradd v9, v91
// CHECK:     v93: int:u64 = iconst 14
// CHECK:     v94: ptr = ptradd v24, v93
// CHECK:     v95: int:u16 = load.2 v90, v88
// CHECK:     v96: int:u16 = load.2 v92, v88
// CHECK:     v97: int:u16 = shr v95, v96
// CHECK:     v98: mem = store.2 v97, v94, v88
// CHECK:     v99: int:i64 = load.8 v24, v98
// CHECK:     v100: mem = store.8 v99, v7, v98
// CHECK:     v101: int:i64 = iconst 8
// CHECK:     v102: ptr = ptradd v24, v101
// CHECK:     v103: int:i64 = load.8 v102, v100
// CHECK:     v104: int:i64 = iconst 8
// CHECK:     v105: ptr = ptradd v7, v104
// CHECK:     v106: mem = store.8 v103, v105, v100
// CHECK:     br bb3(v106)
// CHECK:
// CHECK:   bb3(v108: mem):
// CHECK:     v109: int:i64 = load.8 v7, v108
// CHECK:     v110: mem = store.8 v109, v2, v108
// CHECK:     v111: int:i64 = iconst 8
// CHECK:     v112: ptr = ptradd v7, v111
// CHECK:     v113: int:i64 = load.8 v112, v110
// CHECK:     v114: int:i64 = iconst 8
// CHECK:     v115: ptr = ptradd v2, v114
// CHECK:     v116: mem = store.8 v113, v115, v110
// CHECK:     v117: int:i64 = iconst 16
// CHECK:     v118: mem = memcopy v1:align8, v2:align8, v117, v116
// CHECK:     ret v1, v118
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
