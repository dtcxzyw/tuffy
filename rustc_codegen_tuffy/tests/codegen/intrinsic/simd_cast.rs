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
// CHECK: func @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_9simd_cast(ptr, ptr) -> ptr {
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
// CHECK: func @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdmKj8_E5splatC$HASH_9simd_cast(ptr, int:u32) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u64 = iconst 255
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int:u64 = iconst 72340172838076673
// CHECK:     v6: int:u64 = mul v4, v5
// CHECK:     v7: ptr = stack_slot 32
// CHECK:     v8: mem = store.8 v6, v7, v0
// CHECK:     v9: int:u64 = iconst 8
// CHECK:     v10: ptr = ptradd v7, v9
// CHECK:     v11: mem = store.8 v6, v10, v8
// CHECK:     v12: int:u64 = iconst 16
// CHECK:     v13: ptr = ptradd v7, v12
// CHECK:     v14: mem = store.8 v6, v13, v11
// CHECK:     v15: int:u64 = iconst 24
// CHECK:     v16: ptr = ptradd v7, v15
// CHECK:     v17: mem = store.8 v6, v16, v14
// CHECK:     v18: int:i64 = load.8 v7, v17
// CHECK:     v19: mem = store.8 v18, v1, v17
// CHECK:     v20: int:i64 = iconst 8
// CHECK:     v21: ptr = ptradd v7, v20
// CHECK:     v22: int:i64 = load.8 v21, v19
// CHECK:     v23: int:i64 = iconst 8
// CHECK:     v24: ptr = ptradd v1, v23
// CHECK:     v25: mem = store.8 v22, v24, v19
// CHECK:     v26: int:i64 = iconst 16
// CHECK:     v27: ptr = ptradd v7, v26
// CHECK:     v28: int:i64 = load.8 v27, v25
// CHECK:     v29: int:i64 = iconst 16
// CHECK:     v30: ptr = ptradd v1, v29
// CHECK:     v31: mem = store.8 v28, v30, v25
// CHECK:     v32: int:i64 = iconst 24
// CHECK:     v33: ptr = ptradd v7, v32
// CHECK:     v34: int:i64 = load.8 v33, v31
// CHECK:     v35: int:i64 = iconst 24
// CHECK:     v36: ptr = ptradd v1, v35
// CHECK:     v37: mem = store.8 v34, v36, v31
// CHECK:     br bb1(v37)
// CHECK:
// CHECK:   bb1(v39: mem):
// CHECK:     ret v1, v39
// CHECK: }
// CHECK:
// CHECK: fn core::arch::x86_64::_mm_mulhi_epu16(_1: core::arch::x86_64::__m128i, _2: core::arch::x86_64::__m128i) -> core::arch::x86_64::__m128i {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: core::arch::x86_64::__m128i;
// CHECK:     let _3: core::core_arch::simd::Simd<u32, 8>;
// CHECK:     let mut _4: core::core_arch::simd::Simd<u16, 8>;
// CHECK:     let mut _6: core::core_arch::simd::Simd<u16, 8>;
// CHECK:     let mut _8: core::core_arch::simd::Simd<u32, 8>;
// CHECK:     let mut _9: core::core_arch::simd::Simd<u32, 8>;
// CHECK:     let mut _10: core::core_arch::simd::Simd<u16, 8>;
// CHECK:     scope 1 {
// CHECK:         debug a => _3;
// CHECK:         let _5: core::core_arch::simd::Simd<u32, 8>;
// CHECK:         scope 2 {
// CHECK:             debug b => _5;
// CHECK:             let _7: core::core_arch::simd::Simd<u32, 8>;
// CHECK:             scope 3 {
// CHECK:                 debug r => _7;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = core::arch::x86_64::__m128i::as_u16x8(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = core::intrinsics::simd::simd_cast::<core::core_arch::simd::Simd<u16, 8>, core::core_arch::simd::Simd<u32, 8>>(move _4) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_4);
// CHECK:         StorageLive(_6);
// CHECK:         _6 = core::arch::x86_64::__m128i::as_u16x8(move _2) -> [return: bb3, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _5 = core::intrinsics::simd::simd_cast::<core::core_arch::simd::Simd<u16, 8>, core::core_arch::simd::Simd<u32, 8>>(move _6) -> [return: bb4, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageDead(_6);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = core::intrinsics::simd::simd_mul::<core::core_arch::simd::Simd<u32, 8>>(move _3, move _5) -> [return: bb5, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_9);
// CHECK:         _9 = core::core_arch::simd::Simd::<u32, 8>::splat(const 16_u32) -> [return: bb6, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _7 = core::intrinsics::simd::simd_shr::<core::core_arch::simd::Simd<u32, 8>>(move _8, move _9) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = core::intrinsics::simd::simd_cast::<core::core_arch::simd::Simd<u32, 8>, core::core_arch::simd::Simd<u16, 8>>(move _7) -> [return: bb8, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         _0 = move _10 as core::arch::x86_64::__m128i (Transmute);
// CHECK:         StorageDead(_10);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtNtNtC$HASH_4core9core_arch3x864sse215__mm_mulhi_epu16C$HASH_9simd_cast(ptr, ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: ptr = param 2
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: int:i64 = iconst 16
// CHECK:     v7: mem = memcopy v3:align8, v2:align8, v6, v0
// CHECK:     v8: int:i64 = iconst 16
// CHECK:     v9: mem = memcopy v5:align8, v4:align8, v8, v7
// CHECK:     v10: ptr = stack_slot 32 align 32
// CHECK:     v11: ptr = stack_slot 16 align 16
// CHECK:     v12: ptr = stack_slot 32 align 32
// CHECK:     v13: ptr = stack_slot 16 align 16
// CHECK:     v14: ptr = stack_slot 32 align 32
// CHECK:     v15: ptr = stack_slot 32 align 32
// CHECK:     v16: ptr = stack_slot 32 align 32
// CHECK:     v17: ptr = stack_slot 16 align 16
// CHECK:     v18: ptr = stack_slot 16
// CHECK:     v19: int:i64 = iconst 16
// CHECK:     v20: mem = memcopy v18:align16, v3:align16, v19, v9
// CHECK:     v21: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_9simd_cast
// CHECK:     v22: mem, v23: int:i64 = call v21(v11, v18), v20 -> int:i64
// CHECK:     br bb1(v22)
// CHECK:
// CHECK:   bb1(v25: mem):
// CHECK:     v26: ptr = stack_slot 32
// CHECK:     v27: ptr = stack_slot 4
// CHECK:     v28: int:u16 = load.2 v11, v25
// CHECK:     v29: int:u32 = zext v28, 32
// CHECK:     v30: mem = store.4 v29, v26, v25
// CHECK:     v31: int:u64 = iconst 2
// CHECK:     v32: ptr = ptradd v11, v31
// CHECK:     v33: int:u64 = iconst 4
// CHECK:     v34: ptr = ptradd v26, v33
// CHECK:     v35: int:u16 = load.2 v32, v30
// CHECK:     v36: int:u32 = zext v35, 32
// CHECK:     v37: mem = store.4 v36, v34, v30
// CHECK:     v38: int:u64 = iconst 4
// CHECK:     v39: ptr = ptradd v11, v38
// CHECK:     v40: int:u64 = iconst 8
// CHECK:     v41: ptr = ptradd v26, v40
// CHECK:     v42: int:u16 = load.2 v39, v37
// CHECK:     v43: int:u32 = zext v42, 32
// CHECK:     v44: mem = store.4 v43, v41, v37
// CHECK:     v45: int:u64 = iconst 6
// CHECK:     v46: ptr = ptradd v11, v45
// CHECK:     v47: int:u64 = iconst 12
// CHECK:     v48: ptr = ptradd v26, v47
// CHECK:     v49: int:u16 = load.2 v46, v44
// CHECK:     v50: int:u32 = zext v49, 32
// CHECK:     v51: mem = store.4 v50, v48, v44
// CHECK:     v52: int:u64 = iconst 8
// CHECK:     v53: ptr = ptradd v11, v52
// CHECK:     v54: int:u64 = iconst 16
// CHECK:     v55: ptr = ptradd v26, v54
// CHECK:     v56: int:u16 = load.2 v53, v51
// CHECK:     v57: int:u32 = zext v56, 32
// CHECK:     v58: mem = store.4 v57, v55, v51
// CHECK:     v59: int:u64 = iconst 10
// CHECK:     v60: ptr = ptradd v11, v59
// CHECK:     v61: int:u64 = iconst 20
// CHECK:     v62: ptr = ptradd v26, v61
// CHECK:     v63: int:u16 = load.2 v60, v58
// CHECK:     v64: int:u32 = zext v63, 32
// CHECK:     v65: mem = store.4 v64, v62, v58
// CHECK:     v66: int:u64 = iconst 12
// CHECK:     v67: ptr = ptradd v11, v66
// CHECK:     v68: int:u64 = iconst 24
// CHECK:     v69: ptr = ptradd v26, v68
// CHECK:     v70: int:u16 = load.2 v67, v65
// CHECK:     v71: int:u32 = zext v70, 32
// CHECK:     v72: mem = store.4 v71, v69, v65
// CHECK:     v73: int:u64 = iconst 14
// CHECK:     v74: ptr = ptradd v11, v73
// CHECK:     v75: int:u64 = iconst 28
// CHECK:     v76: ptr = ptradd v26, v75
// CHECK:     v77: int:u16 = load.2 v74, v72
// CHECK:     v78: int:u32 = zext v77, 32
// CHECK:     v79: mem = store.4 v78, v76, v72
// CHECK:     v80: int:i64 = load.8 v26, v79
// CHECK:     v81: mem = store.8 v80, v10, v79
// CHECK:     v82: int:i64 = iconst 8
// CHECK:     v83: ptr = ptradd v26, v82
// CHECK:     v84: int:i64 = load.8 v83, v81
// CHECK:     v85: int:i64 = iconst 8
// CHECK:     v86: ptr = ptradd v10, v85
// CHECK:     v87: mem = store.8 v84, v86, v81
// CHECK:     v88: int:i64 = iconst 16
// CHECK:     v89: ptr = ptradd v26, v88
// CHECK:     v90: int:i64 = load.8 v89, v87
// CHECK:     v91: int:i64 = iconst 16
// CHECK:     v92: ptr = ptradd v10, v91
// CHECK:     v93: mem = store.8 v90, v92, v87
// CHECK:     v94: int:i64 = iconst 24
// CHECK:     v95: ptr = ptradd v26, v94
// CHECK:     v96: int:i64 = load.8 v95, v93
// CHECK:     v97: int:i64 = iconst 24
// CHECK:     v98: ptr = ptradd v10, v97
// CHECK:     v99: mem = store.8 v96, v98, v93
// CHECK:     br bb2(v99)
// CHECK:
// CHECK:   bb2(v101: mem):
// CHECK:     v102: ptr = stack_slot 16
// CHECK:     v103: int:i64 = iconst 16
// CHECK:     v104: mem = memcopy v102:align16, v5:align16, v103, v101
// CHECK:     v105: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_9simd_cast
// CHECK:     v106: mem, v107: int:i64 = call v105(v13, v102), v104 -> int:i64
// CHECK:     br bb3(v106)
// CHECK:
// CHECK:   bb3(v109: mem):
// CHECK:     v110: ptr = stack_slot 32
// CHECK:     v111: ptr = stack_slot 4
// CHECK:     v112: int:u16 = load.2 v13, v109
// CHECK:     v113: int:u32 = zext v112, 32
// CHECK:     v114: mem = store.4 v113, v110, v109
// CHECK:     v115: int:u64 = iconst 2
// CHECK:     v116: ptr = ptradd v13, v115
// CHECK:     v117: int:u64 = iconst 4
// CHECK:     v118: ptr = ptradd v110, v117
// CHECK:     v119: int:u16 = load.2 v116, v114
// CHECK:     v120: int:u32 = zext v119, 32
// CHECK:     v121: mem = store.4 v120, v118, v114
// CHECK:     v122: int:u64 = iconst 4
// CHECK:     v123: ptr = ptradd v13, v122
// CHECK:     v124: int:u64 = iconst 8
// CHECK:     v125: ptr = ptradd v110, v124
// CHECK:     v126: int:u16 = load.2 v123, v121
// CHECK:     v127: int:u32 = zext v126, 32
// CHECK:     v128: mem = store.4 v127, v125, v121
// CHECK:     v129: int:u64 = iconst 6
// CHECK:     v130: ptr = ptradd v13, v129
// CHECK:     v131: int:u64 = iconst 12
// CHECK:     v132: ptr = ptradd v110, v131
// CHECK:     v133: int:u16 = load.2 v130, v128
// CHECK:     v134: int:u32 = zext v133, 32
// CHECK:     v135: mem = store.4 v134, v132, v128
// CHECK:     v136: int:u64 = iconst 8
// CHECK:     v137: ptr = ptradd v13, v136
// CHECK:     v138: int:u64 = iconst 16
// CHECK:     v139: ptr = ptradd v110, v138
// CHECK:     v140: int:u16 = load.2 v137, v135
// CHECK:     v141: int:u32 = zext v140, 32
// CHECK:     v142: mem = store.4 v141, v139, v135
// CHECK:     v143: int:u64 = iconst 10
// CHECK:     v144: ptr = ptradd v13, v143
// CHECK:     v145: int:u64 = iconst 20
// CHECK:     v146: ptr = ptradd v110, v145
// CHECK:     v147: int:u16 = load.2 v144, v142
// CHECK:     v148: int:u32 = zext v147, 32
// CHECK:     v149: mem = store.4 v148, v146, v142
// CHECK:     v150: int:u64 = iconst 12
// CHECK:     v151: ptr = ptradd v13, v150
// CHECK:     v152: int:u64 = iconst 24
// CHECK:     v153: ptr = ptradd v110, v152
// CHECK:     v154: int:u16 = load.2 v151, v149
// CHECK:     v155: int:u32 = zext v154, 32
// CHECK:     v156: mem = store.4 v155, v153, v149
// CHECK:     v157: int:u64 = iconst 14
// CHECK:     v158: ptr = ptradd v13, v157
// CHECK:     v159: int:u64 = iconst 28
// CHECK:     v160: ptr = ptradd v110, v159
// CHECK:     v161: int:u16 = load.2 v158, v156
// CHECK:     v162: int:u32 = zext v161, 32
// CHECK:     v163: mem = store.4 v162, v160, v156
// CHECK:     v164: int:i64 = load.8 v110, v163
// CHECK:     v165: mem = store.8 v164, v12, v163
// CHECK:     v166: int:i64 = iconst 8
// CHECK:     v167: ptr = ptradd v110, v166
// CHECK:     v168: int:i64 = load.8 v167, v165
// CHECK:     v169: int:i64 = iconst 8
// CHECK:     v170: ptr = ptradd v12, v169
// CHECK:     v171: mem = store.8 v168, v170, v165
// CHECK:     v172: int:i64 = iconst 16
// CHECK:     v173: ptr = ptradd v110, v172
// CHECK:     v174: int:i64 = load.8 v173, v171
// CHECK:     v175: int:i64 = iconst 16
// CHECK:     v176: ptr = ptradd v12, v175
// CHECK:     v177: mem = store.8 v174, v176, v171
// CHECK:     v178: int:i64 = iconst 24
// CHECK:     v179: ptr = ptradd v110, v178
// CHECK:     v180: int:i64 = load.8 v179, v177
// CHECK:     v181: int:i64 = iconst 24
// CHECK:     v182: ptr = ptradd v12, v181
// CHECK:     v183: mem = store.8 v180, v182, v177
// CHECK:     br bb4(v183)
// CHECK:
// CHECK:   bb4(v185: mem):
// CHECK:     v186: ptr = stack_slot 32
// CHECK:     v187: int:i32 = load.4 v10, v185
// CHECK:     v188: int:i32 = load.4 v12, v185
// CHECK:     v189: int:i32 = mul v187, v188
// CHECK:     v190: mem = store.4 v189, v186, v185
// CHECK:     v191: int:u64 = iconst 4
// CHECK:     v192: ptr = ptradd v10, v191
// CHECK:     v193: int:u64 = iconst 4
// CHECK:     v194: ptr = ptradd v12, v193
// CHECK:     v195: int:u64 = iconst 4
// CHECK:     v196: ptr = ptradd v186, v195
// CHECK:     v197: int:i32 = load.4 v192, v190
// CHECK:     v198: int:i32 = load.4 v194, v190
// CHECK:     v199: int:i32 = mul v197, v198
// CHECK:     v200: mem = store.4 v199, v196, v190
// CHECK:     v201: int:u64 = iconst 8
// CHECK:     v202: ptr = ptradd v10, v201
// CHECK:     v203: int:u64 = iconst 8
// CHECK:     v204: ptr = ptradd v12, v203
// CHECK:     v205: int:u64 = iconst 8
// CHECK:     v206: ptr = ptradd v186, v205
// CHECK:     v207: int:i32 = load.4 v202, v200
// CHECK:     v208: int:i32 = load.4 v204, v200
// CHECK:     v209: int:i32 = mul v207, v208
// CHECK:     v210: mem = store.4 v209, v206, v200
// CHECK:     v211: int:u64 = iconst 12
// CHECK:     v212: ptr = ptradd v10, v211
// CHECK:     v213: int:u64 = iconst 12
// CHECK:     v214: ptr = ptradd v12, v213
// CHECK:     v215: int:u64 = iconst 12
// CHECK:     v216: ptr = ptradd v186, v215
// CHECK:     v217: int:i32 = load.4 v212, v210
// CHECK:     v218: int:i32 = load.4 v214, v210
// CHECK:     v219: int:i32 = mul v217, v218
// CHECK:     v220: mem = store.4 v219, v216, v210
// CHECK:     v221: int:u64 = iconst 16
// CHECK:     v222: ptr = ptradd v10, v221
// CHECK:     v223: int:u64 = iconst 16
// CHECK:     v224: ptr = ptradd v12, v223
// CHECK:     v225: int:u64 = iconst 16
// CHECK:     v226: ptr = ptradd v186, v225
// CHECK:     v227: int:i32 = load.4 v222, v220
// CHECK:     v228: int:i32 = load.4 v224, v220
// CHECK:     v229: int:i32 = mul v227, v228
// CHECK:     v230: mem = store.4 v229, v226, v220
// CHECK:     v231: int:u64 = iconst 20
// CHECK:     v232: ptr = ptradd v10, v231
// CHECK:     v233: int:u64 = iconst 20
// CHECK:     v234: ptr = ptradd v12, v233
// CHECK:     v235: int:u64 = iconst 20
// CHECK:     v236: ptr = ptradd v186, v235
// CHECK:     v237: int:i32 = load.4 v232, v230
// CHECK:     v238: int:i32 = load.4 v234, v230
// CHECK:     v239: int:i32 = mul v237, v238
// CHECK:     v240: mem = store.4 v239, v236, v230
// CHECK:     v241: int:u64 = iconst 24
// CHECK:     v242: ptr = ptradd v10, v241
// CHECK:     v243: int:u64 = iconst 24
// CHECK:     v244: ptr = ptradd v12, v243
// CHECK:     v245: int:u64 = iconst 24
// CHECK:     v246: ptr = ptradd v186, v245
// CHECK:     v247: int:i32 = load.4 v242, v240
// CHECK:     v248: int:i32 = load.4 v244, v240
// CHECK:     v249: int:i32 = mul v247, v248
// CHECK:     v250: mem = store.4 v249, v246, v240
// CHECK:     v251: int:u64 = iconst 28
// CHECK:     v252: ptr = ptradd v10, v251
// CHECK:     v253: int:u64 = iconst 28
// CHECK:     v254: ptr = ptradd v12, v253
// CHECK:     v255: int:u64 = iconst 28
// CHECK:     v256: ptr = ptradd v186, v255
// CHECK:     v257: int:i32 = load.4 v252, v250
// CHECK:     v258: int:i32 = load.4 v254, v250
// CHECK:     v259: int:i32 = mul v257, v258
// CHECK:     v260: mem = store.4 v259, v256, v250
// CHECK:     v261: int:i64 = load.8 v186, v260
// CHECK:     v262: mem = store.8 v261, v15, v260
// CHECK:     v263: int:i64 = iconst 8
// CHECK:     v264: ptr = ptradd v186, v263
// CHECK:     v265: int:i64 = load.8 v264, v262
// CHECK:     v266: int:i64 = iconst 8
// CHECK:     v267: ptr = ptradd v15, v266
// CHECK:     v268: mem = store.8 v265, v267, v262
// CHECK:     v269: int:i64 = iconst 16
// CHECK:     v270: ptr = ptradd v186, v269
// CHECK:     v271: int:i64 = load.8 v270, v268
// CHECK:     v272: int:i64 = iconst 16
// CHECK:     v273: ptr = ptradd v15, v272
// CHECK:     v274: mem = store.8 v271, v273, v268
// CHECK:     v275: int:i64 = iconst 24
// CHECK:     v276: ptr = ptradd v186, v275
// CHECK:     v277: int:i64 = load.8 v276, v274
// CHECK:     v278: int:i64 = iconst 24
// CHECK:     v279: ptr = ptradd v15, v278
// CHECK:     v280: mem = store.8 v277, v279, v274
// CHECK:     br bb5(v280)
// CHECK:
// CHECK:   bb5(v282: mem):
// CHECK:     v283: int:i32 = iconst 16
// CHECK:     v284: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdmKj8_E5splatC$HASH_9simd_cast
// CHECK:     v285: mem = call v284(v16, v283:u32), v282
// CHECK:     v286: int:i64 = iconst 0
// CHECK:     br bb6(v285)
// CHECK:
// CHECK:   bb6(v288: mem):
// CHECK:     v289: ptr = stack_slot 32
// CHECK:     v290: int:u32 = load.4 v15, v288
// CHECK:     v291: int:u32 = load.4 v16, v288
// CHECK:     v292: int:u32 = shr v290, v291
// CHECK:     v293: mem = store.4 v292, v289, v288
// CHECK:     v294: int:u64 = iconst 4
// CHECK:     v295: ptr = ptradd v15, v294
// CHECK:     v296: int:u64 = iconst 4
// CHECK:     v297: ptr = ptradd v16, v296
// CHECK:     v298: int:u64 = iconst 4
// CHECK:     v299: ptr = ptradd v289, v298
// CHECK:     v300: int:u32 = load.4 v295, v293
// CHECK:     v301: int:u32 = load.4 v297, v293
// CHECK:     v302: int:u32 = shr v300, v301
// CHECK:     v303: mem = store.4 v302, v299, v293
// CHECK:     v304: int:u64 = iconst 8
// CHECK:     v305: ptr = ptradd v15, v304
// CHECK:     v306: int:u64 = iconst 8
// CHECK:     v307: ptr = ptradd v16, v306
// CHECK:     v308: int:u64 = iconst 8
// CHECK:     v309: ptr = ptradd v289, v308
// CHECK:     v310: int:u32 = load.4 v305, v303
// CHECK:     v311: int:u32 = load.4 v307, v303
// CHECK:     v312: int:u32 = shr v310, v311
// CHECK:     v313: mem = store.4 v312, v309, v303
// CHECK:     v314: int:u64 = iconst 12
// CHECK:     v315: ptr = ptradd v15, v314
// CHECK:     v316: int:u64 = iconst 12
// CHECK:     v317: ptr = ptradd v16, v316
// CHECK:     v318: int:u64 = iconst 12
// CHECK:     v319: ptr = ptradd v289, v318
// CHECK:     v320: int:u32 = load.4 v315, v313
// CHECK:     v321: int:u32 = load.4 v317, v313
// CHECK:     v322: int:u32 = shr v320, v321
// CHECK:     v323: mem = store.4 v322, v319, v313
// CHECK:     v324: int:u64 = iconst 16
// CHECK:     v325: ptr = ptradd v15, v324
// CHECK:     v326: int:u64 = iconst 16
// CHECK:     v327: ptr = ptradd v16, v326
// CHECK:     v328: int:u64 = iconst 16
// CHECK:     v329: ptr = ptradd v289, v328
// CHECK:     v330: int:u32 = load.4 v325, v323
// CHECK:     v331: int:u32 = load.4 v327, v323
// CHECK:     v332: int:u32 = shr v330, v331
// CHECK:     v333: mem = store.4 v332, v329, v323
// CHECK:     v334: int:u64 = iconst 20
// CHECK:     v335: ptr = ptradd v15, v334
// CHECK:     v336: int:u64 = iconst 20
// CHECK:     v337: ptr = ptradd v16, v336
// CHECK:     v338: int:u64 = iconst 20
// CHECK:     v339: ptr = ptradd v289, v338
// CHECK:     v340: int:u32 = load.4 v335, v333
// CHECK:     v341: int:u32 = load.4 v337, v333
// CHECK:     v342: int:u32 = shr v340, v341
// CHECK:     v343: mem = store.4 v342, v339, v333
// CHECK:     v344: int:u64 = iconst 24
// CHECK:     v345: ptr = ptradd v15, v344
// CHECK:     v346: int:u64 = iconst 24
// CHECK:     v347: ptr = ptradd v16, v346
// CHECK:     v348: int:u64 = iconst 24
// CHECK:     v349: ptr = ptradd v289, v348
// CHECK:     v350: int:u32 = load.4 v345, v343
// CHECK:     v351: int:u32 = load.4 v347, v343
// CHECK:     v352: int:u32 = shr v350, v351
// CHECK:     v353: mem = store.4 v352, v349, v343
// CHECK:     v354: int:u64 = iconst 28
// CHECK:     v355: ptr = ptradd v15, v354
// CHECK:     v356: int:u64 = iconst 28
// CHECK:     v357: ptr = ptradd v16, v356
// CHECK:     v358: int:u64 = iconst 28
// CHECK:     v359: ptr = ptradd v289, v358
// CHECK:     v360: int:u32 = load.4 v355, v353
// CHECK:     v361: int:u32 = load.4 v357, v353
// CHECK:     v362: int:u32 = shr v360, v361
// CHECK:     v363: mem = store.4 v362, v359, v353
// CHECK:     v364: int:i64 = load.8 v289, v363
// CHECK:     v365: mem = store.8 v364, v14, v363
// CHECK:     v366: int:i64 = iconst 8
// CHECK:     v367: ptr = ptradd v289, v366
// CHECK:     v368: int:i64 = load.8 v367, v365
// CHECK:     v369: int:i64 = iconst 8
// CHECK:     v370: ptr = ptradd v14, v369
// CHECK:     v371: mem = store.8 v368, v370, v365
// CHECK:     v372: int:i64 = iconst 16
// CHECK:     v373: ptr = ptradd v289, v372
// CHECK:     v374: int:i64 = load.8 v373, v371
// CHECK:     v375: int:i64 = iconst 16
// CHECK:     v376: ptr = ptradd v14, v375
// CHECK:     v377: mem = store.8 v374, v376, v371
// CHECK:     v378: int:i64 = iconst 24
// CHECK:     v379: ptr = ptradd v289, v378
// CHECK:     v380: int:i64 = load.8 v379, v377
// CHECK:     v381: int:i64 = iconst 24
// CHECK:     v382: ptr = ptradd v14, v381
// CHECK:     v383: mem = store.8 v380, v382, v377
// CHECK:     br bb7(v383)
// CHECK:
// CHECK:   bb7(v385: mem):
// CHECK:     v386: ptr = stack_slot 16
// CHECK:     v387: ptr = stack_slot 4
// CHECK:     v388: int:u32 = load.4 v14, v385
// CHECK:     v389: mem = store.4 v388, v387, v385
// CHECK:     v390: int:u16 = load.2 v387, v389
// CHECK:     v391: mem = store.2 v390, v386, v389
// CHECK:     v392: int:u64 = iconst 4
// CHECK:     v393: ptr = ptradd v14, v392
// CHECK:     v394: int:u64 = iconst 2
// CHECK:     v395: ptr = ptradd v386, v394
// CHECK:     v396: int:u32 = load.4 v393, v391
// CHECK:     v397: mem = store.4 v396, v387, v391
// CHECK:     v398: int:u16 = load.2 v387, v397
// CHECK:     v399: mem = store.2 v398, v395, v397
// CHECK:     v400: int:u64 = iconst 8
// CHECK:     v401: ptr = ptradd v14, v400
// CHECK:     v402: int:u64 = iconst 4
// CHECK:     v403: ptr = ptradd v386, v402
// CHECK:     v404: int:u32 = load.4 v401, v399
// CHECK:     v405: mem = store.4 v404, v387, v399
// CHECK:     v406: int:u16 = load.2 v387, v405
// CHECK:     v407: mem = store.2 v406, v403, v405
// CHECK:     v408: int:u64 = iconst 12
// CHECK:     v409: ptr = ptradd v14, v408
// CHECK:     v410: int:u64 = iconst 6
// CHECK:     v411: ptr = ptradd v386, v410
// CHECK:     v412: int:u32 = load.4 v409, v407
// CHECK:     v413: mem = store.4 v412, v387, v407
// CHECK:     v414: int:u16 = load.2 v387, v413
// CHECK:     v415: mem = store.2 v414, v411, v413
// CHECK:     v416: int:u64 = iconst 16
// CHECK:     v417: ptr = ptradd v14, v416
// CHECK:     v418: int:u64 = iconst 8
// CHECK:     v419: ptr = ptradd v386, v418
// CHECK:     v420: int:u32 = load.4 v417, v415
// CHECK:     v421: mem = store.4 v420, v387, v415
// CHECK:     v422: int:u16 = load.2 v387, v421
// CHECK:     v423: mem = store.2 v422, v419, v421
// CHECK:     v424: int:u64 = iconst 20
// CHECK:     v425: ptr = ptradd v14, v424
// CHECK:     v426: int:u64 = iconst 10
// CHECK:     v427: ptr = ptradd v386, v426
// CHECK:     v428: int:u32 = load.4 v425, v423
// CHECK:     v429: mem = store.4 v428, v387, v423
// CHECK:     v430: int:u16 = load.2 v387, v429
// CHECK:     v431: mem = store.2 v430, v427, v429
// CHECK:     v432: int:u64 = iconst 24
// CHECK:     v433: ptr = ptradd v14, v432
// CHECK:     v434: int:u64 = iconst 12
// CHECK:     v435: ptr = ptradd v386, v434
// CHECK:     v436: int:u32 = load.4 v433, v431
// CHECK:     v437: mem = store.4 v436, v387, v431
// CHECK:     v438: int:u16 = load.2 v387, v437
// CHECK:     v439: mem = store.2 v438, v435, v437
// CHECK:     v440: int:u64 = iconst 28
// CHECK:     v441: ptr = ptradd v14, v440
// CHECK:     v442: int:u64 = iconst 14
// CHECK:     v443: ptr = ptradd v386, v442
// CHECK:     v444: int:u32 = load.4 v441, v439
// CHECK:     v445: mem = store.4 v444, v387, v439
// CHECK:     v446: int:u16 = load.2 v387, v445
// CHECK:     v447: mem = store.2 v446, v443, v445
// CHECK:     v448: int:i64 = load.8 v386, v447
// CHECK:     v449: mem = store.8 v448, v17, v447
// CHECK:     v450: int:i64 = iconst 8
// CHECK:     v451: ptr = ptradd v386, v450
// CHECK:     v452: int:i64 = load.8 v451, v449
// CHECK:     v453: int:i64 = iconst 8
// CHECK:     v454: ptr = ptradd v17, v453
// CHECK:     v455: mem = store.8 v452, v454, v449
// CHECK:     br bb8(v455)
// CHECK:
// CHECK:   bb8(v457: mem):
// CHECK:     v458: int:i64 = load.8 v17, v457
// CHECK:     v459: mem = store.8 v458, v1, v457
// CHECK:     v460: int:i64 = iconst 8
// CHECK:     v461: ptr = ptradd v17, v460
// CHECK:     v462: int:i64 = load.8 v461, v459
// CHECK:     v463: int:i64 = iconst 8
// CHECK:     v464: ptr = ptradd v1, v463
// CHECK:     v465: mem = store.8 v462, v464, v459
// CHECK:     ret v1, v465
// CHECK: }
// CHECK:
// CHECK: fn mulhi_words(_1: core::arch::x86_64::__m128i, _2: core::arch::x86_64::__m128i) -> core::arch::x86_64::__m128i {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: core::arch::x86_64::__m128i;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::arch::x86_64::_mm_mulhi_epu16(move _1, move _2) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mulhi_words(ptr, ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: ptr = param 2
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: int:i64 = iconst 16
// CHECK:     v7: mem = memcopy v3:align8, v2:align8, v6, v0
// CHECK:     v8: int:i64 = iconst 16
// CHECK:     v9: mem = memcopy v5:align8, v4:align8, v8, v7
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v10:align16, v3:align16, v11, v9
// CHECK:     v13: ptr = stack_slot 16
// CHECK:     v14: int:i64 = iconst 16
// CHECK:     v15: mem = memcopy v13:align16, v5:align16, v14, v12
// CHECK:     v16: ptr = symbol_addr @_RNvNtNtNtC$HASH_4core9core_arch3x864sse215__mm_mulhi_epu16C$HASH_9simd_cast
// CHECK:     v17: mem, v18: int:i64 = call v16(v1, v10, v13), v15 -> int:i64
// CHECK:     br bb1(v17)
// CHECK:
// CHECK:   bb1(v20: mem):
// CHECK:     ret v1, v20
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::arch::x86_64::{__m128i, _mm_mulhi_epu16};

#[no_mangle]
#[target_feature(enable = "sse2")]
pub unsafe fn mulhi_words(a: __m128i, b: __m128i) -> __m128i {
    _mm_mulhi_epu16(a, b)
}
