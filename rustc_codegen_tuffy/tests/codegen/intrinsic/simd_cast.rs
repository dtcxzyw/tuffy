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
// CHECK: func @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdmKj8_E5splatC$HASH_9simd_cast(ptr, int:u32) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 32 align 32
// CHECK:     v3: int:u32 = param 1
// CHECK:     v4: int:u64 = iconst 255
// CHECK:     v5: int:u64 = and v3, v4
// CHECK:     v6: int:u64 = iconst 72340172838076673
// CHECK:     v7: int:u64 = mul v5, v6
// CHECK:     v8: ptr = stack_slot 32
// CHECK:     v9: mem = store.8 v7, v8, v0
// CHECK:     v10: int:u64 = iconst 8
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.8 v7, v11, v9
// CHECK:     v13: int:u64 = iconst 16
// CHECK:     v14: ptr = ptradd v8, v13
// CHECK:     v15: mem = store.8 v7, v14, v12
// CHECK:     v16: int:u64 = iconst 24
// CHECK:     v17: ptr = ptradd v8, v16
// CHECK:     v18: mem = store.8 v7, v17, v15
// CHECK:     v19: int:i64 = load.8 v8, v18
// CHECK:     v20: mem = store.8 v19, v2, v18
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v8, v21
// CHECK:     v23: int:i64 = load.8 v22, v20
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v2, v24
// CHECK:     v26: mem = store.8 v23, v25, v20
// CHECK:     v27: int:i64 = iconst 16
// CHECK:     v28: ptr = ptradd v8, v27
// CHECK:     v29: int:i64 = load.8 v28, v26
// CHECK:     v30: int:i64 = iconst 16
// CHECK:     v31: ptr = ptradd v2, v30
// CHECK:     v32: mem = store.8 v29, v31, v26
// CHECK:     v33: int:i64 = iconst 24
// CHECK:     v34: ptr = ptradd v8, v33
// CHECK:     v35: int:i64 = load.8 v34, v32
// CHECK:     v36: int:i64 = iconst 24
// CHECK:     v37: ptr = ptradd v2, v36
// CHECK:     v38: mem = store.8 v35, v37, v32
// CHECK:     br bb1(v38)
// CHECK:
// CHECK:   bb1(v40: mem):
// CHECK:     v41: int:i64 = iconst 32
// CHECK:     v42: mem = memcopy v1:align8, v2:align8, v41, v40
// CHECK:     ret v1, v42
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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: ptr = param 2
// CHECK:     v6: ptr = stack_slot 16 align 16
// CHECK:     v7: int:i64 = iconst 16
// CHECK:     v8: mem = memcopy v4:align8, v3:align8, v7, v0
// CHECK:     v9: int:i64 = iconst 16
// CHECK:     v10: mem = memcopy v6:align8, v5:align8, v9, v8
// CHECK:     v11: ptr = stack_slot 32 align 32
// CHECK:     v12: ptr = stack_slot 16 align 16
// CHECK:     v13: ptr = stack_slot 32 align 32
// CHECK:     v14: ptr = stack_slot 16 align 16
// CHECK:     v15: ptr = stack_slot 32 align 32
// CHECK:     v16: ptr = stack_slot 32 align 32
// CHECK:     v17: ptr = stack_slot 32 align 32
// CHECK:     v18: ptr = stack_slot 16 align 16
// CHECK:     v19: ptr = stack_slot 16
// CHECK:     v20: int:i64 = iconst 16
// CHECK:     v21: mem = memcopy v19:align16, v4:align16, v20, v10
// CHECK:     v22: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_9simd_cast
// CHECK:     v23: mem, v24: int:i64 = call v22(v12, v19), v21 -> int:i64
// CHECK:     br bb1(v23)
// CHECK:
// CHECK:   bb1(v26: mem):
// CHECK:     v27: ptr = stack_slot 32
// CHECK:     v28: ptr = stack_slot 4
// CHECK:     v29: int:u16 = load.2 v12, v26
// CHECK:     v30: int:u32 = zext v29, 32
// CHECK:     v31: mem = store.4 v30, v27, v26
// CHECK:     v32: int:u64 = iconst 2
// CHECK:     v33: ptr = ptradd v12, v32
// CHECK:     v34: int:u64 = iconst 4
// CHECK:     v35: ptr = ptradd v27, v34
// CHECK:     v36: int:u16 = load.2 v33, v31
// CHECK:     v37: int:u32 = zext v36, 32
// CHECK:     v38: mem = store.4 v37, v35, v31
// CHECK:     v39: int:u64 = iconst 4
// CHECK:     v40: ptr = ptradd v12, v39
// CHECK:     v41: int:u64 = iconst 8
// CHECK:     v42: ptr = ptradd v27, v41
// CHECK:     v43: int:u16 = load.2 v40, v38
// CHECK:     v44: int:u32 = zext v43, 32
// CHECK:     v45: mem = store.4 v44, v42, v38
// CHECK:     v46: int:u64 = iconst 6
// CHECK:     v47: ptr = ptradd v12, v46
// CHECK:     v48: int:u64 = iconst 12
// CHECK:     v49: ptr = ptradd v27, v48
// CHECK:     v50: int:u16 = load.2 v47, v45
// CHECK:     v51: int:u32 = zext v50, 32
// CHECK:     v52: mem = store.4 v51, v49, v45
// CHECK:     v53: int:u64 = iconst 8
// CHECK:     v54: ptr = ptradd v12, v53
// CHECK:     v55: int:u64 = iconst 16
// CHECK:     v56: ptr = ptradd v27, v55
// CHECK:     v57: int:u16 = load.2 v54, v52
// CHECK:     v58: int:u32 = zext v57, 32
// CHECK:     v59: mem = store.4 v58, v56, v52
// CHECK:     v60: int:u64 = iconst 10
// CHECK:     v61: ptr = ptradd v12, v60
// CHECK:     v62: int:u64 = iconst 20
// CHECK:     v63: ptr = ptradd v27, v62
// CHECK:     v64: int:u16 = load.2 v61, v59
// CHECK:     v65: int:u32 = zext v64, 32
// CHECK:     v66: mem = store.4 v65, v63, v59
// CHECK:     v67: int:u64 = iconst 12
// CHECK:     v68: ptr = ptradd v12, v67
// CHECK:     v69: int:u64 = iconst 24
// CHECK:     v70: ptr = ptradd v27, v69
// CHECK:     v71: int:u16 = load.2 v68, v66
// CHECK:     v72: int:u32 = zext v71, 32
// CHECK:     v73: mem = store.4 v72, v70, v66
// CHECK:     v74: int:u64 = iconst 14
// CHECK:     v75: ptr = ptradd v12, v74
// CHECK:     v76: int:u64 = iconst 28
// CHECK:     v77: ptr = ptradd v27, v76
// CHECK:     v78: int:u16 = load.2 v75, v73
// CHECK:     v79: int:u32 = zext v78, 32
// CHECK:     v80: mem = store.4 v79, v77, v73
// CHECK:     v81: int:i64 = load.8 v27, v80
// CHECK:     v82: mem = store.8 v81, v11, v80
// CHECK:     v83: int:i64 = iconst 8
// CHECK:     v84: ptr = ptradd v27, v83
// CHECK:     v85: int:i64 = load.8 v84, v82
// CHECK:     v86: int:i64 = iconst 8
// CHECK:     v87: ptr = ptradd v11, v86
// CHECK:     v88: mem = store.8 v85, v87, v82
// CHECK:     v89: int:i64 = iconst 16
// CHECK:     v90: ptr = ptradd v27, v89
// CHECK:     v91: int:i64 = load.8 v90, v88
// CHECK:     v92: int:i64 = iconst 16
// CHECK:     v93: ptr = ptradd v11, v92
// CHECK:     v94: mem = store.8 v91, v93, v88
// CHECK:     v95: int:i64 = iconst 24
// CHECK:     v96: ptr = ptradd v27, v95
// CHECK:     v97: int:i64 = load.8 v96, v94
// CHECK:     v98: int:i64 = iconst 24
// CHECK:     v99: ptr = ptradd v11, v98
// CHECK:     v100: mem = store.8 v97, v99, v94
// CHECK:     br bb2(v100)
// CHECK:
// CHECK:   bb2(v102: mem):
// CHECK:     v103: ptr = stack_slot 16
// CHECK:     v104: int:i64 = iconst 16
// CHECK:     v105: mem = memcopy v103:align16, v6:align16, v104, v102
// CHECK:     v106: ptr = symbol_addr @_RNvMs1K_NtNtC$HASH_4core9core_arch3x86NtB6_7___m128i8as_u16x8C$HASH_9simd_cast
// CHECK:     v107: mem, v108: int:i64 = call v106(v14, v103), v105 -> int:i64
// CHECK:     br bb3(v107)
// CHECK:
// CHECK:   bb3(v110: mem):
// CHECK:     v111: ptr = stack_slot 32
// CHECK:     v112: ptr = stack_slot 4
// CHECK:     v113: int:u16 = load.2 v14, v110
// CHECK:     v114: int:u32 = zext v113, 32
// CHECK:     v115: mem = store.4 v114, v111, v110
// CHECK:     v116: int:u64 = iconst 2
// CHECK:     v117: ptr = ptradd v14, v116
// CHECK:     v118: int:u64 = iconst 4
// CHECK:     v119: ptr = ptradd v111, v118
// CHECK:     v120: int:u16 = load.2 v117, v115
// CHECK:     v121: int:u32 = zext v120, 32
// CHECK:     v122: mem = store.4 v121, v119, v115
// CHECK:     v123: int:u64 = iconst 4
// CHECK:     v124: ptr = ptradd v14, v123
// CHECK:     v125: int:u64 = iconst 8
// CHECK:     v126: ptr = ptradd v111, v125
// CHECK:     v127: int:u16 = load.2 v124, v122
// CHECK:     v128: int:u32 = zext v127, 32
// CHECK:     v129: mem = store.4 v128, v126, v122
// CHECK:     v130: int:u64 = iconst 6
// CHECK:     v131: ptr = ptradd v14, v130
// CHECK:     v132: int:u64 = iconst 12
// CHECK:     v133: ptr = ptradd v111, v132
// CHECK:     v134: int:u16 = load.2 v131, v129
// CHECK:     v135: int:u32 = zext v134, 32
// CHECK:     v136: mem = store.4 v135, v133, v129
// CHECK:     v137: int:u64 = iconst 8
// CHECK:     v138: ptr = ptradd v14, v137
// CHECK:     v139: int:u64 = iconst 16
// CHECK:     v140: ptr = ptradd v111, v139
// CHECK:     v141: int:u16 = load.2 v138, v136
// CHECK:     v142: int:u32 = zext v141, 32
// CHECK:     v143: mem = store.4 v142, v140, v136
// CHECK:     v144: int:u64 = iconst 10
// CHECK:     v145: ptr = ptradd v14, v144
// CHECK:     v146: int:u64 = iconst 20
// CHECK:     v147: ptr = ptradd v111, v146
// CHECK:     v148: int:u16 = load.2 v145, v143
// CHECK:     v149: int:u32 = zext v148, 32
// CHECK:     v150: mem = store.4 v149, v147, v143
// CHECK:     v151: int:u64 = iconst 12
// CHECK:     v152: ptr = ptradd v14, v151
// CHECK:     v153: int:u64 = iconst 24
// CHECK:     v154: ptr = ptradd v111, v153
// CHECK:     v155: int:u16 = load.2 v152, v150
// CHECK:     v156: int:u32 = zext v155, 32
// CHECK:     v157: mem = store.4 v156, v154, v150
// CHECK:     v158: int:u64 = iconst 14
// CHECK:     v159: ptr = ptradd v14, v158
// CHECK:     v160: int:u64 = iconst 28
// CHECK:     v161: ptr = ptradd v111, v160
// CHECK:     v162: int:u16 = load.2 v159, v157
// CHECK:     v163: int:u32 = zext v162, 32
// CHECK:     v164: mem = store.4 v163, v161, v157
// CHECK:     v165: int:i64 = load.8 v111, v164
// CHECK:     v166: mem = store.8 v165, v13, v164
// CHECK:     v167: int:i64 = iconst 8
// CHECK:     v168: ptr = ptradd v111, v167
// CHECK:     v169: int:i64 = load.8 v168, v166
// CHECK:     v170: int:i64 = iconst 8
// CHECK:     v171: ptr = ptradd v13, v170
// CHECK:     v172: mem = store.8 v169, v171, v166
// CHECK:     v173: int:i64 = iconst 16
// CHECK:     v174: ptr = ptradd v111, v173
// CHECK:     v175: int:i64 = load.8 v174, v172
// CHECK:     v176: int:i64 = iconst 16
// CHECK:     v177: ptr = ptradd v13, v176
// CHECK:     v178: mem = store.8 v175, v177, v172
// CHECK:     v179: int:i64 = iconst 24
// CHECK:     v180: ptr = ptradd v111, v179
// CHECK:     v181: int:i64 = load.8 v180, v178
// CHECK:     v182: int:i64 = iconst 24
// CHECK:     v183: ptr = ptradd v13, v182
// CHECK:     v184: mem = store.8 v181, v183, v178
// CHECK:     br bb4(v184)
// CHECK:
// CHECK:   bb4(v186: mem):
// CHECK:     v187: ptr = stack_slot 32
// CHECK:     v188: int:i32 = load.4 v11, v186
// CHECK:     v189: int:i32 = load.4 v13, v186
// CHECK:     v190: int:i32 = mul v188, v189
// CHECK:     v191: mem = store.4 v190, v187, v186
// CHECK:     v192: int:u64 = iconst 4
// CHECK:     v193: ptr = ptradd v11, v192
// CHECK:     v194: int:u64 = iconst 4
// CHECK:     v195: ptr = ptradd v13, v194
// CHECK:     v196: int:u64 = iconst 4
// CHECK:     v197: ptr = ptradd v187, v196
// CHECK:     v198: int:i32 = load.4 v193, v191
// CHECK:     v199: int:i32 = load.4 v195, v191
// CHECK:     v200: int:i32 = mul v198, v199
// CHECK:     v201: mem = store.4 v200, v197, v191
// CHECK:     v202: int:u64 = iconst 8
// CHECK:     v203: ptr = ptradd v11, v202
// CHECK:     v204: int:u64 = iconst 8
// CHECK:     v205: ptr = ptradd v13, v204
// CHECK:     v206: int:u64 = iconst 8
// CHECK:     v207: ptr = ptradd v187, v206
// CHECK:     v208: int:i32 = load.4 v203, v201
// CHECK:     v209: int:i32 = load.4 v205, v201
// CHECK:     v210: int:i32 = mul v208, v209
// CHECK:     v211: mem = store.4 v210, v207, v201
// CHECK:     v212: int:u64 = iconst 12
// CHECK:     v213: ptr = ptradd v11, v212
// CHECK:     v214: int:u64 = iconst 12
// CHECK:     v215: ptr = ptradd v13, v214
// CHECK:     v216: int:u64 = iconst 12
// CHECK:     v217: ptr = ptradd v187, v216
// CHECK:     v218: int:i32 = load.4 v213, v211
// CHECK:     v219: int:i32 = load.4 v215, v211
// CHECK:     v220: int:i32 = mul v218, v219
// CHECK:     v221: mem = store.4 v220, v217, v211
// CHECK:     v222: int:u64 = iconst 16
// CHECK:     v223: ptr = ptradd v11, v222
// CHECK:     v224: int:u64 = iconst 16
// CHECK:     v225: ptr = ptradd v13, v224
// CHECK:     v226: int:u64 = iconst 16
// CHECK:     v227: ptr = ptradd v187, v226
// CHECK:     v228: int:i32 = load.4 v223, v221
// CHECK:     v229: int:i32 = load.4 v225, v221
// CHECK:     v230: int:i32 = mul v228, v229
// CHECK:     v231: mem = store.4 v230, v227, v221
// CHECK:     v232: int:u64 = iconst 20
// CHECK:     v233: ptr = ptradd v11, v232
// CHECK:     v234: int:u64 = iconst 20
// CHECK:     v235: ptr = ptradd v13, v234
// CHECK:     v236: int:u64 = iconst 20
// CHECK:     v237: ptr = ptradd v187, v236
// CHECK:     v238: int:i32 = load.4 v233, v231
// CHECK:     v239: int:i32 = load.4 v235, v231
// CHECK:     v240: int:i32 = mul v238, v239
// CHECK:     v241: mem = store.4 v240, v237, v231
// CHECK:     v242: int:u64 = iconst 24
// CHECK:     v243: ptr = ptradd v11, v242
// CHECK:     v244: int:u64 = iconst 24
// CHECK:     v245: ptr = ptradd v13, v244
// CHECK:     v246: int:u64 = iconst 24
// CHECK:     v247: ptr = ptradd v187, v246
// CHECK:     v248: int:i32 = load.4 v243, v241
// CHECK:     v249: int:i32 = load.4 v245, v241
// CHECK:     v250: int:i32 = mul v248, v249
// CHECK:     v251: mem = store.4 v250, v247, v241
// CHECK:     v252: int:u64 = iconst 28
// CHECK:     v253: ptr = ptradd v11, v252
// CHECK:     v254: int:u64 = iconst 28
// CHECK:     v255: ptr = ptradd v13, v254
// CHECK:     v256: int:u64 = iconst 28
// CHECK:     v257: ptr = ptradd v187, v256
// CHECK:     v258: int:i32 = load.4 v253, v251
// CHECK:     v259: int:i32 = load.4 v255, v251
// CHECK:     v260: int:i32 = mul v258, v259
// CHECK:     v261: mem = store.4 v260, v257, v251
// CHECK:     v262: int:i64 = load.8 v187, v261
// CHECK:     v263: mem = store.8 v262, v16, v261
// CHECK:     v264: int:i64 = iconst 8
// CHECK:     v265: ptr = ptradd v187, v264
// CHECK:     v266: int:i64 = load.8 v265, v263
// CHECK:     v267: int:i64 = iconst 8
// CHECK:     v268: ptr = ptradd v16, v267
// CHECK:     v269: mem = store.8 v266, v268, v263
// CHECK:     v270: int:i64 = iconst 16
// CHECK:     v271: ptr = ptradd v187, v270
// CHECK:     v272: int:i64 = load.8 v271, v269
// CHECK:     v273: int:i64 = iconst 16
// CHECK:     v274: ptr = ptradd v16, v273
// CHECK:     v275: mem = store.8 v272, v274, v269
// CHECK:     v276: int:i64 = iconst 24
// CHECK:     v277: ptr = ptradd v187, v276
// CHECK:     v278: int:i64 = load.8 v277, v275
// CHECK:     v279: int:i64 = iconst 24
// CHECK:     v280: ptr = ptradd v16, v279
// CHECK:     v281: mem = store.8 v278, v280, v275
// CHECK:     br bb5(v281)
// CHECK:
// CHECK:   bb5(v283: mem):
// CHECK:     v284: int:i32 = iconst 16
// CHECK:     v285: ptr = symbol_addr @_RNvMs9_NtNtC$HASH_4core9core_arch4simdINtB5_4SimdmKj8_E5splatC$HASH_9simd_cast
// CHECK:     v286: mem = call v285(v17, v284:u32), v283
// CHECK:     v287: int:i64 = iconst 0
// CHECK:     br bb6(v286)
// CHECK:
// CHECK:   bb6(v289: mem):
// CHECK:     v290: ptr = stack_slot 32
// CHECK:     v291: int:u32 = load.4 v16, v289
// CHECK:     v292: int:u32 = load.4 v17, v289
// CHECK:     v293: int:u32 = shr v291, v292
// CHECK:     v294: mem = store.4 v293, v290, v289
// CHECK:     v295: int:u64 = iconst 4
// CHECK:     v296: ptr = ptradd v16, v295
// CHECK:     v297: int:u64 = iconst 4
// CHECK:     v298: ptr = ptradd v17, v297
// CHECK:     v299: int:u64 = iconst 4
// CHECK:     v300: ptr = ptradd v290, v299
// CHECK:     v301: int:u32 = load.4 v296, v294
// CHECK:     v302: int:u32 = load.4 v298, v294
// CHECK:     v303: int:u32 = shr v301, v302
// CHECK:     v304: mem = store.4 v303, v300, v294
// CHECK:     v305: int:u64 = iconst 8
// CHECK:     v306: ptr = ptradd v16, v305
// CHECK:     v307: int:u64 = iconst 8
// CHECK:     v308: ptr = ptradd v17, v307
// CHECK:     v309: int:u64 = iconst 8
// CHECK:     v310: ptr = ptradd v290, v309
// CHECK:     v311: int:u32 = load.4 v306, v304
// CHECK:     v312: int:u32 = load.4 v308, v304
// CHECK:     v313: int:u32 = shr v311, v312
// CHECK:     v314: mem = store.4 v313, v310, v304
// CHECK:     v315: int:u64 = iconst 12
// CHECK:     v316: ptr = ptradd v16, v315
// CHECK:     v317: int:u64 = iconst 12
// CHECK:     v318: ptr = ptradd v17, v317
// CHECK:     v319: int:u64 = iconst 12
// CHECK:     v320: ptr = ptradd v290, v319
// CHECK:     v321: int:u32 = load.4 v316, v314
// CHECK:     v322: int:u32 = load.4 v318, v314
// CHECK:     v323: int:u32 = shr v321, v322
// CHECK:     v324: mem = store.4 v323, v320, v314
// CHECK:     v325: int:u64 = iconst 16
// CHECK:     v326: ptr = ptradd v16, v325
// CHECK:     v327: int:u64 = iconst 16
// CHECK:     v328: ptr = ptradd v17, v327
// CHECK:     v329: int:u64 = iconst 16
// CHECK:     v330: ptr = ptradd v290, v329
// CHECK:     v331: int:u32 = load.4 v326, v324
// CHECK:     v332: int:u32 = load.4 v328, v324
// CHECK:     v333: int:u32 = shr v331, v332
// CHECK:     v334: mem = store.4 v333, v330, v324
// CHECK:     v335: int:u64 = iconst 20
// CHECK:     v336: ptr = ptradd v16, v335
// CHECK:     v337: int:u64 = iconst 20
// CHECK:     v338: ptr = ptradd v17, v337
// CHECK:     v339: int:u64 = iconst 20
// CHECK:     v340: ptr = ptradd v290, v339
// CHECK:     v341: int:u32 = load.4 v336, v334
// CHECK:     v342: int:u32 = load.4 v338, v334
// CHECK:     v343: int:u32 = shr v341, v342
// CHECK:     v344: mem = store.4 v343, v340, v334
// CHECK:     v345: int:u64 = iconst 24
// CHECK:     v346: ptr = ptradd v16, v345
// CHECK:     v347: int:u64 = iconst 24
// CHECK:     v348: ptr = ptradd v17, v347
// CHECK:     v349: int:u64 = iconst 24
// CHECK:     v350: ptr = ptradd v290, v349
// CHECK:     v351: int:u32 = load.4 v346, v344
// CHECK:     v352: int:u32 = load.4 v348, v344
// CHECK:     v353: int:u32 = shr v351, v352
// CHECK:     v354: mem = store.4 v353, v350, v344
// CHECK:     v355: int:u64 = iconst 28
// CHECK:     v356: ptr = ptradd v16, v355
// CHECK:     v357: int:u64 = iconst 28
// CHECK:     v358: ptr = ptradd v17, v357
// CHECK:     v359: int:u64 = iconst 28
// CHECK:     v360: ptr = ptradd v290, v359
// CHECK:     v361: int:u32 = load.4 v356, v354
// CHECK:     v362: int:u32 = load.4 v358, v354
// CHECK:     v363: int:u32 = shr v361, v362
// CHECK:     v364: mem = store.4 v363, v360, v354
// CHECK:     v365: int:i64 = load.8 v290, v364
// CHECK:     v366: mem = store.8 v365, v15, v364
// CHECK:     v367: int:i64 = iconst 8
// CHECK:     v368: ptr = ptradd v290, v367
// CHECK:     v369: int:i64 = load.8 v368, v366
// CHECK:     v370: int:i64 = iconst 8
// CHECK:     v371: ptr = ptradd v15, v370
// CHECK:     v372: mem = store.8 v369, v371, v366
// CHECK:     v373: int:i64 = iconst 16
// CHECK:     v374: ptr = ptradd v290, v373
// CHECK:     v375: int:i64 = load.8 v374, v372
// CHECK:     v376: int:i64 = iconst 16
// CHECK:     v377: ptr = ptradd v15, v376
// CHECK:     v378: mem = store.8 v375, v377, v372
// CHECK:     v379: int:i64 = iconst 24
// CHECK:     v380: ptr = ptradd v290, v379
// CHECK:     v381: int:i64 = load.8 v380, v378
// CHECK:     v382: int:i64 = iconst 24
// CHECK:     v383: ptr = ptradd v15, v382
// CHECK:     v384: mem = store.8 v381, v383, v378
// CHECK:     br bb7(v384)
// CHECK:
// CHECK:   bb7(v386: mem):
// CHECK:     v387: ptr = stack_slot 16
// CHECK:     v388: ptr = stack_slot 4
// CHECK:     v389: int:u32 = load.4 v15, v386
// CHECK:     v390: mem = store.4 v389, v388, v386
// CHECK:     v391: int:u16 = load.2 v388, v390
// CHECK:     v392: mem = store.2 v391, v387, v390
// CHECK:     v393: int:u64 = iconst 4
// CHECK:     v394: ptr = ptradd v15, v393
// CHECK:     v395: int:u64 = iconst 2
// CHECK:     v396: ptr = ptradd v387, v395
// CHECK:     v397: int:u32 = load.4 v394, v392
// CHECK:     v398: mem = store.4 v397, v388, v392
// CHECK:     v399: int:u16 = load.2 v388, v398
// CHECK:     v400: mem = store.2 v399, v396, v398
// CHECK:     v401: int:u64 = iconst 8
// CHECK:     v402: ptr = ptradd v15, v401
// CHECK:     v403: int:u64 = iconst 4
// CHECK:     v404: ptr = ptradd v387, v403
// CHECK:     v405: int:u32 = load.4 v402, v400
// CHECK:     v406: mem = store.4 v405, v388, v400
// CHECK:     v407: int:u16 = load.2 v388, v406
// CHECK:     v408: mem = store.2 v407, v404, v406
// CHECK:     v409: int:u64 = iconst 12
// CHECK:     v410: ptr = ptradd v15, v409
// CHECK:     v411: int:u64 = iconst 6
// CHECK:     v412: ptr = ptradd v387, v411
// CHECK:     v413: int:u32 = load.4 v410, v408
// CHECK:     v414: mem = store.4 v413, v388, v408
// CHECK:     v415: int:u16 = load.2 v388, v414
// CHECK:     v416: mem = store.2 v415, v412, v414
// CHECK:     v417: int:u64 = iconst 16
// CHECK:     v418: ptr = ptradd v15, v417
// CHECK:     v419: int:u64 = iconst 8
// CHECK:     v420: ptr = ptradd v387, v419
// CHECK:     v421: int:u32 = load.4 v418, v416
// CHECK:     v422: mem = store.4 v421, v388, v416
// CHECK:     v423: int:u16 = load.2 v388, v422
// CHECK:     v424: mem = store.2 v423, v420, v422
// CHECK:     v425: int:u64 = iconst 20
// CHECK:     v426: ptr = ptradd v15, v425
// CHECK:     v427: int:u64 = iconst 10
// CHECK:     v428: ptr = ptradd v387, v427
// CHECK:     v429: int:u32 = load.4 v426, v424
// CHECK:     v430: mem = store.4 v429, v388, v424
// CHECK:     v431: int:u16 = load.2 v388, v430
// CHECK:     v432: mem = store.2 v431, v428, v430
// CHECK:     v433: int:u64 = iconst 24
// CHECK:     v434: ptr = ptradd v15, v433
// CHECK:     v435: int:u64 = iconst 12
// CHECK:     v436: ptr = ptradd v387, v435
// CHECK:     v437: int:u32 = load.4 v434, v432
// CHECK:     v438: mem = store.4 v437, v388, v432
// CHECK:     v439: int:u16 = load.2 v388, v438
// CHECK:     v440: mem = store.2 v439, v436, v438
// CHECK:     v441: int:u64 = iconst 28
// CHECK:     v442: ptr = ptradd v15, v441
// CHECK:     v443: int:u64 = iconst 14
// CHECK:     v444: ptr = ptradd v387, v443
// CHECK:     v445: int:u32 = load.4 v442, v440
// CHECK:     v446: mem = store.4 v445, v388, v440
// CHECK:     v447: int:u16 = load.2 v388, v446
// CHECK:     v448: mem = store.2 v447, v444, v446
// CHECK:     v449: int:i64 = load.8 v387, v448
// CHECK:     v450: mem = store.8 v449, v18, v448
// CHECK:     v451: int:i64 = iconst 8
// CHECK:     v452: ptr = ptradd v387, v451
// CHECK:     v453: int:i64 = load.8 v452, v450
// CHECK:     v454: int:i64 = iconst 8
// CHECK:     v455: ptr = ptradd v18, v454
// CHECK:     v456: mem = store.8 v453, v455, v450
// CHECK:     br bb8(v456)
// CHECK:
// CHECK:   bb8(v458: mem):
// CHECK:     v459: int:i64 = load.8 v18, v458
// CHECK:     v460: mem = store.8 v459, v2, v458
// CHECK:     v461: int:i64 = iconst 8
// CHECK:     v462: ptr = ptradd v18, v461
// CHECK:     v463: int:i64 = load.8 v462, v460
// CHECK:     v464: int:i64 = iconst 8
// CHECK:     v465: ptr = ptradd v2, v464
// CHECK:     v466: mem = store.8 v463, v465, v460
// CHECK:     v467: int:i64 = iconst 16
// CHECK:     v468: mem = memcopy v1:align8, v2:align8, v467, v466
// CHECK:     ret v1, v468
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
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: ptr = param 2
// CHECK:     v6: ptr = stack_slot 16 align 16
// CHECK:     v7: int:i64 = iconst 16
// CHECK:     v8: mem = memcopy v4:align8, v3:align8, v7, v0
// CHECK:     v9: int:i64 = iconst 16
// CHECK:     v10: mem = memcopy v6:align8, v5:align8, v9, v8
// CHECK:     v11: ptr = stack_slot 16
// CHECK:     v12: int:i64 = iconst 16
// CHECK:     v13: mem = memcopy v11:align16, v4:align16, v12, v10
// CHECK:     v14: ptr = stack_slot 16
// CHECK:     v15: int:i64 = iconst 16
// CHECK:     v16: mem = memcopy v14:align16, v6:align16, v15, v13
// CHECK:     v17: ptr = symbol_addr @_RNvNtNtNtC$HASH_4core9core_arch3x864sse215__mm_mulhi_epu16C$HASH_9simd_cast
// CHECK:     v18: mem, v19: int:i64 = call v17(v2, v11, v14), v16 -> int:i64
// CHECK:     br bb1(v18)
// CHECK:
// CHECK:   bb1(v21: mem):
// CHECK:     v22: int:i64 = iconst 16
// CHECK:     v23: mem = memcopy v1:align8, v2:align8, v22, v21
// CHECK:     ret v1, v23
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
