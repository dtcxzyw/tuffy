// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn core::intrinsics::carrying_mul_add(_1: T, _2: T, _3: T, _4: T) -> (U, T) {
// CHECK:     debug multiplier => _1;
// CHECK:     debug multiplicand => _2;
// CHECK:     debug addend => _3;
// CHECK:     debug carry => _4;
// CHECK:     let mut _0: (U, T);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(move _1, move _2, move _3, move _4) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics16carrying_mul_addmmEC$HASH_16carrying_mul_add(int:u32, int:u32, int:u32, int:u32) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: int:u32 = param 3
// CHECK:     v5: ptr = stack_slot 8 align 4
// CHECK:     v6: ptr = symbol_addr @_RNvXs2_NtNtC$HASH_4core10intrinsics8fallbackmNtB5_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add
// CHECK:     v7: mem, v8: int:i32 = call v6(v1, v2, v3, v4), v0 -> int:i32
// CHECK:     v9: mem = store.4 v8, v5, v7
// CHECK:     v10: int:i32 = call_ret2 v7
// CHECK:     v11: int:i64 = iconst 4
// CHECK:     v12: ptr = ptradd v5, v11
// CHECK:     v13: mem = store.4 v10, v12, v9
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     v16: int:i32 = load.4 v5, v15
// CHECK:     v17: int:i64 = iconst 4
// CHECK:     v18: ptr = ptradd v5, v17
// CHECK:     v19: int:i32 = load.4 v18, v15
// CHECK:     ret v16, v19, v15
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::carrying_mul_add(_1: T, _2: T, _3: T, _4: T) -> (U, T) {
// CHECK:     debug multiplier => _1;
// CHECK:     debug multiplicand => _2;
// CHECK:     debug addend => _3;
// CHECK:     debug carry => _4;
// CHECK:     let mut _0: (U, T);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(move _1, move _2, move _3, move _4) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics16carrying_mul_addnoEC$HASH_16carrying_mul_add(ptr, int:s128, int:s128, int:s128, int:s128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:s128 = param 1
// CHECK:     v3: int:s128 = param 2
// CHECK:     v4: int:s128 = param 3
// CHECK:     v5: int:s128 = param 4
// CHECK:     v6: ptr = symbol_addr @_RNvXs_NtNtC$HASH_4core10intrinsics8fallbacknNtB4_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add
// CHECK:     v7: mem = call v6(v1, v2, v3, v4, v5), v0
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     br bb1(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v1, v10
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::carrying_mul_add(_1: T, _2: T, _3: T, _4: T) -> (U, T) {
// CHECK:     debug multiplier => _1;
// CHECK:     debug multiplicand => _2;
// CHECK:     debug addend => _3;
// CHECK:     debug carry => _4;
// CHECK:     let mut _0: (U, T);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(move _1, move _2, move _3, move _4) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics16carrying_mul_addooEC$HASH_16carrying_mul_add(ptr, int:u128, int:u128, int:u128, int:u128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u128 = param 2
// CHECK:     v4: int:u128 = param 3
// CHECK:     v5: int:u128 = param 4
// CHECK:     v6: ptr = symbol_addr @_RNvXNtNtC$HASH_4core10intrinsics8fallbackoNtB2_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add
// CHECK:     v7: mem = call v6(v1, v2, v3, v4, v5), v0
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     br bb1(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v1, v10
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::carrying_mul_add(_1: T, _2: T, _3: T, _4: T) -> (U, T) {
// CHECK:     debug multiplier => _1;
// CHECK:     debug multiplicand => _2;
// CHECK:     debug addend => _3;
// CHECK:     debug carry => _4;
// CHECK:     let mut _0: (U, T);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(move _1, move _2, move _3, move _4) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics16carrying_mul_addyyEC$HASH_16carrying_mul_add(int:u64, int:u64, int:u64, int:u64) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: ptr = symbol_addr @_RNvXs3_NtNtC$HASH_4core10intrinsics8fallbackyNtB5_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add
// CHECK:     v7: mem, v8: int:i64 = call v6(v1, v2, v3, v4), v0 -> int:i64
// CHECK:     v9: mem = store.8 v8, v5, v7
// CHECK:     v10: int:i64 = call_ret2 v7
// CHECK:     v11: int:i64 = iconst 8
// CHECK:     v12: ptr = ptradd v5, v11
// CHECK:     v13: mem = store.8 v10, v12, v9
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     v16: int:i64 = load.8 v5, v15
// CHECK:     v17: int:i64 = iconst 8
// CHECK:     v18: ptr = ptradd v5, v17
// CHECK:     v19: int:i64 = load.8 v18, v15
// CHECK:     ret v16, v19, v15
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::fallback::wide_mul_u128(_1: u128, _2: u128) -> (u128, u128) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: (u128, u128);
// CHECK:     let mut _3: u128;
// CHECK:     let mut _4: u128;
// CHECK:     let mut _5: u128;
// CHECK:     let mut _7: u128;
// CHECK:     let mut _8: u128;
// CHECK:     scope 1 {
// CHECK:         scope 2 {
// CHECK:             scope 3 {
// CHECK:                 scope 4 {
// CHECK:                     scope 5 {
// CHECK:                         scope 6 {
// CHECK:                             scope 7 {
// CHECK:                                 let _6: u128;
// CHECK:                                 scope 8 {
// CHECK:                                     scope 23 (inlined core::intrinsics::fallback::wide_mul_u128::from_low_high) {
// CHECK:                                         let mut _31: u128;
// CHECK:                                     }
// CHECK:                                     scope 24 (inlined core::intrinsics::fallback::wide_mul_u128::from_low_high) {
// CHECK:                                         let mut _32: u128;
// CHECK:                                     }
// CHECK:                                 }
// CHECK:                             }
// CHECK:                             scope 22 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                                 let mut _29: u128;
// CHECK:                                 let mut _30: u128;
// CHECK:                             }
// CHECK:                         }
// CHECK:                         scope 21 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                             let mut _27: u128;
// CHECK:                             let mut _28: u128;
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 16 (inlined core::intrinsics::fallback::wide_mul_u128::scalar_mul) {
// CHECK:                     let mut _20: u128;
// CHECK:                     let mut _21: u128;
// CHECK:                     let mut _22: u128;
// CHECK:                     scope 17 {
// CHECK:                         scope 18 {
// CHECK:                         }
// CHECK:                         scope 20 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                             let mut _25: u128;
// CHECK:                             let mut _26: u128;
// CHECK:                         }
// CHECK:                     }
// CHECK:                     scope 19 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                         let mut _23: u128;
// CHECK:                         let mut _24: u128;
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 11 (inlined core::intrinsics::fallback::wide_mul_u128::scalar_mul) {
// CHECK:                 let mut _13: u128;
// CHECK:                 let mut _14: u128;
// CHECK:                 let mut _15: u128;
// CHECK:                 scope 12 {
// CHECK:                     scope 13 {
// CHECK:                     }
// CHECK:                     scope 15 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                         let mut _18: u128;
// CHECK:                         let mut _19: u128;
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 14 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:                     let mut _16: u128;
// CHECK:                     let mut _17: u128;
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 10 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:             let mut _11: u128;
// CHECK:             let mut _12: u128;
// CHECK:         }
// CHECK:     }
// CHECK:     scope 9 (inlined core::intrinsics::fallback::wide_mul_u128::to_low_high) {
// CHECK:         let mut _9: u128;
// CHECK:         let mut _10: u128;
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _9 = BitAnd(copy _1, const 18446744073709551615_u128);
// CHECK:         _10 = Shr(copy _1, const 64_i32);
// CHECK:         _11 = BitAnd(copy _2, const 18446744073709551615_u128);
// CHECK:         _12 = Shr(copy _2, const 64_i32);
// CHECK:         StorageLive(_17);
// CHECK:         StorageLive(_13);
// CHECK:         _13 = Mul(copy _11, copy _9);
// CHECK:         _16 = BitAnd(copy _13, const 18446744073709551615_u128);
// CHECK:         _17 = Shr(copy _13, const 64_i32);
// CHECK:         StorageDead(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         _15 = Mul(copy _11, copy _10);
// CHECK:         _14 = Add(move _15, copy _17);
// CHECK:         StorageDead(_15);
// CHECK:         _18 = BitAnd(copy _14, const 18446744073709551615_u128);
// CHECK:         _19 = Shr(copy _14, const 64_i32);
// CHECK:         StorageDead(_14);
// CHECK:         StorageDead(_17);
// CHECK:         StorageLive(_24);
// CHECK:         StorageLive(_20);
// CHECK:         _20 = Mul(copy _12, copy _9);
// CHECK:         _23 = BitAnd(copy _20, const 18446744073709551615_u128);
// CHECK:         _24 = Shr(copy _20, const 64_i32);
// CHECK:         StorageDead(_20);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         _22 = Mul(copy _12, copy _10);
// CHECK:         _21 = Add(move _22, copy _24);
// CHECK:         StorageDead(_22);
// CHECK:         _25 = BitAnd(copy _21, const 18446744073709551615_u128);
// CHECK:         _26 = Shr(copy _21, const 64_i32);
// CHECK:         StorageDead(_21);
// CHECK:         StorageDead(_24);
// CHECK:         StorageLive(_3);
// CHECK:         _3 = Add(copy _18, copy _23);
// CHECK:         _27 = BitAnd(copy _3, const 18446744073709551615_u128);
// CHECK:         _28 = Shr(copy _3, const 64_i32);
// CHECK:         StorageDead(_3);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = Add(copy _19, copy _25);
// CHECK:         _4 = Add(move _5, copy _28);
// CHECK:         StorageDead(_5);
// CHECK:         _29 = BitAnd(copy _4, const 18446744073709551615_u128);
// CHECK:         _30 = Shr(copy _4, const 64_i32);
// CHECK:         StorageDead(_4);
// CHECK:         _6 = Add(copy _26, copy _30);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_31);
// CHECK:         _31 = Shl(copy _27, const 64_i32);
// CHECK:         _7 = BitOr(copy _16, move _31);
// CHECK:         StorageDead(_31);
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_32);
// CHECK:         _32 = Shl(copy _6, const 64_i32);
// CHECK:         _8 = BitOr(copy _29, move _32);
// CHECK:         StorageDead(_32);
// CHECK:         _0 = (move _7, move _8);
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_7);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtNtC$HASH_4core10intrinsics8fallback13wide_mul_u128C$HASH_16carrying_mul_add(ptr, int:u128, int:u128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u128 = param 2
// CHECK:     v4: int:i128 = iconst 18446744073709551615
// CHECK:     v5: int:i128 = and v2, v4:u128
// CHECK:     v6: int:i32 = iconst 64
// CHECK:     v7: int:i64 = iconst 127
// CHECK:     v8: int:i64 = and v6, v7
// CHECK:     v9: int:u128 = shr v2, v8
// CHECK:     v10: int:i128 = iconst 18446744073709551615
// CHECK:     v11: int:i128 = and v3, v10:u128
// CHECK:     v12: int:i32 = iconst 64
// CHECK:     v13: int:i64 = iconst 127
// CHECK:     v14: int:i64 = and v12, v13
// CHECK:     v15: int:u128 = shr v3, v14
// CHECK:     v16: int:i128 = mul v11:u128, v5:u128
// CHECK:     v17: int:i128 = iconst 18446744073709551615
// CHECK:     v18: int:i128 = and v16:u128, v17:u128
// CHECK:     v19: int:i32 = iconst 64
// CHECK:     v20: int:i64 = iconst 127
// CHECK:     v21: int:i64 = and v19, v20
// CHECK:     v22: int:u128 = shr v16:u128, v21
// CHECK:     v23: int:i128 = mul v11:u128, v9
// CHECK:     v24: int:i128 = add v23:u128, v22
// CHECK:     v25: int:i128 = iconst 18446744073709551615
// CHECK:     v26: int:i128 = and v24:u128, v25:u128
// CHECK:     v27: int:i32 = iconst 64
// CHECK:     v28: int:i64 = iconst 127
// CHECK:     v29: int:i64 = and v27, v28
// CHECK:     v30: int:u128 = shr v24:u128, v29
// CHECK:     v31: int:i128 = mul v15, v5:u128
// CHECK:     v32: int:i128 = iconst 18446744073709551615
// CHECK:     v33: int:i128 = and v31:u128, v32:u128
// CHECK:     v34: int:i32 = iconst 64
// CHECK:     v35: int:i64 = iconst 127
// CHECK:     v36: int:i64 = and v34, v35
// CHECK:     v37: int:u128 = shr v31:u128, v36
// CHECK:     v38: int:i128 = mul v15, v9
// CHECK:     v39: int:i128 = add v38:u128, v37
// CHECK:     v40: int:i128 = iconst 18446744073709551615
// CHECK:     v41: int:i128 = and v39:u128, v40:u128
// CHECK:     v42: int:i32 = iconst 64
// CHECK:     v43: int:i64 = iconst 127
// CHECK:     v44: int:i64 = and v42, v43
// CHECK:     v45: int:u128 = shr v39:u128, v44
// CHECK:     v46: int:i128 = add v26:u128, v33:u128
// CHECK:     v47: int:i128 = iconst 18446744073709551615
// CHECK:     v48: int:i128 = and v46:u128, v47:u128
// CHECK:     v49: int:i32 = iconst 64
// CHECK:     v50: int:i64 = iconst 127
// CHECK:     v51: int:i64 = and v49, v50
// CHECK:     v52: int:u128 = shr v46:u128, v51
// CHECK:     v53: int:i128 = add v30, v41:u128
// CHECK:     v54: int:i128 = add v53:u128, v52
// CHECK:     v55: int:i128 = iconst 18446744073709551615
// CHECK:     v56: int:i128 = and v54:u128, v55:u128
// CHECK:     v57: int:i32 = iconst 64
// CHECK:     v58: int:i64 = iconst 127
// CHECK:     v59: int:i64 = and v57, v58
// CHECK:     v60: int:u128 = shr v54:u128, v59
// CHECK:     v61: int:i128 = add v45, v60
// CHECK:     v62: int:i32 = iconst 64
// CHECK:     v63: int:i64 = iconst 127
// CHECK:     v64: int:i64 = and v62, v63
// CHECK:     v65: int:i128 = shl v48:u128, v64
// CHECK:     v66: int:i128 = or v18:u128, v65:u128
// CHECK:     v67: int:i32 = iconst 64
// CHECK:     v68: int:i64 = iconst 127
// CHECK:     v69: int:i64 = and v67, v68
// CHECK:     v70: int:i128 = shl v61:u128, v69
// CHECK:     v71: int:i128 = or v56:u128, v70:u128
// CHECK:     v72: mem = store.16 v66, v1, v0
// CHECK:     v73: int:i64 = iconst 16
// CHECK:     v74: ptr = ptradd v1, v73
// CHECK:     v75: mem = store.16 v71, v74, v72
// CHECK:     ret v1, v75
// CHECK: }
// CHECK:
// CHECK: fn <u128 as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(_1: u128, _2: u128, _3: u128, _4: u128) -> (u128, u128) {
// CHECK:     debug self => _1;
// CHECK:     debug b => _2;
// CHECK:     debug c => _3;
// CHECK:     debug d => _4;
// CHECK:     let mut _0: (u128, u128);
// CHECK:     let _5: u128;
// CHECK:     let mut _6: u128;
// CHECK:     let mut _7: (u128, u128);
// CHECK:     let mut _10: (u128, bool);
// CHECK:     let mut _11: u128;
// CHECK:     let mut _14: (u128, bool);
// CHECK:     let mut _15: u128;
// CHECK:     scope 1 {
// CHECK:         debug low => _5;
// CHECK:         debug high => _6;
// CHECK:         let _8: u128;
// CHECK:         let _9: bool;
// CHECK:         scope 2 {
// CHECK:             debug low => _8;
// CHECK:             debug carry => _9;
// CHECK:             let _12: u128;
// CHECK:             let _13: bool;
// CHECK:             scope 3 {
// CHECK:                 debug low => _12;
// CHECK:                 debug carry => _13;
// CHECK:             }
// CHECK:             scope 6 (inlined core::num::<impl u128>::overflowing_add) {
// CHECK:                 debug self => _8;
// CHECK:                 debug rhs => _4;
// CHECK:                 scope 7 {
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 4 (inlined core::num::<impl u128>::overflowing_add) {
// CHECK:             debug self => _5;
// CHECK:             debug rhs => _3;
// CHECK:             scope 5 {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_7);
// CHECK:         _7 = core::intrinsics::fallback::wide_mul_u128(move _1, move _2) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _5 = copy (_7.0: u128);
// CHECK:         _6 = copy (_7.1: u128);
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = AddWithOverflow(copy _5, copy _3);
// CHECK:         _8 = copy (_10.0: u128);
// CHECK:         _9 = copy (_10.1: bool);
// CHECK:         StorageDead(_10);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _9 as u128 (IntToInt);
// CHECK:         _6 = Add(copy _6, move _11);
// CHECK:         StorageDead(_11);
// CHECK:         StorageLive(_14);
// CHECK:         _14 = AddWithOverflow(copy _8, copy _4);
// CHECK:         _12 = copy (_14.0: u128);
// CHECK:         _13 = copy (_14.1: bool);
// CHECK:         StorageDead(_14);
// CHECK:         StorageLive(_15);
// CHECK:         _15 = copy _13 as u128 (IntToInt);
// CHECK:         _6 = Add(copy _6, move _15);
// CHECK:         StorageDead(_15);
// CHECK:         _0 = (copy _12, move _6);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXNtNtC$HASH_4core10intrinsics8fallbackoNtB2_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add(ptr, int:u128, int:u128, int:u128, int:u128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u128 = param 2
// CHECK:     v4: int:u128 = param 3
// CHECK:     v5: int:u128 = param 4
// CHECK:     v6: ptr = stack_slot 32
// CHECK:     v7: ptr = symbol_addr @_RNvNtNtC$HASH_4core10intrinsics8fallback13wide_mul_u128C$HASH_16carrying_mul_add
// CHECK:     v8: mem = call v7(v6, v2, v3), v0
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u128 = load.16 v6, v11
// CHECK:     v13: int:i64 = iconst 16
// CHECK:     v14: ptr = ptradd v6, v13
// CHECK:     v15: int:u128 = load.16 v14, v11
// CHECK:     v16: int:u128, v17: bool = uadd_overflow.128 v12, v4
// CHECK:     v18: int:u64 = iconst 1
// CHECK:     v19: int:u64 = iconst 0
// CHECK:     v20: int:u64 = select v17, v18, v19
// CHECK:     v21: int:u64 = zext v20:u8, 64
// CHECK:     v22: int:u128 = zext v21, 128
// CHECK:     v23: int:i128 = add v15, v22
// CHECK:     v24: int:u128, v25: bool = uadd_overflow.128 v16, v5
// CHECK:     v26: int:u64 = iconst 1
// CHECK:     v27: int:u64 = iconst 0
// CHECK:     v28: int:u64 = select v25, v26, v27
// CHECK:     v29: int:u64 = zext v28:u8, 64
// CHECK:     v30: int:u128 = zext v29, 128
// CHECK:     v31: int:i128 = add v23:u128, v30
// CHECK:     v32: mem = store.16 v24, v1, v11
// CHECK:     v33: int:i64 = iconst 16
// CHECK:     v34: ptr = ptradd v1, v33
// CHECK:     v35: mem = store.16 v31, v34, v32
// CHECK:     ret v1, v35
// CHECK: }
// CHECK:
// CHECK: fn <u32 as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(_1: u32, _2: u32, _3: u32, _4: u32) -> (u32, u32) {
// CHECK:     debug self => _1;
// CHECK:     debug a => _2;
// CHECK:     debug b => _3;
// CHECK:     debug c => _4;
// CHECK:     let mut _0: (u32, u32);
// CHECK:     let _5: u64;
// CHECK:     let mut _6: u64;
// CHECK:     let mut _7: u64;
// CHECK:     let mut _8: u64;
// CHECK:     let mut _9: u64;
// CHECK:     let mut _10: u64;
// CHECK:     let mut _11: u64;
// CHECK:     let mut _12: u32;
// CHECK:     let mut _13: u32;
// CHECK:     let mut _14: u64;
// CHECK:     scope 1 {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _1 as u64 (IntToInt);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _2 as u64 (IntToInt);
// CHECK:         _7 = Mul(move _8, move _9);
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = copy _3 as u64 (IntToInt);
// CHECK:         _6 = Add(move _7, move _10);
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _4 as u64 (IntToInt);
// CHECK:         _5 = Add(move _6, move _11);
// CHECK:         StorageDead(_11);
// CHECK:         StorageDead(_6);
// CHECK:         _12 = copy _5 as u32 (IntToInt);
// CHECK:         StorageLive(_14);
// CHECK:         _14 = Shr(copy _5, const 32_u32);
// CHECK:         _13 = move _14 as u32 (IntToInt);
// CHECK:         StorageDead(_14);
// CHECK:         _0 = (copy _12, copy _13);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXs2_NtNtC$HASH_4core10intrinsics8fallbackmNtB5_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add(int:u32, int:u32, int:u32, int:u32) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: int:u32 = param 3
// CHECK:     v5: ptr = stack_slot 8 align 4
// CHECK:     v6: int:u64 = zext v1, 64
// CHECK:     v7: int:u64 = zext v2, 64
// CHECK:     v8: int:i64 = mul v6, v7
// CHECK:     v9: int:u64 = zext v8, 64
// CHECK:     v10: int:u64 = zext v3, 64
// CHECK:     v11: int:i64 = add v9, v10
// CHECK:     v12: int:u64 = zext v11, 64
// CHECK:     v13: int:u64 = zext v4, 64
// CHECK:     v14: int:i64 = add v12, v13
// CHECK:     v15: int:u64 = zext v14, 64
// CHECK:     v16: int:u64 = iconst 4294967295
// CHECK:     v17: int:u32 = and v15, v16
// CHECK:     v18: int:i32 = iconst 32
// CHECK:     v19: int:i64 = iconst 63
// CHECK:     v20: int:i64 = and v18, v19
// CHECK:     v21: int:u64 = shr v15, v20
// CHECK:     v22: int:u64 = iconst 4294967295
// CHECK:     v23: int:u32 = and v21, v22
// CHECK:     v24: mem = store.4 v17, v5, v0
// CHECK:     v25: int:i64 = iconst 4
// CHECK:     v26: ptr = ptradd v5, v25
// CHECK:     v27: mem = store.4 v23, v26, v24
// CHECK:     v28: int:i32 = load.4 v5, v27
// CHECK:     v29: int:i64 = iconst 4
// CHECK:     v30: ptr = ptradd v5, v29
// CHECK:     v31: int:i32 = load.4 v30, v27
// CHECK:     ret v28, v31, v27
// CHECK: }
// CHECK:
// CHECK: fn <u64 as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(_1: u64, _2: u64, _3: u64, _4: u64) -> (u64, u64) {
// CHECK:     debug self => _1;
// CHECK:     debug a => _2;
// CHECK:     debug b => _3;
// CHECK:     debug c => _4;
// CHECK:     let mut _0: (u64, u64);
// CHECK:     let _5: u128;
// CHECK:     let mut _6: u128;
// CHECK:     let mut _7: u128;
// CHECK:     let mut _8: u128;
// CHECK:     let mut _9: u128;
// CHECK:     let mut _10: u128;
// CHECK:     let mut _11: u128;
// CHECK:     let mut _12: u64;
// CHECK:     let mut _13: u64;
// CHECK:     let mut _14: u128;
// CHECK:     scope 1 {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _1 as u128 (IntToInt);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _2 as u128 (IntToInt);
// CHECK:         _7 = Mul(move _8, move _9);
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = copy _3 as u128 (IntToInt);
// CHECK:         _6 = Add(move _7, move _10);
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _4 as u128 (IntToInt);
// CHECK:         _5 = Add(move _6, move _11);
// CHECK:         StorageDead(_11);
// CHECK:         StorageDead(_6);
// CHECK:         _12 = copy _5 as u64 (IntToInt);
// CHECK:         StorageLive(_14);
// CHECK:         _14 = Shr(copy _5, const 64_u32);
// CHECK:         _13 = move _14 as u64 (IntToInt);
// CHECK:         StorageDead(_14);
// CHECK:         _0 = (copy _12, copy _13);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXs3_NtNtC$HASH_4core10intrinsics8fallbackyNtB5_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add(int:u64, int:u64, int:u64, int:u64) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: int:u128 = zext v1, 128
// CHECK:     v7: int:u128 = zext v2, 128
// CHECK:     v8: int:i128 = mul v6, v7
// CHECK:     v9: int:u128 = zext v3, 128
// CHECK:     v10: int:i128 = add v8:u128, v9
// CHECK:     v11: int:u128 = zext v4, 128
// CHECK:     v12: int:i128 = add v10:u128, v11
// CHECK:     v13: int:u64 = iconst -1
// CHECK:     v14: int:u64 = and v12, v13
// CHECK:     v15: int:i32 = iconst 64
// CHECK:     v16: int:i64 = iconst 127
// CHECK:     v17: int:i64 = and v15, v16
// CHECK:     v18: int:u128 = shr v12:u128, v17
// CHECK:     v19: int:u64 = iconst -1
// CHECK:     v20: int:u64 = and v18, v19
// CHECK:     v21: mem = store.8 v14, v5, v0
// CHECK:     v22: int:i64 = iconst 8
// CHECK:     v23: ptr = ptradd v5, v22
// CHECK:     v24: mem = store.8 v20, v23, v21
// CHECK:     v25: int:i64 = load.8 v5, v24
// CHECK:     v26: int:i64 = iconst 8
// CHECK:     v27: ptr = ptradd v5, v26
// CHECK:     v28: int:i64 = load.8 v27, v24
// CHECK:     ret v25, v28, v24
// CHECK: }
// CHECK:
// CHECK: fn <i128 as core::intrinsics::fallback::CarryingMulAdd>::carrying_mul_add(_1: i128, _2: i128, _3: i128, _4: i128) -> (u128, i128) {
// CHECK:     debug self => _1;
// CHECK:     debug b => _2;
// CHECK:     debug c => _3;
// CHECK:     debug d => _4;
// CHECK:     let mut _0: (u128, i128);
// CHECK:     let _5: u128;
// CHECK:     let _6: u128;
// CHECK:     let mut _7: (u128, u128);
// CHECK:     let mut _8: u128;
// CHECK:     let mut _9: u128;
// CHECK:     let mut _11: i128;
// CHECK:     let mut _12: i128;
// CHECK:     let mut _13: i128;
// CHECK:     let mut _14: i128;
// CHECK:     let mut _15: i128;
// CHECK:     let mut _16: i128;
// CHECK:     let mut _19: (u128, bool);
// CHECK:     let mut _20: u128;
// CHECK:     let mut _21: i128;
// CHECK:     let mut _22: i128;
// CHECK:     let mut _23: i128;
// CHECK:     let mut _24: i128;
// CHECK:     let mut _27: (u128, bool);
// CHECK:     let mut _28: u128;
// CHECK:     let mut _29: i128;
// CHECK:     let mut _30: i128;
// CHECK:     let mut _31: i128;
// CHECK:     let mut _32: i128;
// CHECK:     scope 1 {
// CHECK:         debug low => _5;
// CHECK:         debug high => _6;
// CHECK:         let mut _10: i128;
// CHECK:         scope 2 {
// CHECK:             debug high => _10;
// CHECK:             let _17: u128;
// CHECK:             let _18: bool;
// CHECK:             scope 3 {
// CHECK:                 debug low => _17;
// CHECK:                 debug carry => _18;
// CHECK:                 let _25: u128;
// CHECK:                 let _26: bool;
// CHECK:                 scope 4 {
// CHECK:                     debug low => _25;
// CHECK:                     debug carry => _26;
// CHECK:                     scope 14 (inlined core::num::<impl i128>::wrapping_add) {
// CHECK:                         debug self => _10;
// CHECK:                         debug rhs => _30;
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 11 (inlined core::num::<impl i128>::wrapping_add) {
// CHECK:                     debug self => _10;
// CHECK:                     debug rhs => _22;
// CHECK:                 }
// CHECK:                 scope 12 (inlined core::num::<impl u128>::overflowing_add) {
// CHECK:                     debug self => _17;
// CHECK:                     debug rhs => _28;
// CHECK:                     scope 13 {
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 5 (inlined core::num::<impl i128>::wrapping_mul) {
// CHECK:                 debug self => _13;
// CHECK:                 debug rhs => _2;
// CHECK:             }
// CHECK:             scope 6 (inlined core::num::<impl i128>::wrapping_add) {
// CHECK:                 debug self => _10;
// CHECK:                 debug rhs => _12;
// CHECK:             }
// CHECK:             scope 7 (inlined core::num::<impl i128>::wrapping_mul) {
// CHECK:                 debug self => _1;
// CHECK:                 debug rhs => _16;
// CHECK:             }
// CHECK:             scope 8 (inlined core::num::<impl i128>::wrapping_add) {
// CHECK:                 debug self => _10;
// CHECK:                 debug rhs => _15;
// CHECK:             }
// CHECK:             scope 9 (inlined core::num::<impl u128>::overflowing_add) {
// CHECK:                 debug self => _5;
// CHECK:                 debug rhs => _20;
// CHECK:                 scope 10 {
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _1 as u128 (IntToInt);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _2 as u128 (IntToInt);
// CHECK:         _7 = core::intrinsics::fallback::wide_mul_u128(move _8, move _9) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         _5 = copy (_7.0: u128);
// CHECK:         _6 = copy (_7.1: u128);
// CHECK:         StorageDead(_7);
// CHECK:         _10 = copy _6 as i128 (IntToInt);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_13);
// CHECK:         _13 = Shr(copy _1, const 127_i32);
// CHECK:         _12 = Mul(copy _13, copy _2);
// CHECK:         StorageDead(_13);
// CHECK:         _11 = Add(copy _10, copy _12);
// CHECK:         StorageDead(_12);
// CHECK:         _10 = move _11;
// CHECK:         StorageDead(_11);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         StorageLive(_16);
// CHECK:         _16 = Shr(copy _2, const 127_i32);
// CHECK:         _15 = Mul(copy _1, copy _16);
// CHECK:         StorageDead(_16);
// CHECK:         _14 = Add(copy _10, copy _15);
// CHECK:         StorageDead(_15);
// CHECK:         _10 = move _14;
// CHECK:         StorageDead(_14);
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_20);
// CHECK:         _20 = copy _3 as u128 (IntToInt);
// CHECK:         _19 = AddWithOverflow(copy _5, copy _20);
// CHECK:         StorageDead(_20);
// CHECK:         _17 = copy (_19.0: u128);
// CHECK:         _18 = copy (_19.1: bool);
// CHECK:         StorageDead(_19);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_23);
// CHECK:         _23 = copy _18 as i128 (IntToInt);
// CHECK:         StorageLive(_24);
// CHECK:         _24 = Shr(copy _3, const 127_i32);
// CHECK:         _22 = Add(move _23, move _24);
// CHECK:         StorageDead(_24);
// CHECK:         StorageDead(_23);
// CHECK:         _21 = Add(copy _10, copy _22);
// CHECK:         StorageDead(_22);
// CHECK:         _10 = move _21;
// CHECK:         StorageDead(_21);
// CHECK:         StorageLive(_27);
// CHECK:         StorageLive(_28);
// CHECK:         _28 = copy _4 as u128 (IntToInt);
// CHECK:         _27 = AddWithOverflow(copy _17, copy _28);
// CHECK:         StorageDead(_28);
// CHECK:         _25 = copy (_27.0: u128);
// CHECK:         _26 = copy (_27.1: bool);
// CHECK:         StorageDead(_27);
// CHECK:         StorageLive(_29);
// CHECK:         StorageLive(_30);
// CHECK:         StorageLive(_31);
// CHECK:         _31 = copy _26 as i128 (IntToInt);
// CHECK:         StorageLive(_32);
// CHECK:         _32 = Shr(copy _4, const 127_i32);
// CHECK:         _30 = Add(move _31, move _32);
// CHECK:         StorageDead(_32);
// CHECK:         StorageDead(_31);
// CHECK:         _29 = Add(copy _10, copy _30);
// CHECK:         StorageDead(_30);
// CHECK:         _10 = move _29;
// CHECK:         StorageDead(_29);
// CHECK:         _0 = (copy _25, move _10);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXs_NtNtC$HASH_4core10intrinsics8fallbacknNtB4_14CarryingMulAdd16carrying_mul_addC$HASH_16carrying_mul_add(ptr, int:s128, int:s128, int:s128, int:s128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:s128 = param 1
// CHECK:     v3: int:s128 = param 2
// CHECK:     v4: int:s128 = param 3
// CHECK:     v5: int:s128 = param 4
// CHECK:     v6: ptr = stack_slot 32
// CHECK:     v7: ptr = symbol_addr @_RNvNtNtC$HASH_4core10intrinsics8fallback13wide_mul_u128C$HASH_16carrying_mul_add
// CHECK:     v8: mem = call v7(v6, v2:u128, v3:u128), v0
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u128 = load.16 v6, v11
// CHECK:     v13: int:i64 = iconst 16
// CHECK:     v14: ptr = ptradd v6, v13
// CHECK:     v15: int:u128 = load.16 v14, v11
// CHECK:     v16: int:i32 = iconst 127
// CHECK:     v17: int:i64 = iconst 127
// CHECK:     v18: int:i64 = and v16, v17
// CHECK:     v19: int:s128 = shr v2, v18
// CHECK:     v20: int:i128 = mul v19, v3
// CHECK:     v21: int:i128 = add v15:s128, v20:s128
// CHECK:     v22: int:i32 = iconst 127
// CHECK:     v23: int:i64 = iconst 127
// CHECK:     v24: int:i64 = and v22, v23
// CHECK:     v25: int:s128 = shr v3, v24
// CHECK:     v26: int:i128 = mul v2, v25
// CHECK:     v27: int:i128 = add v21:s128, v26:s128
// CHECK:     v28: int:u128, v29: bool = uadd_overflow.128 v12, v4:u128
// CHECK:     v30: int:u64 = iconst 1
// CHECK:     v31: int:u64 = iconst 0
// CHECK:     v32: int:u64 = select v29, v30, v31
// CHECK:     v33: int:u64 = zext v32:u8, 64
// CHECK:     v34: int:u128 = zext v33, 128
// CHECK:     v35: int:i32 = iconst 127
// CHECK:     v36: int:i64 = iconst 127
// CHECK:     v37: int:i64 = and v35, v36
// CHECK:     v38: int:s128 = shr v4, v37
// CHECK:     v39: int:i128 = add v34:s128, v38
// CHECK:     v40: int:i128 = add v27:s128, v39:s128
// CHECK:     v41: int:u128, v42: bool = uadd_overflow.128 v28, v5:u128
// CHECK:     v43: int:u64 = iconst 1
// CHECK:     v44: int:u64 = iconst 0
// CHECK:     v45: int:u64 = select v42, v43, v44
// CHECK:     v46: int:u64 = zext v45:u8, 64
// CHECK:     v47: int:u128 = zext v46, 128
// CHECK:     v48: int:i32 = iconst 127
// CHECK:     v49: int:i64 = iconst 127
// CHECK:     v50: int:i64 = and v48, v49
// CHECK:     v51: int:s128 = shr v5, v50
// CHECK:     v52: int:i128 = add v47:s128, v51
// CHECK:     v53: int:i128 = add v40:s128, v52:s128
// CHECK:     v54: mem = store.16 v41, v1, v11
// CHECK:     v55: int:i64 = iconst 16
// CHECK:     v56: ptr = ptradd v1, v55
// CHECK:     v57: mem = store.16 v53, v56, v54
// CHECK:     ret v1, v57
// CHECK: }
// CHECK:
// CHECK: fn carrying_mul_add_i128(_1: i128, _2: i128, _3: i128, _4: i128) -> (u128, i128) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug carry => _3;
// CHECK:     debug add => _4;
// CHECK:     let mut _0: (u128, i128);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::carrying_mul_add::<i128, u128>(move _1, move _2, move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @carrying_mul_add_i128(ptr, int:s128, int:s128, int:s128, int:s128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:s128 = param 1
// CHECK:     v3: int:s128 = param 2
// CHECK:     v4: int:s128 = param 3
// CHECK:     v5: int:s128 = param 4
// CHECK:     v6: int:s128, v7: int = scarrying_mul_add.128 v2, v3, v4, v5
// CHECK:     v8: ptr = stack_slot 32
// CHECK:     v9: mem = store.16 v6, v8, v0
// CHECK:     v10: int:u64 = iconst 16
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.16 v7, v11, v9
// CHECK:     v13: int:i64 = load.8 v8, v12
// CHECK:     v14: mem = store.8 v13, v1, v12
// CHECK:     v15: int:i64 = iconst 8
// CHECK:     v16: ptr = ptradd v8, v15
// CHECK:     v17: int:i64 = load.8 v16, v14
// CHECK:     v18: int:i64 = iconst 8
// CHECK:     v19: ptr = ptradd v1, v18
// CHECK:     v20: mem = store.8 v17, v19, v14
// CHECK:     v21: int:i64 = iconst 16
// CHECK:     v22: ptr = ptradd v8, v21
// CHECK:     v23: int:i64 = load.8 v22, v20
// CHECK:     v24: int:i64 = iconst 16
// CHECK:     v25: ptr = ptradd v1, v24
// CHECK:     v26: mem = store.8 v23, v25, v20
// CHECK:     v27: int:i64 = iconst 24
// CHECK:     v28: ptr = ptradd v8, v27
// CHECK:     v29: int:i64 = load.8 v28, v26
// CHECK:     v30: int:i64 = iconst 24
// CHECK:     v31: ptr = ptradd v1, v30
// CHECK:     v32: mem = store.8 v29, v31, v26
// CHECK:     br bb1(v32)
// CHECK:
// CHECK:   bb1(v34: mem):
// CHECK:     ret v1, v34
// CHECK: }
// CHECK:
// CHECK: fn carrying_mul_add_u128(_1: u128, _2: u128, _3: u128, _4: u128) -> (u128, u128) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug carry => _3;
// CHECK:     debug add => _4;
// CHECK:     let mut _0: (u128, u128);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::carrying_mul_add::<u128, u128>(move _1, move _2, move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @carrying_mul_add_u128(ptr, int:u128, int:u128, int:u128, int:u128) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u128 = param 2
// CHECK:     v4: int:u128 = param 3
// CHECK:     v5: int:u128 = param 4
// CHECK:     v6: int:u128, v7: int = ucarrying_mul_add.128 v2, v3, v4, v5
// CHECK:     v8: ptr = stack_slot 32
// CHECK:     v9: mem = store.16 v6, v8, v0
// CHECK:     v10: int:u64 = iconst 16
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.16 v7, v11, v9
// CHECK:     v13: int:i64 = load.8 v8, v12
// CHECK:     v14: mem = store.8 v13, v1, v12
// CHECK:     v15: int:i64 = iconst 8
// CHECK:     v16: ptr = ptradd v8, v15
// CHECK:     v17: int:i64 = load.8 v16, v14
// CHECK:     v18: int:i64 = iconst 8
// CHECK:     v19: ptr = ptradd v1, v18
// CHECK:     v20: mem = store.8 v17, v19, v14
// CHECK:     v21: int:i64 = iconst 16
// CHECK:     v22: ptr = ptradd v8, v21
// CHECK:     v23: int:i64 = load.8 v22, v20
// CHECK:     v24: int:i64 = iconst 16
// CHECK:     v25: ptr = ptradd v1, v24
// CHECK:     v26: mem = store.8 v23, v25, v20
// CHECK:     v27: int:i64 = iconst 24
// CHECK:     v28: ptr = ptradd v8, v27
// CHECK:     v29: int:i64 = load.8 v28, v26
// CHECK:     v30: int:i64 = iconst 24
// CHECK:     v31: ptr = ptradd v1, v30
// CHECK:     v32: mem = store.8 v29, v31, v26
// CHECK:     br bb1(v32)
// CHECK:
// CHECK:   bb1(v34: mem):
// CHECK:     ret v1, v34
// CHECK: }
// CHECK:
// CHECK: fn carrying_mul_add_u32(_1: u32, _2: u32, _3: u32, _4: u32) -> (u32, u32) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug carry => _3;
// CHECK:     debug add => _4;
// CHECK:     let mut _0: (u32, u32);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::carrying_mul_add::<u32, u32>(move _1, move _2, move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @carrying_mul_add_u32(int:u32, int:u32, int:u32, int:u32) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: int:u32 = param 3
// CHECK:     v5: ptr = stack_slot 8 align 4
// CHECK:     v6: int:u32, v7: int = ucarrying_mul_add.32 v1, v2, v3, v4
// CHECK:     v8: ptr = stack_slot 8
// CHECK:     v9: mem = store.4 v6, v8, v0
// CHECK:     v10: int:u64 = iconst 4
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.4 v7, v11, v9
// CHECK:     v13: int:i64 = load.8 v8, v12
// CHECK:     v14: mem = store.8 v13, v5, v12
// CHECK:     br bb1(v14)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i32 = load.4 v5, v16
// CHECK:     v18: int:i64 = iconst 4
// CHECK:     v19: ptr = ptradd v5, v18
// CHECK:     v20: int:i32 = load.4 v19, v16
// CHECK:     ret v17, v20, v16
// CHECK: }
// CHECK:
// CHECK: fn carrying_mul_add_u64(_1: u64, _2: u64, _3: u64, _4: u64) -> (u64, u64) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug carry => _3;
// CHECK:     debug add => _4;
// CHECK:     let mut _0: (u64, u64);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::carrying_mul_add::<u64, u64>(move _1, move _2, move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @carrying_mul_add_u64(int:u64, int:u64, int:u64, int:u64) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: int:u64, v7: int = ucarrying_mul_add.64 v1, v2, v3, v4
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: mem = store.8 v6, v8, v0
// CHECK:     v10: int:u64 = iconst 8
// CHECK:     v11: ptr = ptradd v8, v10
// CHECK:     v12: mem = store.8 v7, v11, v9
// CHECK:     v13: int:i64 = load.8 v8, v12
// CHECK:     v14: mem = store.8 v13, v5, v12
// CHECK:     v15: int:i64 = iconst 8
// CHECK:     v16: ptr = ptradd v8, v15
// CHECK:     v17: int:i64 = load.8 v16, v14
// CHECK:     v18: int:i64 = iconst 8
// CHECK:     v19: ptr = ptradd v5, v18
// CHECK:     v20: mem = store.8 v17, v19, v14
// CHECK:     br bb1(v20)
// CHECK:
// CHECK:   bb1(v22: mem):
// CHECK:     v23: int:i64 = load.8 v5, v22
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v5, v24
// CHECK:     v26: int:i64 = load.8 v25, v22
// CHECK:     ret v23, v26, v22
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::carrying_mul_add;

#[no_mangle]
pub unsafe fn carrying_mul_add_u32(a: u32, b: u32, carry: u32, add: u32) -> (u32, u32) {
    carrying_mul_add(a, b, carry, add)
}

#[no_mangle]
pub unsafe fn carrying_mul_add_u64(a: u64, b: u64, carry: u64, add: u64) -> (u64, u64) {
    carrying_mul_add(a, b, carry, add)
}

#[no_mangle]
pub unsafe fn carrying_mul_add_u128(
    a: u128,
    b: u128,
    carry: u128,
    add: u128,
) -> (u128, u128) {
    carrying_mul_add(a, b, carry, add)
}

#[no_mangle]
pub unsafe fn carrying_mul_add_i128(a: i128, b: i128, carry: i128, add: i128) -> (u128, i128) {
    carrying_mul_add(a, b, carry, add)
}
