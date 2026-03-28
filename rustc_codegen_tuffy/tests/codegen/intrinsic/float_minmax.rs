// compile-flags: -Zmir-opt-level=0 -C debug-assertions=off
// CHECK: fn core::intrinsics::maximumf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug x => _1;
// CHECK:     debug y => _2;
// CHECK:     let mut _0: f32;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::f32::<impl f32>::is_sign_positive) {
// CHECK:         debug self => _1;
// CHECK:         let mut _7: bool;
// CHECK:         scope 2 (inlined core::f32::<impl f32>::is_sign_negative) {
// CHECK:             let mut _8: u32;
// CHECK:             let mut _9: u32;
// CHECK:             scope 3 (inlined core::f32::<impl f32>::to_bits) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 4 (inlined core::f32::<impl f32>::is_sign_negative) {
// CHECK:         debug self => _2;
// CHECK:         let mut _10: u32;
// CHECK:         let mut _11: u32;
// CHECK:         scope 5 (inlined core::f32::<impl f32>::to_bits) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = Gt(copy _1, copy _2);
// CHECK:         switchInt(move _3) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Gt(copy _2, copy _1);
// CHECK:         switchInt(move _4) -> [0: bb4, otherwise: bb3];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = Eq(copy _1, copy _2);
// CHECK:         switchInt(move _5) -> [0: bb12, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _1 as u32 (Transmute);
// CHECK:         _8 = BitAnd(move _9, const 2147483648_u32);
// CHECK:         StorageDead(_9);
// CHECK:         _7 = Ne(move _8, const 0_u32);
// CHECK:         StorageDead(_8);
// CHECK:         _6 = Not(move _7);
// CHECK:         StorageDead(_7);
// CHECK:         switchInt(move _6) -> [0: bb9, otherwise: bb6];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _2 as u32 (Transmute);
// CHECK:         _10 = BitAnd(move _11, const 2147483648_u32);
// CHECK:         StorageDead(_11);
// CHECK:         switchInt(copy _10) -> [0: bb8, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_10);
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageDead(_10);
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         StorageDead(_6);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageDead(_4);
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsa3SJzwB9S2T_4core10intrinsics10maximumf32CshcqLDH83PT8_12float_minmax(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: ptr = stack_slot 4
// CHECK:     v4: bool = fcmp.ogt v1, v2
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.4 v1, v3, v13
// CHECK:     br bb15(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: bool = fcmp.ogt v2, v1
// CHECK:     v18: int:u64 = iconst 1
// CHECK:     v19: int:u64 = iconst 0
// CHECK:     v20: int:u64 = select v17, v18, v19
// CHECK:     v21: int:i64 = iconst 255
// CHECK:     v22: int:u64 = and v20, v21
// CHECK:     v23: int:i8 = iconst 0
// CHECK:     v24: bool = icmp.eq v22, v23
// CHECK:     brif v24, bb4(v16), bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     v27: mem = store.4 v2, v3, v26
// CHECK:     br bb14(v27)
// CHECK:
// CHECK:   bb4(v29: mem):
// CHECK:     v30: bool = fcmp.oeq v1, v2
// CHECK:     v31: int:u64 = iconst 1
// CHECK:     v32: int:u64 = iconst 0
// CHECK:     v33: int:u64 = select v30, v31, v32
// CHECK:     v34: int:i64 = iconst 255
// CHECK:     v35: int:u64 = and v33, v34
// CHECK:     v36: int:i8 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb12(v29), bb5(v29)
// CHECK:
// CHECK:   bb5(v39: mem):
// CHECK:     v40: ptr = stack_slot 4
// CHECK:     v41: mem = store.4 v1, v40, v39
// CHECK:     v42: int:i32 = load.4 v40, v41
// CHECK:     v43: int:i32 = iconst 2147483648
// CHECK:     v44: int:i32 = and v42:u32, v43:u32
// CHECK:     v45: int:u32 = zext v44, 32
// CHECK:     v46: int:i32 = iconst 0
// CHECK:     v47: bool = icmp.ne v45, v46:u32
// CHECK:     v48: int:u64 = iconst 1
// CHECK:     v49: int:u64 = iconst 0
// CHECK:     v50: int:u64 = select v47, v48, v49
// CHECK:     v51: int:i64 = iconst 1
// CHECK:     v52: int:i64 = xor v50, v51
// CHECK:     v53: int:i64 = iconst 255
// CHECK:     v54: int:u64 = and v52, v53
// CHECK:     v55: int:i8 = iconst 0
// CHECK:     v56: bool = icmp.eq v54, v55
// CHECK:     brif v56, bb9(v41), bb6(v41)
// CHECK:
// CHECK:   bb6(v58: mem):
// CHECK:     v59: ptr = stack_slot 4
// CHECK:     v60: mem = store.4 v2, v59, v58
// CHECK:     v61: int:i32 = load.4 v59, v60
// CHECK:     v62: int:i32 = iconst 2147483648
// CHECK:     v63: int:i32 = and v61:u32, v62:u32
// CHECK:     v64: int:u32 = zext v63, 32
// CHECK:     v65: int:i64 = iconst 4294967295
// CHECK:     v66: int:u64 = and v64, v65
// CHECK:     v67: int:i32 = iconst 0
// CHECK:     v68: bool = icmp.eq v66, v67
// CHECK:     brif v68, bb8(v60), bb7(v60)
// CHECK:
// CHECK:   bb7(v70: mem):
// CHECK:     v71: mem = store.4 v1, v3, v70
// CHECK:     br bb11(v71)
// CHECK:
// CHECK:   bb8(v73: mem):
// CHECK:     br bb10(v73)
// CHECK:
// CHECK:   bb9(v75: mem):
// CHECK:     br bb10(v75)
// CHECK:
// CHECK:   bb10(v77: mem):
// CHECK:     v78: mem = store.4 v2, v3, v77
// CHECK:     br bb11(v78)
// CHECK:
// CHECK:   bb11(v80: mem):
// CHECK:     br bb13(v80)
// CHECK:
// CHECK:   bb12(v82: mem):
// CHECK:     v83: f32 = fadd v1, v2
// CHECK:     v84: mem = store.4 v83, v3, v82
// CHECK:     br bb13(v84)
// CHECK:
// CHECK:   bb13(v86: mem):
// CHECK:     br bb14(v86)
// CHECK:
// CHECK:   bb14(v88: mem):
// CHECK:     br bb15(v88)
// CHECK:
// CHECK:   bb15(v90: mem):
// CHECK:     v91: f32 = load.4 v3, v90
// CHECK:     ret v91, v90
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::maximumf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug x => _1;
// CHECK:     debug y => _2;
// CHECK:     let mut _0: f64;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::f64::<impl f64>::is_sign_positive) {
// CHECK:         debug self => _1;
// CHECK:         let mut _7: bool;
// CHECK:         scope 2 (inlined core::f64::<impl f64>::is_sign_negative) {
// CHECK:             let mut _8: u64;
// CHECK:             let mut _9: u64;
// CHECK:             scope 3 (inlined core::f64::<impl f64>::to_bits) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 4 (inlined core::f64::<impl f64>::is_sign_negative) {
// CHECK:         debug self => _2;
// CHECK:         let mut _10: u64;
// CHECK:         let mut _11: u64;
// CHECK:         scope 5 (inlined core::f64::<impl f64>::to_bits) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = Gt(copy _1, copy _2);
// CHECK:         switchInt(move _3) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Gt(copy _2, copy _1);
// CHECK:         switchInt(move _4) -> [0: bb4, otherwise: bb3];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = Eq(copy _1, copy _2);
// CHECK:         switchInt(move _5) -> [0: bb12, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _1 as u64 (Transmute);
// CHECK:         _8 = BitAnd(move _9, const 9223372036854775808_u64);
// CHECK:         StorageDead(_9);
// CHECK:         _7 = Ne(move _8, const 0_u64);
// CHECK:         StorageDead(_8);
// CHECK:         _6 = Not(move _7);
// CHECK:         StorageDead(_7);
// CHECK:         switchInt(move _6) -> [0: bb9, otherwise: bb6];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _2 as u64 (Transmute);
// CHECK:         _10 = BitAnd(move _11, const 9223372036854775808_u64);
// CHECK:         StorageDead(_11);
// CHECK:         switchInt(copy _10) -> [0: bb8, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_10);
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageDead(_10);
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         StorageDead(_6);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageDead(_4);
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsa3SJzwB9S2T_4core10intrinsics10maximumf64CshcqLDH83PT8_12float_minmax(f64, f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: f64 = param 1
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: bool = fcmp.ogt v1, v2
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.8 v1, v3, v13
// CHECK:     br bb15(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: bool = fcmp.ogt v2, v1
// CHECK:     v18: int:u64 = iconst 1
// CHECK:     v19: int:u64 = iconst 0
// CHECK:     v20: int:u64 = select v17, v18, v19
// CHECK:     v21: int:i64 = iconst 255
// CHECK:     v22: int:u64 = and v20, v21
// CHECK:     v23: int:i8 = iconst 0
// CHECK:     v24: bool = icmp.eq v22, v23
// CHECK:     brif v24, bb4(v16), bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     v27: mem = store.8 v2, v3, v26
// CHECK:     br bb14(v27)
// CHECK:
// CHECK:   bb4(v29: mem):
// CHECK:     v30: bool = fcmp.oeq v1, v2
// CHECK:     v31: int:u64 = iconst 1
// CHECK:     v32: int:u64 = iconst 0
// CHECK:     v33: int:u64 = select v30, v31, v32
// CHECK:     v34: int:i64 = iconst 255
// CHECK:     v35: int:u64 = and v33, v34
// CHECK:     v36: int:i8 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb12(v29), bb5(v29)
// CHECK:
// CHECK:   bb5(v39: mem):
// CHECK:     v40: ptr = stack_slot 8
// CHECK:     v41: mem = store.8 v1, v40, v39
// CHECK:     v42: int:i64 = load.8 v40, v41
// CHECK:     v43: int:i64 = iconst 9223372036854775808
// CHECK:     v44: int:i64 = and v42:u64, v43:u64
// CHECK:     v45: int:u64 = zext v44, 64
// CHECK:     v46: int:i64 = iconst 0
// CHECK:     v47: bool = icmp.ne v45, v46:u64
// CHECK:     v48: int:u64 = iconst 1
// CHECK:     v49: int:u64 = iconst 0
// CHECK:     v50: int:u64 = select v47, v48, v49
// CHECK:     v51: int:i64 = iconst 1
// CHECK:     v52: int:i64 = xor v50, v51
// CHECK:     v53: int:i64 = iconst 255
// CHECK:     v54: int:u64 = and v52, v53
// CHECK:     v55: int:i8 = iconst 0
// CHECK:     v56: bool = icmp.eq v54, v55
// CHECK:     brif v56, bb9(v41), bb6(v41)
// CHECK:
// CHECK:   bb6(v58: mem):
// CHECK:     v59: ptr = stack_slot 8
// CHECK:     v60: mem = store.8 v2, v59, v58
// CHECK:     v61: int:i64 = load.8 v59, v60
// CHECK:     v62: int:i64 = iconst 9223372036854775808
// CHECK:     v63: int:i64 = and v61:u64, v62:u64
// CHECK:     v64: int:u64 = zext v63, 64
// CHECK:     v65: int:i64 = iconst 0
// CHECK:     v66: bool = icmp.eq v64, v65
// CHECK:     brif v66, bb8(v60), bb7(v60)
// CHECK:
// CHECK:   bb7(v68: mem):
// CHECK:     v69: mem = store.8 v1, v3, v68
// CHECK:     br bb11(v69)
// CHECK:
// CHECK:   bb8(v71: mem):
// CHECK:     br bb10(v71)
// CHECK:
// CHECK:   bb9(v73: mem):
// CHECK:     br bb10(v73)
// CHECK:
// CHECK:   bb10(v75: mem):
// CHECK:     v76: mem = store.8 v2, v3, v75
// CHECK:     br bb11(v76)
// CHECK:
// CHECK:   bb11(v78: mem):
// CHECK:     br bb13(v78)
// CHECK:
// CHECK:   bb12(v80: mem):
// CHECK:     v81: f64 = fadd v1, v2
// CHECK:     v82: mem = store.8 v81, v3, v80
// CHECK:     br bb13(v82)
// CHECK:
// CHECK:   bb13(v84: mem):
// CHECK:     br bb14(v84)
// CHECK:
// CHECK:   bb14(v86: mem):
// CHECK:     br bb15(v86)
// CHECK:
// CHECK:   bb15(v88: mem):
// CHECK:     v89: f64 = load.8 v3, v88
// CHECK:     ret v89, v88
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::minimumf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug x => _1;
// CHECK:     debug y => _2;
// CHECK:     let mut _0: f32;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::f32::<impl f32>::is_sign_negative) {
// CHECK:         debug self => _1;
// CHECK:         let mut _7: u32;
// CHECK:         let mut _8: u32;
// CHECK:         scope 2 (inlined core::f32::<impl f32>::to_bits) {
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined core::f32::<impl f32>::is_sign_positive) {
// CHECK:         debug self => _2;
// CHECK:         let mut _9: bool;
// CHECK:         scope 4 (inlined core::f32::<impl f32>::is_sign_negative) {
// CHECK:             let mut _10: u32;
// CHECK:             let mut _11: u32;
// CHECK:             scope 5 (inlined core::f32::<impl f32>::to_bits) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = Lt(copy _1, copy _2);
// CHECK:         switchInt(move _3) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _2, copy _1);
// CHECK:         switchInt(move _4) -> [0: bb4, otherwise: bb3];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = Eq(copy _1, copy _2);
// CHECK:         switchInt(move _5) -> [0: bb12, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _1 as u32 (Transmute);
// CHECK:         _7 = BitAnd(move _8, const 2147483648_u32);
// CHECK:         StorageDead(_8);
// CHECK:         switchInt(copy _7) -> [0: bb9, otherwise: bb6];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _2 as u32 (Transmute);
// CHECK:         _10 = BitAnd(move _11, const 2147483648_u32);
// CHECK:         StorageDead(_11);
// CHECK:         _9 = Ne(move _10, const 0_u32);
// CHECK:         StorageDead(_10);
// CHECK:         _6 = Not(move _9);
// CHECK:         StorageDead(_9);
// CHECK:         switchInt(move _6) -> [0: bb8, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         StorageDead(_7);
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         StorageDead(_6);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageDead(_4);
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsa3SJzwB9S2T_4core10intrinsics10minimumf32CshcqLDH83PT8_12float_minmax(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: ptr = stack_slot 4
// CHECK:     v4: bool = fcmp.olt v1, v2
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.4 v1, v3, v13
// CHECK:     br bb15(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: bool = fcmp.olt v2, v1
// CHECK:     v18: int:u64 = iconst 1
// CHECK:     v19: int:u64 = iconst 0
// CHECK:     v20: int:u64 = select v17, v18, v19
// CHECK:     v21: int:i64 = iconst 255
// CHECK:     v22: int:u64 = and v20, v21
// CHECK:     v23: int:i8 = iconst 0
// CHECK:     v24: bool = icmp.eq v22, v23
// CHECK:     brif v24, bb4(v16), bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     v27: mem = store.4 v2, v3, v26
// CHECK:     br bb14(v27)
// CHECK:
// CHECK:   bb4(v29: mem):
// CHECK:     v30: bool = fcmp.oeq v1, v2
// CHECK:     v31: int:u64 = iconst 1
// CHECK:     v32: int:u64 = iconst 0
// CHECK:     v33: int:u64 = select v30, v31, v32
// CHECK:     v34: int:i64 = iconst 255
// CHECK:     v35: int:u64 = and v33, v34
// CHECK:     v36: int:i8 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb12(v29), bb5(v29)
// CHECK:
// CHECK:   bb5(v39: mem):
// CHECK:     v40: ptr = stack_slot 4
// CHECK:     v41: mem = store.4 v1, v40, v39
// CHECK:     v42: int:i32 = load.4 v40, v41
// CHECK:     v43: int:i32 = iconst 2147483648
// CHECK:     v44: int:i32 = and v42:u32, v43:u32
// CHECK:     v45: int:u32 = zext v44, 32
// CHECK:     v46: int:i64 = iconst 4294967295
// CHECK:     v47: int:u64 = and v45, v46
// CHECK:     v48: int:i32 = iconst 0
// CHECK:     v49: bool = icmp.eq v47, v48
// CHECK:     brif v49, bb9(v41), bb6(v41)
// CHECK:
// CHECK:   bb6(v51: mem):
// CHECK:     v52: ptr = stack_slot 4
// CHECK:     v53: mem = store.4 v2, v52, v51
// CHECK:     v54: int:i32 = load.4 v52, v53
// CHECK:     v55: int:i32 = iconst 2147483648
// CHECK:     v56: int:i32 = and v54:u32, v55:u32
// CHECK:     v57: int:u32 = zext v56, 32
// CHECK:     v58: int:i32 = iconst 0
// CHECK:     v59: bool = icmp.ne v57, v58:u32
// CHECK:     v60: int:u64 = iconst 1
// CHECK:     v61: int:u64 = iconst 0
// CHECK:     v62: int:u64 = select v59, v60, v61
// CHECK:     v63: int:i64 = iconst 1
// CHECK:     v64: int:i64 = xor v62, v63
// CHECK:     v65: int:i64 = iconst 255
// CHECK:     v66: int:u64 = and v64, v65
// CHECK:     v67: int:i8 = iconst 0
// CHECK:     v68: bool = icmp.eq v66, v67
// CHECK:     brif v68, bb8(v53), bb7(v53)
// CHECK:
// CHECK:   bb7(v70: mem):
// CHECK:     v71: mem = store.4 v1, v3, v70
// CHECK:     br bb11(v71)
// CHECK:
// CHECK:   bb8(v73: mem):
// CHECK:     br bb10(v73)
// CHECK:
// CHECK:   bb9(v75: mem):
// CHECK:     br bb10(v75)
// CHECK:
// CHECK:   bb10(v77: mem):
// CHECK:     v78: mem = store.4 v2, v3, v77
// CHECK:     br bb11(v78)
// CHECK:
// CHECK:   bb11(v80: mem):
// CHECK:     br bb13(v80)
// CHECK:
// CHECK:   bb12(v82: mem):
// CHECK:     v83: f32 = fadd v1, v2
// CHECK:     v84: mem = store.4 v83, v3, v82
// CHECK:     br bb13(v84)
// CHECK:
// CHECK:   bb13(v86: mem):
// CHECK:     br bb14(v86)
// CHECK:
// CHECK:   bb14(v88: mem):
// CHECK:     br bb15(v88)
// CHECK:
// CHECK:   bb15(v90: mem):
// CHECK:     v91: f32 = load.4 v3, v90
// CHECK:     ret v91, v90
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::minimumf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug x => _1;
// CHECK:     debug y => _2;
// CHECK:     let mut _0: f64;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::f64::<impl f64>::is_sign_negative) {
// CHECK:         debug self => _1;
// CHECK:         let mut _7: u64;
// CHECK:         let mut _8: u64;
// CHECK:         scope 2 (inlined core::f64::<impl f64>::to_bits) {
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined core::f64::<impl f64>::is_sign_positive) {
// CHECK:         debug self => _2;
// CHECK:         let mut _9: bool;
// CHECK:         scope 4 (inlined core::f64::<impl f64>::is_sign_negative) {
// CHECK:             let mut _10: u64;
// CHECK:             let mut _11: u64;
// CHECK:             scope 5 (inlined core::f64::<impl f64>::to_bits) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = Lt(copy _1, copy _2);
// CHECK:         switchInt(move _3) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _2, copy _1);
// CHECK:         switchInt(move _4) -> [0: bb4, otherwise: bb3];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = Eq(copy _1, copy _2);
// CHECK:         switchInt(move _5) -> [0: bb12, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _1 as u64 (Transmute);
// CHECK:         _7 = BitAnd(move _8, const 9223372036854775808_u64);
// CHECK:         StorageDead(_8);
// CHECK:         switchInt(copy _7) -> [0: bb9, otherwise: bb6];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         _11 = copy _2 as u64 (Transmute);
// CHECK:         _10 = BitAnd(move _11, const 9223372036854775808_u64);
// CHECK:         StorageDead(_11);
// CHECK:         _9 = Ne(move _10, const 0_u64);
// CHECK:         StorageDead(_10);
// CHECK:         _6 = Not(move _9);
// CHECK:         StorageDead(_9);
// CHECK:         switchInt(move _6) -> [0: bb8, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         StorageDead(_7);
// CHECK:         goto -> bb10;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb11;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         StorageDead(_6);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         goto -> bb13;
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb14;
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageDead(_4);
// CHECK:         goto -> bb15;
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsa3SJzwB9S2T_4core10intrinsics10minimumf64CshcqLDH83PT8_12float_minmax(f64, f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: f64 = param 1
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: bool = fcmp.olt v1, v2
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.8 v1, v3, v13
// CHECK:     br bb15(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: bool = fcmp.olt v2, v1
// CHECK:     v18: int:u64 = iconst 1
// CHECK:     v19: int:u64 = iconst 0
// CHECK:     v20: int:u64 = select v17, v18, v19
// CHECK:     v21: int:i64 = iconst 255
// CHECK:     v22: int:u64 = and v20, v21
// CHECK:     v23: int:i8 = iconst 0
// CHECK:     v24: bool = icmp.eq v22, v23
// CHECK:     brif v24, bb4(v16), bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     v27: mem = store.8 v2, v3, v26
// CHECK:     br bb14(v27)
// CHECK:
// CHECK:   bb4(v29: mem):
// CHECK:     v30: bool = fcmp.oeq v1, v2
// CHECK:     v31: int:u64 = iconst 1
// CHECK:     v32: int:u64 = iconst 0
// CHECK:     v33: int:u64 = select v30, v31, v32
// CHECK:     v34: int:i64 = iconst 255
// CHECK:     v35: int:u64 = and v33, v34
// CHECK:     v36: int:i8 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb12(v29), bb5(v29)
// CHECK:
// CHECK:   bb5(v39: mem):
// CHECK:     v40: ptr = stack_slot 8
// CHECK:     v41: mem = store.8 v1, v40, v39
// CHECK:     v42: int:i64 = load.8 v40, v41
// CHECK:     v43: int:i64 = iconst 9223372036854775808
// CHECK:     v44: int:i64 = and v42:u64, v43:u64
// CHECK:     v45: int:u64 = zext v44, 64
// CHECK:     v46: int:i64 = iconst 0
// CHECK:     v47: bool = icmp.eq v45, v46
// CHECK:     brif v47, bb9(v41), bb6(v41)
// CHECK:
// CHECK:   bb6(v49: mem):
// CHECK:     v50: ptr = stack_slot 8
// CHECK:     v51: mem = store.8 v2, v50, v49
// CHECK:     v52: int:i64 = load.8 v50, v51
// CHECK:     v53: int:i64 = iconst 9223372036854775808
// CHECK:     v54: int:i64 = and v52:u64, v53:u64
// CHECK:     v55: int:u64 = zext v54, 64
// CHECK:     v56: int:i64 = iconst 0
// CHECK:     v57: bool = icmp.ne v55, v56:u64
// CHECK:     v58: int:u64 = iconst 1
// CHECK:     v59: int:u64 = iconst 0
// CHECK:     v60: int:u64 = select v57, v58, v59
// CHECK:     v61: int:i64 = iconst 1
// CHECK:     v62: int:i64 = xor v60, v61
// CHECK:     v63: int:i64 = iconst 255
// CHECK:     v64: int:u64 = and v62, v63
// CHECK:     v65: int:i8 = iconst 0
// CHECK:     v66: bool = icmp.eq v64, v65
// CHECK:     brif v66, bb8(v51), bb7(v51)
// CHECK:
// CHECK:   bb7(v68: mem):
// CHECK:     v69: mem = store.8 v1, v3, v68
// CHECK:     br bb11(v69)
// CHECK:
// CHECK:   bb8(v71: mem):
// CHECK:     br bb10(v71)
// CHECK:
// CHECK:   bb9(v73: mem):
// CHECK:     br bb10(v73)
// CHECK:
// CHECK:   bb10(v75: mem):
// CHECK:     v76: mem = store.8 v2, v3, v75
// CHECK:     br bb11(v76)
// CHECK:
// CHECK:   bb11(v78: mem):
// CHECK:     br bb13(v78)
// CHECK:
// CHECK:   bb12(v80: mem):
// CHECK:     v81: f64 = fadd v1, v2
// CHECK:     v82: mem = store.8 v81, v3, v80
// CHECK:     br bb13(v82)
// CHECK:
// CHECK:   bb13(v84: mem):
// CHECK:     br bb14(v84)
// CHECK:
// CHECK:   bb14(v86: mem):
// CHECK:     br bb15(v86)
// CHECK:
// CHECK:   bb15(v88: mem):
// CHECK:     v89: f64 = load.8 v3, v88
// CHECK:     ret v89, v88
// CHECK: }
// CHECK:
// CHECK: fn maxf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:     let mut _3: f32;
// CHECK:     let mut _4: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = copy _1;
// CHECK:         StorageLive(_4);
// CHECK:         _4 = copy _2;
// CHECK:         _0 = core::intrinsics::maximumf32(move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_4);
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @maxf32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fmaxnum v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn maxf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f64;
// CHECK:     let mut _3: f64;
// CHECK:     let mut _4: f64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = copy _1;
// CHECK:         StorageLive(_4);
// CHECK:         _4 = copy _2;
// CHECK:         _0 = core::intrinsics::maximumf64(move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_4);
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @maxf64(f64, f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: f64 = param 1
// CHECK:     v3: f64 = fmaxnum v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn minf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:     let mut _3: f32;
// CHECK:     let mut _4: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = copy _1;
// CHECK:         StorageLive(_4);
// CHECK:         _4 = copy _2;
// CHECK:         _0 = core::intrinsics::minimumf32(move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_4);
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @minf32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fminnum v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn minf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f64;
// CHECK:     let mut _3: f64;
// CHECK:     let mut _4: f64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         _3 = copy _1;
// CHECK:         StorageLive(_4);
// CHECK:         _4 = copy _2;
// CHECK:         _0 = core::intrinsics::minimumf64(move _3, move _4) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_4);
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @minf64(f64, f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: f64 = param 1
// CHECK:     v3: f64 = fminnum v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::{minimumf32, minimumf64, maximumf32, maximumf64};

#[no_mangle]
pub unsafe fn minf32(a: f32, b: f32) -> f32 {
    minimumf32(a, b)
}

#[no_mangle]
pub unsafe fn maxf32(a: f32, b: f32) -> f32 {
    maximumf32(a, b)
}

#[no_mangle]
pub unsafe fn minf64(a: f64, b: f64) -> f64 {
    minimumf64(a, b)
}

#[no_mangle]
pub unsafe fn maxf64(a: f64, b: f64) -> f64 {
    maximumf64(a, b)
}
