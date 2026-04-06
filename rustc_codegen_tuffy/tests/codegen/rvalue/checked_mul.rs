// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn checked_mul_u32(_1: u32, _2: u32) -> (u64, bool) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: (u64, bool);
// CHECK:     let _3: u32;
// CHECK:     let _4: bool;
// CHECK:     let mut _5: (u32, bool);
// CHECK:     let mut _6: u64;
// CHECK:     scope 1 {
// CHECK:         debug val => _3;
// CHECK:         debug overflow => _4;
// CHECK:     }
// CHECK:     scope 2 (inlined core::num::<impl u32>::overflowing_mul) {
// CHECK:         scope 3 {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _5 = MulWithOverflow(copy _1, copy _2);
// CHECK:         _3 = copy (_5.0: u32);
// CHECK:         _4 = copy (_5.1: bool);
// CHECK:         _6 = copy _3 as u64 (IntToInt);
// CHECK:         _0 = (move _6, copy _4);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @checked_mul_u32(int:u32, int:u32) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: int:u32, v5: bool = umul_overflow.32 v1, v2
// CHECK:     v6: int:u64 = zext v4, 64
// CHECK:     v7: mem = store.8 v6, v3, v0
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v3, v8
// CHECK:     v10: mem = store.1 v5, v9, v7
// CHECK:     v11: int:i64 = load.8 v3, v10
// CHECK:     v12: int:i64 = iconst 8
// CHECK:     v13: ptr = ptradd v3, v12
// CHECK:     v14: int:i8 = load.1 v13, v10
// CHECK:     ret v11, v14, v10
// CHECK: }
// CHECK:
// CHECK: fn checked_mul_u64(_1: u64, _2: u64) -> (u64, bool) {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: (u64, bool);
// CHECK:     scope 1 (inlined core::num::<impl u64>::overflowing_mul) {
// CHECK:         scope 2 {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = MulWithOverflow(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @checked_mul_u64(int:u64, int:u64) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: int:u64, v5: bool = umul_overflow.64 v1, v2
// CHECK:     v6: mem = store.8 v4, v3, v0
// CHECK:     v7: int:i64 = iconst 8
// CHECK:     v8: ptr = ptradd v3, v7
// CHECK:     v9: mem = store.1 v5, v8, v6
// CHECK:     v10: int:i64 = load.8 v3, v9
// CHECK:     v11: int:i64 = iconst 8
// CHECK:     v12: ptr = ptradd v3, v11
// CHECK:     v13: int:i8 = load.1 v12, v9
// CHECK:     ret v10, v13, v9
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn checked_mul_u64(a: u64, b: u64) -> (u64, bool) {
    a.overflowing_mul(b)
}

#[no_mangle]
pub fn checked_mul_u32(a: u32, b: u32) -> (u64, bool) {
    let (val, overflow) = a.overflowing_mul(b);
    (val as u64, overflow)
}
