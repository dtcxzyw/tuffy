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
// CHECK: func @checked_mul_u32(ptr, int:u32, int:u32) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 16
// CHECK:     v3: int:u32 = param 1
// CHECK:     v4: int:u32 = param 2
// CHECK:     v5: int:u32, v6: bool = umul_overflow.32 v3, v4
// CHECK:     v7: int:u64 = zext v5, 64
// CHECK:     v8: mem = store.8 v7, v2, v0
// CHECK:     v9: int:i64 = iconst 8
// CHECK:     v10: ptr = ptradd v2, v9
// CHECK:     v11: mem = store.1 v6, v10, v8
// CHECK:     v12: int:i64 = iconst 16
// CHECK:     v13: mem = memcopy v1:align8, v2:align8, v12, v11
// CHECK:     ret v1, v13
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
// CHECK: func @checked_mul_u64(ptr, int:u64, int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 16
// CHECK:     v3: int:u64 = param 1
// CHECK:     v4: int:u64 = param 2
// CHECK:     v5: int:u64, v6: bool = umul_overflow.64 v3, v4
// CHECK:     v7: mem = store.8 v5, v2, v0
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v2, v8
// CHECK:     v10: mem = store.1 v6, v9, v7
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: mem = memcopy v1:align8, v2:align8, v11, v10
// CHECK:     ret v1, v12
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
