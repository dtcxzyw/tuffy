// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn unchecked_add_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = AddUnchecked(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @unchecked_add_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = add v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn unchecked_mul_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = MulUnchecked(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @unchecked_mul_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = mul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn unchecked_shl_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = ShlUnchecked(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @unchecked_shl_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:i64 = and v2, v3
// CHECK:     v5: int:u32 = shl v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn unchecked_shr_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = ShrUnchecked(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @unchecked_shr_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:i64 = and v2, v3
// CHECK:     v5: int:u32 = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn unchecked_sub_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = SubUnchecked(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @unchecked_sub_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = sub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::{unchecked_add, unchecked_sub, unchecked_mul, unchecked_shl, unchecked_shr};

#[no_mangle]
pub unsafe fn unchecked_add_u32(a: u32, b: u32) -> u32 {
    unchecked_add(a, b)
}

#[no_mangle]
pub unsafe fn unchecked_sub_u32(a: u32, b: u32) -> u32 {
    unchecked_sub(a, b)
}

#[no_mangle]
pub unsafe fn unchecked_mul_u32(a: u32, b: u32) -> u32 {
    unchecked_mul(a, b)
}

#[no_mangle]
pub unsafe fn unchecked_shl_u32(a: u32, b: u32) -> u32 {
    unchecked_shl(a, b)
}

#[no_mangle]
pub unsafe fn unchecked_shr_u32(a: u32, b: u32) -> u32 {
    unchecked_shr(a, b)
}
