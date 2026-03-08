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
// CHECK: func @unchecked_add_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = add v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for unchecked_add_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @unchecked_add_u32] param 0: Int type requires annotation
// CHECK:   [func @unchecked_add_u32] param 1: Int type requires annotation
// CHECK:   [func @unchecked_add_u32] return type: Int type requires annotation
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
// CHECK: func @unchecked_mul_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = mul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for unchecked_mul_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @unchecked_mul_u32] param 0: Int type requires annotation
// CHECK:   [func @unchecked_mul_u32] param 1: Int type requires annotation
// CHECK:   [func @unchecked_mul_u32] return type: Int type requires annotation
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
// CHECK: func @unchecked_shl_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int = shl v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for unchecked_shl_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @unchecked_shl_u32] param 0: Int type requires annotation
// CHECK:   [func @unchecked_shl_u32] param 1: Int type requires annotation
// CHECK:   [func @unchecked_shl_u32] return type: Int type requires annotation
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
// CHECK: func @unchecked_shr_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for unchecked_shr_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @unchecked_shr_u32] param 0: Int type requires annotation
// CHECK:   [func @unchecked_shr_u32] param 1: Int type requires annotation
// CHECK:   [func @unchecked_shr_u32] return type: Int type requires annotation
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
// CHECK: func @unchecked_sub_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = sub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for unchecked_sub_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @unchecked_sub_u32] param 0: Int type requires annotation
// CHECK:   [func @unchecked_sub_u32] param 1: Int type requires annotation
// CHECK:   [func @unchecked_sub_u32] return type: Int type requires annotation
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
