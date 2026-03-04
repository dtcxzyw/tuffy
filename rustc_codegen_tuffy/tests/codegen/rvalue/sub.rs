// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn mul_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @mul_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3:s32 = mul v1:s32, v2:s32
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn mul_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @mul_u64(%a: int:u64, %b: int:u64) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u64 = param %a
// CHECK:     v2:u64 = param %b
// CHECK:     v3:u64 = mul v1:u64, v2:u64
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn sub_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @sub_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3:s32 = sub v1:s32, v2:s32
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn sub_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @sub_u64(%a: int:u64, %b: int:u64) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u64 = param %a
// CHECK:     v2:u64 = param %b
// CHECK:     v3:u64 = sub v1:u64, v2:u64
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn sub_i32(a: i32, b: i32) -> i32 {
    a - b
}

#[no_mangle]
pub fn mul_i32(a: i32, b: i32) -> i32 {
    a * b
}

#[no_mangle]
pub fn sub_u64(a: u64, b: u64) -> u64 {
    a - b
}

#[no_mangle]
pub fn mul_u64(a: u64, b: u64) -> u64 {
    a * b
}
