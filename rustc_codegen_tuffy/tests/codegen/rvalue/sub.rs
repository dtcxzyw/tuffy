// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn mul_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mul_i32(int:s32, int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param 0
// CHECK:     v2: int:s32 = param 1
// CHECK:     v3: int:i32 = mul v1, v2
// CHECK:     v4: int:s32 = sext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn mul_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mul_u64(int:u64, int:u64) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: int:i64 = mul v1, v2
// CHECK:     v4: int:u64 = zext v3, 64
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn sub_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @sub_i32(int:s32, int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param 0
// CHECK:     v2: int:s32 = param 1
// CHECK:     v3: int:i32 = sub v1, v2
// CHECK:     v4: int:s32 = sext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn sub_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @sub_u64(int:u64, int:u64) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: int:i64 = sub v1, v2
// CHECK:     v4: int:u64 = zext v3, 64
// CHECK:     ret v4, v0
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
