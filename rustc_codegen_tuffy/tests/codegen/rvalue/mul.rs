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
// CHECK: func @mul_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3:i32 = mul v1:s32, v2:s32
// CHECK:     v4 = sext v3:i32, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn mul_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mul_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2:u32 = param %b
// CHECK:     v3:i32 = mul v1:u32, v2:u32
// CHECK:     v4 = zext v3:i32, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn mul_u32(a: u32, b: u32) -> u32 {
    a * b
}

#[no_mangle]
pub fn mul_i32(a: i32, b: i32) -> i32 {
    a * b
}
