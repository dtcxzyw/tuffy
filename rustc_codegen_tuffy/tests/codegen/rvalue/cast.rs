// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn narrow_i64_to_i32(_1: i64) -> i32 {
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i32 (IntToInt)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @narrow_i64_to_i32(%a: int:s64) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s64 = param %a
// CHECK:     v2 = iconst 4294967295
// CHECK:     v3 = and v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn widen_i32_to_i64(_1: i32) -> i64 {
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i64 (IntToInt)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @widen_i32_to_i64(%a: int:s32) -> int:s64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2 = iconst 32
// CHECK:     v3 = shl v1, v2
// CHECK:     v4 = iconst 32
// CHECK:     v5 = shr v3:s64, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn widen_u32_to_u64(_1: u32) -> u64 {
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as u64 (IntToInt)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @widen_u32_to_u64(%a: int:u32) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2 = iconst 4294967295
// CHECK:     v3 = and v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn narrow_i64_to_i32(a: i64) -> i32 {
    a as i32
}

#[no_mangle]
pub fn widen_i32_to_i64(a: i32) -> i64 {
    a as i64
}

#[no_mangle]
pub fn widen_u32_to_u64(a: u32) -> u64 {
    a as u64
}
