// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn narrow_i64_to_i32(_1: i64) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i32 (IntToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @narrow_i64_to_i32(%a: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int:i64 = iconst 4294967295
// CHECK:     v3: int:u64 = and v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for narrow_i64_to_i32, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @narrow_i64_to_i32] param 0: Int type requires annotation
// CHECK:   [func @narrow_i64_to_i32] return type: Int type requires annotation
// CHECK:
// CHECK: fn widen_i32_to_i64(_1: i32) -> i64 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i64 (IntToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @widen_i32_to_i64(%a: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int:i64 = iconst 32
// CHECK:     v3: int = shl v1, v2
// CHECK:     v4: int:i64 = iconst 32
// CHECK:     v5: int = shr v3, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for widen_i32_to_i64, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @widen_i32_to_i64] param 0: Int type requires annotation
// CHECK:   [func @widen_i32_to_i64] return type: Int type requires annotation
// CHECK:
// CHECK: fn widen_u32_to_u64(_1: u32) -> u64 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: u64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as u64 (IntToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @widen_u32_to_u64(%a: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int:i64 = iconst 4294967295
// CHECK:     v3: int:u64 = and v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for widen_u32_to_u64, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @widen_u32_to_u64] param 0: Int type requires annotation
// CHECK:   [func @widen_u32_to_u64] return type: Int type requires annotation
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
