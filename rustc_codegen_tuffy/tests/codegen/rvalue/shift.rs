// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn shl_i32(_1: i32, _2: u32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shl(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shl_i32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int = shl v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for shl_i32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @shl_i32] param 0: Int type requires annotation
// CHECK:   [func @shl_i32] param 1: Int type requires annotation
// CHECK:   [func @shl_i32] return type: Int type requires annotation
// CHECK:
// CHECK: fn shr_i32(_1: i32, _2: u32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shr_i32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for shr_i32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @shr_i32] param 0: Int type requires annotation
// CHECK:   [func @shr_i32] param 1: Int type requires annotation
// CHECK:   [func @shr_i32] return type: Int type requires annotation
// CHECK:
// CHECK: fn shr_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shr_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for shr_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @shr_u32] param 0: Int type requires annotation
// CHECK:   [func @shr_u32] param 1: Int type requires annotation
// CHECK:   [func @shr_u32] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn shl_i32(a: i32, b: u32) -> i32 {
    a << b
}

#[no_mangle]
pub fn shr_i32(a: i32, b: u32) -> i32 {
    a >> b
}

#[no_mangle]
pub fn shr_u32(a: u32, b: u32) -> u32 {
    a >> b
}
