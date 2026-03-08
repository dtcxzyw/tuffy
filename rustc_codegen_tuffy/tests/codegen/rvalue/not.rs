// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn not_bool(_1: bool) -> bool {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Not(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @not_bool(%a: bool) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param %a
// CHECK:     v2: int:u64 = bool_to_int v1
// CHECK:     v3: int:i64 = iconst 1
// CHECK:     v4: int:u64 = xor v2, v3
// CHECK:     v5: bool = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn not_u32(_1: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Not(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @not_u32(%a: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int:i64 = iconst -1
// CHECK:     v3: int:u64 = xor v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for not_u32, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @not_u32] param 0: Int type requires annotation
// CHECK:   [func @not_u32] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn not_u32(a: u32) -> u32 {
    !a
}

#[no_mangle]
pub fn not_bool(a: bool) -> bool {
    !a
}
