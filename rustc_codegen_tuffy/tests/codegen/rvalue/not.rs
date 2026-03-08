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
// CHECK:     v2: int:u64 = iconst 1
// CHECK:     v3: int:u64 = iconst 0
// CHECK:     v4: int:u64 = select v1, v2, v3
// CHECK:     v5: int:i64 = iconst 1
// CHECK:     v6: int:i64 = xor v4, v5
// CHECK:     v7: int:i64 = iconst 0
// CHECK:     v8: bool = icmp.ne v6, v7
// CHECK:     ret v8, v0
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
// CHECK: func @not_u32(%a: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:i64 = iconst -1
// CHECK:     v3: int:i32 = xor v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
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
