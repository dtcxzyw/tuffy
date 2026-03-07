// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn neg_i128(_1: i128) -> i128 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Neg(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @neg_i128(%a: int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param %a
// CHECK:     v2: int = iconst 0
// CHECK:     v3: int:s128 = sub v2, v1
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn neg_i32(_1: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Neg(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @neg_i32(%a: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int = iconst 0
// CHECK:     v3: int:s32 = sub v2, v1
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
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
// CHECK:     v2: int = bool_to_int v1
// CHECK:     v3: int = iconst 1
// CHECK:     v4: int = xor v2, v3
// CHECK:     v5: bool = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn not_i128(_1: i128) -> i128 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Not(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @not_i128(%a: int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param %a
// CHECK:     v2: int = iconst -1
// CHECK:     v3: int:s128 = xor v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn not_u128(_1: u128) -> u128 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Not(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @not_u128(%a: int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param %a
// CHECK:     v2: int = iconst -1
// CHECK:     v3: int:u128 = xor v1, v2
// CHECK:     ret v3, v0
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
// CHECK:     v2: int = iconst -1
// CHECK:     v3: int:u32 = xor v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn neg_i32(a: i32) -> i32 {
    -a
}

#[no_mangle]
pub fn not_bool(a: bool) -> bool {
    !a
}

#[no_mangle]
pub fn not_u32(a: u32) -> u32 {
    !a
}

#[no_mangle]
pub fn neg_i128(a: i128) -> i128 {
    -a
}

#[no_mangle]
pub fn not_i128(a: i128) -> i128 {
    !a
}

#[no_mangle]
pub fn not_u128(a: u128) -> u128 {
    !a
}
