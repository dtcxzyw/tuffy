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
// CHECK: func @neg_i128(int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: int:i128 = sub v3, v1
// CHECK:     v5: int:s128 = sext v4, 128
// CHECK:     v6: mem = store.16 v5, v2, v0
// CHECK:     v7: int:s128 = load.16 v2, v6
// CHECK:     ret v7, v6
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
// CHECK: func @neg_i32(int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param 0
// CHECK:     v2: int:i64 = iconst 0
// CHECK:     v3: int:i32 = sub v2, v1
// CHECK:     v4: int:s32 = sext v3, 32
// CHECK:     ret v4, v0
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
// CHECK: func @not_bool(bool) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param 0
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
// CHECK: fn not_i128(_1: i128) -> i128 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Not(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @not_i128(int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i128 = iconst -1
// CHECK:     v4: int:i128 = xor v1, v3
// CHECK:     v5: int:s128 = sext v4, 128
// CHECK:     v6: mem = store.16 v5, v2, v0
// CHECK:     v7: int:s128 = load.16 v2, v6
// CHECK:     ret v7, v6
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
// CHECK: func @not_u128(int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i128 = iconst -1
// CHECK:     v4: int:i128 = xor v1, v3
// CHECK:     v5: int:u128 = zext v4, 128
// CHECK:     v6: mem = store.16 v5, v2, v0
// CHECK:     v7: int:u128 = load.16 v2, v6
// CHECK:     ret v7, v6
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
// CHECK: func @not_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:i32 = iconst -1
// CHECK:     v3: int:i32 = xor v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
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
