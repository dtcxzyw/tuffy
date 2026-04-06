// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn callee_i128(_1: i128) -> i128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: i128;
// CHECK:     scope 1 (inlined core::num::<impl i128>::wrapping_sub) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, const 1_i128);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @callee_i128(int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i128 = iconst 1
// CHECK:     v4: int:i128 = sub v1, v3:s128
// CHECK:     v5: mem = store.16 v4, v2, v0
// CHECK:     v6: int:s128 = load.16 v2, v5
// CHECK:     ret v6, v5
// CHECK: }
// CHECK:
// CHECK: fn callee_u128(_1: u128) -> u128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u128;
// CHECK:     scope 1 (inlined core::num::<impl u128>::wrapping_add) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, const 1_u128);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @callee_u128(int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i128 = iconst 1
// CHECK:     v4: int:i128 = add v1, v3:u128
// CHECK:     v5: mem = store.16 v4, v2, v0
// CHECK:     v6: int:u128 = load.16 v2, v5
// CHECK:     ret v6, v5
// CHECK: }
// CHECK:
// CHECK: fn caller_i128(_1: i128) -> i128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = callee_i128(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @caller_i128(int:s128) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = symbol_addr @callee_i128
// CHECK:     v4: mem, v5: int:s128 = call v3(v1), v0 -> int:s128
// CHECK:     v6: mem = store.16 v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     v9: int:s128 = load.16 v2, v8
// CHECK:     ret v9, v8
// CHECK: }
// CHECK:
// CHECK: fn caller_u128(_1: u128) -> u128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = callee_u128(move _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @caller_u128(int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: ptr = symbol_addr @callee_u128
// CHECK:     v4: mem, v5: int:u128 = call v3(v1), v0 -> int:u128
// CHECK:     v6: mem = store.16 v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     v9: int:u128 = load.16 v2, v8
// CHECK:     ret v9, v8
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
#[inline(never)]
pub fn callee_u128(x: u128) -> u128 {
    x.wrapping_add(1)
}

#[no_mangle]
pub fn caller_u128(x: u128) -> u128 {
    callee_u128(x)
}

#[no_mangle]
#[inline(never)]
pub fn callee_i128(x: i128) -> i128 {
    x.wrapping_sub(1)
}

#[no_mangle]
pub fn caller_i128(x: i128) -> i128 {
    callee_i128(x)
}
