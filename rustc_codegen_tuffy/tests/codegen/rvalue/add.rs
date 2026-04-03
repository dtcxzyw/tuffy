// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off -C opt-level=3
// CHECK: fn add(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @add(int:s32, int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param 0
// CHECK:     v2: int:s32 = param 1
// CHECK:     v3: int:i32 = add v1, v2
// CHECK:     v4: int:s32 = sext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn add128(_1: u128, _2: u128) -> u128 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @add128(int:u128, int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: ptr = stack_slot 16
// CHECK:     v4: int:i128 = add v1, v2
// CHECK:     v5: mem = store.16 v4, v3, v0
// CHECK:     v6: int:u128 = load.16 v3, v5
// CHECK:     ret v6, v5
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[no_mangle]
pub fn add128(a: u128, b: u128) -> u128 {
    a + b
}
