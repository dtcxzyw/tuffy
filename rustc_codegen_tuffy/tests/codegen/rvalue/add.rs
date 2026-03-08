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
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int:s32 = param %b
// CHECK:     v3: int:u64 = add v1, v2
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
// CHECK: func @add128(%a: int:u128, %b: int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param %a
// CHECK:     v2: int:u128 = param %b
// CHECK:     v3: int:u64 = add v1, v2
// CHECK:     v4: int:u128 = zext v3, 128
// CHECK:     ret v4, v0
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
