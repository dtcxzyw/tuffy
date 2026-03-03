// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off -C opt-level=3
// CHECK: fn add(_1: i32, _2: i32) -> i32 {
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3:s32 = add v1:s32, v2:s32
// CHECK:     ret v3, v0
// CHECK: }

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
