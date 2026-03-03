// compile-flags: -C opt-level=0
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3:s32 = add v1:s32, v2:s32
// CHECK:     v4 = iconst 0
// CHECK:     v5 = iconst 0
// CHECK:     v6 = icmp.eq v4, v5
// CHECK:     brif v6, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v3, v8
// CHECK:
// CHECK:   bb2(v10: mem):
// CHECK:     trap
// CHECK: }

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
