// compile-flags: -C opt-level=0
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32
// CHECK: v3:s32 = add v1:s32, v2:s32
// CHECK: ret v3

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
