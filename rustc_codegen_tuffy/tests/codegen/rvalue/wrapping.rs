// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn wrapping_add_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_add) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_add_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = add v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn wrapping_mul_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_mul) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_mul_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = mul v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn wrapping_sub_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_sub) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_sub_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = sub v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn wrapping_add_u32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[no_mangle]
pub fn wrapping_sub_u32(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

#[no_mangle]
pub fn wrapping_mul_u32(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}
