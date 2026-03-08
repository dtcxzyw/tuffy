// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn bitand_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitAnd(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitand_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = and v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn bitor_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitOr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitor_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = or v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn bitxor_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitXor(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitxor_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i32 = xor v1, v2
// CHECK:     v4: int:u32 = zext v3, 32
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn bitand_u32(a: u32, b: u32) -> u32 {
    a & b
}

#[no_mangle]
pub fn bitor_u32(a: u32, b: u32) -> u32 {
    a | b
}

#[no_mangle]
pub fn bitxor_u32(a: u32, b: u32) -> u32 {
    a ^ b
}
