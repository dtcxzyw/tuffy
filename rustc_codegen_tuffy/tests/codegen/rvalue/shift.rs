// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn shl_i32(_1: i32, _2: u32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shl(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shl_i32(%a: int:s32, %b: int:u32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int:s32 = shl v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn shr_i32(_1: i32, _2: u32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shr_i32(%a: int:s32, %b: int:u32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int:s32 = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn shr_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Shr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @shr_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int:i64 = iconst 31
// CHECK:     v4: int:u64 = and v2, v3
// CHECK:     v5: int:u32 = shr v1, v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn shl_i32(a: i32, b: u32) -> i32 {
    a << b
}

#[no_mangle]
pub fn shr_i32(a: i32, b: u32) -> i32 {
    a >> b
}

#[no_mangle]
pub fn shr_u32(a: u32, b: u32) -> u32 {
    a >> b
}
