// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn div_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = Eq(copy _2, const 0_i32);
// CHECK:         assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _4 = Eq(copy _2, const -1_i32);
// CHECK:         _5 = Eq(copy _1, const i32::MIN);
// CHECK:         _6 = BitAnd(move _4, move _5);
// CHECK:         assert(!move _6, "attempt to compute `{} / {}`, which would overflow", copy _1, copy _2) -> [success: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = Div(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @div_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int:s32 = param %b
// CHECK:     v3: int = iconst 0
// CHECK:     v4: bool = icmp.eq v2:s32, v3:s32
// CHECK:     v5: int = bool_to_int v4
// CHECK:     v6: int = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: int = iconst -1
// CHECK:     v11: bool = icmp.eq v2:s32, v10:s32
// CHECK:     v12: int = bool_to_int v11
// CHECK:     v13: int = iconst -2147483648
// CHECK:     v14: bool = icmp.eq v1:s32, v13:s32
// CHECK:     v15: int = bool_to_int v14
// CHECK:     v16: int = and v12, v15
// CHECK:     v17: int = iconst 0
// CHECK:     v18: bool = icmp.eq v16, v17
// CHECK:     brif v18, bb2(v9), bb4(v9)
// CHECK:
// CHECK:   bb2(v20: mem):
// CHECK:     v21: int:s32 = div v1:s32, v2:s32
// CHECK:     ret v21, v20
// CHECK:
// CHECK:   bb3(v23: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v25: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn div_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     let mut _3: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = Eq(copy _2, const 0_u32);
// CHECK:         assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = Div(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @div_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int = iconst 0
// CHECK:     v4: bool = icmp.eq v2:u32, v3:u32
// CHECK:     v5: int = bool_to_int v4
// CHECK:     v6: int = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: int:u32 = div v1:u32, v2:u32
// CHECK:     ret v10, v9
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn rem_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = Eq(copy _2, const 0_i32);
// CHECK:         assert(!move _3, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _1) -> [success: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _4 = Eq(copy _2, const -1_i32);
// CHECK:         _5 = Eq(copy _1, const i32::MIN);
// CHECK:         _6 = BitAnd(move _4, move _5);
// CHECK:         assert(!move _6, "attempt to compute the remainder of `{} % {}`, which would overflow", copy _1, copy _2) -> [success: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = Rem(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rem_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:s32 = param %a
// CHECK:     v2: int:s32 = param %b
// CHECK:     v3: int = iconst 0
// CHECK:     v4: bool = icmp.eq v2:s32, v3:s32
// CHECK:     v5: int = bool_to_int v4
// CHECK:     v6: int = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: int = iconst -1
// CHECK:     v11: bool = icmp.eq v2:s32, v10:s32
// CHECK:     v12: int = bool_to_int v11
// CHECK:     v13: int = iconst -2147483648
// CHECK:     v14: bool = icmp.eq v1:s32, v13:s32
// CHECK:     v15: int = bool_to_int v14
// CHECK:     v16: int = and v12, v15
// CHECK:     v17: int = iconst 0
// CHECK:     v18: bool = icmp.eq v16, v17
// CHECK:     brif v18, bb2(v9), bb4(v9)
// CHECK:
// CHECK:   bb2(v20: mem):
// CHECK:     v21: int:s32 = rem v1:s32, v2:s32
// CHECK:     ret v21, v20
// CHECK:
// CHECK:   bb3(v23: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v25: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn rem_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     let mut _3: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = Eq(copy _2, const 0_u32);
// CHECK:         assert(!move _3, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _1) -> [success: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = Rem(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rem_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %a
// CHECK:     v2: int:u32 = param %b
// CHECK:     v3: int = iconst 0
// CHECK:     v4: bool = icmp.eq v2:u32, v3:u32
// CHECK:     v5: int = bool_to_int v4
// CHECK:     v6: int = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: int:u32 = rem v1:u32, v2:u32
// CHECK:     ret v10, v9
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     trap
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn div_u32(a: u32, b: u32) -> u32 {
    a / b
}

#[no_mangle]
pub fn div_i32(a: i32, b: i32) -> i32 {
    a / b
}

#[no_mangle]
pub fn rem_u32(a: u32, b: u32) -> u32 {
    a % b
}

#[no_mangle]
pub fn rem_i32(a: i32, b: i32) -> i32 {
    a % b
}
