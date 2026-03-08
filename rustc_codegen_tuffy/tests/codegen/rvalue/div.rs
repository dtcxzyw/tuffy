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
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: bool = icmp.eq v2, v3:s32
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:i64 = iconst -1
// CHECK:     v13: bool = icmp.eq v2, v12:s32
// CHECK:     v14: int:i64 = iconst -2147483648
// CHECK:     v15: bool = icmp.eq v1, v14:s32
// CHECK:     v16: int:u64 = iconst 1
// CHECK:     v17: int:u64 = iconst 0
// CHECK:     v18: int:u64 = select v13, v16, v17
// CHECK:     v19: int:u64 = iconst 1
// CHECK:     v20: int:u64 = iconst 0
// CHECK:     v21: int:u64 = select v15, v19, v20
// CHECK:     v22: int:i64 = and v18, v21
// CHECK:     v23: int:u64 = zext v22, 64
// CHECK:     v24: int:i64 = iconst 0
// CHECK:     v25: bool = icmp.eq v23, v24
// CHECK:     brif v25, bb2(v11), bb4(v11)
// CHECK:
// CHECK:   bb2(v27: mem):
// CHECK:     v28: int:i64 = div v1, v2
// CHECK:     ret v28, v27
// CHECK:
// CHECK:   bb3(v30: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v32: mem):
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
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: bool = icmp.eq v2, v3:u32
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:i64 = div v1, v2
// CHECK:     ret v12, v11
// CHECK:
// CHECK:   bb2(v14: mem):
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
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: bool = icmp.eq v2, v3:s32
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:i64 = iconst -1
// CHECK:     v13: bool = icmp.eq v2, v12:s32
// CHECK:     v14: int:i64 = iconst -2147483648
// CHECK:     v15: bool = icmp.eq v1, v14:s32
// CHECK:     v16: int:u64 = iconst 1
// CHECK:     v17: int:u64 = iconst 0
// CHECK:     v18: int:u64 = select v13, v16, v17
// CHECK:     v19: int:u64 = iconst 1
// CHECK:     v20: int:u64 = iconst 0
// CHECK:     v21: int:u64 = select v15, v19, v20
// CHECK:     v22: int:i64 = and v18, v21
// CHECK:     v23: int:u64 = zext v22, 64
// CHECK:     v24: int:i64 = iconst 0
// CHECK:     v25: bool = icmp.eq v23, v24
// CHECK:     brif v25, bb2(v11), bb4(v11)
// CHECK:
// CHECK:   bb2(v27: mem):
// CHECK:     v28: int:i64 = rem v1, v2
// CHECK:     ret v28, v27
// CHECK:
// CHECK:   bb3(v30: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v32: mem):
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
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: bool = icmp.eq v2, v3:u32
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v4, v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:i64 = rem v1, v2
// CHECK:     ret v12, v11
// CHECK:
// CHECK:   bb2(v14: mem):
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
