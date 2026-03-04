// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn eq_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Eq(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @eq_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.eq v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn ge_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Ge(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @ge_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.ge v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn gt_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Gt(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @gt_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.gt v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn le_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Le(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @le_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.le v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn lt_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Lt(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @lt_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.lt v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:
// CHECK: fn ne_i32(_1: i32, _2: i32) -> bool {
// CHECK:     bb0: {
// CHECK:         _0 = Ne(copy _1, copy _2)
// CHECK:         return
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: func @ne_i32(%a: int:s32, %b: int:s32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = icmp.ne v1:s32, v2:s32
// CHECK:     v4 = bool_to_int v3
// CHECK:     v5 = int_to_bool v4
// CHECK:     ret v5, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn eq_i32(a: i32, b: i32) -> bool {
    a == b
}

#[no_mangle]
pub fn ne_i32(a: i32, b: i32) -> bool {
    a != b
}

#[no_mangle]
pub fn lt_i32(a: i32, b: i32) -> bool {
    a < b
}

#[no_mangle]
pub fn le_i32(a: i32, b: i32) -> bool {
    a <= b
}

#[no_mangle]
pub fn gt_i32(a: i32, b: i32) -> bool {
    a > b
}

#[no_mangle]
pub fn ge_i32(a: i32, b: i32) -> bool {
    a >= b
}
