// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn select_i64(_1: bool, _2: i64, _3: i64) -> i64 {
// CHECK:     debug cond => _1;
// CHECK:     debug a => _2;
// CHECK:     debug b => _3;
// CHECK:     let mut _0: i64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(copy _1) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = copy _3;
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @select_i64(%cond: bool, %a: int:s64, %b: int:s64) -> int:s64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param %cond
// CHECK:     v2: int:s64 = param %a
// CHECK:     v3: int:s64 = param %b
// CHECK:     v4: ptr = stack_slot 8
// CHECK:     v5: int:u64 = bool_to_int v1
// CHECK:     v6: int:i64 = iconst 255
// CHECK:     v7: int:u64 = and v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: mem = store.8 v2, v4, v11
// CHECK:     br bb3(v12)
// CHECK:
// CHECK:   bb2(v14: mem):
// CHECK:     v15: mem = store.8 v3, v4, v14
// CHECK:     br bb3(v15)
// CHECK:
// CHECK:   bb3(v17: mem):
// CHECK:     v18: int:s64 = load.8 v4, v17
// CHECK:     ret v18, v17
// CHECK: }
// CHECK:
// CHECK: fn select_u32(_1: bool, _2: u32, _3: u32) -> u32 {
// CHECK:     debug cond => _1;
// CHECK:     debug a => _2;
// CHECK:     debug b => _3;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(copy _1) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = copy _3;
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @select_u32(%cond: bool, %a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param %cond
// CHECK:     v2: int:u32 = param %a
// CHECK:     v3: int:u32 = param %b
// CHECK:     v4: ptr = stack_slot 4
// CHECK:     v5: int:u64 = bool_to_int v1
// CHECK:     v6: int:i64 = iconst 255
// CHECK:     v7: int:u64 = and v5, v6
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     v9: bool = icmp.eq v7, v8
// CHECK:     brif v9, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: mem = store.4 v2, v4, v11
// CHECK:     br bb3(v12)
// CHECK:
// CHECK:   bb2(v14: mem):
// CHECK:     v15: mem = store.4 v3, v4, v14
// CHECK:     br bb3(v15)
// CHECK:
// CHECK:   bb3(v17: mem):
// CHECK:     v18: int:u32 = load.4 v4, v17
// CHECK:     ret v18, v17
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn select_u32(cond: bool, a: u32, b: u32) -> u32 {
    if cond { a } else { b }
}

#[no_mangle]
pub fn select_i64(cond: bool, a: i64, b: i64) -> i64 {
    if cond { a } else { b }
}
