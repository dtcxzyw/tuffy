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
// CHECK: func @select_i64(bool, int:s64, int:s64) -> int:s64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param 0
// CHECK:     v2: int:s64 = param 1
// CHECK:     v3: int:s64 = param 2
// CHECK:     v4: ptr = stack_slot 8 align 8
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v1, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.8 v2, v4, v13
// CHECK:     br bb3(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: mem = store.8 v3, v4, v16
// CHECK:     br bb3(v17)
// CHECK:
// CHECK:   bb3(v19: mem):
// CHECK:     v20: int:s64 = load.8 v4, v19
// CHECK:     ret v20, v19
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
// CHECK: func @select_u32(bool, int:u32, int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = stack_slot 4 align 4
// CHECK:     v5: int:u64 = iconst 1
// CHECK:     v6: int:u64 = iconst 0
// CHECK:     v7: int:u64 = select v1, v5, v6
// CHECK:     v8: int:i64 = iconst 255
// CHECK:     v9: int:u64 = and v7, v8
// CHECK:     v10: int:i8 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: mem = store.4 v2, v4, v13
// CHECK:     br bb3(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: mem = store.4 v3, v4, v16
// CHECK:     br bb3(v17)
// CHECK:
// CHECK:   bb3(v19: mem):
// CHECK:     v20: int:u32 = load.4 v4, v19
// CHECK:     ret v20, v19
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
