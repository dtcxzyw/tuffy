//@ compile-flags: -C llvm-args=dump-ir
// CHECK: fn use_large(_1: Large) -> u64 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u64;
// CHECK:     let mut _2: u64;
// CHECK:     let mut _3: u64;
// CHECK:     let mut _4: u64;
// CHECK:     let mut _5: (u64, bool);
// CHECK:     let mut _6: u64;
// CHECK:     let mut _7: (u64, bool);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = copy (_1.0: u64);
// CHECK:         _4 = copy (_1.1: u64);
// CHECK:         _5 = AddWithOverflow(copy _3, copy _4);
// CHECK:         assert(!move (_5.1: bool), "attempt to compute `{} + {}`, which would overflow", move _3, move _4) -> [success: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _2 = move (_5.0: u64);
// CHECK:         _6 = copy (_1.2: u64);
// CHECK:         _7 = AddWithOverflow(copy _2, copy _6);
// CHECK:         assert(!move (_7.1: bool), "attempt to compute `{} + {}`, which would overflow", move _2, move _6) -> [success: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = move (_7.0: u64);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @use_large() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 0
// CHECK:     v2: ptr = stack_slot 24
// CHECK:     v3: mem = store.24 v1, v2, v0
// CHECK:     v4: int = load.8 v2, v3
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v2, v5
// CHECK:     v7: int = load.8 v6, v3
// CHECK:     v8: int:u64, v9: bool = uadd_overflow.64 v4, v7
// CHECK:     v10: int:u64 = bool_to_int v9
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb1(v3), bb3(v3)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     v15: int:i64 = iconst 16
// CHECK:     v16: ptr = ptradd v2, v15
// CHECK:     v17: int = load.8 v16, v14
// CHECK:     v18: int:u64, v19: bool = uadd_overflow.64 v8, v17
// CHECK:     v20: int:u64 = bool_to_int v19
// CHECK:     v21: int:i64 = iconst 0
// CHECK:     v22: bool = icmp.eq v20, v21
// CHECK:     brif v22, bb2(v14), bb4(v14)
// CHECK:
// CHECK:   bb2(v24: mem):
// CHECK:     ret v18, v24
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for use_large, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @use_large] return type: Int type requires annotation
// CHECK:   [func @use_large, bb0, inst 7] result annotation: int annotation on non-Int type Bool
// CHECK:   [func @use_large, bb1, inst 3] result annotation: int annotation on non-Int type Bool
// CHECK:

#![crate_type = "lib"]

#[repr(C)]
pub struct Large {
    a: u64,
    b: u64,
    c: u64,
}

#[no_mangle]
pub fn use_large(x: Large) -> u64 {
    x.a + x.b + x.c
}
