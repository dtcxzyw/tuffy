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
// CHECK: func @use_large() -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 0
// CHECK:     v2: ptr = stack_slot 24
// CHECK:     v3: mem = store.24 v1, v2, v0
// CHECK:     v4: int:i64 = load.8 v2, v3
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v2, v5
// CHECK:     v7: int:i64 = load.8 v6, v3
// CHECK:     v8: int:u64, v9: bool = uadd_overflow.64 v4:u64, v7:u64
// CHECK:     v10: int:u64 = iconst 1
// CHECK:     v11: int:u64 = iconst 0
// CHECK:     v12: int:u64 = select v9, v10, v11
// CHECK:     v13: int:i64 = iconst 0
// CHECK:     v14: bool = icmp.eq v12, v13
// CHECK:     brif v14, bb1(v3), bb3(v3)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i64 = iconst 16
// CHECK:     v18: ptr = ptradd v2, v17
// CHECK:     v19: int:i64 = load.8 v18, v16
// CHECK:     v20: int:u64, v21: bool = uadd_overflow.64 v8, v19:u64
// CHECK:     v22: int:u64 = iconst 1
// CHECK:     v23: int:u64 = iconst 0
// CHECK:     v24: int:u64 = select v21, v22, v23
// CHECK:     v25: int:i64 = iconst 0
// CHECK:     v26: bool = icmp.eq v24, v25
// CHECK:     brif v26, bb2(v16), bb4(v16)
// CHECK:
// CHECK:   bb2(v28: mem):
// CHECK:     ret v20, v28
// CHECK:
// CHECK:   bb3(v30: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v32: mem):
// CHECK:     trap
// CHECK: }
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
