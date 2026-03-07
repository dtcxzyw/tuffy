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
// CHECK: func @use_large(%x: byval ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %x
// CHECK:     v2 = load.8 v1, v0
// CHECK:     v3 = iconst 8
// CHECK:     v4 = ptradd v1, v3
// CHECK:     v5 = load.8 v4, v0
// CHECK:     v6 = uadd_overflow.64 v2:u64, v5:u64
// CHECK:     v8 = bool_to_int v7
// CHECK:     v9 = iconst 0
// CHECK:     v10 = icmp.eq v8, v9
// CHECK:     brif v10, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     v13 = iconst 16
// CHECK:     v14 = ptradd v1, v13
// CHECK:     v15 = load.8 v14, v12
// CHECK:     v16 = uadd_overflow.64 v6:u64, v15:u64
// CHECK:     v18 = bool_to_int v17
// CHECK:     v19 = iconst 0
// CHECK:     v20 = icmp.eq v18, v19
// CHECK:     brif v20, bb2(v12), bb4(v12)
// CHECK:
// CHECK:   bb2(v22: mem):
// CHECK:     ret v16, v22
// CHECK:
// CHECK:   bb3(v24: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v26: mem):
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
