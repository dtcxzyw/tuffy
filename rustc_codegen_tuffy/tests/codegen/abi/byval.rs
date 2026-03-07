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
// CHECK: func @use_large(%x: ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %x
// CHECK:     v2 = stack_slot 24
// CHECK:     v3 = iconst 24
// CHECK:     v4 = memcopy v2, v1, v3, align=8, v0
// CHECK:     v5 = load.8 v2, v4
// CHECK:     v6 = iconst 8
// CHECK:     v7 = ptradd v2, v6
// CHECK:     v8 = load.8 v7, v4
// CHECK:     v9 = uadd_overflow.64 v5:u64, v8:u64
// CHECK:     v11 = bool_to_int v10
// CHECK:     v12 = iconst 0
// CHECK:     v13 = icmp.eq v11, v12
// CHECK:     brif v13, bb1(v4), bb3(v4)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     v16 = iconst 16
// CHECK:     v17 = ptradd v2, v16
// CHECK:     v18 = load.8 v17, v15
// CHECK:     v19 = uadd_overflow.64 v9:u64, v18:u64
// CHECK:     v21 = bool_to_int v20
// CHECK:     v22 = iconst 0
// CHECK:     v23 = icmp.eq v21, v22
// CHECK:     brif v23, bb2(v15), bb4(v15)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     ret v19, v25
// CHECK:
// CHECK:   bb3(v27: mem):
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v29: mem):
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
