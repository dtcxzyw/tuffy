//@ compile-flags: -C llvm-args=dump-ir
// CHECK: fn make_large() -> Large {
// CHECK:     let mut _0: Large;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Large { a: const 1_u64, b: const 2_u64, c: const 3_u64 };
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @make_large(sret ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param 0
// CHECK:     v2 = iconst 1
// CHECK:     v3 = store.8 v2, v1, v0
// CHECK:     v4 = iconst 2
// CHECK:     v5 = iconst 8
// CHECK:     v6 = ptradd v1, v5
// CHECK:     v7 = store.8 v4, v6, v3
// CHECK:     v8 = iconst 3
// CHECK:     v9 = iconst 16
// CHECK:     v10 = ptradd v1, v9
// CHECK:     v11 = store.8 v8, v10, v7
// CHECK:     ret v1, v11
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
pub fn make_large() -> Large {
    Large { a: 1, b: 2, c: 3 }
}
