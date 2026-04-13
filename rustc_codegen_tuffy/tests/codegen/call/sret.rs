//@ compile-flags: -C llvm-args=dump-ir
// CHECK: fn forward_large() -> Large {
// CHECK:     let mut _0: Large;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = make_large() -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @forward_large(ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = symbol_addr @make_large
// CHECK:     v3: mem = call v2(v1), v0
// CHECK:     v4: int:i64 = iconst 0
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v1, v6
// CHECK: }
// CHECK:
// CHECK: fn make_large() -> Large {
// CHECK:     let mut _0: Large;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Large { a: const 1_u64, b: const 2_u64, c: const 3_u64 };
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @make_large(ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i64 = iconst 1
// CHECK:     v3: mem = store.8 v2, v1, v0
// CHECK:     v4: int:i64 = iconst 2
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v1, v5
// CHECK:     v7: mem = store.8 v4, v6, v3
// CHECK:     v8: int:i64 = iconst 3
// CHECK:     v9: int:i64 = iconst 16
// CHECK:     v10: ptr = ptradd v1, v9
// CHECK:     v11: mem = store.8 v8, v10, v7
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

#[no_mangle]
pub fn forward_large() -> Large {
    make_large()
}
