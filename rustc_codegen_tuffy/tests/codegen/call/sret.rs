//@ compile-flags: -C llvm-args=dump-ir
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
// CHECK:     v2: ptr = stack_slot 24 align 8
// CHECK:     v3: int:i64 = iconst 1
// CHECK:     v4: mem = store.8 v3, v2, v0
// CHECK:     v5: int:i64 = iconst 2
// CHECK:     v6: int:i64 = iconst 8
// CHECK:     v7: ptr = ptradd v2, v6
// CHECK:     v8: mem = store.8 v5, v7, v4
// CHECK:     v9: int:i64 = iconst 3
// CHECK:     v10: int:i64 = iconst 16
// CHECK:     v11: ptr = ptradd v2, v10
// CHECK:     v12: mem = store.8 v9, v11, v8
// CHECK:     v13: int:i64 = iconst 24
// CHECK:     v14: mem = memcopy v1:align8, v2:align8, v13, v12
// CHECK:     ret v1, v14
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
