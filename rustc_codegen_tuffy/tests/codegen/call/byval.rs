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
// CHECK: data @.Lloc_file.0 = "/tuffy/rustc_codegen_tuffy/tests/codegen/call/byval.rs"
// CHECK: data @.Lloc.1 = "..." relocs [0: @.Lloc_file.0]
// CHECK: data @.Lloc_file.2 = "/tuffy/rustc_codegen_tuffy/tests/codegen/call/byval.rs"
// CHECK: data @.Lloc.3 = "..." relocs [0: @.Lloc_file.2]
// CHECK: func @use_large(ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 24 align 8
// CHECK:     v3: int:i64 = iconst 24
// CHECK:     v4: mem = memcopy v2:align8, v1:align8, v3, v0
// CHECK:     v5: int:i64 = load.8 v2, v4
// CHECK:     v6: int:i64 = iconst 8
// CHECK:     v7: ptr = ptradd v2, v6
// CHECK:     v8: int:i64 = load.8 v7, v4
// CHECK:     v9: int:u64, v10: bool = uadd_overflow.64 v5:u64, v8:u64
// CHECK:     v11: int:u64 = iconst 1
// CHECK:     v12: int:u64 = iconst 0
// CHECK:     v13: int:u64 = select v10, v11, v12
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: bool = icmp.eq v13, v14
// CHECK:     brif v15, bb1(v4), bb3(v4)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:i64 = iconst 16
// CHECK:     v19: ptr = ptradd v2, v18
// CHECK:     v20: int:i64 = load.8 v19, v17
// CHECK:     v21: int:u64, v22: bool = uadd_overflow.64 v9, v20:u64
// CHECK:     v23: int:u64 = iconst 1
// CHECK:     v24: int:u64 = iconst 0
// CHECK:     v25: int:u64 = select v22, v23, v24
// CHECK:     v26: int:i64 = iconst 0
// CHECK:     v27: bool = icmp.eq v25, v26
// CHECK:     brif v27, bb2(v17), bb4(v17)
// CHECK:
// CHECK:   bb2(v29: mem):
// CHECK:     ret v21, v29
// CHECK:
// CHECK:   bb3(v31: mem):
// CHECK:     v32: ptr = symbol_addr @.Lloc.1
// CHECK:     v33: ptr = symbol_addr @_RNvNtNtC$HASH_4core9panicking11panic_const24panic_const_add_overflow
// CHECK:     v34: mem = call v33(v32), v31
// CHECK:     trap
// CHECK:
// CHECK:   bb4(v36: mem):
// CHECK:     v37: ptr = symbol_addr @.Lloc.3
// CHECK:     v38: ptr = symbol_addr @_RNvNtNtC$HASH_4core9panicking11panic_const24panic_const_add_overflow
// CHECK:     v39: mem = call v38(v37), v36
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
