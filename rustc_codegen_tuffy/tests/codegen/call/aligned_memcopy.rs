// CHECK: fn echo_big(_1: Big) -> Big {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: Big;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = move _1;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @echo_big(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 64 align 32
// CHECK:     v4: int:i64 = iconst 64
// CHECK:     v5: mem = memcopy v3:align32, v2:align32, v4, v0
// CHECK:     v6: int:i64 = load.8 v3, v5
// CHECK:     v7: mem = store.8 v6, v1, v5
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v3, v8
// CHECK:     v10: int:i64 = load.8 v9, v7
// CHECK:     v11: int:i64 = iconst 8
// CHECK:     v12: ptr = ptradd v1, v11
// CHECK:     v13: mem = store.8 v10, v12, v7
// CHECK:     v14: int:i64 = iconst 16
// CHECK:     v15: ptr = ptradd v3, v14
// CHECK:     v16: int:i64 = load.8 v15, v13
// CHECK:     v17: int:i64 = iconst 16
// CHECK:     v18: ptr = ptradd v1, v17
// CHECK:     v19: mem = store.8 v16, v18, v13
// CHECK:     v20: int:i64 = iconst 24
// CHECK:     v21: ptr = ptradd v3, v20
// CHECK:     v22: int:i64 = load.8 v21, v19
// CHECK:     v23: int:i64 = iconst 24
// CHECK:     v24: ptr = ptradd v1, v23
// CHECK:     v25: mem = store.8 v22, v24, v19
// CHECK:     v26: int:i64 = iconst 32
// CHECK:     v27: ptr = ptradd v3, v26
// CHECK:     v28: int:i64 = load.8 v27, v25
// CHECK:     v29: int:i64 = iconst 32
// CHECK:     v30: ptr = ptradd v1, v29
// CHECK:     v31: mem = store.8 v28, v30, v25
// CHECK:     v32: int:i64 = iconst 40
// CHECK:     v33: ptr = ptradd v3, v32
// CHECK:     v34: int:i64 = load.8 v33, v31
// CHECK:     v35: int:i64 = iconst 40
// CHECK:     v36: ptr = ptradd v1, v35
// CHECK:     v37: mem = store.8 v34, v36, v31
// CHECK:     v38: int:i64 = iconst 48
// CHECK:     v39: ptr = ptradd v3, v38
// CHECK:     v40: int:i64 = load.8 v39, v37
// CHECK:     v41: int:i64 = iconst 48
// CHECK:     v42: ptr = ptradd v1, v41
// CHECK:     v43: mem = store.8 v40, v42, v37
// CHECK:     v44: int:i64 = iconst 56
// CHECK:     v45: ptr = ptradd v3, v44
// CHECK:     v46: int:i64 = load.8 v45, v43
// CHECK:     v47: int:i64 = iconst 56
// CHECK:     v48: ptr = ptradd v1, v47
// CHECK:     v49: mem = store.8 v46, v48, v43
// CHECK:     ret v1, v49
// CHECK: }
// CHECK:
#![crate_type = "lib"]
#![no_std]

#[repr(C, align(32))]
pub struct Big(pub [u8; 64]);

#[no_mangle]
pub extern "C" fn echo_big(x: Big) -> Big {
    x
}
