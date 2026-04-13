// compile-flags: -Zmir-opt-level=0 -C debug-assertions=off
// CHECK: fn repeat_big_const() -> [Big; 2] {
// CHECK:     let mut _0: [Big; 2];
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = [const BIG; 2];
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: data @.Lconst.0 = "\x01\0\0\0\0\0\0\0\x02\0\0\0\0\0\0\0\x03\0\0\0\0\0\0\0"
// CHECK: func @repeat_big_const(ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = symbol_addr @.Lconst.0
// CHECK:     v3: int:i64 = load.8 v2, v0
// CHECK:     v4: mem = store.8 v3, v1, v0
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v2, v5
// CHECK:     v7: int:i64 = load.8 v6, v4
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v1, v8
// CHECK:     v10: mem = store.8 v7, v9, v4
// CHECK:     v11: int:i64 = iconst 16
// CHECK:     v12: ptr = ptradd v2, v11
// CHECK:     v13: int:i64 = load.8 v12, v10
// CHECK:     v14: int:i64 = iconst 16
// CHECK:     v15: ptr = ptradd v1, v14
// CHECK:     v16: mem = store.8 v13, v15, v10
// CHECK:     v17: int:i64 = iconst 24
// CHECK:     v18: ptr = ptradd v1, v17
// CHECK:     v19: int:i64 = load.8 v2, v16
// CHECK:     v20: mem = store.8 v19, v18, v16
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v2, v21
// CHECK:     v23: int:i64 = load.8 v22, v20
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v18, v24
// CHECK:     v26: mem = store.8 v23, v25, v20
// CHECK:     v27: int:i64 = iconst 16
// CHECK:     v28: ptr = ptradd v2, v27
// CHECK:     v29: int:i64 = load.8 v28, v26
// CHECK:     v30: int:i64 = iconst 16
// CHECK:     v31: ptr = ptradd v18, v30
// CHECK:     v32: mem = store.8 v29, v31, v26
// CHECK:     ret v1, v32
// CHECK: }
// CHECK:
// CHECK: fn repeat_big_local(_1: Big) -> [Big; 2] {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: [Big; 2];
// CHECK:     let mut _2: Big;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_2);
// CHECK:         _2 = copy _1;
// CHECK:         _0 = [move _2; 2];
// CHECK:         StorageDead(_2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @repeat_big_local(ptr, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: ptr = stack_slot 24 align 8
// CHECK:     v4: int:i64 = iconst 24
// CHECK:     v5: mem = memcopy v3:align8, v2:align8, v4, v0
// CHECK:     v6: ptr = stack_slot 24 align 8
// CHECK:     v7: int:i64 = load.8 v3, v5
// CHECK:     v8: mem = store.8 v7, v6, v5
// CHECK:     v9: int:i64 = iconst 8
// CHECK:     v10: ptr = ptradd v3, v9
// CHECK:     v11: int:i64 = load.8 v10, v8
// CHECK:     v12: int:i64 = iconst 8
// CHECK:     v13: ptr = ptradd v6, v12
// CHECK:     v14: mem = store.8 v11, v13, v8
// CHECK:     v15: int:i64 = iconst 16
// CHECK:     v16: ptr = ptradd v3, v15
// CHECK:     v17: int:i64 = load.8 v16, v14
// CHECK:     v18: int:i64 = iconst 16
// CHECK:     v19: ptr = ptradd v6, v18
// CHECK:     v20: mem = store.8 v17, v19, v14
// CHECK:     v21: int:i64 = load.8 v6, v20
// CHECK:     v22: mem = store.8 v21, v1, v20
// CHECK:     v23: int:i64 = iconst 8
// CHECK:     v24: ptr = ptradd v6, v23
// CHECK:     v25: int:i64 = load.8 v24, v22
// CHECK:     v26: int:i64 = iconst 8
// CHECK:     v27: ptr = ptradd v1, v26
// CHECK:     v28: mem = store.8 v25, v27, v22
// CHECK:     v29: int:i64 = iconst 16
// CHECK:     v30: ptr = ptradd v6, v29
// CHECK:     v31: int:i64 = load.8 v30, v28
// CHECK:     v32: int:i64 = iconst 16
// CHECK:     v33: ptr = ptradd v1, v32
// CHECK:     v34: mem = store.8 v31, v33, v28
// CHECK:     v35: int:i64 = iconst 24
// CHECK:     v36: ptr = ptradd v1, v35
// CHECK:     v37: int:i64 = load.8 v6, v34
// CHECK:     v38: mem = store.8 v37, v36, v34
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v6, v39
// CHECK:     v41: int:i64 = load.8 v40, v38
// CHECK:     v42: int:i64 = iconst 8
// CHECK:     v43: ptr = ptradd v36, v42
// CHECK:     v44: mem = store.8 v41, v43, v38
// CHECK:     v45: int:i64 = iconst 16
// CHECK:     v46: ptr = ptradd v6, v45
// CHECK:     v47: int:i64 = load.8 v46, v44
// CHECK:     v48: int:i64 = iconst 16
// CHECK:     v49: ptr = ptradd v36, v48
// CHECK:     v50: mem = store.8 v47, v49, v44
// CHECK:     ret v1, v50
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Big {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

pub const BIG: Big = Big { a: 1, b: 2, c: 3 };

#[no_mangle]
pub fn repeat_big_const() -> [Big; 2] {
    [BIG; 2]
}

#[no_mangle]
pub fn repeat_big_local(x: Big) -> [Big; 2] {
    [x; 2]
}
