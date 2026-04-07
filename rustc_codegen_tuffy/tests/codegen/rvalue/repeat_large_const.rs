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
// CHECK:     v2: ptr = stack_slot 48 align 8
// CHECK:     v3: ptr = symbol_addr @.Lconst.0
// CHECK:     v4: int:i64 = load.8 v3, v0
// CHECK:     v5: mem = store.8 v4, v2, v0
// CHECK:     v6: int:i64 = iconst 8
// CHECK:     v7: ptr = ptradd v3, v6
// CHECK:     v8: int:i64 = load.8 v7, v5
// CHECK:     v9: int:i64 = iconst 8
// CHECK:     v10: ptr = ptradd v2, v9
// CHECK:     v11: mem = store.8 v8, v10, v5
// CHECK:     v12: int:i64 = iconst 16
// CHECK:     v13: ptr = ptradd v3, v12
// CHECK:     v14: int:i64 = load.8 v13, v11
// CHECK:     v15: int:i64 = iconst 16
// CHECK:     v16: ptr = ptradd v2, v15
// CHECK:     v17: mem = store.8 v14, v16, v11
// CHECK:     v18: int:i64 = iconst 24
// CHECK:     v19: ptr = ptradd v2, v18
// CHECK:     v20: int:i64 = load.8 v3, v17
// CHECK:     v21: mem = store.8 v20, v19, v17
// CHECK:     v22: int:i64 = iconst 8
// CHECK:     v23: ptr = ptradd v3, v22
// CHECK:     v24: int:i64 = load.8 v23, v21
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v19, v25
// CHECK:     v27: mem = store.8 v24, v26, v21
// CHECK:     v28: int:i64 = iconst 16
// CHECK:     v29: ptr = ptradd v3, v28
// CHECK:     v30: int:i64 = load.8 v29, v27
// CHECK:     v31: int:i64 = iconst 16
// CHECK:     v32: ptr = ptradd v19, v31
// CHECK:     v33: mem = store.8 v30, v32, v27
// CHECK:     v34: int:i64 = iconst 48
// CHECK:     v35: mem = memcopy v1:align8, v2:align8, v34, v33
// CHECK:     ret v1, v35
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
// CHECK:     v2: ptr = stack_slot 48 align 8
// CHECK:     v3: ptr = param 1
// CHECK:     v4: ptr = stack_slot 24 align 8
// CHECK:     v5: int:i64 = iconst 24
// CHECK:     v6: mem = memcopy v4:align8, v3:align8, v5, v0
// CHECK:     v7: ptr = stack_slot 24 align 8
// CHECK:     v8: int:i64 = load.8 v4, v6
// CHECK:     v9: mem = store.8 v8, v7, v6
// CHECK:     v10: int:i64 = iconst 8
// CHECK:     v11: ptr = ptradd v4, v10
// CHECK:     v12: int:i64 = load.8 v11, v9
// CHECK:     v13: int:i64 = iconst 8
// CHECK:     v14: ptr = ptradd v7, v13
// CHECK:     v15: mem = store.8 v12, v14, v9
// CHECK:     v16: int:i64 = iconst 16
// CHECK:     v17: ptr = ptradd v4, v16
// CHECK:     v18: int:i64 = load.8 v17, v15
// CHECK:     v19: int:i64 = iconst 16
// CHECK:     v20: ptr = ptradd v7, v19
// CHECK:     v21: mem = store.8 v18, v20, v15
// CHECK:     v22: int:i64 = load.8 v7, v21
// CHECK:     v23: mem = store.8 v22, v2, v21
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v7, v24
// CHECK:     v26: int:i64 = load.8 v25, v23
// CHECK:     v27: int:i64 = iconst 8
// CHECK:     v28: ptr = ptradd v2, v27
// CHECK:     v29: mem = store.8 v26, v28, v23
// CHECK:     v30: int:i64 = iconst 16
// CHECK:     v31: ptr = ptradd v7, v30
// CHECK:     v32: int:i64 = load.8 v31, v29
// CHECK:     v33: int:i64 = iconst 16
// CHECK:     v34: ptr = ptradd v2, v33
// CHECK:     v35: mem = store.8 v32, v34, v29
// CHECK:     v36: int:i64 = iconst 24
// CHECK:     v37: ptr = ptradd v2, v36
// CHECK:     v38: int:i64 = load.8 v7, v35
// CHECK:     v39: mem = store.8 v38, v37, v35
// CHECK:     v40: int:i64 = iconst 8
// CHECK:     v41: ptr = ptradd v7, v40
// CHECK:     v42: int:i64 = load.8 v41, v39
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v37, v43
// CHECK:     v45: mem = store.8 v42, v44, v39
// CHECK:     v46: int:i64 = iconst 16
// CHECK:     v47: ptr = ptradd v7, v46
// CHECK:     v48: int:i64 = load.8 v47, v45
// CHECK:     v49: int:i64 = iconst 16
// CHECK:     v50: ptr = ptradd v37, v49
// CHECK:     v51: mem = store.8 v48, v50, v45
// CHECK:     v52: int:i64 = iconst 48
// CHECK:     v53: mem = memcopy v1:align8, v2:align8, v52, v51
// CHECK:     ret v1, v53
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
