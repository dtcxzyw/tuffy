// CHECK: fn call_id_wide(_1: Wide) -> Wide {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: Wide;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = id_wide(copy _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @call_id_wide(int:i64, int:i64) -> int:i128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = param 0
// CHECK:     v2: int:i64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v3, v5
// CHECK:     v7: mem = store.8 v2, v6, v4
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: int:i128 = load.16 v3, v7
// CHECK:     v10: ptr = symbol_addr @id_wide
// CHECK:     v11: mem, v12: int:i128 = call v10(v9), v7 -> int:i128
// CHECK:     v13: mem = store.16 v12, v8, v11
// CHECK:     br bb1(v13)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     v16: int:i128 = load.16 v8, v15
// CHECK:     ret v16, v15
// CHECK: }
// CHECK:
// CHECK: fn id_wide(_1: Wide) -> Wide {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: Wide;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = move _1;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @id_wide(int:i64, int:i64) -> int:i128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = param 0
// CHECK:     v2: int:i64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v3, v5
// CHECK:     v7: mem = store.8 v2, v6, v4
// CHECK:     v8: ptr = stack_slot 16 align 16
// CHECK:     v9: int:i128 = load.16 v3, v7
// CHECK:     v10: mem = store.16 v9, v8, v7
// CHECK:     v11: int:i128 = load.16 v8, v10
// CHECK:     ret v11, v10
// CHECK: }
// CHECK:
#![crate_type = "lib"]
#![no_std]

#[repr(transparent)]
pub struct Wide(pub u128);

#[inline(never)]
#[no_mangle]
pub fn id_wide(x: Wide) -> Wide {
    x
}

#[no_mangle]
pub fn call_id_wide(x: Wide) -> Wide {
    id_wide(x)
}
