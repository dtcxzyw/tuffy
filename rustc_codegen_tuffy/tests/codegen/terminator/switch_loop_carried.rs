// CHECK: fn core::num::<impl u8>::wrapping_add(_1: u8, _2: u8) -> u8 {
// CHECK:     debug self => _1;
// CHECK:     debug rhs => _2;
// CHECK:     let mut _0: u8;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMs4_NtC$HASH_4core3numh12wrapping_add(int:u8, int:u8) -> int:u8 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u8 = param 0
// CHECK:     v2: int:u8 = param 1
// CHECK:     v3: int:i8 = add v1, v2
// CHECK:     v4: int:u8 = zext v3, 8
// CHECK:     ret v4, v0
// CHECK: }
// CHECK:
// CHECK: fn advance_state(_1: u8, _2: u8) -> u8 {
// CHECK:     debug state => _1;
// CHECK:     debug limit => _2;
// CHECK:     let mut _0: u8;
// CHECK:     let mut _3: u8;
// CHECK:     let mut _4: u8;
// CHECK:     let mut _5: u8;
// CHECK:     let mut _6: u8;
// CHECK:     let mut _7: bool;
// CHECK:     let mut _8: u8;
// CHECK:     scope 1 {
// CHECK:         debug steps => _3;
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = const 0_u8;
// CHECK:         goto -> bb1;
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         switchInt(copy _1) -> [0: bb4, 1: bb3, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb8;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _4 = const 2_u8;
// CHECK:         goto -> bb5;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _4 = const 1_u8;
// CHECK:         goto -> bb5;
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _1 = move _4;
// CHECK:         _6 = copy _3;
// CHECK:         _5 = core::num::<impl u8>::wrapping_add(move _6, const 1_u8) -> [return: bb6, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _3 = move _5;
// CHECK:         _8 = copy _3;
// CHECK:         _7 = Eq(move _8, copy _2);
// CHECK:         switchInt(move _7) -> [0: bb1, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb8;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @advance_state(int:u8, int:u8) -> int:u8 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u8 = param 0
// CHECK:     v2: int:u8 = param 1
// CHECK:     v3: ptr = stack_slot 1 align 1
// CHECK:     v4: ptr = stack_slot 1 align 1
// CHECK:     v5: mem = store.1 v1, v4, v0
// CHECK:     v6: ptr = stack_slot 1 align 1
// CHECK:     v7: ptr = stack_slot 1 align 1
// CHECK:     v8: int:i8 = iconst 0
// CHECK:     v9: mem = store.1 v8, v6, v5
// CHECK:     br bb1(v9)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u8 = load.1 v4, v11
// CHECK:     v13: int:i64 = iconst 255
// CHECK:     v14: int:u64 = and v12, v13
// CHECK:     v15: int:i8 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb4(v11), bb9(v11)
// CHECK:
// CHECK:   bb2(v18: mem):
// CHECK:     v19: int:u8 = load.1 v4, v18
// CHECK:     v20: mem = store.1 v19, v7, v18
// CHECK:     br bb8(v20)
// CHECK:
// CHECK:   bb3(v22: mem):
// CHECK:     v23: int:i8 = iconst 2
// CHECK:     v24: mem = store.1 v23, v3, v22
// CHECK:     br bb5(v24)
// CHECK:
// CHECK:   bb4(v26: mem):
// CHECK:     v27: int:i8 = iconst 1
// CHECK:     v28: mem = store.1 v27, v3, v26
// CHECK:     br bb5(v28)
// CHECK:
// CHECK:   bb5(v30: mem):
// CHECK:     v31: int:u8 = load.1 v3, v30
// CHECK:     v32: mem = store.1 v31, v4, v30
// CHECK:     v33: int:u8 = load.1 v6, v32
// CHECK:     v34: int:i8 = iconst 1
// CHECK:     v35: ptr = symbol_addr @_RNvMs4_NtC$HASH_4core3numh12wrapping_add
// CHECK:     v36: mem, v37: int:u8 = call v35(v33, v34:u8), v32 -> int:u8
// CHECK:     br bb6(v36)
// CHECK:
// CHECK:   bb6(v39: mem):
// CHECK:     v40: mem = store.1 v37, v6, v39
// CHECK:     v41: int:u8 = load.1 v6, v40
// CHECK:     v42: bool = icmp.eq v41, v2
// CHECK:     v43: int:u64 = iconst 1
// CHECK:     v44: int:u64 = iconst 0
// CHECK:     v45: int:u64 = select v42, v43, v44
// CHECK:     v46: int:i64 = iconst 255
// CHECK:     v47: int:u64 = and v45, v46
// CHECK:     v48: int:i8 = iconst 0
// CHECK:     v49: bool = icmp.eq v47, v48
// CHECK:     brif v49, bb1(v40), bb7(v40)
// CHECK:
// CHECK:   bb7(v51: mem):
// CHECK:     v52: int:u8 = load.1 v4, v51
// CHECK:     v53: mem = store.1 v52, v7, v51
// CHECK:     br bb8(v53)
// CHECK:
// CHECK:   bb8(v55: mem):
// CHECK:     v56: int:u8 = load.1 v7, v55
// CHECK:     ret v56, v55
// CHECK:
// CHECK:   bb9(v58: mem):
// CHECK:     v59: int:i8 = iconst 1
// CHECK:     v60: bool = icmp.eq v14, v59
// CHECK:     brif v60, bb3(v58), bb2(v58)
// CHECK: }
// CHECK:
#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn advance_state(mut state: u8, limit: u8) -> u8 {
    let mut steps = 0u8;
    loop {
        state = match state {
            0 => 1,
            1 => 2,
            _ => return state,
        };
        steps = steps.wrapping_add(1);
        if steps == limit {
            return state;
        }
    }
}
