// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn core::intrinsics::rotate_left(_1: T, _2: u32) -> T {
// CHECK:     debug x => _1;
// CHECK:     debug shift => _2;
// CHECK:     let mut _0: T;
// CHECK:     let mut _3: u32;
// CHECK:     let mut _4: u32;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::mem::size_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const <T as core::mem::SizedTypeProperties>::SIZE as u32 (IntToInt);
// CHECK:         _4 = Mul(move _5, const 8_u32);
// CHECK:         StorageDead(_5);
// CHECK:         _6 = Eq(copy _4, const 0_u32);
// CHECK:         assert(!move _6, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _2) -> [success: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = Rem(copy _2, move _4);
// CHECK:         StorageDead(_4);
// CHECK:         _0 = core::intrinsics::unchecked_funnel_shl::<T>(copy _1, move _1, move _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core10intrinsics11rotate_leftmECsj3JcaTRyli_6rotate(%x: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %x
// CHECK:     v2:u32 = param %shift
// CHECK:     v3 = iconst 4
// CHECK:     v4 = iconst 4294967295
// CHECK:     v5 = and v3, v4
// CHECK:     v6 = iconst 8
// CHECK:     v7:u32 = mul v5:u32, v6:u32
// CHECK:     v8 = iconst 0
// CHECK:     v9 = icmp.eq v7:u32, v8:u32
// CHECK:     v10 = bool_to_int v9
// CHECK:     v11 = iconst 0
// CHECK:     v12 = icmp.eq v10, v11
// CHECK:     brif v12, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     v15:u32 = rem v2:u32, v7:u32
// CHECK:     v16 = iconst 32
// CHECK:     v17 = sub v16, v15
// CHECK:     v18 = shl v1, v15
// CHECK:     v19 = shr v1, v17
// CHECK:     v20 = or v18, v19
// CHECK:     br bb2(v14)
// CHECK:
// CHECK:   bb2(v22: mem):
// CHECK:     ret v20, v22
// CHECK:
// CHECK:   bb3(v24: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::rotate_right(_1: T, _2: u32) -> T {
// CHECK:     debug x => _1;
// CHECK:     debug shift => _2;
// CHECK:     let mut _0: T;
// CHECK:     let mut _3: u32;
// CHECK:     let mut _4: u32;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::mem::size_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const <T as core::mem::SizedTypeProperties>::SIZE as u32 (IntToInt);
// CHECK:         _4 = Mul(move _5, const 8_u32);
// CHECK:         StorageDead(_5);
// CHECK:         _6 = Eq(copy _4, const 0_u32);
// CHECK:         assert(!move _6, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _2) -> [success: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = Rem(copy _2, move _4);
// CHECK:         StorageDead(_4);
// CHECK:         _0 = core::intrinsics::unchecked_funnel_shr::<T>(copy _1, move _1, move _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core10intrinsics12rotate_rightmECsj3JcaTRyli_6rotate(%x: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %x
// CHECK:     v2:u32 = param %shift
// CHECK:     v3 = iconst 4
// CHECK:     v4 = iconst 4294967295
// CHECK:     v5 = and v3, v4
// CHECK:     v6 = iconst 8
// CHECK:     v7:u32 = mul v5:u32, v6:u32
// CHECK:     v8 = iconst 0
// CHECK:     v9 = icmp.eq v7:u32, v8:u32
// CHECK:     v10 = bool_to_int v9
// CHECK:     v11 = iconst 0
// CHECK:     v12 = icmp.eq v10, v11
// CHECK:     brif v12, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     v15:u32 = rem v2:u32, v7:u32
// CHECK:     v16 = iconst 32
// CHECK:     v17 = sub v16, v15
// CHECK:     v18 = shl v1, v17
// CHECK:     v19 = shr v1, v15
// CHECK:     v20 = or v18, v19
// CHECK:     br bb2(v14)
// CHECK:
// CHECK:   bb2(v22: mem):
// CHECK:     ret v20, v22
// CHECK:
// CHECK:   bb3(v24: mem):
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::disjoint_bitor(_1: T, _2: T) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::DisjointBitOr>::disjoint_bitor(move _1, move _2) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core10intrinsics14disjoint_bitormECsj3JcaTRyli_6rotate(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2:u32 = param %b
// CHECK:     v3 = symbol_addr @_RNvXsd_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_13DisjointBitOr14disjoint_bitorCsj3JcaTRyli_6rotate
// CHECK:     v4, v5 = call v3(v1, v2), v0 -> int
// CHECK:     br bb1(v4)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::unchecked_funnel_shl(_1: T, _2: T, _3: u32) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shl(move _1, move _2, move _3) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core10intrinsics20unchecked_funnel_shlmECsj3JcaTRyli_6rotate(%a: int:u32, %b: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2:u32 = param %b
// CHECK:     v3:u32 = param %shift
// CHECK:     v4 = symbol_addr @_RNvXsp_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_11FunnelShift20unchecked_funnel_shlCsj3JcaTRyli_6rotate
// CHECK:     v5, v6 = call v4(v1, v2, v3), v0 -> int
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v6, v8
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::unchecked_funnel_shr(_1: T, _2: T, _3: u32) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shr(move _1, move _2, move _3) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core10intrinsics20unchecked_funnel_shrmECsj3JcaTRyli_6rotate(%a: int:u32, %b: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2:u32 = param %b
// CHECK:     v3:u32 = param %shift
// CHECK:     v4 = symbol_addr @_RNvXsp_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_11FunnelShift20unchecked_funnel_shrCsj3JcaTRyli_6rotate
// CHECK:     v5, v6 = call v4(v1, v2, v3), v0 -> int
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v6, v8
// CHECK: }
// CHECK:
// CHECK: fn <u32 as core::intrinsics::fallback::DisjointBitOr>::disjoint_bitor(_1: u32, _2: u32) -> u32 {
// CHECK:     debug self => _1;
// CHECK:     debug other => _2;
// CHECK:     let mut _0: u32;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         _4 = BitAnd(copy _1, copy _2);
// CHECK:         _3 = Eq(move _4, const 0_u32);
// CHECK:         StorageDead(_4);
// CHECK:         assume(move _3);
// CHECK:         StorageDead(_3);
// CHECK:         _0 = BitOr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsd_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_13DisjointBitOr14disjoint_bitorCsj3JcaTRyli_6rotate(%self: int:u32, %other: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %self
// CHECK:     v2:u32 = param %other
// CHECK:     v3:u32 = and v1:u32, v2:u32
// CHECK:     v4 = iconst 0
// CHECK:     v5 = icmp.eq v3:u32, v4:u32
// CHECK:     v6 = bool_to_int v5
// CHECK:     v7:u32 = or v1:u32, v2:u32
// CHECK:     ret v7, v0
// CHECK: }
// CHECK:
// CHECK: fn <u32 as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shl(_1: u32, _2: u32, _3: u32) -> u32 {
// CHECK:     debug self => _1;
// CHECK:     debug rhs => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: u32;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: u32;
// CHECK:     let mut _7: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _3, const 32_u32);
// CHECK:         assume(move _4);
// CHECK:         StorageDead(_4);
// CHECK:         switchInt(copy _3) -> [0: bb1, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = ShlUnchecked(copy _1, copy _3);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = Sub(const 32_u32, copy _3);
// CHECK:         _6 = ShrUnchecked(copy _2, move _7);
// CHECK:         StorageDead(_7);
// CHECK:         _0 = core::intrinsics::disjoint_bitor::<u32>(move _5, move _6) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsp_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_11FunnelShift20unchecked_funnel_shlCsj3JcaTRyli_6rotate(%self: int:u32, %rhs: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %self
// CHECK:     v2:u32 = param %rhs
// CHECK:     v3:u32 = param %shift
// CHECK:     v4 = stack_slot 4
// CHECK:     v5 = iconst 32
// CHECK:     v6 = icmp.lt v3:u32, v5:u32
// CHECK:     v7 = bool_to_int v6
// CHECK:     v8 = iconst 4294967295
// CHECK:     v9 = and v3, v8
// CHECK:     v10 = iconst 0
// CHECK:     v11 = icmp.eq v9, v10
// CHECK:     brif v11, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14 = store.4 v1, v4, v13
// CHECK:     br bb4(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17 = iconst 31
// CHECK:     v18 = and v3, v17
// CHECK:     v19:u32 = shl v1:u32, v18
// CHECK:     v20 = iconst 32
// CHECK:     v21:u32 = sub v20:u32, v3:u32
// CHECK:     v22 = iconst 31
// CHECK:     v23 = and v21, v22
// CHECK:     v24 = shr v2:u32, v23
// CHECK:     br bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     br bb4(v26)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     v29 = load.4 v4, v28
// CHECK:     ret v29, v28
// CHECK: }
// CHECK:
// CHECK: fn <u32 as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shr(_1: u32, _2: u32, _3: u32) -> u32 {
// CHECK:     debug self => _1;
// CHECK:     debug rhs => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: u32;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: u32;
// CHECK:     let mut _7: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _3, const 32_u32);
// CHECK:         assume(move _4);
// CHECK:         StorageDead(_4);
// CHECK:         switchInt(copy _3) -> [0: bb1, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_6);
// CHECK:         _6 = Sub(const 32_u32, copy _3);
// CHECK:         _5 = ShlUnchecked(copy _1, move _6);
// CHECK:         StorageDead(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = ShrUnchecked(copy _2, copy _3);
// CHECK:         _0 = core::intrinsics::disjoint_bitor::<u32>(move _5, move _7) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsp_NtNtCsgc7BJoiPOQP_4core10intrinsics8fallbackmNtB5_11FunnelShift20unchecked_funnel_shrCsj3JcaTRyli_6rotate(%self: int:u32, %rhs: int:u32, %shift: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %self
// CHECK:     v2:u32 = param %rhs
// CHECK:     v3:u32 = param %shift
// CHECK:     v4 = stack_slot 4
// CHECK:     v5 = iconst 32
// CHECK:     v6 = icmp.lt v3:u32, v5:u32
// CHECK:     v7 = bool_to_int v6
// CHECK:     v8 = iconst 4294967295
// CHECK:     v9 = and v3, v8
// CHECK:     v10 = iconst 0
// CHECK:     v11 = icmp.eq v9, v10
// CHECK:     brif v11, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14 = store.4 v2, v4, v13
// CHECK:     br bb4(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17 = iconst 32
// CHECK:     v18:u32 = sub v17:u32, v3:u32
// CHECK:     v19 = iconst 31
// CHECK:     v20 = and v18, v19
// CHECK:     v21:u32 = shl v1:u32, v20
// CHECK:     v22 = iconst 31
// CHECK:     v23 = and v3, v22
// CHECK:     v24 = shr v2:u32, v23
// CHECK:     br bb3(v16)
// CHECK:
// CHECK:   bb3(v26: mem):
// CHECK:     br bb4(v26)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     v29 = load.4 v4, v28
// CHECK:     ret v29, v28
// CHECK: }
// CHECK:
// CHECK: fn rotate_left_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     debug n => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::rotate_left) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::rotate_left::<u32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rotate_left_u32(%x: int:u32, %n: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %x
// CHECK:     v2:u32 = param %n
// CHECK:     v3 = rotate_left.32 v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn rotate_right_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     debug n => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::rotate_right) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::rotate_right::<u32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rotate_right_u32(%x: int:u32, %n: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %x
// CHECK:     v2:u32 = param %n
// CHECK:     v3 = rotate_right.32 v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn rotate_left_u32(x: u32, n: u32) -> u32 {
    x.rotate_left(n)
}

#[no_mangle]
pub fn rotate_right_u32(x: u32, n: u32) -> u32 {
    x.rotate_right(n)
}
