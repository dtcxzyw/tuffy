// CHECK: fn core::ptr::with_exposed_provenance(_1: usize) -> *const T {
// CHECK:     debug addr => _1;
// CHECK:     let mut _0: *const T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as *const T (PointerWithExposedProvenance);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core3ptr23with_exposed_provenancehEC$HASH_15provenance_cast(int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: ptr = inttoptr v1
// CHECK:     ret v2, v0
// CHECK: }
// CHECK:
// CHECK: fn core::ptr::const_ptr::<impl *const T>::addr(_1: *const T) -> usize {
// CHECK:     debug self => _1;
// CHECK:     let mut _0: usize;
// CHECK:     let mut _2: *const ();
// CHECK:     scope 1 (inlined core::ptr::const_ptr::<impl *const T>::cast::<()>) {
// CHECK:         debug self => _1;
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_2);
// CHECK:         _2 = copy _1 as *const () (PtrToPtr);
// CHECK:         _0 = copy _2 as usize (Transmute);
// CHECK:         StorageDead(_2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMNtNtC$HASH_4core3ptr9const_ptrPh4addrC$HASH_15provenance_cast(ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = ptrtoaddr v1
// CHECK:     ret v2, v0
// CHECK: }
// CHECK:
// CHECK: fn expose_provenance(_1: *const u8) -> usize {
// CHECK:     debug ptr => _1;
// CHECK:     let mut _0: usize;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::ptr::const_ptr::<impl *const u8>::addr(copy _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @expose_provenance(ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPh4addrC$HASH_15provenance_cast
// CHECK:     v3: mem, v4: int:u64 = call v2(v1), v0 -> int:u64
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
// CHECK: fn with_exposed_provenance(_1: usize) -> *const u8 {
// CHECK:     debug addr => _1;
// CHECK:     let mut _0: *const u8;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::ptr::with_exposed_provenance::<u8>(copy _1) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @with_exposed_provenance(int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u64 = param 0
// CHECK:     v2: ptr = symbol_addr @_RINvNtC$HASH_4core3ptr23with_exposed_provenancehEC$HASH_15provenance_cast
// CHECK:     v3: mem, v4: ptr = call v2(v1), v0 -> ptr
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
#![crate_type = "lib"]
#![no_std]

use core::ptr;

#[no_mangle]
pub fn expose_provenance(ptr: *const u8) -> usize {
    ptr.addr()
}

#[no_mangle]
pub fn with_exposed_provenance(addr: usize) -> *const u8 {
    ptr::with_exposed_provenance(addr)
}
