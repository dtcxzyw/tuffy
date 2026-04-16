#![feature(allocator_api)]

use std::alloc::{Allocator, Global, Layout};
use std::ptr::NonNull;

fn do_alloc(layout: Layout) -> Result<NonNull<[u8]>, ()> {
    Global.allocate(layout).map_err(|_| ())
}

fn main() {
    let layout = Layout::from_size_align(24, 8).unwrap();
    let block = do_alloc(layout).unwrap();
    assert_eq!(block.len(), layout.size());

    let data = block.as_ptr() as *mut u8;
    unsafe {
        std::ptr::write_bytes(data, 0xA5, block.len());
        Global.deallocate(NonNull::new(data).unwrap(), layout);
    }

    println!("ok");
}
