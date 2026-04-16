use std::ptr::NonNull;

const fn dangling_slice<T>() -> NonNull<[T]> {
    NonNull::<[T; 1]>::dangling()
}

const C: NonNull<[i32]> = dangling_slice();

fn main() {
    assert_eq!(C.as_ptr(), NonNull::<[i32; 1]>::dangling().as_ptr() as *mut _);
    assert_eq!(C.as_ptr().len(), 1);
    println!("ok");
}
