use std::panic::{AssertUnwindSafe, catch_unwind};

struct Bomb;

impl Drop for Bomb {
    fn drop(&mut self) {}
}

#[inline(never)]
fn may_panic() {
    panic!("boom");
}

#[inline(never)]
fn boom() {
    let _guard = Bomb;
    may_panic();
}

fn main() {
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(boom));
    std::panic::set_hook(previous_hook);
    assert!(result.is_err());
    println!("ok");
}
