// compile-flags: -C opt-level=3

#[inline(never)]
fn opt_eq(a: Option<usize>, b: Option<usize>) -> bool {
    a == b
}

#[inline(never)]
fn tuple_eq(a: (usize, usize), b: (usize, usize)) -> bool {
    a == b
}

fn main() {
    assert!(opt_eq(Some(3), Some(3)));
    assert!(!opt_eq(Some(3), Some(4)));
    assert!(opt_eq(None, None));
    assert!(tuple_eq((1, 2), (1, 2)));
    assert!(!tuple_eq((1, 2), (1, 3)));
    println!("ok");
}
