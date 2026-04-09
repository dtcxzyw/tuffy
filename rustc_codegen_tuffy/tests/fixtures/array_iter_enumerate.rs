// compile-flags: -C opt-level=3

fn main() {
    let xs = [42_u32; 1];
    let mut seen = 0_usize;
    for (i, v) in xs.iter().enumerate() {
        assert_eq!(i, 0);
        assert_eq!(*v, 42);
        seen += 1;
    }
    assert_eq!(seen, 1);
    println!("ok");
}
