struct Wrapper<'a, Q: ?Sized> {
    hash: u64,
    key: &'a Q,
}

#[inline(never)]
fn call_with_key<Q: ?Sized, F: FnOnce(&Q) -> usize>(wrapper: Wrapper<'_, Q>, f: F) -> usize {
    f(wrapper.key)
}

fn main() {
    let wrapper = Wrapper {
        hash: 7,
        key: "poneyland",
    };
    let count = call_with_key(wrapper, |key: &str| key.chars().count());
    println!("{count}");
}
