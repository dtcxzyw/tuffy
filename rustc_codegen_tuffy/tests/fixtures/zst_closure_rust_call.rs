use std::marker::PhantomData;

fn main() {
    struct Symbol<'a, F: Fn(Vec<&'a str>) -> &'a str> {
        function: F,
        marker: PhantomData<&'a ()>,
    }

    let f = |x: Vec<&str>| -> &str {
        assert!(x.is_empty());
        "foobar"
    };
    let sym = Symbol {
        function: f,
        marker: PhantomData,
    };

    let out = (sym.function)(vec![]);
    assert_eq!(out, "foobar");
    println!("{out}");
}
