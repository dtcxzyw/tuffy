fn create_arr<const N: usize>(start: i32, step: i32) -> [(i32, i32); N] {
    let mut outs = [(start, start); N];
    let mut element = step;
    outs.iter_mut().skip(1).for_each(|(k, v)| {
        *k += element;
        *v += element;
        element += step;
    });
    outs
}

fn main() {
    let arr = create_arr::<5>(200, 1);
    assert_eq!(arr[0], (200, 200));
    assert_eq!(arr[4], (204, 204));
    println!("ok");
}
