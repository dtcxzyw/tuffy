const ALLOWED_CFGS: &[&str] = &[
    "emscripten_old_stat_abi",
    "espidf_time32",
    "freebsd10",
    "freebsd11",
    "freebsd12",
    "freebsd13",
    "freebsd14",
    "freebsd15",
];

fn main() {
    assert_eq!(ALLOWED_CFGS[0], "emscripten_old_stat_abi");
    assert_eq!(ALLOWED_CFGS[4], "freebsd12");
    assert!(ALLOWED_CFGS.contains(&"freebsd12"));
    println!("ok");
}
