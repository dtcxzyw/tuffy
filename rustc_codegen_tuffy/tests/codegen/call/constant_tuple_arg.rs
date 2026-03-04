//@ compile-flags: -Zmir-opt-level=3 -C debug-assertions=off

// Test that constant tuple arguments are loaded correctly in optimized MIR.
// This is a regression test for a bug where constant tuples were passed as
// pointers instead of being loaded and passed by value.

#![crate_type = "lib"]

use std::hint::black_box;

#[inline(never)]
pub fn consume_tuple(x: (i32,)) -> i32 {
    x.0
}

pub fn test_constant_tuple() -> i32 {
    consume_tuple((42,))
}

pub fn caller() {
    black_box(test_constant_tuple());
}
