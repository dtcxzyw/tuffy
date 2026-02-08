//! Tests for x86-64 target definitions.

use crate::reg::Gpr;

#[test]
fn gpr_encoding() {
    assert_eq!(Gpr::Rax.encoding(), 0);
    assert_eq!(Gpr::Rcx.encoding(), 1);
    assert_eq!(Gpr::Rdi.encoding(), 7);
}

#[test]
fn gpr_names() {
    assert_eq!(Gpr::Rax.name32(), "eax");
    assert_eq!(Gpr::Rdi.name64(), "rdi");
}
