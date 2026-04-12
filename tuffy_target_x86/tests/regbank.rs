//! Tests for x86 register-bank classification and aliasing.

use tuffy_target::regbank::{RegBank, RegClass, make_preg, preg_class, preg_reg_num};
use tuffy_target_x86::reg::{X86RegBank, Xmm, Ymm, Zmm};

#[test]
fn test_preg_encoding() {
    let xmm0 = make_preg(RegClass::XMM, 0);
    assert_eq!(preg_class(xmm0), RegClass::XMM);
    assert_eq!(preg_reg_num(xmm0), 0);

    let zmm31 = make_preg(RegClass::ZMM, 31);
    assert_eq!(preg_class(zmm31), RegClass::ZMM);
    assert_eq!(preg_reg_num(zmm31), 31);
}

#[test]
fn test_x86_aliasing() {
    let xmm0 = Xmm::Xmm0.to_preg();
    let ymm0 = Ymm::Ymm0.to_preg();
    let zmm0 = Zmm::Zmm0.to_preg();

    assert!(X86RegBank::aliases(xmm0, ymm0));
    assert!(X86RegBank::aliases(ymm0, zmm0));
    assert!(X86RegBank::aliases(xmm0, zmm0));

    let xmm1 = Xmm::Xmm1.to_preg();
    assert!(!X86RegBank::aliases(xmm0, xmm1));
}
