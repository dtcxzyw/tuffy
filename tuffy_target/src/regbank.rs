//! Register-class helpers shared by target backends.

use tuffy_regalloc::PReg;

/// Register class identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegClass(pub u8);

impl RegClass {
    /// General-purpose register class.
    pub const GPR: RegClass = RegClass(0);
    /// 128-bit vector register class.
    pub const XMM: RegClass = RegClass(1);
    /// 256-bit vector register class.
    pub const YMM: RegClass = RegClass(2);
    /// 512-bit vector register class.
    pub const ZMM: RegClass = RegClass(3);
}

/// Extract the register class encoded in a physical register.
pub fn preg_class(preg: PReg) -> RegClass {
    RegClass(preg.0 >> 5)
}

/// Extract the register number within its class from a physical register.
pub fn preg_reg_num(preg: PReg) -> u8 {
    preg.0 & 0x1F
}

/// Build a physical register encoding from its class and class-local register number.
pub fn make_preg(class: RegClass, reg_num: u8) -> PReg {
    PReg((class.0 << 5) | reg_num)
}

/// Register aliasing trait for target-specific implementations.
pub trait RegBank {
    /// Return whether two physical registers alias the same storage.
    fn aliases(p1: PReg, p2: PReg) -> bool;
}
