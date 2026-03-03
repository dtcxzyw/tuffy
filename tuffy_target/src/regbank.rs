use tuffy_regalloc::PReg;

/// Register class identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegClass(pub u8);

impl RegClass {
    pub const GPR: RegClass = RegClass(0);
    pub const XMM: RegClass = RegClass(1);
    pub const YMM: RegClass = RegClass(2);
    pub const ZMM: RegClass = RegClass(3);
}

pub fn preg_class(preg: PReg) -> RegClass {
    RegClass(preg.0 >> 5)
}

pub fn preg_reg_num(preg: PReg) -> u8 {
    preg.0 & 0x1F
}

pub fn make_preg(class: RegClass, reg_num: u8) -> PReg {
    PReg((class.0 << 5) | reg_num)
}

/// Register aliasing trait for target-specific implementations.
pub trait RegBank {
    fn aliases(p1: PReg, p2: PReg) -> bool;
}
