//! x86-64 register definitions.

use tuffy_regalloc::PReg;
use tuffy_target::regbank::{RegBank, RegClass, make_preg, preg_class, preg_reg_num};

/// x86-64 general-purpose registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Gpr {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl Gpr {
    /// Hardware encoding (3-bit register number in ModR/M).
    pub fn encoding(self) -> u8 {
        (self as u8) & 0x7
    }

    /// Whether this register requires a REX prefix (R8-R15).
    pub fn needs_rex(self) -> bool {
        (self as u8) >= 8
    }

    /// Display name for 32-bit sub-register.
    pub fn name32(self) -> &'static str {
        match self {
            Gpr::Rax => "eax",
            Gpr::Rcx => "ecx",
            Gpr::Rdx => "edx",
            Gpr::Rbx => "ebx",
            Gpr::Rsp => "esp",
            Gpr::Rbp => "ebp",
            Gpr::Rsi => "esi",
            Gpr::Rdi => "edi",
            Gpr::R8 => "r8d",
            Gpr::R9 => "r9d",
            Gpr::R10 => "r10d",
            Gpr::R11 => "r11d",
            Gpr::R12 => "r12d",
            Gpr::R13 => "r13d",
            Gpr::R14 => "r14d",
            Gpr::R15 => "r15d",
        }
    }

    /// Display name for 64-bit register.
    pub fn name64(self) -> &'static str {
        match self {
            Gpr::Rax => "rax",
            Gpr::Rcx => "rcx",
            Gpr::Rdx => "rdx",
            Gpr::Rbx => "rbx",
            Gpr::Rsp => "rsp",
            Gpr::Rbp => "rbp",
            Gpr::Rsi => "rsi",
            Gpr::Rdi => "rdi",
            Gpr::R8 => "r8",
            Gpr::R9 => "r9",
            Gpr::R10 => "r10",
            Gpr::R11 => "r11",
            Gpr::R12 => "r12",
            Gpr::R13 => "r13",
            Gpr::R14 => "r14",
            Gpr::R15 => "r15",
        }
    }

    /// Convert to target-agnostic physical register.
    pub fn to_preg(self) -> PReg {
        PReg(self as u8)
    }

    /// Convert from target-agnostic physical register.
    pub fn from_preg(preg: PReg) -> Self {
        ALL_GPRS[preg.0 as usize]
    }
}

/// All 16 GPRs indexed by hardware encoding.
const ALL_GPRS: [Gpr; 16] = [
    Gpr::Rax,
    Gpr::Rcx,
    Gpr::Rdx,
    Gpr::Rbx,
    Gpr::Rsp,
    Gpr::Rbp,
    Gpr::Rsi,
    Gpr::Rdi,
    Gpr::R8,
    Gpr::R9,
    Gpr::R10,
    Gpr::R11,
    Gpr::R12,
    Gpr::R13,
    Gpr::R14,
    Gpr::R15,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Xmm {
    Xmm0 = 0,
    Xmm1 = 1,
    Xmm2 = 2,
    Xmm3 = 3,
    Xmm4 = 4,
    Xmm5 = 5,
    Xmm6 = 6,
    Xmm7 = 7,
    Xmm8 = 8,
    Xmm9 = 9,
    Xmm10 = 10,
    Xmm11 = 11,
    Xmm12 = 12,
    Xmm13 = 13,
    Xmm14 = 14,
    Xmm15 = 15,
}

impl Xmm {
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::XMM, self as u8)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Ymm {
    Ymm0 = 0,
    Ymm1 = 1,
    Ymm2 = 2,
    Ymm3 = 3,
    Ymm4 = 4,
    Ymm5 = 5,
    Ymm6 = 6,
    Ymm7 = 7,
    Ymm8 = 8,
    Ymm9 = 9,
    Ymm10 = 10,
    Ymm11 = 11,
    Ymm12 = 12,
    Ymm13 = 13,
    Ymm14 = 14,
    Ymm15 = 15,
}

impl Ymm {
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::YMM, self as u8)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Zmm {
    Zmm0 = 0,
    Zmm1 = 1,
    Zmm2 = 2,
    Zmm3 = 3,
    Zmm4 = 4,
    Zmm5 = 5,
    Zmm6 = 6,
    Zmm7 = 7,
    Zmm8 = 8,
    Zmm9 = 9,
    Zmm10 = 10,
    Zmm11 = 11,
    Zmm12 = 12,
    Zmm13 = 13,
    Zmm14 = 14,
    Zmm15 = 15,
    Zmm16 = 16,
    Zmm17 = 17,
    Zmm18 = 18,
    Zmm19 = 19,
    Zmm20 = 20,
    Zmm21 = 21,
    Zmm22 = 22,
    Zmm23 = 23,
    Zmm24 = 24,
    Zmm25 = 25,
    Zmm26 = 26,
    Zmm27 = 27,
    Zmm28 = 28,
    Zmm29 = 29,
    Zmm30 = 30,
    Zmm31 = 31,
}

impl Zmm {
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::ZMM, self as u8)
    }
}

pub struct X86RegBank;

impl RegBank for X86RegBank {
    fn aliases(p1: PReg, p2: PReg) -> bool {
        let c1 = preg_class(p1);
        let c2 = preg_class(p2);
        let n1 = preg_reg_num(p1);
        let n2 = preg_reg_num(p2);

        if n1 == n2 {
            let is_vec1 = c1.0 >= 1 && c1.0 <= 3;
            let is_vec2 = c2.0 >= 1 && c2.0 <= 3;
            return is_vec1 && is_vec2;
        }
        false
    }
}
