//! x86-64 register definitions.

use tuffy_regalloc::PReg;
use tuffy_target::regbank::{RegBank, RegClass, make_preg, preg_class, preg_reg_num};

/// x86-64 general-purpose registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Gpr {
    /// `%rax`
    Rax = 0,
    /// `%rcx`
    Rcx = 1,
    /// `%rdx`
    Rdx = 2,
    /// `%rbx`
    Rbx = 3,
    /// `%rsp`
    Rsp = 4,
    /// `%rbp`
    Rbp = 5,
    /// `%rsi`
    Rsi = 6,
    /// `%rdi`
    Rdi = 7,
    /// `%r8`
    R8 = 8,
    /// `%r9`
    R9 = 9,
    /// `%r10`
    R10 = 10,
    /// `%r11`
    R11 = 11,
    /// `%r12`
    R12 = 12,
    /// `%r13`
    R13 = 13,
    /// `%r14`
    R14 = 14,
    /// `%r15`
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
    /// The PReg must be a GPR (class 0). Panics if given an XMM or other class register.
    pub fn from_preg(preg: PReg) -> Self {
        debug_assert!(
            preg.0 < 16,
            "Gpr::from_preg called with non-GPR PReg({}), class={}",
            preg.0,
            preg.0 >> 5
        );
        ALL_GPRS[(preg.0 & 0x1F) as usize]
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
/// x86-64 XMM registers.
pub enum Xmm {
    /// `%xmm0`
    Xmm0 = 0,
    /// `%xmm1`
    Xmm1 = 1,
    /// `%xmm2`
    Xmm2 = 2,
    /// `%xmm3`
    Xmm3 = 3,
    /// `%xmm4`
    Xmm4 = 4,
    /// `%xmm5`
    Xmm5 = 5,
    /// `%xmm6`
    Xmm6 = 6,
    /// `%xmm7`
    Xmm7 = 7,
    /// `%xmm8`
    Xmm8 = 8,
    /// `%xmm9`
    Xmm9 = 9,
    /// `%xmm10`
    Xmm10 = 10,
    /// `%xmm11`
    Xmm11 = 11,
    /// `%xmm12`
    Xmm12 = 12,
    /// `%xmm13`
    Xmm13 = 13,
    /// `%xmm14`
    Xmm14 = 14,
    /// `%xmm15`
    Xmm15 = 15,
}

impl Xmm {
    /// Convert to a target-agnostic physical register.
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::XMM, self as u8)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
/// x86-64 YMM registers.
pub enum Ymm {
    /// `%ymm0`
    Ymm0 = 0,
    /// `%ymm1`
    Ymm1 = 1,
    /// `%ymm2`
    Ymm2 = 2,
    /// `%ymm3`
    Ymm3 = 3,
    /// `%ymm4`
    Ymm4 = 4,
    /// `%ymm5`
    Ymm5 = 5,
    /// `%ymm6`
    Ymm6 = 6,
    /// `%ymm7`
    Ymm7 = 7,
    /// `%ymm8`
    Ymm8 = 8,
    /// `%ymm9`
    Ymm9 = 9,
    /// `%ymm10`
    Ymm10 = 10,
    /// `%ymm11`
    Ymm11 = 11,
    /// `%ymm12`
    Ymm12 = 12,
    /// `%ymm13`
    Ymm13 = 13,
    /// `%ymm14`
    Ymm14 = 14,
    /// `%ymm15`
    Ymm15 = 15,
}

impl Ymm {
    /// Convert to a target-agnostic physical register.
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::YMM, self as u8)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
/// x86-64 ZMM registers.
pub enum Zmm {
    /// `%zmm0`
    Zmm0 = 0,
    /// `%zmm1`
    Zmm1 = 1,
    /// `%zmm2`
    Zmm2 = 2,
    /// `%zmm3`
    Zmm3 = 3,
    /// `%zmm4`
    Zmm4 = 4,
    /// `%zmm5`
    Zmm5 = 5,
    /// `%zmm6`
    Zmm6 = 6,
    /// `%zmm7`
    Zmm7 = 7,
    /// `%zmm8`
    Zmm8 = 8,
    /// `%zmm9`
    Zmm9 = 9,
    /// `%zmm10`
    Zmm10 = 10,
    /// `%zmm11`
    Zmm11 = 11,
    /// `%zmm12`
    Zmm12 = 12,
    /// `%zmm13`
    Zmm13 = 13,
    /// `%zmm14`
    Zmm14 = 14,
    /// `%zmm15`
    Zmm15 = 15,
    /// `%zmm16`
    Zmm16 = 16,
    /// `%zmm17`
    Zmm17 = 17,
    /// `%zmm18`
    Zmm18 = 18,
    /// `%zmm19`
    Zmm19 = 19,
    /// `%zmm20`
    Zmm20 = 20,
    /// `%zmm21`
    Zmm21 = 21,
    /// `%zmm22`
    Zmm22 = 22,
    /// `%zmm23`
    Zmm23 = 23,
    /// `%zmm24`
    Zmm24 = 24,
    /// `%zmm25`
    Zmm25 = 25,
    /// `%zmm26`
    Zmm26 = 26,
    /// `%zmm27`
    Zmm27 = 27,
    /// `%zmm28`
    Zmm28 = 28,
    /// `%zmm29`
    Zmm29 = 29,
    /// `%zmm30`
    Zmm30 = 30,
    /// `%zmm31`
    Zmm31 = 31,
}

impl Zmm {
    /// Convert to a target-agnostic physical register.
    pub fn to_preg(self) -> PReg {
        make_preg(RegClass::ZMM, self as u8)
    }
}

/// Register-bank implementation for x86 register aliasing rules.
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
