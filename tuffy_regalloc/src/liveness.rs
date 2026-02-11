//! Liveness analysis for virtual registers.

use crate::VReg;

/// A live range for a single VReg: [start, end) in instruction indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveRange {
    pub vreg: VReg,
    pub start: u32,
    pub end: u32,
}
