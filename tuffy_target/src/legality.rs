//! Target-specific legality information for operation legalization.
//!
//! This module defines the trait and types used to query whether operations
//! are legal on a target, and what action to take for illegal operations.

use tuffy_ir::instruction::Op;

/// Legalization action for an operation on a given width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegalizeAction {
    /// Operation is natively supported — no transformation needed.
    Legal,
    /// Expand into a sequence of legal operations.
    ///
    /// Examples:
    /// - Wide integer split: 128-bit add → two 64-bit adds with carry
    /// - Rotate expansion: rotate → shift + or sequence
    /// - PopCount expansion: popcount → Kernighan's algorithm
    Expand,
    /// Replace with a library call to the named symbol.
    ///
    /// Examples:
    /// - `__divdi3` / `__divti3` for signed exact-double-width division
    /// - `__udivdi3` / `__udivti3` for unsigned exact-double-width division
    /// - `__moddi3` / `__modti3` for signed exact-double-width remainder
    /// - `__umoddi3` / `__umodti3` for unsigned exact-double-width remainder
    LibCall(&'static str),
}

/// Target-specific legality information.
///
/// Implementations declare which operations are legal on the target,
/// and what action to take for illegal operations.
pub trait LegalityInfo {
    /// Query the legalization action for an operation.
    ///
    /// # Arguments
    ///
    /// * `op` — the operation to query
    /// * `width` — optional annotation width (e.g., Some(128) for i128/u128)
    ///
    /// # Returns
    ///
    /// The action to take: `Legal`, `Expand`, or `LibCall`.
    fn legalize_action(&self, op: &Op, width: Option<u32>) -> LegalizeAction;

    /// Maximum integer width natively supported by this target.
    ///
    /// For x86-64, this is 64. Operations on wider integers must be split
    /// or lowered to library calls.
    fn max_int_width(&self) -> u32;

    /// Check if an operation on a given width needs legalization.
    ///
    /// Default implementation: returns true if the legalize_action
    /// returns `Expand` or `LibCall`.
    fn needs_legalization(&self, op: &Op, width: Option<u32>) -> bool {
        match self.legalize_action(op, width) {
            LegalizeAction::Legal => false,
            LegalizeAction::Expand | LegalizeAction::LibCall(_) => true,
        }
    }
}
