//! X86-64 target legality information.
//!
//! Declares which operations are legal on x86-64 and what action to take
//! for illegal operations (expand inline or lower to library calls).

use tuffy_ir::instruction::Op;
use tuffy_target::legality::{LegalityInfo, LegalizeAction};

/// X86-64 legality information.
///
/// x86-64 natively supports 64-bit integer operations. Operations on wider
/// integers (e.g., 128-bit) must be split into pairs of 64-bit operations
/// or lowered to library calls.
pub struct X86LegalityInfo;

impl LegalityInfo for X86LegalityInfo {
    fn legalize_action(&self, op: &Op, width: Option<u32>) -> LegalizeAction {
        match (op, width) {
            // FRem: x86 has no SSE remainder instruction → expand to fmod/fmodf call
            (Op::FRem(_, _, _), _) => LegalizeAction::Expand,
            // Arithmetic operations legal at ≤64 bits
            (
                Op::Add(_, _)
                | Op::Sub(_, _)
                | Op::Mul(_, _)
                | Op::And(_, _)
                | Op::Or(_, _)
                | Op::Xor(_, _),
                Some(w),
            ) if w <= 64 => LegalizeAction::Legal,
            // Shift operations legal at ≤64 bits
            (Op::Shl(_, _) | Op::Shr(_, _), Some(w)) if w <= 64 => LegalizeAction::Legal,
            // Rotate operations: x86 has rol/ror instructions
            (Op::RotateLeft(_, _, _) | Op::RotateRight(_, _, _), _) => LegalizeAction::Legal,
            // PopCount: x86 has popcnt instruction
            (Op::CountOnes(_), _) => LegalizeAction::Legal,
            // Division/remainder on >64 bits → libcall
            (Op::Div(_, _), Some(w)) if w > 64 => {
                // Determine signedness from the operation context
                // For now, assume unsigned; the caller should provide this info
                LegalizeAction::LibCall("__udivti3")
            }
            (Op::Rem(_, _), Some(w)) if w > 64 => LegalizeAction::LibCall("__umodti3"),
            // Everything else on >64 bits → expand (split)
            (_, Some(w)) if w > 64 => LegalizeAction::Expand,
            // Default: legal
            _ => LegalizeAction::Legal,
        }
    }

    fn max_int_width(&self) -> u32 {
        64
    }
}
