//! Atomic intrinsic helpers for MIR to IR lowering.

use tuffy_ir::types::MemoryOrdering;

/// Parse memory ordering from an atomic intrinsic name suffix.
pub(super) fn parse_atomic_ordering(name: &str) -> MemoryOrdering {
    if name.ends_with("_relaxed") {
        MemoryOrdering::Relaxed
    } else if name.ends_with("_acquire") {
        MemoryOrdering::Acquire
    } else if name.ends_with("_release") {
        MemoryOrdering::Release
    } else if name.ends_with("_acqrel") {
        MemoryOrdering::AcqRel
    } else {
        MemoryOrdering::SeqCst
    }
}
