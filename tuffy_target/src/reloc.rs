//! Relocation types shared between target backends and the codegen layer.

use crate::types::DebugLineRecord;

/// Kind of relocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocKind {
    /// PC-relative call (e.g., R_X86_64_PLT32 on x86-64).
    Call,
    /// PC-relative data reference (e.g., R_X86_64_PC32 on x86-64).
    PcRel,
    /// Absolute 64-bit address (e.g., R_X86_64_64 on x86-64).
    Abs64,
    /// Thread-local Initial Exec GOT offset (R_X86_64_GOTTPOFF on x86-64).
    TlsGotTpOff,
}

/// A relocation for an external symbol reference (e.g., CALL or LEA).
#[derive(Debug, Clone)]
pub struct Relocation {
    /// Byte offset in the code buffer where the rel32 displacement starts.
    pub offset: usize,
    /// The symbol name this relocation targets.
    pub symbol: String,
    /// Kind of relocation.
    pub kind: RelocKind,
}

/// Result of encoding a function.
pub struct EncodeResult {
    /// Encoded machine code bytes.
    pub code: Vec<u8>,
    /// Relocations for external symbol references.
    pub relocations: Vec<Relocation>,
    /// Call-site table for LSDA generation (panic cleanup / landing pads).
    pub call_site_table: Vec<crate::types::CallSiteEntry>,
    /// Source line transitions indexed by machine-code offset.
    pub line_records: Vec<DebugLineRecord>,
}
