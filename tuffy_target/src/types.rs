//! Common types shared between target backends and the codegen layer.

use tuffy_ir::debug::FunctionDebugInfo;

use crate::reloc::Relocation;

/// A machine-code offset tagged with a source id from `FunctionDebugInfo`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugLineRecord {
    /// Machine-code offset where the source location becomes active.
    pub offset: u32,
    /// Index into `FunctionDebugInfo::sources`.
    pub source: u32,
}

/// A location that a debugger can use to recover a variable value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DebugLocation {
    /// Variable lives in a machine register.
    Register(u16),
    /// Variable lives at a frame-pointer-relative offset.
    FrameOffset(i32),
}

/// One half-open machine-code range where a variable lives in one location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugVariableRange {
    /// Inclusive machine-code range start.
    pub start: u32,
    /// Exclusive machine-code range end.
    pub end: u32,
    /// Location used for the variable within this range.
    pub location: DebugLocation,
}

/// Resolved machine locations for one source-level variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledDebugVariable {
    /// Index into `FunctionDebugInfo::variables`.
    pub variable: u32,
    /// Machine-code ranges describing where the variable lives.
    pub ranges: Vec<DebugVariableRange>,
}

/// Debug info attached to a compiled function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledDebugInfo {
    /// Function-level debug side tables carried over from the IR.
    pub function: FunctionDebugInfo,
    /// Source line records for machine-code offsets.
    pub lines: Vec<DebugLineRecord>,
    /// Resolved machine locations for source variables.
    pub variables: Vec<CompiledDebugVariable>,
}

/// A compiled function ready for object file emission.
pub struct CompiledFunction {
    /// Symbol name emitted for the compiled function.
    pub name: String,
    /// Encoded machine code bytes.
    pub code: Vec<u8>,
    /// Relocations recorded within `code`.
    pub relocations: Vec<Relocation>,
    /// Optional debug information for the function.
    pub debug: Option<CompiledDebugInfo>,
    /// If true, emit with weak binding (STB_WEAK) so the linker can
    /// deduplicate identical instantiations across codegen units.
    pub weak: bool,
    /// If true, emit with local scope (STB_LOCAL) so the symbol is
    /// file-local and won't conflict with identically-named symbols
    /// in other object files.
    pub local: bool,
    /// If true, the function uses a standard frame pointer prologue
    /// (push rbp; mov rbp, rsp). Used to generate correct .eh_frame
    /// unwind information.
    pub has_frame_pointer: bool,
    /// Call-site table for LSDA generation (panic cleanup / landing pads).
    /// Each entry maps a call instruction region to its landing pad.
    /// Empty if the function has no cleanup blocks.
    pub call_site_table: Vec<CallSiteEntry>,
    /// DWARF register numbers of callee-saved registers saved in the prologue,
    /// in push order. Used to generate correct .eh_frame unwind rules so the
    /// unwinder can restore these registers.
    pub callee_saved_dwarf_regs: Vec<u8>,
    /// The `sub $N, %rsp` amount from the prologue. Needed to compute the
    /// CFA offset of each callee-saved register save location.
    pub sub_amount: i32,
}

/// One entry in the call-site table embedded in the LSDA.
///
/// Describes a region of code (a call instruction) and its associated
/// landing pad for stack unwinding.
#[derive(Debug, Clone)]
pub struct CallSiteEntry {
    /// Byte offset of the call region start, relative to function start.
    pub call_start: usize,
    /// Length of the call region in bytes.
    pub call_length: usize,
    /// Byte offset of the landing pad, relative to function start.
    /// 0 means no landing pad (should not appear in practice for entries
    /// that are explicitly tracked).
    pub landing_pad: usize,
}

/// A static data blob to be placed in a data section.
pub struct StaticData {
    /// Symbol name emitted for the static blob.
    pub name: String,
    /// Raw bytes stored in the static blob.
    pub data: Vec<u8>,
    /// Relocations within the data (e.g. function pointers in vtables).
    pub relocations: Vec<Relocation>,
    /// If true, place in a writable section (.data) instead of .rodata.
    pub writable: bool,
    /// If true, the static has `#[used]` semantics and must survive
    /// linker garbage collection (e.g. proc_macro_decls).
    pub used: bool,
    /// If true, emit as a weak undefined symbol (no data, no section).
    /// Used for `#[linkage = "extern_weak"]` statics.
    pub weak_undefined: bool,
    /// Required alignment in bytes (must be a power of two).
    /// Defaults to 1 if unknown.
    pub align: u64,
    /// If true, place in a TLS section (.tdata/.tbss) and mark as STT_TLS.
    pub thread_local: bool,
}
