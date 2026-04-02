//! Common types shared between target backends and the codegen layer.

use crate::reloc::Relocation;

/// A compiled function ready for object file emission.
pub struct CompiledFunction {
    pub name: String,
    pub code: Vec<u8>,
    pub relocations: Vec<Relocation>,
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
}

/// A static data blob to be placed in a data section.
pub struct StaticData {
    pub name: String,
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
