//! Backend trait for target-specific code generation.

use tuffy_ir::function::Function;
use tuffy_ir::module::SymbolTable;

use crate::types::{CompiledFunction, StaticData};

/// Target-specific ABI metadata collected during MIR-to-IR translation.
///
/// Each backend defines how secondary return values (e.g., RDX on x86-64)
/// are captured and moved. The codegen layer uses this trait to communicate
/// ABI-specific information without knowing the target details.
pub trait AbiMetadata: Default {
    /// Mark an IR instruction as capturing the secondary return register
    /// from the preceding call (e.g., RDX on x86-64).
    fn mark_secondary_return_capture(&mut self, inst_idx: u32);

    /// Mark an IR instruction as moving a value into the secondary return
    /// register before a return (e.g., moving into RDX on x86-64).
    fn mark_secondary_return_move(&mut self, inst_idx: u32, source_idx: u32);
}

/// Allocator stub definition: a pair of (export_name, target_name).
pub type AllocatorPair<'a> = (&'a str, &'a str);

/// Target-specific code generation backend.
///
/// Implementations provide instruction selection, encoding, object file
/// emission, and generation of runtime stubs for a specific architecture.
pub trait Backend {
    /// The ABI metadata type for this backend.
    type Metadata: AbiMetadata;

    /// Compile a single IR function to machine code.
    ///
    /// Returns `None` if the function contains unsupported IR operations.
    fn compile_function(
        &self,
        func: &Function,
        symbols: &SymbolTable,
        metadata: &Self::Metadata,
    ) -> Option<CompiledFunction>;

    /// Emit compiled functions and static data as an object file.
    fn emit_object(&self, functions: &[CompiledFunction], statics: &[StaticData]) -> Vec<u8>;

    /// Generate allocator forwarding stubs (e.g., `__rust_alloc` → `__rdl_alloc`).
    ///
    /// Each pair is `(export_name, target_name)`. The `shim_marker` symbol
    /// should be emitted as a trivial function (e.g., just `ret`).
    fn generate_allocator_stubs(
        &self,
        pairs: &[(&str, &str)],
        shim_marker: &str,
    ) -> Vec<CompiledFunction>;

    /// Generate the C `main` entry point and a hand-crafted `lang_start`.
    ///
    /// `main_sym` is the user's Rust main function symbol.
    /// `start_sym` is the `lang_start` function symbol.
    fn generate_entry_point(&self, main_sym: &str, start_sym: &str) -> Vec<CompiledFunction>;
}
