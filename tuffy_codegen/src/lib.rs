//! tuffy_codegen: Target-dispatching code generation facade.
//!
//! This crate provides `CodegenSession`, which selects the appropriate
//! backend based on the target triple and delegates all code generation
//! calls through enum dispatch.

mod legalize;

use tuffy_ir::function::Function;
use tuffy_ir::module::SymbolTable;
use tuffy_target::backend::{AbiMetadata, Backend};
use tuffy_target::legality::LegalityInfo;
use tuffy_target::types::{CompiledFunction, StaticData};
use tuffy_target_x86::backend::{X86AbiMetadata, X86Backend};
use tuffy_target_x86::legality::X86LegalityInfo;

/// Target-agnostic code generation session.
///
/// Created from a target triple string, dispatches to the appropriate
/// backend implementation via enum variants.
pub struct CodegenSession {
    inner: CodegenInner,
}

enum CodegenInner {
    X86(X86Backend),
}

/// Target-agnostic ABI metadata container.
///
/// Wraps backend-specific metadata so that MIR translation code can
/// record ABI information without knowing the target.
pub enum AbiMetadataBox {
    X86(X86AbiMetadata),
}

impl CodegenSession {
    /// Create a new codegen session for the given target triple.
    ///
    /// Currently only x86-64 targets are supported. Panics if the
    /// target is not recognized.
    pub fn new(target_triple: &str) -> Self {
        if target_triple.starts_with("x86_64") {
            CodegenSession {
                inner: CodegenInner::X86(X86Backend),
            }
        } else {
            panic!("unsupported target triple: {target_triple}");
        }
    }

    /// Create a default ABI metadata container for this session's backend.
    pub fn new_metadata(&self) -> AbiMetadataBox {
        match &self.inner {
            CodegenInner::X86(_) => AbiMetadataBox::X86(X86AbiMetadata::default()),
        }
    }

    /// Return the maximum legal integer width for the active target.
    pub fn max_int_width(&self) -> u32 {
        match &self.inner {
            CodegenInner::X86(_) => X86LegalityInfo.max_int_width(),
        }
    }

    /// Return how many legal integer-sized parts the active target can use
    /// for direct integer-class ABI passing/return.
    pub fn max_abi_int_parts(&self) -> u32 {
        match &self.inner {
            CodegenInner::X86(_) => 2,
        }
    }

    /// Return the maximum byte size handled directly by the target's
    /// integer-class ABI path before lowering switches to indirect passing.
    pub fn max_direct_abi_int_bytes(&self) -> u32 {
        (self.max_int_width() / 8) * self.max_abi_int_parts()
    }

    /// Compile a single IR function to machine code.
    ///
    /// Runs legalization according to the target's legality rules before
    /// dispatching to the backend.
    pub fn compile_function(
        &self,
        func: &Function,
        symbols: &mut SymbolTable,
        metadata: &AbiMetadataBox,
    ) -> Option<CompiledFunction> {
        match (&self.inner, metadata) {
            (CodegenInner::X86(backend), AbiMetadataBox::X86(meta)) => {
                let legality = X86LegalityInfo;
                let legalized = legalize::legalize(func, meta, &legality, symbols);
                let (func_ref, meta_ref) = match &legalized {
                    Some((f, m)) => (f, m),
                    None => (func, meta),
                };
                backend.compile_function(func_ref, symbols, meta_ref)
            }
        }
    }

    /// Emit compiled functions and static data as an object file.
    pub fn emit_object(&self, functions: &[CompiledFunction], statics: &[StaticData]) -> Vec<u8> {
        match &self.inner {
            CodegenInner::X86(backend) => backend.emit_object(functions, statics),
        }
    }

    /// Generate allocator forwarding stubs.
    pub fn generate_allocator_stubs(
        &self,
        pairs: &[(&str, &str)],
        shim_marker: &str,
    ) -> Vec<CompiledFunction> {
        match &self.inner {
            CodegenInner::X86(backend) => backend.generate_allocator_stubs(pairs, shim_marker),
        }
    }

    /// Generate the C `main` entry point and hand-crafted `lang_start`.
    pub fn generate_entry_point(&self, main_sym: &str, start_sym: &str) -> Vec<CompiledFunction> {
        match &self.inner {
            CodegenInner::X86(backend) => backend.generate_entry_point(main_sym, start_sym),
        }
    }
}

impl AbiMetadataBox {
    /// Mark an IR instruction as capturing the secondary return register.
    pub fn mark_secondary_return_capture(&mut self, inst_idx: u32, call_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_secondary_return_capture(inst_idx, call_idx),
        }
    }

    /// Mark a call instruction as producing a secondary return value.
    pub fn mark_call_secondary_return(&mut self, call_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_call_secondary_return(call_idx),
        }
    }

    /// Mark an IR instruction as moving a value into the secondary return register.
    pub fn mark_secondary_return_move(&mut self, inst_idx: u32, source_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_secondary_return_move(inst_idx, source_idx),
        }
    }

    /// Mark a call instruction as returning an exact double-width integer value.
    pub fn mark_double_width_return_call(&mut self, call_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_double_width_return_call(call_idx),
        }
    }

    /// Record that the call at `call_idx` has a cleanup landing pad at `label`.
    pub fn mark_call_cleanup(&mut self, call_idx: u32, label: u32) {
        match self {
            AbiMetadataBox::X86(meta) => {
                meta.call_cleanup_labels.insert(call_idx, label);
            }
        }
    }
}
