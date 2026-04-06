//! tuffy_codegen: Target-dispatching code generation facade.
//!
//! This crate provides `CodegenSession`, which selects the appropriate
//! backend based on the target triple and delegates all code generation
//! calls through enum dispatch.

mod legalize;

use tuffy_ir::function::Function;
use tuffy_ir::module::SymbolTable;
use tuffy_target::backend::Backend;
use tuffy_target::legality::LegalityInfo;
use tuffy_target::types::{CompiledFunction, StaticData};
use tuffy_target_x86::backend::X86Backend;
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
    ) -> Option<CompiledFunction> {
        match &self.inner {
            CodegenInner::X86(backend) => {
                let legality = X86LegalityInfo;
                let legalized = legalize::legalize(func, &legality, symbols);
                let func_ref = legalized.as_ref().unwrap_or(func);
                backend.compile_function(func_ref, symbols)
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
