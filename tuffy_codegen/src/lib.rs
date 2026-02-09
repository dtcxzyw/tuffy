//! tuffy_codegen: Target-dispatching code generation facade.
//!
//! This crate provides `CodegenSession`, which selects the appropriate
//! backend based on the target triple and delegates all code generation
//! calls through enum dispatch.

use std::collections::HashMap;

use tuffy_ir::function::Function;
use tuffy_target::backend::{AbiMetadata, Backend};
use tuffy_target::types::{CompiledFunction, StaticData};
use tuffy_target_x86::backend::{X86AbiMetadata, X86Backend};

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

    /// Compile a single IR function to machine code.
    pub fn compile_function(
        &self,
        func: &Function,
        call_targets: &HashMap<u32, String>,
        static_refs: &HashMap<u32, String>,
        metadata: &AbiMetadataBox,
    ) -> Option<CompiledFunction> {
        match (&self.inner, metadata) {
            (CodegenInner::X86(backend), AbiMetadataBox::X86(meta)) => {
                backend.compile_function(func, call_targets, static_refs, meta)
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
    pub fn mark_secondary_return_capture(&mut self, inst_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_secondary_return_capture(inst_idx),
        }
    }

    /// Mark an IR instruction as moving a value into the secondary return register.
    pub fn mark_secondary_return_move(&mut self, inst_idx: u32, source_idx: u32) {
        match self {
            AbiMetadataBox::X86(meta) => meta.mark_secondary_return_move(inst_idx, source_idx),
        }
    }
}
