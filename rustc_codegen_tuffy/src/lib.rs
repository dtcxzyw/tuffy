//! rustc_codegen_tuffy: Rustc codegen backend using tuffy IR.
//!
//! This crate implements `CodegenBackend` from `rustc_codegen_ssa`,
//! translating rustc MIR into tuffy IR for optimization and code generation.
//!
//! Build with: `rustc -Z codegen-backend=path/to/librustc_codegen_tuffy.so`

#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;

/// Allocator shim emission for rustc-required symbols.
mod allocator;
/// Backend option parsing and rustc target configuration.
mod config;
/// AOT crate codegen orchestration and object emission.
mod driver;
/// C-compatible process entry shims for crates with `main`.
mod main_shim;
/// MIR-to-Tuffy IR translation.
mod mir_to_ir;
/// `__rust_try` helper emission for unwinding support.
mod rust_try;
/// Static allocation relocation extraction and lowering.
mod static_data;

use std::any::Any;

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModules, CrateInfo, TargetConfig};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_session::config::OutputFilenames;

/// `rustc_codegen_ssa` backend implementation backed by Tuffy IR.
pub struct TuffyCodegenBackend;

impl CodegenBackend for TuffyCodegenBackend {
    fn name(&self) -> &'static str {
        "tuffy"
    }

    fn init(&self, sess: &Session) {
        config::init(sess);
    }

    fn target_config(&self, sess: &Session) -> TargetConfig {
        config::target_config(sess)
    }

    fn target_cpu(&self, sess: &Session) -> String {
        sess.target.cpu.to_string()
    }

    fn print_version(&self) {
        println!("rustc_codegen_tuffy {}", env!("CARGO_PKG_VERSION"));
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>, crate_info: &CrateInfo) -> Box<dyn Any> {
        driver::codegen_crate(tcx, crate_info)
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
        _outputs: &OutputFilenames,
    ) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>) {
        driver::join_codegen(ongoing_codegen)
    }

    // `link` uses the default implementation from CodegenBackend,
    // which delegates to ArArchiveBuilderBuilder.
}

/// Entry point called by rustc to create the backend.
#[unsafe(no_mangle)]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(TuffyCodegenBackend)
}
