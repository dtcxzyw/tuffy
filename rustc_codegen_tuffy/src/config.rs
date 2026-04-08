use std::path::PathBuf;

use rustc_codegen_ssa::TargetConfig;
use rustc_session::Session;
use rustc_session::config::{InstrumentCoverage, Lto, OptLevel};
use rustc_span::Symbol;

#[derive(Clone, Debug)]
pub(crate) struct BackendOptions {
    pub dump_ir: bool,
    pub dump_module_path: Option<PathBuf>,
    pub run_tuffy_opt: bool,
}

impl BackendOptions {
    pub(crate) fn from_session(sess: &Session) -> Self {
        let dump_ir = sess.opts.cg.llvm_args.iter().any(|arg| arg == "dump-ir");
        let dump_module_path = sess
            .opts
            .cg
            .llvm_args
            .iter()
            .find_map(|arg| arg.strip_prefix("dump-module="))
            .map(PathBuf::from);
        let run_tuffy_opt = sess.opts.optimize != OptLevel::No;

        Self {
            dump_ir,
            dump_module_path,
            run_tuffy_opt,
        }
    }
}

pub(crate) fn init(sess: &Session) {
    match sess.lto() {
        Lto::No | Lto::ThinLocal => {}
        Lto::Thin | Lto::Fat => sess
            .dcx()
            .warn("LTO is not supported by rustc_codegen_tuffy. You may get a linker error."),
    }

    if sess.opts.cg.instrument_coverage() != InstrumentCoverage::No {
        sess.dcx()
            .fatal("`-Cinstrument-coverage` is not supported by rustc_codegen_tuffy");
    }
}

pub(crate) fn target_config(sess: &Session) -> TargetConfig {
    let features: Vec<Symbol> = sess
        .target
        .rust_target_features()
        .iter()
        .filter(|(feature, _, _)| matches!(*feature, "x87" | "sse" | "sse2" | "fxsr"))
        .flat_map(|(feature, _, _)| {
            sess.target
                .implied_target_features(feature)
                .into_iter()
                .map(Symbol::intern)
        })
        .collect();

    TargetConfig {
        target_features: features.clone(),
        unstable_target_features: features,
        has_reliable_f16: false,
        has_reliable_f16_math: false,
        has_reliable_f128: false,
        has_reliable_f128_math: false,
    }
}
