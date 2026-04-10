use std::path::PathBuf;

use rustc_codegen_ssa::TargetConfig;
use rustc_session::Session;
use rustc_session::config::{DebugInfo, InstrumentCoverage, Lto, OptLevel};
use rustc_span::Symbol;
use tuffy_ir::debug::FunctionDebugInfo;

#[derive(Clone, Debug)]
pub(crate) struct BackendOptions {
    pub dump_ir: bool,
    pub dump_module_path: Option<PathBuf>,
    pub run_tuffy_opt: bool,
    pub trace_timings: bool,
    pub debuginfo: DebugInfo,
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
        let run_tuffy_opt = should_run_tuffy_opt(sess.opts.optimize);
        let trace_timings = std::env::var_os("TUFFY_TRACE_TIMINGS").is_some();
        let debuginfo = sess.opts.cg.debuginfo;

        Self {
            dump_ir,
            dump_module_path,
            run_tuffy_opt,
            trace_timings,
            debuginfo,
        }
    }

    pub(crate) fn emit_debuginfo(&self) -> bool {
        self.debuginfo != DebugInfo::None
    }

    pub(crate) fn retain_variable_debuginfo(&self) -> bool {
        matches!(self.debuginfo, DebugInfo::Limited | DebugInfo::Full)
    }

    pub(crate) fn strip_debug_for_codegen(
        &self,
        func: &tuffy_ir::function::Function,
    ) -> tuffy_ir::function::Function {
        if self.emit_debuginfo() && self.retain_variable_debuginfo() {
            return func.clone();
        }
        let mut stripped = func.clone();
        if !self.emit_debuginfo() {
            stripped.debug = FunctionDebugInfo::default();
        } else {
            stripped.debug.variables.clear();
            stripped.debug.bindings.clear();
        }
        stripped
    }
}

fn should_run_tuffy_opt(opt_level: OptLevel) -> bool {
    !matches!(opt_level, OptLevel::No)
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

#[cfg(test)]
mod tests {
    use super::should_run_tuffy_opt;
    use rustc_session::config::OptLevel;

    #[test]
    fn enables_tuffy_opt_for_non_o0_levels() {
        assert!(!should_run_tuffy_opt(OptLevel::No));
        assert!(should_run_tuffy_opt(OptLevel::Less));
        assert!(should_run_tuffy_opt(OptLevel::More));
        assert!(should_run_tuffy_opt(OptLevel::Aggressive));
        assert!(should_run_tuffy_opt(OptLevel::Size));
        assert!(should_run_tuffy_opt(OptLevel::SizeMin));
    }
}
