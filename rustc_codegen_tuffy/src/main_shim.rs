use std::fs;

use rustc_codegen_ssa::{CompiledModule, ModuleKind};
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_codegen::CodegenSession;

/// Generate the C `main` entry point and a hand-crafted `lang_start`.
///
/// The C runtime calls `main(argc, argv)`. This wrapper forwards to
/// `std::rt::lang_start(rust_main, argc, argv, sigpipe=0)`.
///
/// We also emit a hand-crafted `lang_start` because tuffy cannot yet
/// compile the real `lang_start` (it constructs a `&dyn Fn() -> i32`
/// trait object, which requires vtable support). Our simplified version
/// calls the user's main directly and returns 0.
pub(crate) fn generate_entry_point(
    tcx: TyCtxt<'_>,
    session: &CodegenSession,
) -> Option<CompiledModule> {
    let (entry_def_id, _) = tcx.entry_fn(())?;

    let main_instance = Instance::mono(tcx, entry_def_id);
    let main_sym = tcx.symbol_name(main_instance).name.to_string();

    let start_def_id = tcx.lang_items().start_fn()?;
    let main_ret_ty = tcx
        .fn_sig(entry_def_id)
        .instantiate_identity()
        .output()
        .skip_binder();
    let start_instance = Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        start_def_id,
        tcx.mk_args(&[main_ret_ty.into()]),
    )
    .ok()
    .flatten()?;
    let start_sym = tcx.symbol_name(start_instance).name.to_string();

    let funcs = session.generate_entry_point(&main_sym, &start_sym);
    let object_data = session.emit_object(&funcs, &[]);

    let tmp = tcx.output_filenames(()).temp_path_for_cgu(
        rustc_session::config::OutputType::Object,
        "entry_point",
        tcx.sess.invocation_temp.as_deref(),
    );
    fs::write(&tmp, &object_data).expect("failed to write entry point");

    Some(CompiledModule {
        name: "entry_point".to_string(),
        kind: ModuleKind::Regular,
        object: Some(tmp),
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
        links_from_incr_cache: vec![],
    })
}
