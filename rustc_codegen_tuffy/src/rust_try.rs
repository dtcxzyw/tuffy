use std::fs;
use std::process::Command;

use rustc_codegen_ssa::{CompiledModule, ModuleKind};
use rustc_middle::ty::TyCtxt;

/// Generate a `__rust_try` helper object file using the system assembler.
/// This provides the exception-handling wrapper needed by `catch_unwind`.
pub(crate) fn generate_rust_try(tcx: TyCtxt<'_>) -> Option<CompiledModule> {
    let obj_path = tcx.output_filenames(()).temp_path_for_cgu(
        rustc_session::config::OutputType::Object,
        "rust_try",
        tcx.sess.invocation_temp.as_deref(),
    );
    let asm_path = obj_path.with_extension("S");

    fs::write(
        &asm_path,
        r#"
.text
.globl __rust_try
.type __rust_try, @function
__rust_try:
    .cfi_startproc
    .cfi_personality 155, DW.ref.rust_eh_personality
    .cfi_lsda 27, .Lexcept_table0

    # Stack layout (24 bytes, 16-byte aligned with return addr):
    #   16(%rsp) = catch_fn
    #    8(%rsp) = data
    #    0(%rsp) = alignment padding
    # Values stored on the stack survive unwinding (registers don't).
    subq    $24, %rsp
    .cfi_def_cfa_offset 32

    movq    %rdx, 16(%rsp)
    movq    %rsi, 8(%rsp)
    movq    %rdi, %rax
    movq    %rsi, %rdi

.Ltry_begin:
    callq   *%rax
.Ltry_end:

    xorl    %eax, %eax
    .cfi_remember_state
    addq    $24, %rsp
    .cfi_def_cfa_offset 8
    retq

.Lcatch_landing_pad:
    .cfi_restore_state
    movq    8(%rsp), %rdi
    movq    %rax, %rsi
.Lcatch_call_begin:
    callq   *16(%rsp)
.Lcatch_call_end:

    movl    $1, %eax
    addq    $24, %rsp
    .cfi_def_cfa_offset 8
    retq

    .cfi_endproc
.size __rust_try, . - __rust_try

.section .gcc_except_table,"a",@progbits
.p2align 2
.Lexcept_table0:
    .byte   255
    .byte   155
    .uleb128 .Lttbase0 - .Lttbaseref0
.Lttbaseref0:
    .byte   1
    .uleb128 .Lcst_end0 - .Lcst_begin0
.Lcst_begin0:
    # try_fn call: landing pad = catch handler (action 1 = catch-all)
    .uleb128 .Ltry_begin - __rust_try
    .uleb128 .Ltry_end - .Ltry_begin
    .uleb128 .Lcatch_landing_pad - __rust_try
    .uleb128 1
    # catch_fn call: no landing pad (continue unwinding on double-panic)
    .uleb128 .Lcatch_call_begin - __rust_try
    .uleb128 .Lcatch_call_end - .Lcatch_call_begin
    .uleb128 0
    .uleb128 0
.Lcst_end0:
    .byte   1
    .byte   0
    .p2align 2
    .long   0
.Lttbase0:

.section .data.rel.ro,"aw",@progbits
.p2align 3
DW.ref.rust_eh_personality:
    .quad rust_eh_personality
.type DW.ref.rust_eh_personality, @object
.size DW.ref.rust_eh_personality, 8
.hidden DW.ref.rust_eh_personality
"#,
    )
    .expect("failed to write rust_try assembly");

    let status = Command::new("as")
        .arg("-o")
        .arg(&obj_path)
        .arg(&asm_path)
        .status()
        .expect("failed to run assembler");

    if !status.success() {
        panic!("assembler failed for rust_try.S");
    }

    Some(CompiledModule {
        name: "rust_try".to_string(),
        kind: ModuleKind::Regular,
        object: Some(obj_path),
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
        links_from_incr_cache: vec![],
    })
}
