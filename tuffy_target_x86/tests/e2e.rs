//! End-to-end integration test: IR → isel → encode → ELF → link → run.

use std::collections::HashMap;
use std::fs;
use std::process::Command;

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, Type};
use tuffy_target_x86::{backend, emit, encode, isel};

fn build_add_func() -> (Function, SymbolTable) {
    let s32 = Some(Annotation::Signed(32));
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![s32, s32],
        vec![],
        Some(Type::Int),
        s32,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, s32, Origin::synthetic());
    let b = builder.param(1, Type::Int, s32, Origin::synthetic());
    let sum = builder.add(
        Operand::annotated(a, Annotation::Signed(32)),
        Operand::annotated(b, Annotation::Signed(32)),
        s32,
        Origin::synthetic(),
    );
    builder.ret(
        Some(Operand::annotated(sum, Annotation::Signed(32))),
        mem0.into(),
        Origin::synthetic(),
    );

    builder.exit_region();

    (func, st)
}

fn compile_add_func() -> Vec<u8> {
    let (func, symbols) = build_add_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for add");
    let pinsts = backend::lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);
    emit::emit_elf(&result.name, &enc.code, &enc.relocations)
}

#[test]
fn objdump_disassembly() {
    let elf = compile_add_func();
    let dir = tempfile::tempdir().unwrap();
    let obj_path = dir.path().join("add.o");
    fs::write(&obj_path, &elf).unwrap();

    let output = Command::new("objdump")
        .args(["-d", "-M", "intel"])
        .arg(&obj_path)
        .output()
        .expect("objdump not found");

    let disasm = String::from_utf8_lossy(&output.stdout);
    assert!(
        disasm.contains("mov"),
        "expected mov in disassembly:\n{disasm}"
    );
    assert!(
        disasm.contains("add"),
        "expected add in disassembly:\n{disasm}"
    );
    assert!(
        disasm.contains("ret"),
        "expected ret in disassembly:\n{disasm}"
    );
}

const C_DRIVER: &str = r#"
#include <stdio.h>

extern int add(int a, int b);

int main(void) {
    int result = add(3, 4);
    if (result == 7) {
        printf("PASS: add(3, 4) = %d\n", result);
        return 0;
    } else {
        printf("FAIL: add(3, 4) = %d, expected 7\n", result);
        return 1;
    }
}
"#;

#[test]
fn link_and_run() {
    let elf = compile_add_func();
    let dir = tempfile::tempdir().unwrap();

    let obj_path = dir.path().join("add.o");
    fs::write(&obj_path, &elf).unwrap();

    let driver_path = dir.path().join("driver.c");
    fs::write(&driver_path, C_DRIVER).unwrap();

    let exe_path = dir.path().join("test_add");
    let compile = Command::new("cc")
        .arg(&driver_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&exe_path)
        .output()
        .expect("cc not found");

    assert!(
        compile.status.success(),
        "link failed: {}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&exe_path)
        .output()
        .expect("failed to run test binary");

    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "test binary failed: {stdout}{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("PASS"), "unexpected output: {stdout}");
}
