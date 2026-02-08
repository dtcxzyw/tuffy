//! End-to-end integration test: IR → isel → encode → ELF → link → run.

use std::fs;
use std::process::Command;

use tuffy_codegen::{emit, encode, isel};
use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::Type;

fn build_add_func() -> Function {
    let mut func = Function::new("add", vec![Type::Int, Type::Int], Some(Type::Int));
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, Origin::synthetic());
    let b = builder.param(1, Type::Int, Origin::synthetic());
    let a32 = builder.assert_sext(a, 32, Origin::synthetic());
    let b32 = builder.assert_sext(b, 32, Origin::synthetic());
    let sum = builder.add(a32, b32, Origin::synthetic());
    let result = builder.assert_sext(sum, 32, Origin::synthetic());
    builder.ret(Some(result), Origin::synthetic());

    builder.exit_region();

    func
}

fn compile_add_func() -> Vec<u8> {
    let func = build_add_func();
    let result = isel::isel(&func).expect("isel should succeed for add");
    let code = encode::encode_function(&result.insts);
    emit::emit_elf(&result.name, &code)
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
