//! End-to-end integration test: IR → isel → encode → ELF → link → run.

use std::fs;
use std::process::Command;

use tuffy_ir::builder::Builder;
use tuffy_ir::debug::{
    DebugBinding, DebugSource, DebugValue, DebugVariable, DebugVariableKind, FunctionDebugInfo,
    SourceLocation,
};
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::Origin;
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{IntAnnotation, IntSignedness, Type};
use tuffy_target::backend::Backend;
use tuffy_target_x86::{backend, emit, encode, isel};

const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

fn build_add_func() -> (Function, SymbolTable) {
    let i32_type = Type::Int;
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), i32_type.clone()],
        vec![None, None],
        vec![],
        Some(i32_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i32_type.clone(), None, Origin::synthetic());
    let b = builder.param(1, i32_type.clone(), None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), I64, Origin::synthetic());
    builder.ret(Some(sum.into()), None, mem0.into(), Origin::synthetic());

    builder.exit_region();

    (func, st)
}

fn compile_add_func() -> Vec<u8> {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");
    let pinsts = backend::lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);
    emit::emit_elf(&result.name, &enc.code, &enc.relocations)
}

fn compile_add_func_with_debug() -> Vec<u8> {
    let i32_type = Type::Int;
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), i32_type.clone()],
        vec![None, None],
        vec![],
        Some(i32_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i32_type.clone(), None, Origin::from_source(0));
    let b = builder.param(1, i32_type.clone(), None, Origin::from_source(0));
    let sum = builder.add(a.into(), b.into(), I64, Origin::from_source(0));
    builder.ret(Some(sum.into()), None, mem0.into(), Origin::from_source(0));

    builder.exit_region();

    func.debug = FunctionDebugInfo {
        declaration: Some(SourceLocation {
            file: "/tmp/add.rs".to_string(),
            line: 3,
            column: 8,
        }),
        sources: vec![DebugSource {
            location: SourceLocation {
                file: "/tmp/add.rs".to_string(),
                line: 4,
                column: 12,
            },
        }],
        variables: vec![
            DebugVariable {
                name: "a".to_string(),
                kind: DebugVariableKind::Parameter,
                declaration: Some(SourceLocation {
                    file: "/tmp/add.rs".to_string(),
                    line: 3,
                    column: 12,
                }),
            },
            DebugVariable {
                name: "b".to_string(),
                kind: DebugVariableKind::Parameter,
                declaration: Some(SourceLocation {
                    file: "/tmp/add.rs".to_string(),
                    line: 3,
                    column: 20,
                }),
            },
        ],
        bindings: vec![
            DebugBinding {
                source: 0,
                variable: 0,
                value: DebugValue::IrValue(a),
            },
            DebugBinding {
                source: 0,
                variable: 1,
                value: DebugValue::IrValue(b),
            },
        ],
    };

    let backend = backend::X86Backend;
    let compiled = backend.compile_function(&func, &st).unwrap();
    backend.emit_object(&[compiled], &[])
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

#[test]
fn emits_dwarf_sections_and_entries() {
    let elf = compile_add_func_with_debug();
    let dir = tempfile::tempdir().unwrap();
    let obj_path = dir.path().join("add_debug.o");
    fs::write(&obj_path, &elf).unwrap();

    let sections = Command::new("readelf")
        .args(["-S"])
        .arg(&obj_path)
        .output()
        .expect("readelf not found");
    assert!(
        sections.status.success(),
        "readelf -S failed: {}",
        String::from_utf8_lossy(&sections.stderr)
    );
    let sections_stdout = String::from_utf8_lossy(&sections.stdout);
    assert!(
        sections_stdout.contains(".debug_info"),
        "missing .debug_info:\n{sections_stdout}"
    );
    assert!(
        sections_stdout.contains(".debug_line"),
        "missing .debug_line:\n{sections_stdout}"
    );

    let info = Command::new("readelf")
        .args(["--debug-dump=info"])
        .arg(&obj_path)
        .output()
        .expect("readelf not found");
    assert!(
        info.status.success(),
        "readelf --debug-dump=info failed: {}",
        String::from_utf8_lossy(&info.stderr)
    );
    let info_stdout = String::from_utf8_lossy(&info.stdout);
    assert!(
        info_stdout.contains("DW_TAG_subprogram"),
        "missing subprogram DIE:\n{info_stdout}"
    );
    assert!(
        info_stdout.contains("add"),
        "missing function name:\n{info_stdout}"
    );
    assert!(
        info_stdout.contains("DW_TAG_formal_parameter"),
        "missing parameter DIEs:\n{info_stdout}"
    );
    assert!(
        info_stdout.contains("a"),
        "missing parameter a:\n{info_stdout}"
    );
    assert!(
        info_stdout.contains("b"),
        "missing parameter b:\n{info_stdout}"
    );

    let lines = Command::new("readelf")
        .args(["--debug-dump=decodedline"])
        .arg(&obj_path)
        .output()
        .expect("readelf not found");
    assert!(
        lines.status.success(),
        "readelf --debug-dump=decodedline failed: {}",
        String::from_utf8_lossy(&lines.stderr)
    );
    let lines_stdout = String::from_utf8_lossy(&lines.stdout);
    assert!(
        lines_stdout.contains("/tmp/add.rs"),
        "missing source file in line table:\n{lines_stdout}"
    );
}
