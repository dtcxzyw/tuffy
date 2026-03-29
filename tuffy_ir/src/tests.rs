//! Tests for the tuffy IR builder and display.

use crate::builder::Builder;
use crate::function::{Function, RegionKind};
use crate::instruction::{AtomicRmwOp, ICmpOp, Instruction, Op, Origin};
use crate::module::{Module, SymbolTable};
use crate::typed::IntOperand;
use crate::types::{
    Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, MemoryOrdering, Type,
};

const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

const S64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Signed,
};

#[test]
fn build_add_function() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), None, Origin::synthetic());
    let b = builder.param(1, i64_type, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), I64, Origin::synthetic());
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());

    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
    assert_eq!(func.blocks.len(), 1);
    assert_eq!(func.block(entry).inst_count, 4);

    assert!(matches!(func.inst(0).op, Op::Param(0)));
    assert!(matches!(func.inst(1).op, Op::Param(1)));
    assert!(matches!(func.inst(2).op, Op::Add(_, _)));
    assert!(matches!(func.inst(3).op, Op::Ret(Some(_), _)));
}

#[test]
fn build_with_annotations() {
    let mut st = SymbolTable::new();
    let name = st.intern("add_i32");
    let i32_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), i32_type.clone()],
        vec![],
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
    let b = builder.param(1, i32_type, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), I64, Origin::synthetic());
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());

    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
}

#[test]
fn display_add_function() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type, s64_ann, Origin::synthetic());
    let sum = builder.add(
        a.into(),
        b.into(),
        IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Signed,
        },
        Origin::synthetic(),
    );
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @add(int:s64, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: int:s64 = add v1, v2\n\
         \x20\x20\x20\x20ret v3, v0\n\
         }"
    );
}

#[test]
fn display_named_params() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let a_sym = st.intern("a");
    let b_sym = st.intern("b");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![Some(a_sym), Some(b_sym)],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type, s64_ann, Origin::synthetic());
    let sum = builder.add(
        a.into(),
        b.into(),
        IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Signed,
        },
        Origin::synthetic(),
    );
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @add(%a: int:s64, %b: int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param %a\n\
         \x20\x20\x20\x20v2: int:s64 = param %b\n\
         \x20\x20\x20\x20v3: int:s64 = add v1, v2\n\
         \x20\x20\x20\x20ret v3, v0\n\
         }"
    );
}

#[test]
fn display_multi_block_branch() {
    let mut st = SymbolTable::new();
    let name = st.intern("max");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let bb0 = builder.create_block();
    let bb1 = builder.create_block();
    let bb2 = builder.create_block();

    builder.switch_to_block(bb0);
    let mem0 = builder.add_block_arg(bb0, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type, s64_ann, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Gt, a.into(), b.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    builder.switch_to_block(bb1);
    builder.ret(Some(a.into()), mem0.into(), Origin::synthetic());

    builder.switch_to_block(bb2);
    builder.ret(Some(b.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @max(int:s64, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: bool = icmp.gt v1, v2\n\
         \x20\x20\x20\x20brif v3, bb1, bb2\n\
         \n\
         \x20\x20bb1:\n\
         \x20\x20\x20\x20ret v1, v0\n\
         \n\
         \x20\x20bb2:\n\
         \x20\x20\x20\x20ret v2, v0\n\
         }"
    );
}

#[test]
fn display_nested_loop_region() {
    let mut st = SymbolTable::new();
    let name = st.intern("factorial");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let s64 = IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    };
    let mut func = Function::new(
        name,
        vec![i64_type.clone()],
        vec![s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let bb0 = builder.create_block();
    let mem0 = builder.add_block_arg(bb0, Type::Mem, None);

    let loop_region = builder.create_region(RegionKind::Loop);
    builder.enter_region(loop_region);
    let bb1 = builder.create_block();
    let bb2 = builder.create_block();
    builder.exit_region();

    let bb3 = builder.create_block();

    // bb0: entry
    builder.switch_to_block(bb0);
    let n = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let one = builder.iconst(1, 64, IntSignedness::Signed, Origin::synthetic());
    let init_acc = builder.iconst(1, 64, IntSignedness::Signed, Origin::synthetic());
    builder.br(bb1, vec![init_acc.into(), one.into()], Origin::synthetic());

    // bb1: loop header with block args
    let acc = builder.add_block_arg(bb1, i64_type.clone(), s64_ann);
    let i = builder.add_block_arg(bb1, i64_type, s64_ann);
    builder.switch_to_block(bb1);
    let cmp = builder.icmp(ICmpOp::Le, i.into(), n.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb2, vec![], bb3, vec![], Origin::synthetic());

    // bb2: loop body
    builder.switch_to_block(bb2);
    let new_acc = builder.mul(acc.into(), i.into(), s64, Origin::synthetic());
    let new_i = builder.sub(i.into(), one.into(), s64, Origin::synthetic());
    builder.continue_(vec![new_acc.into(), new_i.into()], Origin::synthetic());

    // bb3: after loop
    builder.switch_to_block(bb3);
    builder.ret(Some(acc.into()), mem0.into(), Origin::synthetic());

    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @factorial(int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = iconst 1\n\
         \x20\x20\x20\x20v3: int:s64 = iconst 1\n\
         \x20\x20\x20\x20br bb1(v3, v2)\n\
         \n\
         \x20\x20region loop {\n\
         \x20\x20\x20\x20bb1(v5: int:s64, v6: int:s64):\n\
         \x20\x20\x20\x20\x20\x20v7: bool = icmp.le v6, v1\n\
         \x20\x20\x20\x20\x20\x20brif v7, bb2, bb3\n\
         \n\
         \x20\x20\x20\x20bb2:\n\
         \x20\x20\x20\x20\x20\x20v9: int:s64 = mul v5, v6\n\
         \x20\x20\x20\x20\x20\x20v10: int:s64 = sub v6, v2\n\
         \x20\x20\x20\x20\x20\x20continue v9, v10\n\
         \x20\x20}\n\
         \n\
         \x20\x20bb3:\n\
         \x20\x20\x20\x20ret v5, v0\n\
         }"
    );
}

#[test]
fn build_bitwise_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("bitwise");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), None, Origin::synthetic());
    let b = builder.param(1, i64_type, None, Origin::synthetic());
    let v_and = builder.and(a.into(), b.into(), I64, Origin::synthetic());
    let v_or = builder.or(a.into(), b.into(), I64, Origin::synthetic());
    let v_xor = builder.xor(v_and.into(), v_or.into(), I64, Origin::synthetic());
    builder.ret(Some(v_xor.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 6);
    assert!(matches!(func.inst(2).op, Op::And(_, _)));
    assert!(matches!(func.inst(3).op, Op::Or(_, _)));
    assert!(matches!(func.inst(4).op, Op::Xor(_, _)));
}

#[test]
fn display_shift_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("shifts");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type, s64_ann, Origin::synthetic());
    let _v_shl = builder.shl(a.into(), b.into(), S64, Origin::synthetic());
    let v_shr = builder.shr(a.into(), b.into(), S64, Origin::synthetic());
    builder.ret(Some(v_shr.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @shifts(int:s64, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: int:s64 = shl v1, v2\n\
         \x20\x20\x20\x20v4: int:s64 = shr v1, v2\n\
         \x20\x20\x20\x20ret v4, v0\n\
         }"
    );
}

#[test]
fn display_division_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("divs");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let s64 = IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    };
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type, s64_ann, Origin::synthetic());
    let v_div = builder.div(a.into(), b.into(), s64, Origin::synthetic());
    let v_rem = builder.rem(a.into(), b.into(), s64, Origin::synthetic());
    let v_add = builder.add(v_div.into(), v_rem.into(), s64, Origin::synthetic());
    builder.ret(Some(v_add.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @divs(int:s64, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: int:s64 = div v1, v2\n\
         \x20\x20\x20\x20v4: int:s64 = rem v1, v2\n\
         \x20\x20\x20\x20v5: int:s64 = add v3, v4\n\
         \x20\x20\x20\x20ret v5, v0\n\
         }"
    );
}

#[test]
fn build_ptradd() {
    let mut st = SymbolTable::new();
    let name = st.intern("ptr_arith");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), i64_type.clone()],
        vec![],
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let off = builder.param(1, i64_type, None, Origin::synthetic());
    let result = builder.ptradd(ptr.into(), off.into(), 0, Origin::synthetic());
    builder.ret(Some(result.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
    assert!(matches!(func.inst(2).op, Op::PtrAdd(_, _)));
    assert_eq!(func.inst(2).ty, Type::Ptr(0));
}

#[test]
fn display_pointer_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("ptr_ops");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Ptr(0), i64_type.clone()],
        vec![None, None, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let p1 = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let p2 = builder.param(1, Type::Ptr(0), None, Origin::synthetic());
    let i = builder.param(2, i64_type, s64_ann, Origin::synthetic());
    let _pa = builder.ptradd(p1.into(), i.into(), 0, Origin::synthetic());
    let _pd = builder.ptrdiff(p1.into(), p2.into(), 64, Origin::synthetic());
    let _pi = builder.ptrtoint(p1.into(), 64, Origin::synthetic());
    let _addr = builder.ptrtoaddr(p2.into(), 64, Origin::synthetic());
    let _ip = builder.inttoptr(i.into(), 0, Origin::synthetic());
    builder.ret(Some(_pi.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @ptr_ops(ptr, ptr, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: ptr = param 0\n\
         \x20\x20\x20\x20v2: ptr = param 1\n\
         \x20\x20\x20\x20v3: int:s64 = param 2\n\
         \x20\x20\x20\x20v4: ptr = ptradd v1, v3\n\
         \x20\x20\x20\x20v5: int:s64 = ptrdiff v1, v2\n\
         \x20\x20\x20\x20v6: int:u64 = ptrtoint v1\n\
         \x20\x20\x20\x20v7: int:u64 = ptrtoaddr v2\n\
         \x20\x20\x20\x20v8: ptr = inttoptr v3\n\
         \x20\x20\x20\x20ret v6, v0\n\
         }"
    );
}

#[test]
fn build_float_binary_ops() {
    let f32_ty = Type::Float(FloatType::F32);
    let mut st = SymbolTable::new();
    let name = st.intern("float_bin");
    let mut func = Function::new(
        name,
        vec![f32_ty.clone(), f32_ty.clone()],
        vec![],
        vec![],
        Some(f32_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, f32_ty.clone(), None, Origin::synthetic());
    let b = builder.param(1, f32_ty.clone(), None, Origin::synthetic());
    let flags = FpRewriteFlags::default();
    let v_fadd = builder.fadd(
        a.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fsub = builder.fsub(
        a.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fmul = builder.fmul(
        v_fadd.into(),
        v_fsub.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fdiv = builder.fdiv(
        v_fmul.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_csign = builder.copysign(v_fdiv.into(), a.into(), f32_ty.clone(), Origin::synthetic());
    let v_neg = builder.fneg(v_csign.into(), f32_ty.clone(), Origin::synthetic());
    let v_abs = builder.fabs(v_neg.into(), f32_ty.clone(), Origin::synthetic());
    builder.ret(Some(v_abs.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 10);
    assert!(matches!(func.inst(2).op, Op::FAdd(_, _, _)));
    assert!(matches!(func.inst(3).op, Op::FSub(_, _, _)));
    assert!(matches!(func.inst(4).op, Op::FMul(_, _, _)));
    assert!(matches!(func.inst(5).op, Op::FDiv(_, _, _)));
    assert!(matches!(func.inst(6).op, Op::CopySign(_, _)));
    assert!(matches!(func.inst(7).op, Op::FNeg(_)));
    assert!(matches!(func.inst(8).op, Op::FAbs(_)));
    assert_eq!(func.inst(2).ty, f32_ty);
}

#[test]
fn display_float_ops() {
    let f64_ty = Type::Float(FloatType::F64);
    let mut st = SymbolTable::new();
    let name = st.intern("float_ops");
    let mut func = Function::new(
        name,
        vec![f64_ty.clone(), f64_ty.clone()],
        vec![],
        vec![],
        Some(f64_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, f64_ty.clone(), None, Origin::synthetic());
    let b = builder.param(1, f64_ty.clone(), None, Origin::synthetic());
    let flags = FpRewriteFlags::default();
    let _v_fadd = builder.fadd(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fsub = builder.fsub(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fmul = builder.fmul(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fdiv = builder.fdiv(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_neg = builder.fneg(a.into(), f64_ty.clone(), Origin::synthetic());
    let _v_abs = builder.fabs(a.into(), f64_ty.clone(), Origin::synthetic());
    let _v_cs = builder.copysign(a.into(), b.into(), f64_ty.clone(), Origin::synthetic());
    builder.ret(Some(_v_cs.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @float_ops(f64, f64) -> f64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: f64 = param 0\n\
         \x20\x20\x20\x20v2: f64 = param 1\n\
         \x20\x20\x20\x20v3: f64 = fadd v1, v2\n\
         \x20\x20\x20\x20v4: f64 = fsub v1, v2\n\
         \x20\x20\x20\x20v5: f64 = fmul v1, v2\n\
         \x20\x20\x20\x20v6: f64 = fdiv v1, v2\n\
         \x20\x20\x20\x20v7: f64 = fneg v1\n\
         \x20\x20\x20\x20v8: f64 = fabs v1\n\
         \x20\x20\x20\x20v9: f64 = copysign v1, v2\n\
         \x20\x20\x20\x20ret v9, v0\n\
         }"
    );
}

#[test]
fn display_f128_const() {
    let f128_ty = Type::Float(FloatType::F128);
    let mut st = SymbolTable::new();
    let name = st.intern("f128_const");
    let mut func = Function::new(name, vec![], vec![], vec![], Some(f128_ty.clone()), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let bits = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210_u128;
    let value = builder.fconst(FloatType::F128, bits, Origin::synthetic());
    builder.ret(Some(value.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let Op::FConst(constant) = &func.inst(0).op else {
        panic!("expected fconst instruction");
    };
    assert_eq!(constant.float_type(), FloatType::F128);
    assert_eq!(constant.to_bits(), bits);

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @f128_const() -> f128 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: f128 = fconst.f128 0x123456789abcdeffedcba9876543210\n\
         \x20\x20\x20\x20ret v1, v0\n\
         }"
    );
}

#[test]
fn build_atomic_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_test");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, i64_type.clone(), None, Origin::synthetic());

    let (mem1, v_la) = builder.load_atomic(
        ptr.into(),
        i64_type.clone(),
        MemoryOrdering::Acquire,
        mem0.into(),
        None,
        Origin::synthetic(),
    );
    let mem2 = builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        mem1.into(),
        Origin::synthetic(),
    );
    let (mem3, _v_rmw) = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        i64_type.clone(),
        MemoryOrdering::SeqCst,
        mem2.into(),
        None,
        Origin::synthetic(),
    );
    let (mem4, v_cx) = builder.atomic_cmpxchg(
        ptr.into(),
        v_la.into(),
        val.into(),
        i64_type,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        mem3.into(),
        None,
        Origin::synthetic(),
    );
    let mem5 = builder.fence(MemoryOrdering::SeqCst, mem4.into(), Origin::synthetic());
    builder.ret(Some(v_cx.into()), mem5.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 8);
    assert!(matches!(func.inst(2).op, Op::LoadAtomic(_, _, _)));
    assert!(matches!(func.inst(3).op, Op::StoreAtomic(_, _, _, _)));
    assert!(matches!(func.inst(4).op, Op::AtomicRmw(_, _, _, _, _)));
    assert!(matches!(
        func.inst(5).op,
        Op::AtomicCmpXchg(_, _, _, _, _, _)
    ));
    assert!(matches!(func.inst(6).op, Op::Fence(_, _)));
}

#[test]
fn display_atomic_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_ops");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), i64_type.clone()],
        vec![None, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, i64_type.clone(), s64_ann, Origin::synthetic());
    let (mem1, _la) = builder.load_atomic(
        ptr.into(),
        i64_type.clone(),
        MemoryOrdering::Acquire,
        mem0.into(),
        s64_ann,
        Origin::synthetic(),
    );
    let mem2 = builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        mem1.into(),
        Origin::synthetic(),
    );
    let (mem3, _rmw) = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        i64_type.clone(),
        MemoryOrdering::SeqCst,
        mem2.into(),
        s64_ann,
        Origin::synthetic(),
    );
    let (mem4, _cx) = builder.atomic_cmpxchg(
        ptr.into(),
        _la.into(),
        val.into(),
        i64_type,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        mem3.into(),
        s64_ann,
        Origin::synthetic(),
    );
    let mem5 = builder.fence(MemoryOrdering::SeqCst, mem4.into(), Origin::synthetic());
    builder.ret(Some(_cx.into()), mem5.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @atomic_ops(ptr, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: ptr = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: mem, v4: int:s64 = load.atomic.acquire v1, v0\n\
         \x20\x20\x20\x20v5: mem = store.atomic.release v2, v1, v3\n\
         \x20\x20\x20\x20v6: mem, v7: int:s64 = rmw.add.seqcst v1, v2, v5\n\
         \x20\x20\x20\x20v8: mem, v9: int:s64 = cmpxchg.acqrel.acquire v1, v4, v2, v6\n\
         \x20\x20\x20\x20v10: mem = fence.seqcst v8\n\
         \x20\x20\x20\x20ret v9, v10\n\
         }"
    );
}

#[test]
fn symbol_table_intern_and_resolve() {
    let mut st = SymbolTable::new();
    let id1 = st.intern("malloc");
    let id2 = st.intern("free");
    let id3 = st.intern("malloc"); // duplicate

    assert_eq!(id1, id3);
    assert_ne!(id1, id2);
    assert_eq!(st.resolve(id1), "malloc");
    assert_eq!(st.resolve(id2), "free");
    assert_eq!(st.len(), 2);
}

#[test]
fn build_symbol_addr() {
    let mut module = Module::new("test");
    let malloc_sym = module.intern("malloc");
    let caller_sym = module.intern("caller");
    let i64_type = Type::Int;

    let mut func = Function::new(
        caller_sym,
        vec![i64_type.clone()],
        vec![],
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let size = builder.param(0, i64_type, None, Origin::synthetic());
    let addr = builder.symbol_addr(malloc_sym, Origin::synthetic());
    let (mem1, Some(result)) = builder.call(
        addr.into(),
        vec![size.into()],
        Type::Ptr(0),
        mem0.into(),
        None,
        Origin::synthetic(),
    ) else {
        panic!("expected non-void call result");
    };
    builder.ret(Some(result.into()), mem1.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
    assert!(matches!(func.inst(1).op, Op::SymbolAddr(_)));
    assert_eq!(func.inst(1).ty, Type::Ptr(0));

    module.add_function(func);
    let output = format!("{module}");
    assert!(output.contains("symbol_addr @malloc"));
}

#[test]
fn display_symbol_addr_without_symbols() {
    let mut st = SymbolTable::new();
    let sym = st.intern("puts");
    let test_sym = st.intern("test");

    let mut func = Function::new(test_sym, vec![], vec![], vec![], None, None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    builder.symbol_addr(sym, Origin::synthetic());
    builder.ret(None, mem0.into(), Origin::synthetic());
    builder.exit_region();

    // Without module context, SymbolAddr and function name show raw ids
    let output = format!("{func}");
    assert!(output.contains("symbol_addr $0"));
    assert!(output.contains("func $1"));
}

#[test]
fn module_static_data() {
    let mut module = Module::new("test_module");
    let sym = module.intern(".Lstr.0");
    module.add_static_data(sym, b"hello".to_vec());

    assert_eq!(module.static_data.len(), 1);
    assert_eq!(module.resolve(module.static_data[0].name), ".Lstr.0");
    assert_eq!(module.static_data[0].data, b"hello");
}

// ---------------------------------------------------------------------------
// Verifier tests
// ---------------------------------------------------------------------------

use crate::verifier::{verify_function, verify_module};

/// Helper: build a valid "add" function and verify it passes.
fn build_valid_add_module() -> Module {
    let mut module = Module::new("test");
    let name = module.intern("add");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let p1 = b.param(1, i64_type, s64_ann, Origin::synthetic());
    let sum = b.add(a.into(), p1.into(), I64, Origin::synthetic());
    b.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    b.exit_region();
    module.add_function(func);
    module
}

#[test]
fn verify_valid_add_function() {
    let module = build_valid_add_module();
    let result = verify_module(&module);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_valid_multi_block() {
    let mut st = SymbolTable::new();
    let name = st.intern("max");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let bb1 = b.create_block();
    let bb2 = b.create_block();

    b.switch_to_block(bb0);
    let mem0 = b.add_block_arg(bb0, Type::Mem, None);
    let a = b.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let p1 = b.param(1, i64_type, s64_ann, Origin::synthetic());
    let cmp = b.icmp(ICmpOp::Gt, a.into(), p1.into(), Origin::synthetic());
    b.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    b.switch_to_block(bb1);
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());

    b.switch_to_block(bb2);
    b.ret(Some(p1.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_valid_loop_region() {
    let mut st = SymbolTable::new();
    let name = st.intern("factorial");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i64_type.clone()],
        vec![s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let mem0 = b.add_block_arg(bb0, Type::Mem, None);
    let loop_region = b.create_region(RegionKind::Loop);
    b.enter_region(loop_region);
    let bb1 = b.create_block();
    let bb2 = b.create_block();
    b.exit_region();
    let bb3 = b.create_block();

    b.switch_to_block(bb0);
    let n = b.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let one = b.iconst(1, 64, IntSignedness::Signed, Origin::synthetic());
    let init = b.iconst(1, 64, IntSignedness::Signed, Origin::synthetic());
    b.br(bb1, vec![init.into(), one.into()], Origin::synthetic());

    let acc = b.add_block_arg(bb1, i64_type.clone(), s64_ann);
    let i = b.add_block_arg(bb1, i64_type, s64_ann);
    b.switch_to_block(bb1);
    let cmp = b.icmp(ICmpOp::Le, i.into(), n.into(), Origin::synthetic());
    b.brif(cmp.into(), bb2, vec![], bb3, vec![], Origin::synthetic());

    b.switch_to_block(bb2);
    let new_acc = b.mul(acc.into(), i.into(), I64, Origin::synthetic());
    let new_i = b.sub(i.into(), one.into(), I64, Origin::synthetic());
    b.continue_(vec![new_acc.into(), new_i.into()], Origin::synthetic());

    b.switch_to_block(bb3);
    b.ret(Some(acc.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_detects_wrong_arith_operand_type() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_add");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );

    let (bb, _mem0, _a, p1, cmp) = {
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);

        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let a = b.param(0, i64_type.clone(), None, Origin::synthetic());
        let p1 = b.param(1, i64_type.clone(), None, Origin::synthetic());
        let cmp = b.icmp(ICmpOp::Gt, a.into(), p1.into(), Origin::synthetic());

        b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
        b.exit_region();
        (bb, mem0, a, p1, cmp)
    };

    // Manually insert invalid Add instruction with Bool operand before the ret
    let ret_idx = func.block(bb).last_inst.unwrap();
    func.insert_inst_before(
        ret_idx,
        Instruction {
            op: Op::Add(IntOperand::from(cmp.raw()), p1.into()),
            ty: i64_type,
            secondary_ty: None,
            origin: Origin::synthetic(),
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("int arith lhs")),
        "should flag Bool operand in Add: {result}"
    );
}

#[test]
fn verify_detects_missing_terminator() {
    let mut st = SymbolTable::new();
    let name = st.intern("no_term");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    b.param(0, i64_type, None, Origin::synthetic());
    // No terminator
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("terminator")),
        "should flag missing terminator: {result}"
    );
}

#[test]
fn verify_detects_load_non_ptr() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_load");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i64_type.clone(), None, Origin::synthetic());
    // Load from Int instead of Ptr — should be flagged.
    let v = b.load(
        a.into(),
        4,
        i64_type,
        mem0.into(),
        None,
        Origin::synthetic(),
    );
    b.ret(Some(v.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("expected Ptr")),
        "should flag non-Ptr load operand: {result}"
    );
}

#[test]
fn verify_detects_branch_arg_count_mismatch() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_br");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let bb1 = b.create_block();
    let _arg = b.add_block_arg(
        bb1,
        i64_type.clone(),
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Signed,
        })),
    );

    b.switch_to_block(bb0);
    let mem0 = b.add_block_arg(bb0, Type::Mem, None);
    let a = b.param(0, i64_type, None, Origin::synthetic());
    // Branch to bb1 which expects 1 arg, but pass 0.
    b.br(bb1, vec![], Origin::synthetic());

    b.switch_to_block(bb1);
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("passes 0 args, expected 1")),
        "should flag branch arg count mismatch: {result}"
    );
}

#[test]
fn verify_detects_duplicate_function_names() {
    let mut module = Module::new("test");
    let name = module.intern("dup");
    let func1 = Function::new(name, vec![], vec![], vec![], None, None);
    let func2 = Function::new(name, vec![], vec![], vec![], None, None);
    module.add_function(func1);
    module.add_function(func2);

    let result = verify_module(&module);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("duplicate function name")),
        "should flag duplicate names: {result}"
    );
}

#[test]
fn display_min_max() {
    let mut st = SymbolTable::new();
    let name = st.intern("minmax");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let s64 = IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    };
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![s64_ann, s64_ann],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i64_type.clone(), s64_ann, Origin::synthetic());
    let b = builder.param(1, i64_type.clone(), s64_ann, Origin::synthetic());
    let v_min = builder.min(a.into(), b.into(), S64, Origin::synthetic());
    let v_max = builder.max(a.into(), b.into(), S64, Origin::synthetic());
    let _sum = builder.add(v_min.into(), v_max.into(), s64, Origin::synthetic());
    builder.ret(Some(_sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    assert!(matches!(func.inst(2).op, Op::Min(_, _)));
    assert!(matches!(func.inst(3).op, Op::Max(_, _)));
    assert_eq!(func.inst(2).ty, i64_type);
    assert_eq!(func.inst(3).ty, i64_type);

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @minmax(int:s64, int:s64) -> int:s64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s64 = param 0\n\
         \x20\x20\x20\x20v2: int:s64 = param 1\n\
         \x20\x20\x20\x20v3: int:s64 = min v1, v2\n\
         \x20\x20\x20\x20v4: int:s64 = max v1, v2\n\
         \x20\x20\x20\x20v5: int:s64 = add v3, v4\n\
         \x20\x20\x20\x20ret v5, v0\n\
         }"
    );

    // Verify passes
    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

// --- MemSSA-specific tests ---

#[test]
fn memssa_store_load_threading() {
    let mut st = SymbolTable::new();
    let name = st.intern("memssa_basic");
    let i32_type = Type::Int;
    let s32_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 32,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), Type::Ptr(0)],
        vec![s32_ann, None],
        vec![],
        Some(i32_type.clone()),
        s32_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let val = b.param(0, i32_type.clone(), s32_ann, Origin::synthetic());
    let ptr = b.param(1, Type::Ptr(0), None, Origin::synthetic());
    // store produces mem1
    let mem1 = b.store(val.into(), ptr.into(), 4, mem0.into(), Origin::synthetic());
    // load consumes mem1 (MemoryUse), produces data only
    let loaded = b.load(
        ptr.into(),
        4,
        i32_type.clone(),
        mem1.into(),
        s32_ann,
        Origin::synthetic(),
    );
    // ret carries mem1 (load does not produce a new mem token)
    b.ret(Some(loaded.into()), mem1.into(), Origin::synthetic());
    b.exit_region();

    // Verify store result is Mem
    assert_eq!(func.inst(2).ty, Type::Mem);
    // Verify load result is Int (not Mem — load is a MemoryUse)
    assert_eq!(func.inst(3).ty, i32_type);
    assert_eq!(func.inst(3).secondary_ty, None);

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn memssa_multi_result_load_atomic() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_load");
    let i64_type = Type::Int;
    let s64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0)],
        vec![None],
        vec![],
        Some(i64_type.clone()),
        s64_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let ptr = b.param(0, Type::Ptr(0), None, Origin::synthetic());
    let (mem1, data) = b.load_atomic(
        ptr.into(),
        i64_type.clone(),
        MemoryOrdering::Acquire,
        mem0.into(),
        s64_ann,
        Origin::synthetic(),
    );
    b.ret(Some(data.into()), mem1.into(), Origin::synthetic());
    b.exit_region();

    let inst = &func.inst(1);
    assert_eq!(inst.ty, Type::Mem);
    assert_eq!(inst.secondary_ty, Some(i64_type));
    assert!(data.is_secondary_result());
    assert!(!mem1.is_secondary_result());

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn memssa_block_arg_phi() {
    let mut st = SymbolTable::new();
    let name = st.intern("mem_phi");
    let i32_type = Type::Int;
    let s32_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 32,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![Type::Bool, i32_type.clone(), Type::Ptr(0)],
        vec![None, s32_ann, None],
        vec![],
        Some(i32_type.clone()),
        s32_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let bb1 = b.create_block();
    let bb2 = b.create_block();
    let bb3 = b.create_block();

    // bb0: branch based on condition
    b.switch_to_block(bb0);
    let mem0 = b.add_block_arg(bb0, Type::Mem, None);
    let cond = b.param(0, Type::Bool, None, Origin::synthetic());
    let val = b.param(1, i32_type.clone(), s32_ann, Origin::synthetic());
    let ptr = b.param(2, Type::Ptr(0), None, Origin::synthetic());
    b.brif(cond.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    // bb1: store, then jump to bb3 with new mem
    b.switch_to_block(bb1);
    let mem1 = b.store(val.into(), ptr.into(), 4, mem0.into(), Origin::synthetic());
    b.br(bb3, vec![mem1.into()], Origin::synthetic());

    // bb2: no store, jump to bb3 with original mem
    b.switch_to_block(bb2);
    b.br(bb3, vec![mem0.into()], Origin::synthetic());

    // bb3: mem phi via block arg
    let mem_phi = b.add_block_arg(bb3, Type::Mem, None);
    b.switch_to_block(bb3);
    let loaded = b.load(
        ptr.into(),
        4,
        i32_type,
        mem_phi.into(),
        s32_ann,
        Origin::synthetic(),
    );
    b.ret(Some(loaded.into()), mem_phi.into(), Origin::synthetic());

    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn memssa_display_store_load() {
    let mut st = SymbolTable::new();
    let name = st.intern("sl");
    let i32_type = Type::Int;
    let s32_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 32,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), Type::Ptr(0)],
        vec![s32_ann, None],
        vec![],
        Some(i32_type.clone()),
        s32_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let val = b.param(0, i32_type.clone(), s32_ann, Origin::synthetic());
    let ptr = b.param(1, Type::Ptr(0), None, Origin::synthetic());
    let mem1 = b.store(val.into(), ptr.into(), 4, mem0.into(), Origin::synthetic());
    let loaded = b.load(
        ptr.into(),
        4,
        i32_type,
        mem1.into(),
        s32_ann,
        Origin::synthetic(),
    );
    b.ret(Some(loaded.into()), mem1.into(), Origin::synthetic());
    b.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @sl(int:s32, ptr) -> int:s32 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1: int:s32 = param 0\n\
         \x20\x20\x20\x20v2: ptr = param 1\n\
         \x20\x20\x20\x20v3: mem = store.4 v1, v2, v0\n\
         \x20\x20\x20\x20v4: int:s32 = load.4 v2, v3\n\
         \x20\x20\x20\x20ret v4, v3\n\
         }"
    );
}

#[test]
fn build_merge() {
    let mut st = SymbolTable::new();
    let name = st.intern("merge_test");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i64_type.clone(), None, Origin::synthetic());
    let lo = b.param(1, i64_type.clone(), None, Origin::synthetic());
    let merged = b.merge(a.into(), lo.into(), 64, Origin::synthetic());
    b.ret(Some(merged.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert!(matches!(func.inst(2).op, Op::Merge(_, _, 64)));
    assert_eq!(func.inst(2).ty, i64_type);

    let output = format!("{}", func.display(&st));
    assert!(output.contains("merge.64 v1, v2"));
}

#[test]
fn build_split() {
    let mut st = SymbolTable::new();
    let name = st.intern("split_test");
    let i128_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i128_type.clone()],
        vec![],
        vec![],
        Some(i128_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let wide = b.param(0, i128_type.clone(), None, Origin::synthetic());
    let (hi, lo) = b.split(wide.into(), 64, Origin::synthetic());

    // hi is primary result, lo is secondary
    assert!(!hi.is_secondary_result());
    assert!(lo.is_secondary_result());

    b.ret(Some(hi.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let inst = &func.inst(1);
    assert_eq!(inst.ty, i128_type);
    assert_eq!(inst.secondary_ty, Some(i128_type));

    let output = format!("{}", func.display(&st));
    assert!(output.contains("split.64 v1"));
}

#[test]
fn build_clmul() {
    let mut st = SymbolTable::new();
    let name = st.intern("clmul_test");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![i64_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i64_type.clone(), None, Origin::synthetic());
    let bv = b.param(1, i64_type.clone(), None, Origin::synthetic());
    let result = b.clmul(a.into(), bv.into(), Origin::synthetic());
    b.ret(Some(result.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert!(matches!(func.inst(2).op, Op::Clmul(_, _)));
    assert_eq!(func.inst(2).ty, i64_type);

    let output = format!("{}", func.display(&st));
    assert!(output.contains("clmul v1, v2"));
}

#[test]
fn test_struct_type_display() {
    let i64_type = Type::Int;
    let struct_ty = Type::Struct(vec![i64_type, Type::Bool, Type::Byte(4)]);
    let display = format!("{:?}", struct_ty);
    assert!(display.contains("Struct"));
}

#[test]
fn test_array_type_display() {
    let i64_type = Type::Int;
    let array_ty = Type::Array(Box::new(i64_type), 10);
    let display = format!("{:?}", array_ty);
    assert!(display.contains("Array"));
}

#[test]
fn test_extractvalue_basic() {
    let mut st = SymbolTable::new();
    let name = st.intern("extract_test");
    let i64_type = Type::Int;
    let struct_ty = Type::Struct(vec![i64_type.clone(), Type::Bool]);
    let mut func = Function::new(
        name,
        vec![struct_ty.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let s = b.param(0, struct_ty, None, Origin::synthetic());
    let field0 = b.extract_value(
        s.into(),
        vec![0],
        i64_type.clone(),
        None,
        Origin::synthetic(),
    );
    b.ret(Some(field0.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert_eq!(func.inst_pool.next_index(), 3);
    assert!(matches!(func.inst(1).op, Op::ExtractValue(_, _)));
    assert_eq!(func.inst(1).ty, i64_type);

    let output = format!("{}", func.display(&st));
    assert!(output.contains("extractvalue"));
}

#[test]
fn test_insertvalue_basic() {
    let mut st = SymbolTable::new();
    let name = st.intern("insert_test");
    let i64_type = Type::Int;
    let struct_ty = Type::Struct(vec![i64_type.clone(), Type::Bool]);
    let mut func = Function::new(
        name,
        vec![struct_ty.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(struct_ty.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let s = b.param(0, struct_ty.clone(), None, Origin::synthetic());
    let val = b.param(1, i64_type, None, Origin::synthetic());
    let result = b.insert_value(s.into(), val.into(), vec![0], None, Origin::synthetic());
    b.ret(Some(result.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
    assert!(matches!(func.inst(2).op, Op::InsertValue(_, _, _)));
    assert_eq!(func.inst(2).ty, struct_ty);

    let output = format!("{}", func.display(&st));
    assert!(output.contains("insertvalue"));
}

#[test]
fn test_extractvalue_array() {
    let mut st = SymbolTable::new();
    let name = st.intern("extract_array_test");
    let i64_type = Type::Int;
    let array_ty = Type::Array(Box::new(i64_type.clone()), 5);
    let mut func = Function::new(
        name,
        vec![array_ty.clone()],
        vec![],
        vec![],
        Some(i64_type.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let arr = b.param(0, array_ty, None, Origin::synthetic());
    let elem = b.extract_value(
        arr.into(),
        vec![2],
        i64_type.clone(),
        None,
        Origin::synthetic(),
    );
    b.ret(Some(elem.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert_eq!(func.inst_pool.next_index(), 3);
    assert!(matches!(func.inst(1).op, Op::ExtractValue(_, _)));
    assert_eq!(func.inst(1).ty, i64_type);
}

#[test]
fn test_insertvalue_array() {
    let mut st = SymbolTable::new();
    let name = st.intern("insert_array_test");
    let i64_type = Type::Int;
    let array_ty = Type::Array(Box::new(i64_type.clone()), 5);
    let mut func = Function::new(
        name,
        vec![array_ty.clone(), i64_type.clone()],
        vec![],
        vec![],
        Some(array_ty.clone()),
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let arr = b.param(0, array_ty.clone(), None, Origin::synthetic());
    let val = b.param(1, i64_type, None, Origin::synthetic());
    let result = b.insert_value(arr.into(), val.into(), vec![3], None, Origin::synthetic());
    b.ret(Some(result.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    assert_eq!(func.inst_pool.next_index(), 4);
    assert!(matches!(func.inst(2).op, Op::InsertValue(_, _, _)));
    assert_eq!(func.inst(2).ty, array_ty);
}

#[test]
fn test_dontcare_annotation_display() {
    let mut st = SymbolTable::new();
    let name = st.intern("test_dc");
    let i32_dc = Type::Int;
    let dc_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 32,
        signedness: IntSignedness::DontCare,
    }));
    let mut func = Function::new(
        name,
        vec![i32_dc.clone()],
        vec![dc_ann],
        vec![],
        Some(i32_dc.clone()),
        dc_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i32_dc, dc_ann, Origin::synthetic());
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let output = format!("{}", func.display(&st));
    assert!(
        output.contains("int:i32"),
        "should display int:i32 for DontCare signedness"
    );
}

#[test]
fn verify_detects_dontcare_zero() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_dc");
    let i0_type = Type::Int;
    let zero_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 0,
        signedness: IntSignedness::DontCare,
    }));
    let mut func = Function::new(
        name,
        vec![i0_type.clone()],
        vec![zero_ann],
        vec![],
        Some(i0_type.clone()),
        zero_ann,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let a = b.param(0, i0_type, zero_ann, Origin::synthetic());
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("bit_width") || e.message.contains("zero")),
        "should reject zero bit width"
    );
}

#[test]
fn mem_copy_builder_and_display() {
    let mut st = SymbolTable::new();
    let name = st.intern("test_memcpy");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Ptr(0), i64_type.clone()],
        vec![],
        vec![],
        None,
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let dst = b.param(0, Type::Ptr(0), None, Origin::synthetic());
    let src = b.param(1, Type::Ptr(0), None, Origin::synthetic());
    let count = b.param(2, i64_type, None, Origin::synthetic());
    let mem1 = b.mem_copy(
        dst.into(),
        src.into(),
        count.into(),
        mem0.into(),
        Origin::synthetic(),
    );
    b.ret(None, mem1.into(), Origin::synthetic());
    b.exit_region();

    assert!(matches!(func.inst(3).op, Op::MemCopy(_, _, _, _)));
    assert_eq!(func.inst(3).ty, Type::Mem);

    let output = format!("{}", func.display(&st));
    assert!(
        output.contains("memcpy"),
        "should display 'memcpy': {output}"
    );
}

#[test]
fn mem_move_builder_and_display() {
    let mut st = SymbolTable::new();
    let name = st.intern("test_memmove");
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Ptr(0), i64_type.clone()],
        vec![],
        vec![],
        None,
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let dst = b.param(0, Type::Ptr(0), None, Origin::synthetic());
    let src = b.param(1, Type::Ptr(0), None, Origin::synthetic());
    let count = b.param(2, i64_type, None, Origin::synthetic());
    let mem1 = b.mem_move(
        dst.into(),
        src.into(),
        count.into(),
        mem0.into(),
        Origin::synthetic(),
    );
    b.ret(None, mem1.into(), Origin::synthetic());
    b.exit_region();

    assert!(matches!(func.inst(3).op, Op::MemMove(_, _, _, _)));
    assert_eq!(func.inst(3).ty, Type::Mem);

    let output = format!("{}", func.display(&st));
    assert!(
        output.contains("memmove"),
        "should display 'memmove': {output}"
    );
}

#[test]
fn mem_set_builder_and_display() {
    let mut st = SymbolTable::new();
    let name = st.intern("test_memset");
    let i8_type = Type::Int;
    let i64_type = Type::Int;
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), i8_type.clone(), i64_type.clone()],
        vec![],
        vec![],
        None,
        None,
    );
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem, None);
    let dst = b.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = b.param(1, i8_type, None, Origin::synthetic());
    let count = b.param(2, i64_type, None, Origin::synthetic());
    let mem1 = b.mem_set(
        dst.into(),
        val.into(),
        count.into(),
        mem0.into(),
        Origin::synthetic(),
    );
    b.ret(None, mem1.into(), Origin::synthetic());
    b.exit_region();

    assert!(matches!(func.inst(3).op, Op::MemSet(_, _, _, _)));
    assert_eq!(func.inst(3).ty, Type::Mem);

    let output = format!("{}", func.display(&st));
    assert!(
        output.contains("memset"),
        "should display 'memset': {output}"
    );
}

#[test]
fn test_boolean_ops() {
    let mut module = Module::new("test");
    let name = module.intern("test_bool_ops");
    let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let t = builder.bconst(true, Origin::synthetic());
    let f = builder.bconst(false, Origin::synthetic());

    let and_result = builder.band(t.into(), f.into(), Origin::synthetic());
    let _or_result = builder.bor(t.into(), f.into(), Origin::synthetic());
    let _xor_result = builder.bxor(t.into(), f.into(), Origin::synthetic());

    builder.ret(Some(and_result.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    module.add_function(func);
    let result = crate::verifier::verify_module(&module);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn test_typed_builder_api() {
    use crate::typed::{BoolOperand, IntOperand};

    let mut module = Module::new("test");
    let name = module.intern("test_typed");
    let ret_ann = Annotation::Int(I64);
    let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Int), Some(ret_ann));
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);

    // Test typed constants
    let a = builder.iconst(10, 64, IntSignedness::Signed, Origin::synthetic());
    let b = builder.iconst(20, 64, IntSignedness::Signed, Origin::synthetic());

    // Test typed arithmetic
    let sum = builder.add(
        IntOperand::from_value(a),
        IntOperand::from_value(b),
        I64,
        Origin::synthetic(),
    );

    // Test typed comparison
    let cmp = builder.icmp(
        ICmpOp::Eq,
        IntOperand::from_value(a),
        IntOperand::from_value(b),
        Origin::synthetic(),
    );

    // Test typed boolean operations
    let t = builder.bconst(true, Origin::synthetic());
    let _and = builder.band(
        BoolOperand::from_value(cmp),
        BoolOperand::from_value(t),
        Origin::synthetic(),
    );

    builder.ret(Some(sum.raw().into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    module.add_function(func);
    let result = crate::verifier::verify_module(&module);
    assert!(result.is_ok(), "expected no errors: {result}");
}
