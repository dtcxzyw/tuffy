//! JSON schema types matching the Lean export format.

use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct IselRule {
    pub name: String,
    pub pattern: IrPattern,
    pub emit: Vec<EmitInst>,
    pub result: ResultKind,
    #[serde(default)]
    pub icmp_cc_from_op: bool,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind")]
pub enum IrPattern {
    #[serde(rename = "binop")]
    Binop {
        op: String,
        lhs: OperandPat,
        rhs: OperandPat,
    },
    #[serde(rename = "unop")]
    Unop { op: String, val: OperandPat },
    #[serde(rename = "icmp")]
    Icmp { lhs: OperandPat, rhs: OperandPat },
}

#[derive(Debug, Deserialize)]
pub struct OperandPat {
    pub reg: String,
    pub ann: AnnGuard,
}

#[derive(Debug, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum AnnGuard {
    Any,
    Signed,
    Unsigned,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind")]
pub enum ResultKind {
    #[serde(rename = "reg")]
    Reg { name: String },
    #[serde(rename = "cmp_flags")]
    CmpFlags,
    #[serde(rename = "none")]
    None,
}

#[derive(Debug, Deserialize)]
pub struct RegRef {
    pub kind: RegRefKind,
    pub name: String,
    #[serde(default)]
    pub reg: Option<String>,
}

#[derive(Debug, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RegRefKind {
    Named,
    Fresh,
    FreshFixed,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "inst")]
pub enum EmitInst {
    MovRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    AddRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    SubRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    ImulRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    OrRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    AndRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    XorRR {
        size: String,
        dst: RegRef,
        src: RegRef,
    },
    ShlRCL {
        size: String,
        dst: RegRef,
    },
    ShrRCL {
        size: String,
        dst: RegRef,
    },
    SarRCL {
        size: String,
        dst: RegRef,
    },
    CmpRR {
        size: String,
        src1: RegRef,
        src2: RegRef,
    },
    CMOVcc {
        size: String,
        cc: String,
        dst: RegRef,
        src: RegRef,
    },
    Popcnt {
        dst: RegRef,
        src: RegRef,
    },
    Lzcnt {
        dst: RegRef,
        src: RegRef,
    },
    Tzcnt {
        dst: RegRef,
        src: RegRef,
    },
}
