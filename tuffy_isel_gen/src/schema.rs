//! JSON schema types matching the Lean export format.

use std::collections::HashMap;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct IselSpec {
    pub format_version: u32,
    pub target: String,
    pub metadata: IselMetadata,
    pub rules: Vec<IselRule>,
}

#[derive(Debug, Deserialize)]
pub struct IselMetadata {
    pub imports: Vec<String>,
    pub maps: IselMaps,
}

#[derive(Debug, Deserialize)]
pub struct IselMaps {
    pub fixed_regs: HashMap<String, String>,
    pub size: HashMap<String, String>,
    pub cc: HashMap<String, String>,
}

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
pub struct EmitInst {
    pub rust_ctor: String,
    pub fields: Vec<EmitField>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum OpSizeValue {
    Fixed(String),
    FromAnnotation { kind: String, reg: String },
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EmitField {
    Reg {
        name: String,
        #[serde(rename = "ref")]
        reg_ref: RegRef,
    },
    Size {
        name: String,
        value: OpSizeValue,
    },
    Cc {
        name: String,
        value: String,
    },
    Literal {
        name: String,
        value: String,
    },
}
