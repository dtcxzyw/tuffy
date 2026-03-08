-- TuffyLean/Target/X86/Export.lean
-- x86-specific JSON export for instruction selection rules.

import TuffyLean.Target.X86.Rules

namespace TuffyLean.Target.X86.Export

open TuffyLean.Target.X86

private def quote (s : String) : String := s!"\"{s}\""

private def jsonObj (fields : List (String × String)) : String :=
  let inner := fields.map (fun (k, v) => s!"{quote k}: {v}") |> String.intercalate ", "
  s!"\{{inner}}"

private def jsonArr (items : List String) : String :=
  s!"[{items |> String.intercalate ", "}]"

private def opSizeToJson : OpSize → String
  | .s8  => quote "s8"
  | .s16 => quote "s16"
  | .s32 => quote "s32"
  | .s64 => quote "s64"
  | .fromAnnotation regName =>
    jsonObj [("kind", quote "from_annotation"), ("reg", quote regName)]

private def condCodeToJson : CondCode → String
  | .e  => quote "e"
  | .ne => quote "ne"
  | .l  => quote "l"
  | .le => quote "le"
  | .g  => quote "g"
  | .ge => quote "ge"
  | .b  => quote "b"
  | .be => quote "be"
  | .a  => quote "a"
  | .ae => quote "ae"

private def fixedRegToJson : FixedReg → String
  | .rax => quote "rax"
  | .rcx => quote "rcx"
  | .rdx => quote "rdx"
  | .rbp => quote "rbp"

private def regRefToJson : RegRef → String
  | .named name => jsonObj [("kind", quote "named"), ("name", quote name)]
  | .fresh name => jsonObj [("kind", quote "fresh"), ("name", quote name)]
  | .freshFixed name reg =>
    jsonObj [
      ("kind", quote "fresh_fixed"),
      ("name", quote name),
      ("reg", fixedRegToJson reg)
    ]

private def annGuardToJson : AnnGuard → String
  | .any      => quote "any"
  | .signed   => quote "signed"
  | .unsigned => quote "unsigned"

private def operandPatToJson (p : OperandPat) : String :=
  jsonObj [("reg", quote p.regName), ("ann", annGuardToJson p.annGuard)]

private def emitFieldRegToJson (name : String) (ref : RegRef) : String :=
  jsonObj [
    ("name", quote name),
    ("kind", quote "reg"),
    ("ref", regRefToJson ref)
  ]

private def emitFieldValueToJson (name kind value : String) : String :=
  jsonObj [
    ("name", quote name),
    ("kind", quote kind),
    ("value", value)
  ]

private def emitInstToJson : EmitInst → String
  | .movRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::MovRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .addRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::AddRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .subRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::SubRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .imulRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::ImulRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .orRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::OrRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .andRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::AndRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .xorRR size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::XorRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .shlRCL size dst =>
    jsonObj [
      ("rust_ctor", quote "MInst::ShlRCL"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst
      ])
    ]
  | .shrRCL size dst =>
    jsonObj [
      ("rust_ctor", quote "MInst::ShrRCL"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst
      ])
    ]
  | .sarRCL size dst =>
    jsonObj [
      ("rust_ctor", quote "MInst::SarRCL"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst
      ])
    ]
  | .cmpRR size src1 src2 =>
    jsonObj [
      ("rust_ctor", quote "MInst::CmpRR"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "src1" src1,
        emitFieldRegToJson "src2" src2
      ])
    ]
  | .cmovCC size cc dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::CMOVcc"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldValueToJson "cc" "cc" (condCodeToJson cc),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .popcnt size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::Popcnt"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .lzcnt size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::Lzcnt"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]
  | .tzcnt size dst src =>
    jsonObj [
      ("rust_ctor", quote "MInst::Tzcnt"),
      ("fields", jsonArr [
        emitFieldValueToJson "size" "size" (opSizeToJson size),
        emitFieldRegToJson "dst" dst,
        emitFieldRegToJson "src" src
      ])
    ]

private def irPatternToJson : IrPattern → String
  | .binop op lhs rhs =>
    jsonObj [
      ("kind", quote "binop"),
      ("op", quote op),
      ("lhs", operandPatToJson lhs),
      ("rhs", operandPatToJson rhs)
    ]
  | .unop op val =>
    jsonObj [
      ("kind", quote "unop"),
      ("op", quote op),
      ("val", operandPatToJson val)
    ]
  | .icmp lhs rhs =>
    jsonObj [
      ("kind", quote "icmp"),
      ("lhs", operandPatToJson lhs),
      ("rhs", operandPatToJson rhs)
    ]

private def resultKindToJson : ResultKind → String
  | .reg name  => jsonObj [("kind", quote "reg"), ("name", quote name)]
  | .cmpFlags  => jsonObj [("kind", quote "cmp_flags")]
  | .none      => jsonObj [("kind", quote "none")]

private def iselRuleToJson (r : IselRule) : String :=
  jsonObj [
    ("name", quote r.name),
    ("pattern", irPatternToJson r.pattern),
    ("emit", jsonArr (r.emit.map emitInstToJson)),
    ("result", resultKindToJson r.result),
    ("icmp_cc_from_op", if r.icmpCcFromOp then "true" else "false")
  ]

private def metadataToJson : String :=
  jsonObj [
    ("imports", jsonArr [
      quote "use crate::inst::{CondCode, MInst, OpSize};",
      quote "use crate::reg::Gpr;"
    ]),
    ("maps", jsonObj [
      ("fixed_regs", jsonObj [
        ("rax", quote "Gpr::Rax.to_preg()"),
        ("rcx", quote "Gpr::Rcx.to_preg()"),
        ("rdx", quote "Gpr::Rdx.to_preg()"),
        ("rbp", quote "Gpr::Rbp.to_preg()")
      ]),
      ("size", jsonObj [
        ("s8", quote "OpSize::S8"),
        ("s16", quote "OpSize::S16"),
        ("s32", quote "OpSize::S32"),
        ("s64", quote "OpSize::S64")
      ]),
      ("cc", jsonObj [
        ("e", quote "CondCode::E"),
        ("ne", quote "CondCode::Ne"),
        ("l", quote "CondCode::L"),
        ("le", quote "CondCode::Le"),
        ("g", quote "CondCode::G"),
        ("ge", quote "CondCode::Ge"),
        ("b", quote "CondCode::B"),
        ("be", quote "CondCode::Be"),
        ("a", quote "CondCode::A"),
        ("ae", quote "CondCode::Ae")
      ])
    ])
  ]

def exportIselSpec : String :=
  jsonObj [
    ("format_version", "1"),
    ("target", quote "x86"),
    ("metadata", metadataToJson),
    ("rules", jsonArr (allRules.map iselRuleToJson))
  ]

end TuffyLean.Target.X86.Export
