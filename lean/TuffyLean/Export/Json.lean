-- TuffyLean/Export/Json.lean
-- Export x86 instruction selection rules as JSON for the Rust code generator.

import TuffyLean.Target.X86.Rules

namespace TuffyLean.Export

open TuffyLean.Target.X86

-- JSON serialization helpers

private def quote (s : String) : String := s!"\"{s}\""

private def jsonObj (fields : List (String × String)) : String :=
  let inner := fields.map (fun (k, v) => s!"{quote k}: {v}") |> String.intercalate ", "
  s!"\{{inner}}"

private def jsonArr (items : List String) : String :=
  s!"[{items |> String.intercalate ", "}]"

-- Serialize types to JSON

private def opSizeToJson : OpSize → String
  | .s8  => quote "s8"
  | .s16 => quote "s16"
  | .s32 => quote "s32"
  | .s64 => quote "s64"

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
    jsonObj [("kind", quote "fresh_fixed"), ("name", quote name),
             ("reg", fixedRegToJson reg)]

private def annGuardToJson : AnnGuard → String
  | .any      => quote "any"
  | .signed   => quote "signed"
  | .unsigned => quote "unsigned"

private def operandPatToJson (p : OperandPat) : String :=
  jsonObj [("reg", quote p.regName), ("ann", annGuardToJson p.annGuard)]

private def emitInstToJson : EmitInst → String
  | .movRR size dst src =>
    jsonObj [("inst", quote "MovRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .addRR size dst src =>
    jsonObj [("inst", quote "AddRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .subRR size dst src =>
    jsonObj [("inst", quote "SubRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .imulRR size dst src =>
    jsonObj [("inst", quote "ImulRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .orRR size dst src =>
    jsonObj [("inst", quote "OrRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .andRR size dst src =>
    jsonObj [("inst", quote "AndRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .xorRR size dst src =>
    jsonObj [("inst", quote "XorRR"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .shlRCL size dst =>
    jsonObj [("inst", quote "ShlRCL"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst)]
  | .shrRCL size dst =>
    jsonObj [("inst", quote "ShrRCL"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst)]
  | .sarRCL size dst =>
    jsonObj [("inst", quote "SarRCL"), ("size", opSizeToJson size),
             ("dst", regRefToJson dst)]
  | .cmpRR size src1 src2 =>
    jsonObj [("inst", quote "CmpRR"), ("size", opSizeToJson size),
             ("src1", regRefToJson src1), ("src2", regRefToJson src2)]
  | .cmovCC size cc dst src =>
    jsonObj [("inst", quote "CMOVcc"), ("size", opSizeToJson size),
             ("cc", condCodeToJson cc),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]
  | .popcnt dst src =>
    jsonObj [("inst", quote "Popcnt"),
             ("dst", regRefToJson dst), ("src", regRefToJson src)]

private def irPatternToJson : IrPattern → String
  | .binop op lhs rhs =>
    jsonObj [("kind", quote "binop"), ("op", quote op),
             ("lhs", operandPatToJson lhs), ("rhs", operandPatToJson rhs)]
  | .unop op val =>
    jsonObj [("kind", quote "unop"), ("op", quote op),
             ("val", operandPatToJson val)]
  | .icmp lhs rhs =>
    jsonObj [("kind", quote "icmp"),
             ("lhs", operandPatToJson lhs), ("rhs", operandPatToJson rhs)]

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

def exportIselRules : String :=
  jsonArr (allRules.map iselRuleToJson)

/-- Main entry point: print JSON to stdout. -/
def main : IO Unit := do
  IO.println exportIselRules

end TuffyLean.Export

/-- Entry point for `lean --run`. -/
def main : IO Unit := TuffyLean.Export.main
