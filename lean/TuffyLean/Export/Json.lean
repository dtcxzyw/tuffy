-- TuffyLean/Export/Json.lean
-- Export target-agnostic JSON artifacts for downstream Rust consumers.
-- Target-specific isel encoding lives under TuffyLean/Target/*.

import TuffyLean.Rewrites.Basic
import TuffyLean.Target.X86.Export

namespace TuffyLean.Export

open TuffyLean.IR
open TuffyLean.Rewrites

private def quote (s : String) : String := s!"\"{s}\""

private def jsonObj (fields : List (String × String)) : String :=
  let inner := fields.map (fun (k, v) => s!"{quote k}: {v}") |> String.intercalate ", "
  s!"\{{inner}}"

private def jsonArr (items : List String) : String :=
  s!"[{items |> String.intercalate ", "}]"

private def valueTypeToJson : ValueType → String
  | .int => quote "int"
  | .bool => quote "bool"

private def patternOpcodeToJson : PatternOpcode → String
  | .select => quote "select"
  | .and => quote "and"
  | .xor => quote "xor"
  | .icmp => quote "icmp"

private def terminatorOpcodeToJson : TerminatorOpcode → String
  | .brif => quote "brif"

private def constFoldOpcodeToJsonParts : ConstFoldOpcode → String × List String
  | ConstFoldOpcode.add => (quote "add", [])
  | ConstFoldOpcode.sub => (quote "sub", [])
  | ConstFoldOpcode.mul => (quote "mul", [])
  | ConstFoldOpcode.div => (quote "div", [])
  | ConstFoldOpcode.rem => (quote "rem", [])
  | ConstFoldOpcode.and => (quote "and", [])
  | ConstFoldOpcode.or => (quote "or", [])
  | ConstFoldOpcode.xor => (quote "xor", [])
  | ConstFoldOpcode.band => (quote "band", [])
  | ConstFoldOpcode.bor => (quote "bor", [])
  | ConstFoldOpcode.bxor => (quote "bxor", [])
  | ConstFoldOpcode.shl => (quote "shl", [])
  | ConstFoldOpcode.shr => (quote "shr", [])
  | ConstFoldOpcode.min => (quote "min", [])
  | ConstFoldOpcode.max => (quote "max", [])
  | ConstFoldOpcode.countOnes => (quote "count_ones", [])
  | ConstFoldOpcode.countLeadingZeros => (quote "count_leading_zeros", [])
  | ConstFoldOpcode.countTrailingZeros => (quote "count_trailing_zeros", [])
  | ConstFoldOpcode.bswap => (quote "bswap", [])
  | ConstFoldOpcode.bitReverse => (quote "bit_reverse", [])
  | ConstFoldOpcode.rotateLeft => (quote "rotate_left", [])
  | ConstFoldOpcode.rotateRight => (quote "rotate_right", [])
  | ConstFoldOpcode.select => (quote "select", [])
  | ConstFoldOpcode.icmp pred =>
    let predJson :=
      match pred with
      | .eq => quote "eq"
      | .ne => quote "ne"
      | .lt => quote "lt"
      | .le => quote "le"
      | .gt => quote "gt"
      | .ge => quote "ge"
    (quote "icmp",
      [jsonObj [
        ("kind", quote "icmp_pred"),
        ("value", predJson)
      ]])

private def icmpPredToJson : ICmpOp → String
  | .eq => quote "eq"
  | .ne => quote "ne"
  | .lt => quote "lt"
  | .le => quote "le"
  | .gt => quote "gt"
  | .ge => quote "ge"

private def patternAttrToJson : PatternAttr → String
  | .icmpPred pred =>
    jsonObj [
      ("kind", quote "icmp_pred"),
      ("value", icmpPredToJson pred)
    ]

private def transformKindToJson : TransformKind → String
  | .equivalence => quote "equivalence"

private def intPredicateToJson : IntPredicate → String
  | .isZero => quote "is_zero"
  | .isOne => quote "is_one"
  | .isOdd => quote "is_odd"

private def sideConditionToJson : SideCondition → String
  | .intPredicate binding predicate =>
    jsonObj [
      ("kind", quote "int_predicate"),
      ("binding", quote binding),
      ("predicate", intPredicateToJson predicate)
    ]
  | .allOf conditions =>
    jsonObj [
      ("kind", quote "all_of"),
      ("conditions", jsonArr (conditions.map sideConditionToJson))
    ]
  | .anyOf conditions =>
    jsonObj [
      ("kind", quote "any_of"),
      ("conditions", jsonArr (conditions.map sideConditionToJson))
    ]
  | .not condition =>
    jsonObj [
      ("kind", quote "not"),
      ("condition", sideConditionToJson condition)
    ]

private def patternToJson : Pattern → String
  | .capture name ty =>
    let fields :=
      [
        ("kind", quote "capture"),
        ("name", quote name)
      ] ++
      match ty with
      | some ty => [("ty", valueTypeToJson ty)]
      | none => []
    jsonObj fields
  | .bind name pattern =>
    jsonObj [
      ("kind", quote "bind"),
      ("name", quote name),
      ("pattern", patternToJson pattern)
    ]
  | .intConst value =>
    jsonObj [
      ("kind", quote "int_const"),
      ("value", quote (toString value))
    ]
  | .intConstBinding name =>
    jsonObj [
      ("kind", quote "int_const_binding"),
      ("name", quote name)
    ]
  | .inst opcode attrs args =>
    jsonObj [
      ("kind", quote "inst"),
      ("op", patternOpcodeToJson opcode),
      ("attrs", jsonArr (attrs.map patternAttrToJson)),
      ("args", jsonArr (args.map patternToJson))
    ]

private def replacementToJson : Replacement → String
  | .binding name =>
    jsonObj [
      ("kind", quote "binding"),
      ("name", quote name)
    ]

private def matchRootToJson : MatchRoot → String
  | MatchRoot.value root =>
    jsonObj [
      ("kind", quote "value"),
      ("root", patternToJson root)
    ]
  | MatchRoot.terminator opcode operands successorCount =>
    jsonObj [
      ("kind", quote "terminator"),
      ("op", terminatorOpcodeToJson opcode),
      ("operands", jsonArr (operands.map patternToJson)),
      ("successor_count", toString successorCount)
    ]
  | MatchRoot.constFold opcode =>
    let (op, attrs) := constFoldOpcodeToJsonParts opcode
    jsonObj [
      ("kind", quote "const_fold"),
      ("op", op),
      ("attrs", jsonArr attrs)
    ]

private def rootReplacementToJson : RootReplacement → String
  | RootReplacement.value replacement =>
    jsonObj [
      ("kind", quote "value"),
      ("value", replacementToJson replacement)
    ]
  | RootReplacement.terminator opcode operands successors =>
    jsonObj [
      ("kind", quote "terminator"),
      ("op", terminatorOpcodeToJson opcode),
      ("operands", jsonArr (operands.map replacementToJson)),
      ("successors", jsonArr (successors.map toString))
    ]
  | RootReplacement.constFold =>
    jsonObj [
      ("kind", quote "const_fold")
    ]

private def rewriteBodyToJson (body : RewriteBody) : String :=
  jsonObj [
    ("match_root", matchRootToJson body.matchRoot),
    ("replacement", rootReplacementToJson body.replacement)
  ]

private def peepholeRuleToJson (rule : PeepholeRule) : String :=
  jsonObj [
    ("name", quote rule.name),
    ("transform_kind", transformKindToJson rule.transformKind),
    ("proof_ref", quote rule.proofRef),
    ("side_conditions", jsonArr (rule.sideConditions.map sideConditionToJson)),
    ("rewrite", rewriteBodyToJson rule.body)
  ]

private def exportPeepholeSpec : String :=
  jsonObj [
    ("format_version", "3"),
    ("kind", quote "peephole"),
    ("rules", jsonArr (allPeepholeRules.map peepholeRuleToJson))
  ]

private inductive ExportRequest where
  | target (name : String)
  | peephole

private def usage : String :=
  String.intercalate "\n"
    [
      "Usage:",
      "  lean --run TuffyLean/Export/Json.lean",
      "  lean --run TuffyLean/Export/Json.lean <target>",
      "  lean --run TuffyLean/Export/Json.lean --target <target>",
      "  lean --run TuffyLean/Export/Json.lean peephole",
      "  lean --run TuffyLean/Export/Json.lean --kind peephole"
    ]

private def parseRequest (args : List String) : Except String ExportRequest :=
  match args with
  | [] => .ok (.target "x86")
  | ["peephole"] => .ok .peephole
  | ["--kind", "peephole"] => .ok .peephole
  | [target] => .ok (.target target)
  | ["--target", target] => .ok (.target target)
  | _ => .error usage

private def exportForRequest? : ExportRequest → Option String
  | .peephole => some exportPeepholeSpec
  | .target "x86" => some TuffyLean.Target.X86.Export.exportIselSpec
  | .target _ => none

/-- Main entry point: print JSON to stdout. -/
def main (args : List String) : IO Unit := do
  let request ←
    match parseRequest args with
    | .ok request => pure request
    | .error msg => throw <| IO.userError msg
  match exportForRequest? request with
  | some json => IO.println json
  | none =>
    match request with
    | .peephole => throw <| IO.userError "unknown peephole export request"
    | .target target => throw <| IO.userError s!"unknown target: {target}"

end TuffyLean.Export

/-- Entry point for `lean --run`. -/
def main (args : List String) : IO Unit := TuffyLean.Export.main args
