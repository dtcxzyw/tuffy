-- TuffyLean/Export/Json.lean
-- Export target-agnostic JSON artifacts for downstream Rust consumers.
-- Target-specific isel encoding lives under TuffyLean/Target/*.

import TuffyLean.Rewrites.Basic
import TuffyLean.Target.X86.Export

namespace TuffyLean.Export

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

private def patternOpToJson : PatternOp → String
  | .select => quote "select"
  | .and => quote "and"
  | .xor => quote "xor"
  | .icmpEq => quote "icmp_eq"

private def transformKindToJson : TransformKind → String
  | .equivalence => quote "equivalence"

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
  | .inst op args =>
    jsonObj [
      ("kind", quote "inst"),
      ("op", patternOpToJson op),
      ("args", jsonArr (args.map patternToJson))
    ]

private def replacementToJson : Replacement → String
  | .binding name =>
    jsonObj [
      ("kind", quote "binding"),
      ("name", quote name)
    ]

private def rewriteBodyToJson : RewriteBody → String
  | .value root replacement =>
    jsonObj [
      ("kind", quote "value"),
      ("root", patternToJson root),
      ("replacement", replacementToJson replacement)
    ]
  | .brif condition replacement invert =>
    jsonObj [
      ("kind", quote "brif"),
      ("condition", patternToJson condition),
      ("replacement", replacementToJson replacement),
      ("invert", if invert then "true" else "false")
    ]

private def peepholeRuleToJson (rule : PeepholeRule) : String :=
  jsonObj [
    ("name", quote rule.name),
    ("transform_kind", transformKindToJson rule.transformKind),
    ("proof_ref", quote rule.proofRef),
    ("side_conditions", jsonArr (rule.sideConditions.map quote)),
    ("rewrite", rewriteBodyToJson rule.body)
  ]

private def exportPeepholeSpec : String :=
  jsonObj [
    ("format_version", "1"),
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
