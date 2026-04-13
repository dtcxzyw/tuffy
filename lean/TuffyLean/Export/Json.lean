-- TuffyLean/Export/Json.lean
-- Export target-agnostic JSON artifacts for downstream Rust consumers.
-- Target-specific isel encoding lives under TuffyLean/Target/*.

import TuffyLean.Rewrites.Basic
import TuffyLean.Rewrites.AtUse
import TuffyLean.Rewrites.Facts
import TuffyLean.Rewrites.PassManifest
import TuffyLean.Target.X86.Export

namespace TuffyLean.Export

open TuffyLean.IR
open TuffyLean.Rewrites
open TuffyLean.Rewrites.Facts

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
  | .div => quote "div"
  | .rem => quote "rem"
  | .xor => quote "xor"
  | .icmp => quote "icmp"

private def terminatorOpcodeToJson : TerminatorOpcode → String
  | .brif => quote "brif"

private def canonicalBrIfKindToJson : CanonicalBrIfKind → String
  | .boolXorConst => quote "bool_xor_const"
  | .intifiedBoolCompare => quote "intified_bool_compare"

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
  | .isPositivePowerOfTwo => quote "is_positive_power_of_two"

private def knownBitsToJson (known : KnownBits) : String :=
  jsonObj [
    ("kind", quote "known_bits"),
    ("ones", quote (toString known.ones)),
    ("zeros", quote (toString known.zeros)),
    ("demanded", quote (toString known.demanded))
  ]

private def annotationToJson : Annotation → String
  | .signed bits =>
    jsonObj [
      ("kind", quote "signed"),
      ("bits", toString bits)
    ]
  | .unsigned bits =>
    jsonObj [
      ("kind", quote "unsigned"),
      ("bits", toString bits)
    ]
  | .dontCare bits =>
    jsonObj [
      ("kind", quote "dont_care"),
      ("bits", toString bits)
    ]
  | .known known => knownBitsToJson known
  | .align bytes =>
    jsonObj [
      ("kind", quote "align"),
      ("bytes", toString bytes)
    ]

private def sideConditionToJson : SideCondition → String
  | .intPredicate binding predicate =>
    jsonObj [
      ("kind", quote "int_predicate"),
      ("binding", quote binding),
      ("predicate", intPredicateToJson predicate)
    ]
  | .bestIntAnnotation binding annotation =>
    jsonObj [
      ("kind", quote "best_int_annotation"),
      ("binding", quote binding),
      ("annotation", annotationToJson annotation)
    ]
  | .knownOne binding bit =>
    jsonObj [
      ("kind", quote "known_one"),
      ("binding", quote binding),
      ("bit", toString bit)
    ]
  | .valueNonNegative binding =>
    jsonObj [
      ("kind", quote "value_non_negative"),
      ("binding", quote binding)
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
  | .intConst value =>
    jsonObj [
      ("kind", quote "int_const"),
      ("value", quote (toString value))
    ]
  | .boolConst value =>
    jsonObj [
      ("kind", quote "bool_const"),
      ("value", toString value)
    ]
  | .pow2ShiftAmount name =>
    jsonObj [
      ("kind", quote "pow2_shift_amount"),
      ("name", quote name)
    ]
  | .inst opcode args =>
    let op :=
      match opcode with
      | .shr => quote "shr"
    jsonObj [
      ("kind", quote "inst"),
      ("op", op),
      ("args", jsonArr (args.map replacementToJson))
    ]
  | .boolNot value =>
    jsonObj [
      ("kind", quote "bool_not"),
      ("value", replacementToJson value)
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
  | MatchRoot.canonicalBrIf binding kind =>
    jsonObj [
      ("kind", quote "canonical_brif"),
      ("binding", quote binding),
      ("mode", canonicalBrIfKindToJson kind)
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

private def factResultToJson : FactResult → String
  | .primary => quote "primary"
  | .secondary => quote "secondary"

private def knownBitsForwardKindToJson : KnownBitsForwardKind → String
  | .unknown => quote "unknown"
  | .const => quote "const"
  | .select => quote "select"
  | .bitAnd => quote "bit_and"
  | .bitOr => quote "bit_or"
  | .bitXor => quote "bit_xor"
  | .shl => quote "shl"
  | .shr => quote "shr"
  | .merge => quote "merge"
  | .splitHi => quote "split_hi"
  | .splitLo => quote "split_lo"

private def intAnnotationForwardKindToJson : IntAnnotationForwardKind → String
  | .unknown => quote "unknown"
  | .const => quote "const"
  | .select => quote "select"
  | .bitAnd => quote "bit_and"
  | .bitOr => quote "bit_or"
  | .bitXor => quote "bit_xor"
  | .splitLo => quote "split_lo"

private def knownBitsBackwardKindToJson : KnownBitsBackwardKind → String
  | .none => quote "none"
  | .select => quote "select"
  | .bitAnd => quote "bit_and"
  | .bitOr => quote "bit_or"
  | .bitXor => quote "bit_xor"
  | .shl => quote "shl"
  | .shr => quote "shr"
  | .merge => quote "merge"
  | .split => quote "split"

private def intAnnotationBackwardKindToJson : IntAnnotationBackwardKind → String
  | .none => quote "none"
  | .select => quote "select"
  | .split => quote "split"

private def summaryForwardKindToJson : TuffyLean.Rewrites.AtUse.SummaryForwardKind → String
  | .unknown => quote "unknown"
  | .const => quote "const"
  | .select => quote "select"
  | .bitAnd => quote "bit_and"
  | .bitOr => quote "bit_or"
  | .bitXor => quote "bit_xor"

private def atUseForwardRuleToJson (rule : TuffyLean.Rewrites.AtUse.ForwardRule) : String :=
  jsonObj [
    ("op", quote rule.op),
    ("known_bits_forward", knownBitsForwardKindToJson rule.knownBitsForward),
    ("summary_forward", summaryForwardKindToJson rule.summaryForward),
    ("proof_ref", quote rule.proofRef)
  ]

private def atUseTransformKindToJson : TuffyLean.Rewrites.AtUse.TransformKind → String
  | .foldICmp => quote "fold_icmp"
  | .foldBrIf => quote "fold_br_if"
  | .strengthenOperand => quote "strengthen_operand"
  | .strengthenResult => quote "strengthen_result"

private def atUseTransformToJson (transform : TuffyLean.Rewrites.AtUse.Transform) : String :=
  jsonObj [
    ("name", quote transform.name),
    ("kind", atUseTransformKindToJson transform.kind),
    ("proof_ref", quote transform.proofRef)
  ]

private def exportPeepholeSpec : String :=
  jsonObj [
    ("format_version", "4"),
    ("kind", quote "peephole"),
    ("rules", jsonArr (allPeepholeRules.map peepholeRuleToJson)),
    ("at_use_forward_rules",
      jsonArr (TuffyLean.Rewrites.AtUse.forwardRules.map atUseForwardRuleToJson)),
    ("at_use_transforms",
      jsonArr (TuffyLean.Rewrites.AtUse.allTransforms.map atUseTransformToJson))
  ]

private def resultFactRuleToJson (rule : ResultFactRule) : String :=
  jsonObj [
    ("op", quote rule.op),
    ("result", factResultToJson rule.result),
    ("known_bits_forward", knownBitsForwardKindToJson rule.knownBitsForward),
    ("int_annotation_forward", intAnnotationForwardKindToJson rule.intAnnotationForward),
    ("proof_ref", quote rule.proofRef)
  ]

private def instFactRuleToJson (rule : InstFactRule) : String :=
  jsonObj [
    ("op", quote rule.op),
    ("known_bits_backward", knownBitsBackwardKindToJson rule.knownBitsBackward),
    ("int_annotation_backward", intAnnotationBackwardKindToJson rule.intAnnotationBackward),
    ("proof_ref", quote rule.proofRef)
  ]

private def factDefaultsToJson (defaults : FactDefaults) : String :=
  jsonObj [
    ("known_bits_forward", knownBitsForwardKindToJson defaults.knownBitsForward),
    ("int_annotation_forward", intAnnotationForwardKindToJson defaults.intAnnotationForward),
    ("known_bits_backward", knownBitsBackwardKindToJson defaults.knownBitsBackward),
    ("int_annotation_backward", intAnnotationBackwardKindToJson defaults.intAnnotationBackward)
  ]

private def exportPeepholeFactSpec : String :=
  jsonObj [
    ("format_version", "1"),
    ("kind", quote "peephole_facts"),
    ("defaults", factDefaultsToJson factDefaults),
    ("result_rules", jsonArr (resultFactRules.map resultFactRuleToJson)),
    ("inst_rules", jsonArr (instFactRules.map instFactRuleToJson))
  ]

private def cleanupPassVerificationToJson : CleanupPassVerification → String
  | .verified => quote "verified"
  | .legacy => quote "legacy"

private def cleanupPassFamilyToJson (family : CleanupPassFamily) : String :=
  let leanSourceField :=
    match family.leanSource with
    | some source => [("lean_source", quote source)]
    | none => []
  jsonObj <|
    [
      ("name", quote family.name),
      ("runner", quote family.runner),
      ("verification", cleanupPassVerificationToJson family.verification)
    ] ++ leanSourceField

private def exportCleanupPassManifest : String :=
  let localFamilies :=
    allCleanupPassFamilies.filter (fun family => decide (family.stage = .local))
  let moduleFamilies :=
    allCleanupPassFamilies.filter (fun family => decide (family.stage = .module))
  jsonObj [
    ("format_version", "1"),
    ("kind", quote "opt_pass_manifest"),
    ("local_families", jsonArr (localFamilies.map cleanupPassFamilyToJson)),
    ("module_families", jsonArr (moduleFamilies.map cleanupPassFamilyToJson))
  ]

private inductive ExportRequest where
  | target (name : String)
  | peephole
  | peepholeFacts
  | optPassManifest

private def usage : String :=
  String.intercalate "\n"
    [
      "Usage:",
      "  lean --run TuffyLean/Export/Json.lean",
      "  lean --run TuffyLean/Export/Json.lean <target>",
      "  lean --run TuffyLean/Export/Json.lean --target <target>",
      "  lean --run TuffyLean/Export/Json.lean peephole",
      "  lean --run TuffyLean/Export/Json.lean --kind peephole",
      "  lean --run TuffyLean/Export/Json.lean peephole_facts",
      "  lean --run TuffyLean/Export/Json.lean --kind peephole_facts",
      "  lean --run TuffyLean/Export/Json.lean opt_pass_manifest",
      "  lean --run TuffyLean/Export/Json.lean --kind opt_pass_manifest"
    ]

private def parseRequest (args : List String) : Except String ExportRequest :=
  match args with
  | [] => .ok (.target "x86")
  | ["peephole"] => .ok .peephole
  | ["--kind", "peephole"] => .ok .peephole
  | ["peephole_facts"] => .ok .peepholeFacts
  | ["--kind", "peephole_facts"] => .ok .peepholeFacts
  | ["opt_pass_manifest"] => .ok .optPassManifest
  | ["--kind", "opt_pass_manifest"] => .ok .optPassManifest
  | [target] => .ok (.target target)
  | ["--target", target] => .ok (.target target)
  | _ => .error usage

private def exportForRequest? : ExportRequest → Option String
  | .peephole => some exportPeepholeSpec
  | .peepholeFacts => some exportPeepholeFactSpec
  | .optPassManifest => some exportCleanupPassManifest
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
    | .peepholeFacts => throw <| IO.userError "unknown peephole fact export request"
    | .optPassManifest => throw <| IO.userError "unknown optimizer pass manifest request"
    | .target target => throw <| IO.userError s!"unknown target: {target}"

end TuffyLean.Export

/-- Entry point for `lean --run`. -/
def main (args : List String) : IO Unit := TuffyLean.Export.main args
