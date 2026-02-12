-- TuffyLean/Target/X86/IselRule.lean
-- Instruction selection rule structure.

import TuffyLean.Target.X86.Defs

namespace TuffyLean.Target.X86

/-- Operand pattern: binds a register name with an optional annotation guard. -/
structure OperandPat where
  regName : String
  annGuard : AnnGuard := .any
  deriving Repr, BEq, Hashable

/-- IR pattern to match against. -/
inductive IrPattern where
  /-- Binary operation: op(lhs, rhs). -/
  | binop (op : String) (lhs rhs : OperandPat)
  /-- Unary operation: op(val). -/
  | unop (op : String) (val : OperandPat)
  /-- Integer comparison: icmp(lhs, rhs). CC derived from ICmpOp at dispatch. -/
  | icmp (lhs rhs : OperandPat)
  deriving Repr, BEq, Hashable

/-- What the rule produces. -/
inductive ResultKind where
  /-- Result is a virtual register (stored in VRegMap). -/
  | reg (name : String)
  /-- Result is condition flags (stored in CmpMap). -/
  | cmpFlags
  /-- No result (side-effect only). -/
  | none
  deriving Repr, BEq, Hashable

/-- A single instruction selection rule. -/
structure IselRule where
  /-- Unique rule name (used for generated function name). -/
  name : String
  /-- IR pattern to match. -/
  pattern : IrPattern
  /-- Sequence of x86 instructions to emit. -/
  emit : List EmitInst
  /-- What the rule produces. -/
  result : ResultKind
  /-- If true, the condition code is derived from the ICmpOp (for ICmp rules). -/
  icmpCcFromOp : Bool := false
  deriving Repr, BEq, Hashable

end TuffyLean.Target.X86
