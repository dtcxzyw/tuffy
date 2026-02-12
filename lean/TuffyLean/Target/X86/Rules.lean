-- TuffyLean/Target/X86/Rules.lean
-- Concrete x86 instruction selection rule definitions.

import TuffyLean.Target.X86.IselRule

namespace TuffyLean.Target.X86

open EmitInst RegRef OpSize CondCode AnnGuard ResultKind IrPattern

-- Binary arithmetic: Add, Sub, Mul
-- Pattern: mov dst, lhs; <op> dst, rhs

def addRule : IselRule := {
  name := "add"
  pattern := .binop "Add" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           addRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

def subRule : IselRule := {
  name := "sub"
  pattern := .binop "Sub" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           subRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

def mulRule : IselRule := {
  name := "mul"
  pattern := .binop "Mul" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           imulRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

-- Bitwise: Or, And, Xor

def orRule : IselRule := {
  name := "or"
  pattern := .binop "Or" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           orRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

def andRule : IselRule := {
  name := "and"
  pattern := .binop "And" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           andRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

def xorRule : IselRule := {
  name := "xor"
  pattern := .binop "Xor" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           xorRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

-- Shifts: Shl, Shr (unsigned), Shr (signed/arithmetic)
-- Pattern: mov dst, lhs; mov rcx, rhs; <shift> dst

def shlRule : IselRule := {
  name := "shl"
  pattern := .binop "Shl" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           movRR .s64 (.freshFixed "rcx" .rcx) (.named "rhs"),
           shlRCL .s64 (.fresh "dst")]
  result := .reg "dst"
}

def shrUnsignedRule : IselRule := {
  name := "shr_unsigned"
  pattern := .binop "Shr" ⟨"lhs", .unsigned⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           movRR .s64 (.freshFixed "rcx" .rcx) (.named "rhs"),
           shrRCL .s64 (.fresh "dst")]
  result := .reg "dst"
}

def shrSignedRule : IselRule := {
  name := "shr_signed"
  pattern := .binop "Shr" ⟨"lhs", .signed⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           movRR .s64 (.freshFixed "rcx" .rcx) (.named "rhs"),
           sarRCL .s64 (.fresh "dst")]
  result := .reg "dst"
}

-- Min/Max with signed/unsigned condition codes
-- Pattern: mov dst, rhs; cmp lhs, rhs; cmovCC dst, lhs

def minSignedRule : IselRule := {
  name := "min_signed"
  pattern := .binop "Min" ⟨"lhs", .signed⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "rhs"),
           cmpRR .s64 (.named "lhs") (.named "rhs"),
           cmovCC .s64 .l (.fresh "dst") (.named "lhs")]
  result := .reg "dst"
}

def minUnsignedRule : IselRule := {
  name := "min_unsigned"
  pattern := .binop "Min" ⟨"lhs", .unsigned⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "rhs"),
           cmpRR .s64 (.named "lhs") (.named "rhs"),
           cmovCC .s64 .b (.fresh "dst") (.named "lhs")]
  result := .reg "dst"
}

def maxSignedRule : IselRule := {
  name := "max_signed"
  pattern := .binop "Max" ⟨"lhs", .signed⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "rhs"),
           cmpRR .s64 (.named "lhs") (.named "rhs"),
           cmovCC .s64 .g (.fresh "dst") (.named "lhs")]
  result := .reg "dst"
}

def maxUnsignedRule : IselRule := {
  name := "max_unsigned"
  pattern := .binop "Max" ⟨"lhs", .unsigned⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "rhs"),
           cmpRR .s64 (.named "lhs") (.named "rhs"),
           cmovCC .s64 .a (.fresh "dst") (.named "lhs")]
  result := .reg "dst"
}

-- CountOnes (popcnt)

def countOnesRule : IselRule := {
  name := "count_ones"
  pattern := .unop "CountOnes" ⟨"src", .any⟩
  emit := [popcnt (.fresh "dst") (.named "src")]
  result := .reg "dst"
}

-- ICmp: emit CmpRR, store condition code in CmpMap

def icmpRule : IselRule := {
  name := "icmp"
  pattern := .icmp ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [cmpRR .s64 (.named "lhs") (.named "rhs")]
  result := .cmpFlags
  icmpCcFromOp := true
}

-- Pointer arithmetic

def ptrAddRule : IselRule := {
  name := "ptr_add"
  pattern := .binop "PtrAdd" ⟨"ptr", .any⟩ ⟨"offset", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "ptr"),
           addRR .s64 (.fresh "dst") (.named "offset")]
  result := .reg "dst"
}

def ptrDiffRule : IselRule := {
  name := "ptr_diff"
  pattern := .binop "PtrDiff" ⟨"lhs", .any⟩ ⟨"rhs", .any⟩
  emit := [movRR .s64 (.fresh "dst") (.named "lhs"),
           subRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

/-- All instruction selection rules. Order matters: more specific rules
    (e.g. signed/unsigned variants) must come before generic ones. -/
def allRules : List IselRule := [
  addRule, subRule, mulRule,
  orRule, andRule, xorRule,
  shlRule, shrSignedRule, shrUnsignedRule,
  minSignedRule, minUnsignedRule,
  maxSignedRule, maxUnsignedRule,
  countOnesRule,
  icmpRule,
  ptrAddRule, ptrDiffRule
]

end TuffyLean.Target.X86
