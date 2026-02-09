-- TuffyLean/IR/Semantics.lean
-- Operational semantics of tuffy IR instructions

import TuffyLean.IR.Types
import Mathlib.Data.Int.Bitwise

namespace TuffyLean.IR

/-- Integer arithmetic semantics (infinite precision) -/
def evalAdd (a b : Int) : Int := a + b
def evalSub (a b : Int) : Int := a - b
def evalMul (a b : Int) : Int := a * b

/-- Integer division produces poison on division by zero.
    Signedness is a property of operand annotations, not the operation. -/
def evalDiv (a b : Int) : Value :=
  if b = 0 then .poison else .int (a / b)

/-- Integer remainder produces poison on division by zero.
    Signedness is a property of operand annotations, not the operation. -/
def evalRem (a b : Int) : Value :=
  if b = 0 then .poison else .int (a % b)

/-- Bitwise AND (two's complement, infinite width) -/
def evalAnd (a b : Int) : Int := Int.land a b

/-- Bitwise OR (two's complement, infinite width) -/
def evalOr (a b : Int) : Int := Int.lor a b

/-- Bitwise XOR (two's complement, infinite width) -/
def evalXor (a b : Int) : Int := Int.xor a b

/-- Left shift. Poison if shift amount is negative. -/
def evalShl (a b : Int) : Value :=
  if b < 0 then .poison else .int (a <<< b.toNat)

/-- Right shift. Poison if shift amount is negative.
    Signedness is a property of operand annotations, not the operation.
    In infinite precision, logical and arithmetic right shift are identical. -/
def evalShr (a b : Int) : Value :=
  if b < 0 then .poison else .int (a >>> b.toNat)

-- Pointer operation semantics

/-- Pointer addition: offset a pointer by an integer amount.
    Preserves provenance from the base pointer. -/
def evalPtrAdd (base : Pointer) (offset : Int) : Value :=
  .ptr { allocId := base.allocId, offset := base.offset + offset }

/-- Pointer difference: compute the offset between two pointers.
    Both pointers must belong to the same allocation; otherwise poison. -/
def evalPtrDiff (a b : Pointer) : Value :=
  if a.allocId == b.allocId then .int (a.offset - b.offset) else .poison

/-- Pointer to integer: extract the offset as an integer.
    Provenance is captured (the integer "remembers" it came from a pointer). -/
def evalPtrToInt (p : Pointer) : Value := .int p.offset

/-- Pointer to address: extract the address, discarding provenance.
    Returns a plain integer with no provenance information. -/
def evalPtrToAddr (p : Pointer) : Value := .int p.offset

/-- Integer to pointer: create a pointer from an integer address.
    The resulting pointer has no valid provenance (wildcard). -/
def evalIntToPtr (addr : Int) (allocId : AllocId) : Value :=
  .ptr { allocId := allocId, offset := addr }

-- Floating point operation semantics
-- The IR adopts IEEE 754-2008 as the floating-point semantics standard.
-- These use Lean 4's native Float type (IEEE 754 binary64) as a placeholder
-- model. The formal float model will be refined when full NaN payload and
-- denormal semantics are decided.

/-- Floating point addition. -/
def evalFAdd (a b : Float) : Float := a + b

/-- Floating point subtraction. -/
def evalFSub (a b : Float) : Float := a - b

/-- Floating point multiplication. -/
def evalFMul (a b : Float) : Float := a * b

/-- Floating point division. -/
def evalFDiv (a b : Float) : Float := a / b

/-- Floating point negation. -/
def evalFNeg (a : Float) : Float := -a

/-- Floating point absolute value. -/
def evalFAbs (a : Float) : Float := Float.abs a

/-- Copy sign: produce a value with the magnitude of `mag` and the sign of `sign`.
    Uses Float.toBits to check the sign bit (bit 63), correctly handling -0.0 and -NaN. -/
def evalCopySign (mag sign : Float) : Float :=
  let absMag := Float.abs mag
  if sign.toBits >>> 63 != 0 then -absMag else absMag

-- Annotation violation semantics: produce poison if constraint violated.
-- These define the semantics of :s<N> and :u<N> annotations on value
-- definitions (result-side) and use edges (use-side).

/-- Check signed range annotation :s<N>. Returns poison if value outside
    [-2^(N-1), 2^(N-1)-1]. -/
def checkSignedRange (v : Int) (n : Nat) : Value :=
  let min := -(2 ^ (n - 1))
  let max := 2 ^ (n - 1) - 1
  if min ≤ v ∧ v ≤ max then .int v else .poison

/-- Check unsigned range annotation :u<N>. Returns poison if value outside
    [0, 2^N-1]. -/
def checkUnsignedRange (v : Int) (n : Nat) : Value :=
  if 0 ≤ v ∧ v < 2 ^ n then .int v else .poison

/-- Apply an annotation to a value. Returns poison on violation. -/
def applyAnnotation (v : Int) (ann : Annotation) : Value :=
  match ann with
  | .signed n => checkSignedRange v n
  | .unsigned n => checkUnsignedRange v n

-- Bytecast semantics: conversion between byte types and typed values.
-- Annotations are always droppable — they never determine bytecast semantics.

/-- Resolve a single AbstractByte to a concrete byte value (0–255).
    Returns none if the byte is poison, uninit, or a pointer fragment. -/
def resolveAbstractByte (ab : AbstractByte) : Option UInt8 :=
  match ab with
  | .bits val => some val
  | .poison => none
  | .uninit => none
  | .ptrFragment _ _ => none  -- TODO: ptrtoint semantics

/-- Decode the low bits from a list of abstract bytes (little-endian).
    Returns none if any byte is not concrete bits. -/
def decodeBytesLE (bs : List AbstractByte) : Option Int :=
  let rec go (remaining : List AbstractByte) (shift : Nat) (acc : Int) : Option Int :=
    match remaining with
    | [] => some acc
    | b :: rest =>
      match resolveAbstractByte b with
      | none => none
      | some v => go rest (shift + 8) (acc + (v.toNat : Int) <<< shift)
  go bs 0 0

/-- Specification for bytecast bytes→int. The low N*8 bits of the result
    match the decoded bytes; high bits are unspecified. The caller must
    apply zext or sext to obtain a fully determined value.
    Returns poison if any byte is non-concrete. -/
def bytecastToIntValid (bs : List AbstractByte) (result : Value) : Prop :=
  match decodeBytesLE bs with
  | none => result = .poison
  | some decoded =>
    ∃ v : Int, result = .int v ∧ v % (2 ^ (bs.length * 8)) = decoded

/-- Encode an integer as a list of abstract bytes (little-endian, N bytes).
    Truncates to the low N bytes. -/
def evalBytecastFromInt (v : Int) (numBytes : Nat) : List AbstractByte :=
  List.ofFn (fun (i : Fin numBytes) =>
    .bits (UInt8.ofNat ((v >>> (i.val * 8)).toNat % 256)))

-- Memory load/store semantics

/-- Load `size` bytes from memory starting at address `addr`.
    Returns a `bytes` value containing the loaded abstract bytes. -/
def evalLoad (mem : Memory) (addr : Int) (size : Nat) : Value :=
  .bytes (List.ofFn (fun (i : Fin size) => mem.bytes (addr + i.val)))

/-- Store a list of abstract bytes to memory starting at address `addr`.
    Returns the updated memory. -/
def evalStore (mem : Memory) (addr : Int) (bs : List AbstractByte) : Memory :=
  { bytes := fun a =>
      let offset := a - addr
      if 0 ≤ offset ∧ offset < bs.length then
        List.getD bs offset.toNat .uninit
      else mem.bytes a }

-- Atomic operation semantics (sequential model)

-- Integer comparison semantics

/-- Evaluate an integer comparison, returning a Bool value. -/
def evalICmp (op : ICmpOp) (a b : Int) : Value :=
  match op with
  | .eq => .bool (a == b)
  | .ne => .bool (a != b)
  | .lt => .bool (a < b)
  | .le => .bool (a ≤ b)
  | .gt => .bool (a > b)
  | .ge => .bool (a ≥ b)

/-- Select between two values based on a boolean condition. -/
def evalSelect (cond : Bool) (tv fv : Value) : Value :=
  if cond then tv else fv

/-- Convert a boolean to an integer: true → 1, false → 0. -/
def evalBoolToInt (b : Bool) : Value :=
  .int (if b then 1 else 0)

-- Atomic operation semantics (sequential model)
-- NOTE: These define sequential semantics only. A formal concurrency model
-- (e.g., based on C11 or a custom weak memory model) is TBD. Memory ordering
-- parameters are accepted but have no effect in this sequential model.

/-- Atomic load: sequentially equivalent to a regular load. -/
def evalLoadAtomic (mem : Memory) (addr : Int) (size : Nat)
    (_ordering : MemoryOrdering) : Value :=
  evalLoad mem addr size

/-- Atomic store: sequentially equivalent to a regular store. -/
def evalStoreAtomic (mem : Memory) (addr : Int) (bs : List AbstractByte)
    (_ordering : MemoryOrdering) : Memory :=
  evalStore mem addr bs

end TuffyLean.IR
