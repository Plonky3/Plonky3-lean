module

public import Plonky3Lean.Proofs.Word.Eval

@[expose] public section

/-!
# The three relation families

A relation holds when every operand evaluates and the evaluated words satisfy it.

- A zero relation needs its operand to vanish.
- An AND relation needs the bitwise AND of its inputs to equal its output.
- A product relation needs the full product of its factors to equal its two limbs.

An operand with a term outside its segment makes its relation fail.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

/-- What a word instance computes, as plain functions. -/
structure Model {W : Type} [DecidableEq W] (inst : word.Word W) where
  zero : W
  xorf : W → W → W
  andf : W → W → W
  mulf : W → W → W × W
  /-- The meaning of a term on the word it reads. -/
  term : shift.ShiftedValue W → W → W
  /-- When a term applies without panicking. -/
  valid : shift.ShiftedValue W → Prop
  hzero : inst.ZERO = .ok zero
  hxor : ∀ a b, inst.sealedSealedInst.xor a b = .ok (xorf a b)
  hand : ∀ a b, inst.sealedSealedInst.and a b = .ok (andf a b)
  hmul : ∀ a b, inst.sealedSealedInst.wide_mul a b = .ok (mulf a b)
  heq : ∀ a b, inst.corecmpEqInst.PartialEqInst.eq a b = .ok (decide (a = b))
  happly : ∀ t w, valid t → shift.ShiftedValue.apply inst t w = .ok (term t w)

variable {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)

/-- The word an operand denotes, if every term lies inside its segment. -/
def opVal (pub wit : Slice W) (op : constraint.Operand W) : Option W :=
  match evalSpec M.xorf M.term pub wit op.terms.val M.zero with
  | .Ok v => some v
  | .Err _ => none

/-- Every term of an operand applies without panicking. -/
def OpValid (op : constraint.Operand W) : Prop := ∀ t ∈ op.terms.val, M.valid t

theorem evaluate_spec (pub wit : Slice W) (op : constraint.Operand W) (hv : OpValid M op) :
    constraint.Operand.evaluate inst op pub wit =
      .ok (evalSpec M.xorf M.term pub wit op.terms.val M.zero) := by
  rw [evaluate_eq inst M.xorf M.zero M.hzero M.hxor,
    evalTerms_eq inst M.xorf M.term pub wit _ (fun t ht w => M.happly t w (hv t ht))]

theorem evaluate_some {pub wit : Slice W} {op : constraint.Operand W} (hv : OpValid M op)
    {v : W} (h : opVal M pub wit op = some v) :
    constraint.Operand.evaluate inst op pub wit = .ok (.Ok v) := by
  rw [evaluate_spec M pub wit op hv]
  unfold opVal at h
  split at h <;> simp_all

theorem evaluate_none {pub wit : Slice W} {op : constraint.Operand W} (hv : OpValid M op)
    (h : opVal M pub wit op = none) :
    ∃ e, constraint.Operand.evaluate inst op pub wit = .ok (.Err e) := by
  rw [evaluate_spec M pub wit op hv]
  unfold opVal at h
  split at h <;> simp_all

/-- A zero relation holds exactly when its operand denotes zero. -/
theorem zero_sat (pub wit : Slice W) (c : constraint.ZeroConstraint W) (hv : OpValid M c.value) :
    constraint.ZeroConstraint.is_satisfied inst c pub wit =
      .ok (decide (opVal M pub wit c.value = some M.zero)) := by
  simp only [constraint.ZeroConstraint.is_satisfied, M.hzero, bind_ok]
  cases h : opVal M pub wit c.value with
  | some v =>
    rw [evaluate_some M hv h, bind_ok]
    simp [CoreModels.core.result.Result.Insts.CoreCmpPartialEqResult.eq, M.heq]
  | none =>
    obtain ⟨e, he⟩ := evaluate_none M hv h
    rw [he, bind_ok]
    simp [CoreModels.core.result.Result.Insts.CoreCmpPartialEqResult.eq]

/-- Whether an AND relation holds: all three operands denote words, and the AND of the inputs is the output. -/
def andHolds (pub wit : Slice W) (c : constraint.AndConstraint W) : Bool :=
  match opVal M pub wit c.left, opVal M pub wit c.right, opVal M pub wit c.output with
  | some a, some b, some o => decide (M.andf a b = o)
  | _, _, _ => false

/-- Whether a product relation holds: all four operands denote words, and the product is the two limbs. -/
def mulHolds (pub wit : Slice W) (c : constraint.IntegerMulConstraint W) : Bool :=
  match opVal M pub wit c.left, opVal M pub wit c.right, opVal M pub wit c.low,
    opVal M pub wit c.high with
  | some a, some b, some lo, some hi => decide (M.mulf a b = (lo, hi))
  | _, _, _, _ => false

theorem and_sat (pub wit : Slice W) (c : constraint.AndConstraint W) (hl : OpValid M c.left)
    (hr : OpValid M c.right) (ho : OpValid M c.output) :
    constraint.AndConstraint.is_satisfied inst c pub wit = .ok (andHolds M pub wit c) := by
  unfold constraint.AndConstraint.is_satisfied andHolds
  cases h1 : opVal M pub wit c.left with
  | none => obtain ⟨_, e⟩ := evaluate_none M hl h1; simp [e]
  | some a =>
  cases h2 : opVal M pub wit c.right with
  | none => obtain ⟨_, e⟩ := evaluate_none M hr h2; simp [evaluate_some M hl h1, e]
  | some b =>
  cases h3 : opVal M pub wit c.output with
  | none =>
    obtain ⟨_, e⟩ := evaluate_none M ho h3
    simp [evaluate_some M hl h1, evaluate_some M hr h2, e]
  | some o =>
    simp [evaluate_some M hl h1, evaluate_some M hr h2, evaluate_some M ho h3, M.hand, M.heq]

theorem mul_sat (pub wit : Slice W) (c : constraint.IntegerMulConstraint W)
    (hl : OpValid M c.left) (hr : OpValid M c.right) (hlo : OpValid M c.low)
    (hhi : OpValid M c.high) :
    constraint.IntegerMulConstraint.is_satisfied inst c pub wit = .ok (mulHolds M pub wit c) := by
  unfold constraint.IntegerMulConstraint.is_satisfied mulHolds
  cases h1 : opVal M pub wit c.left with
  | none => obtain ⟨_, e⟩ := evaluate_none M hl h1; simp [e]
  | some a =>
  cases h2 : opVal M pub wit c.right with
  | none => obtain ⟨_, e⟩ := evaluate_none M hr h2; simp [evaluate_some M hl h1, e]
  | some b =>
  cases h3 : opVal M pub wit c.low with
  | none =>
    obtain ⟨_, e⟩ := evaluate_none M hlo h3
    simp [evaluate_some M hl h1, evaluate_some M hr h2, e]
  | some lo =>
  cases h4 : opVal M pub wit c.high with
  | none =>
    obtain ⟨_, e⟩ := evaluate_none M hhi h4
    simp [evaluate_some M hl h1, evaluate_some M hr h2, evaluate_some M hlo h3, e]
  | some hi =>
    simp only [evaluate_some M hl h1, evaluate_some M hr h2, evaluate_some M hlo h3,
      evaluate_some M hhi h4, bind_ok, M.hmul]
    obtain ⟨p, q⟩ := M.mulf a b
    by_cases hp : p = lo <;> by_cases hq : q = hi <;>
      simp [CoreModels.core.Pair.Insts.CoreCmpPartialEqPair.eq, M.heq, hp, hq]

end Plonky3Lean.Proofs.Word
