module

public import P3Bus
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-!
# The bit-level comparison

A key is a list of digits, least significant first, each 0 or 1 in a field.

The comparison proves `right = left + delta` with a ripple adder whose final carry is zero, and a running or proving `delta` nonzero.

Over digits that are bits, the adder identities are the integer ones:

```text
    xor3(a, b, c)     = (a + b + c) mod 2
    majority(a, b, c) = (a + b + c) div 2
```

So the accepted keys satisfy `value(right) = value(left) + value(delta) > value(left)` as natural numbers, and nothing wraps.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.ram.mirror p3_air.builder.mirror Finset

set_option linter.unusedSectionVars false

variable {F : Type _} [Field F] [DecidableEq F]

/-- The expression operations of a field. -/
def fieldExprOps (F : Type _) [Field F] : ExprOps F F where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := id

/-- A digit: 0 or 1. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The integer value of a digit. -/
def nb (x : F) : ℕ := if x = 1 then 1 else 0

/-- The value of the first k digits, least significant first. -/
def pv (l : List F) (k : ℕ) : ℕ := ∑ i ∈ range k, 2 ^ i * nb (l.getD i 0)

theorem pv_succ (l : List F) (k : ℕ) : pv l (k + 1) = pv l k + 2 ^ k * nb (l.getD k 0) := by
  simp [pv, sum_range_succ]

/-- Over bits, the sum digit is the parity and the carry is the majority. -/
theorem adder_bits {a b c : F} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    IsBit (xor3 (fieldExprOps F) a b c) ∧ IsBit (majority (fieldExprOps F) a b c) ∧
      nb (xor3 (fieldExprOps F) a b c) + 2 * nb (majority (fieldExprOps F) a b c) =
        nb a + nb b + nb c := by
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  unfold IsBit at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num [xor3, p3_bus.ram.mirror.xor, majority, fieldExprOps, nb, IsBit, h01, h01.symm]

theorem or_bits {a b : F} (ha : IsBit a) (hb : IsBit b) :
    IsBit (p3_bus.ram.mirror.or (fieldExprOps F) a b) ∧ (p3_bus.ram.mirror.or (fieldExprOps F) a b = 1 ↔ a = 1 ∨ b = 1) := by
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  unfold IsBit at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [p3_bus.ram.mirror.or, fieldExprOps, IsBit, h01, h01.symm]

/-- **The ripple adder.** With bit inputs, a zero carry in, and the sum and carry identities on the first k digits, the k-digit values satisfy right + 2^k carry_k = left + delta. -/
theorem ripple {left right delta carry : List F} :
    ∀ k : ℕ, (∀ i < k, IsBit (left.getD i 0)) → (∀ i < k, IsBit (delta.getD i 0)) →
      carry.getD 0 0 = 0 →
      (∀ i < k, right.getD i 0 = xor3 (fieldExprOps F) (left.getD i 0) (delta.getD i 0)
        (carry.getD i 0)) →
      (∀ i < k, carry.getD (i + 1) 0 = majority (fieldExprOps F) (left.getD i 0) (delta.getD i 0)
        (carry.getD i 0)) →
      IsBit (carry.getD k 0) ∧ pv right k + 2 ^ k * nb (carry.getD k 0) = pv left k + pv delta k
  | 0, _, _, h0, _, _ => by rw [h0]; simp [pv, IsBit, nb]
  | k + 1, hl, hd, h0, hr, hc => by
    obtain ⟨hck, ih⟩ := ripple k (fun i hi => hl i (by omega)) (fun i hi => hd i (by omega)) h0
      (fun i hi => hr i (by omega)) (fun i hi => hc i (by omega))
    obtain ⟨-, hmaj, hsum⟩ := adder_bits (hl k (by omega)) (hd k (by omega)) hck
    rw [hc k (by omega)]
    refine ⟨hmaj, ?_⟩
    rw [pv_succ, pv_succ, pv_succ, hr k (by omega), pow_succ]
    linear_combination (norm := ring_nf) ih + 2 ^ k * hsum

/-- **The running or.** The flags of a running or over bits reach 1 exactly when some digit so far is 1. -/
theorem running_or {delta nonzero : List F} :
    ∀ k : ℕ, (∀ i ≤ k, IsBit (delta.getD i 0)) → nonzero.getD 0 0 = delta.getD 0 0 →
      (∀ i < k, nonzero.getD (i + 1) 0 = p3_bus.ram.mirror.or (fieldExprOps F) (nonzero.getD i 0) (delta.getD (i + 1) 0)) →
      IsBit (nonzero.getD k 0) ∧ (nonzero.getD k 0 = 1 ↔ ∃ i ≤ k, delta.getD i 0 = 1)
  | 0, hd, h0, _ => by
    rw [h0]; exact ⟨hd 0 le_rfl, ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨i, hi, h⟩ => by
      rwa [Nat.le_zero.1 hi] at h⟩⟩
  | k + 1, hd, h0, hs => by
    obtain ⟨hb, ih⟩ := running_or k (fun i hi => hd i (by omega)) h0 fun i hi => hs i (by omega)
    rw [hs k (by omega)]
    obtain ⟨hb', hiff⟩ := or_bits hb (hd (k + 1) le_rfl)
    refine ⟨hb', hiff.trans ⟨?_, ?_⟩⟩
    · rintro (h | h)
      · obtain ⟨i, hi, h⟩ := ih.1 h; exact ⟨i, by omega, h⟩
      · exact ⟨k + 1, le_rfl, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i (k + 1) with hi' | hi'
      · exact Or.inl (ih.2 ⟨i, by omega, h⟩)
      · exact Or.inr (by rwa [show i = k + 1 by omega] at h)

theorem pv_pos {l : List F} {k i : ℕ} (hi : i < k) (h : l.getD i 0 = 1) : 0 < pv l k := by
  unfold pv
  exact lt_of_lt_of_le (by rw [h]; simp [nb]) (single_le_sum (f := fun j => 2 ^ j * nb (l.getD j 0))
    (fun _ _ => Nat.zero_le _) (mem_range.2 hi))

end Plonky3Lean.Proofs.Bus
