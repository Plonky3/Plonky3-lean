module

public import Plonky3Lean.Proofs.KeccakAir.Row
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# Bits as field elements

A bit is the field element 0 or 1.

On bits, the arithmetic xor, triple xor and and-not are the Boolean ones.

A limb is the sum of 16 bits weighted by powers of 2, so it lies below 2^16.

In a field of characteristic at least 2^16, distinct naturals below 2^16 are distinct field elements.

So a limb determines its bits.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_keccak_air.mirror

variable {F : Type} [Field F]

/-- A bit as a field element. -/
abbrev bitF (b : Bool) : F := (b.toNat : F)

theorem xor_bit (a b : Bool) : xor fieldOps (bitF a : F) (bitF b) = bitF (a ^^ b) := by
  cases a <;> cases b <;> simp [p3_keccak_air.mirror.xor, fieldOps, double, bitF]

theorem xor3_bit (a b c : Bool) :
    xor3 fieldOps (bitF a : F) (bitF b) (bitF c) = bitF (a ^^ b ^^ c) := by
  simp only [xor3, xor_bit]

theorem andn_bit (a b : Bool) : andn fieldOps (bitF a : F) (bitF b) = bitF (!a && b) := by
  cases a <;> cases b <;> simp [andn, fieldOps, bitF]

theorem sum_eq (l : List F) : sum fieldOps l = l.sum := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [sum, List.sum_cons]
    induction l generalizing a with
    | nil => simp
    | cons b l ih => simp only [List.foldl_cons, List.sum_cons, ← add_assoc]; exact ih _

/-- The natural number whose binary digits, least significant first, are g 0, ..., g (k - 1). -/
def bitsum (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (g 0).toNat + 2 * bitsum (fun j => g (j + 1)) k

theorem bitsum_lt (g : ℕ → Bool) (k : ℕ) : bitsum g k < 2 ^ k := by
  induction k generalizing g with
  | zero => simp [bitsum]
  | succ k ih =>
    have := ih (fun j => g (j + 1))
    have := Bool.toNat_le (g 0)
    simp only [bitsum, pow_succ]
    omega

theorem bitsum_inj {g g' : ℕ → Bool} {k : ℕ} (h : bitsum g k = bitsum g' k) :
    ∀ j < k, g j = g' j := by
  induction k generalizing g g' with
  | zero => simp
  | succ k ih =>
    simp only [bitsum] at h
    have h0 : g 0 = g' 0 := by
      cases h1 : g 0 <;> cases h2 : g' 0 <;> simp [h1, h2] at h ⊢ <;> omega
    have hs : bitsum (fun j => g (j + 1)) k = bitsum (fun j => g' (j + 1)) k := by
      rw [h0] at h; omega
    intro j hj
    cases j with
    | zero => exact h0
    | succ j => exact ih hs j (by omega)

theorem bitsum_congr {g g' : ℕ → Bool} {k : ℕ} (h : ∀ j < k, g j = g' j) :
    bitsum g k = bitsum g' k := by
  induction k generalizing g g' with
  | zero => rfl
  | succ k ih =>
    simp only [bitsum, h 0 (by omega), ih fun j hj => h (j + 1) (by omega)]

/-- Folding bits from the most significant, acc <- 2 acc + bit, appends them below acc. -/
theorem foldl_bits (g : ℕ → Bool) (k s : ℕ) (acc : F) :
    (List.range' s k).reverse.foldl (fun acc z => fieldOps.add (double fieldOps acc) (bitF (g z)))
      acc = 2 ^ k * acc + ((bitsum (fun j => g (s + j)) k : ℕ) : F) := by
  induction k generalizing s acc with
  | zero => simp [bitsum]
  | succ k ih =>
    rw [List.range'_succ, List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, bitsum, fieldOps, double, Nat.add_zero]
    push_cast
    simp only [show ∀ j, s + 1 + j = s + (j + 1) from fun j => by omega]
    ring

/-- A limb of bits is their bit sum. -/
theorem limbOf_bits (g : ℕ → Bool) (limb : ℕ) :
    limbOf fieldOps (fun z => (bitF (g z) : F)) limb =
      ((bitsum (fun j => g (limb * 16 + j)) 16 : ℕ) : F) := by
  rw [limbOf, BITS_PER_LIMB, foldl_bits]
  change 2 ^ 16 * (0 : F) + _ = _
  rw [mul_zero, zero_add]

/-- In characteristic at least 2^16, naturals below 2^16 are equal when their images are. -/
theorem cast_inj (hp : 2 ^ 16 ≤ ringChar F) {a b : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (h : (a : F) = b) : a = b := by
  rw [CharP.natCast_eq_natCast F (ringChar F)] at h
  exact Nat.ModEq.eq_of_lt_of_lt h (by omega) (by omega)

/-- In characteristic at least 2^16, a limb of bits determines the bits. -/
theorem bits_of_limb (hp : 2 ^ 16 ≤ ringChar F) {g g' : ℕ → Bool}
    (h : ((bitsum g 16 : ℕ) : F) = (bitsum g' 16 : ℕ)) : ∀ j < 16, g j = g' j :=
  bitsum_inj (cast_inj hp (bitsum_lt g 16) (bitsum_lt g' 16) h)

/-- A root of x (x - 1) is a bit. -/
theorem eq_bitF [DecidableEq F] {v : F} (h : v * (v - 1) = 0) : v = bitF (decide (v = 1)) := by
  rcases mul_eq_zero.mp h with h | h
  · subst h; simp [bitF]
  · have : v = 1 := sub_eq_zero.mp h
    subst this; simp [bitF]

end Plonky3Lean.Proofs.KeccakAir
