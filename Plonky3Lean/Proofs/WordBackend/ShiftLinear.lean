module

public import Plonky3Lean.Proofs.WordBackend.Lift
public import Plonky3Lean.Proofs.Word.Shift
public import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# Shifts are linear over GF(2), so their transpose reads the shifted word

Every shift kind sends each output bit to zero or to one input bit.

So a shift commutes with XOR.

Read at a bit point, in a ring of characteristic 2, a word is the sum of the weights of its set bits.

That sum is additive over XOR.

So the shifted word, read at a point, equals its unshifted bits paired with the transposed table:

```text
    sum_b  S(x)_b  out_b   =   sum_j  x_j  T_j,      T_j = sum_b  S(2^j)_b  out_b
```

This is the identity the shift reduction's two sumchecks rest on.
-/

open Finset p3_word Plonky3Lean.Proofs.Word

namespace Plonky3Lean.Proofs.WordBackend

/-! ## Every shift commutes with XOR -/

theorem base_xor {n : ℕ} (k : shift.ShiftKind) (a : ℕ) (x y : BitVec n) :
    base k a (x ^^^ y) = base k a x ^^^ base k a y := by
  cases k <;> simp only [base]
  all_goals first
    | exact BitVec.shiftLeft_xor_distrib x y a
    | exact BitVec.ushiftRight_xor_distrib x y a
    | (ext i hi; simp [BitVec.getElem_sshiftRight]; split <;> simp)

theorem lanes_xor (f : BitVec 32 → BitVec 32) (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (x y : BitVec 64) : lanes f (x ^^^ y) = lanes f x ^^^ lanes f y := by
  have he : ∀ s, (x ^^^ y).extractLsb' s 32 = x.extractLsb' s 32 ^^^ y.extractLsb' s 32 := by
    intro s; ext i hi; simp
  simp only [lanes, he, hf]
  exact BitVec.xor_append.symm

theorem sem32_xor (k : shift.ShiftKind) (a : ℕ) (x y : BitVec 32) :
    sem32 k a (x ^^^ y) = sem32 k a x ^^^ sem32 k a y := base_xor k a x y

theorem sem64_xor (k : shift.ShiftKind) (a : ℕ) (x y : BitVec 64) :
    sem64 k a (x ^^^ y) = sem64 k a x ^^^ sem64 k a y := by
  unfold sem64
  split
  · exact lanes_xor _ (base_xor k a) x y
  · exact base_xor k a x y

/-! ## A word read at a bit point -/

variable {R : Type _} [CommRing R] [CharP R 2]

/-- The sum of the weights at the set bits of a pattern, below $n$. -/
def ev (n : ℕ) (x : ℕ) (out : ℕ → R) : R :=
  ∑ b ∈ range n, if x.testBit b then out b else 0

theorem ev_xor (n x y : ℕ) (out : ℕ → R) : ev n (x ^^^ y) out = ev n x out + ev n y out := by
  unfold ev
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> simp [CharTwo.add_self_eq_zero]

omit [CharP R 2] in
theorem ev_two_pow {n j : ℕ} (h : j < n) (out : ℕ → R) : ev n (2 ^ j) out = out j := by
  unfold ev
  rw [sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hj; exact absurd (mem_range.2 h) hj

theorem xor_two_pow_of_lt {a k : ℕ} (h : a < 2 ^ k) : a ^^^ 2 ^ k = a + 2 ^ k := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [mul_one] at this
  rw [Nat.add_comm, this]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : k = i
  · subst hi; simp [Nat.testBit_lt_two_pow h]
  · simp [hi]

/-- A linear map read at a point is the bits of its input paired with its transpose. -/
theorem ev_linear (n : ℕ) (S : ℕ → ℕ) (hS : ∀ x y, S (x ^^^ y) = S x ^^^ S y)
    (out : ℕ → R) (x : ℕ) (k : ℕ) :
    ev n (S (x % 2 ^ k)) out = ∑ j ∈ range k, if x.testBit j then ev n (S (2 ^ j)) out else 0 := by
  have h0 : S 0 = 0 := by
    have := hS 0 0; rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  induction k with
  | zero => simp [ev, Nat.mod_one, h0]
  | succ k ih =>
    rw [sum_range_succ, ← ih, mod_two_pow_succ]
    split
    · rw [← xor_two_pow_of_lt (Nat.mod_lt _ (by positivity)), hS, ev_xor]
    · simp

/-! ## The transpose table -/

/-- The transpose of a map on $n$-bit patterns: column $j$ reads the image of $2^j$. -/
def transposeSpec (n : ℕ) (S : ℕ → ℕ) (out : ℕ → R) : List R :=
  (List.range n).map fun j => ev n (S (2 ^ j)) out

/-- Pairing the bits of a word with the transpose reads the image of the word. -/
theorem pair_transpose (n : ℕ) (S : ℕ → ℕ) (hS : ∀ x y, S (x ^^^ y) = S x ^^^ S y)
    (out : ℕ → R) {x : ℕ} (hx : x < 2 ^ n) :
    ev n x (fun j => (transposeSpec n S out).getD j 0) = ev n (S x) out := by
  rw [← Nat.mod_eq_of_lt hx, ev_linear n S hS out x n, Nat.mod_eq_of_lt hx]
  unfold ev transposeSpec
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  simp [List.getD_eq_getElem?_getD, hj, ev]

end Plonky3Lean.Proofs.WordBackend
