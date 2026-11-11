module

public import Plonky3Lean.Proofs.Sha256Air.Row
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# What the addition checks prove

An addition check asserts two products: one on the whole words, one on the low limbs.

Each product vanishes only at its listed roots.

So it fixes the sum up to a multiple of `2^32`, and the low limb up to a multiple of `2^16`.

A word is tracked by two integers:

- `L`, the value of its low limb
- `Z`, the value of its packing `x_0 + 2^16 x_1`

They agree modulo `2^16`.

```text
    committed output:   L = L_1 + L_2 (+ L_3) - k 2^16    Z = Z_1 + Z_2 (+ Z_3) - j 2^32
    bit output:         L and Z are the limbs of a 32-bit word
```

A committed output needs nothing of the field: its limbs need not lie below `2^16`.

A bit output pins the sum modulo `2^32`.

This needs the characteristic to exceed the spread of the integers it compares.

In this AIR the widest spread is `7 * 2^16`, at the round's new `a`.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

variable {F : Type} [Field F]

/-! ## Roots of the checks -/

theorem roots2 {x c : F} (h : x * (x + c) = 0) : ∃ k : ℤ, (k = 0 ∨ k = 1) ∧ x = -(k * c) := by
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨0, by simp, by simp [h]⟩
  · exact ⟨1, by simp, by simp; linear_combination h⟩

theorem roots3 {x c : F} (h : x * (x + c) * (x + (c + c)) = 0) :
    ∃ k : ℤ, (k = 0 ∨ k = 1 ∨ k = 2) ∧ x = -(k * c) := by
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · exact ⟨1, by simp, by simp; linear_combination h⟩
  · exact ⟨2, by simp, by push_cast; linear_combination h⟩

/-! ## Words as pairs of integers -/

/-- A two-limb word with low limb `L` and packing `Z`, both integers.

They agree modulo `2^16`. -/
structure PW (x : ℕ → F) (L Z : ℤ) : Prop where
  lo : x 0 = (L : F)
  val : x 0 + x 1 * 65536 = (Z : F)
  cong : L ≡ Z [ZMOD 65536]

/-- A word with limbs below `2^16`. -/
theorem PW.of_limbs {x : ℕ → F} {a0 a1 : ℕ} (h0 : x 0 = a0) (h1 : x 1 = a1) :
    PW x a0 (a0 + a1 * 65536) where
  lo := by rw [h0]; norm_cast
  val := by rw [h0, h1]; push_cast; ring
  cong := by
    rw [Int.ModEq]; simp

theorem PW.of_add2 {o b c : ℕ → F} {Lb Zb Lc Zc : ℤ} (h : Add2P o b c) (hb : PW b Lb Zb)
    (hc : PW c Lc Zc) : ∃ k j : ℤ, (0 ≤ k ∧ k ≤ 1) ∧ (0 ≤ j ∧ j ≤ 1) ∧
      PW o (Lb + Lc - k * 65536) (Zb + Zc - j * 4294967296) := by
  obtain ⟨h32, h16⟩ := h
  obtain ⟨k, hk, ek⟩ := roots2 h16
  obtain ⟨j, hj, ej⟩ := roots2 h32
  refine ⟨k, j, by omega, by omega, ⟨?_, ?_, ?_⟩⟩
  · push_cast; rw [← hb.lo, ← hc.lo]; linear_combination ek
  · push_cast; rw [← hb.val, ← hc.val]; linear_combination ej
  · exact (hb.cong.add hc.cong).sub (Int.modEq_iff_dvd.mpr ⟨j * 65536 - k, by ring⟩)

theorem PW.of_add3 {o b c d : ℕ → F} {Lb Zb Lc Zc Ld Zd : ℤ} (h : Add3P o b c d) (hb : PW b Lb Zb)
    (hc : PW c Lc Zc) (hd : PW d Ld Zd) : ∃ k j : ℤ, (0 ≤ k ∧ k ≤ 2) ∧ (0 ≤ j ∧ j ≤ 2) ∧
      PW o (Lb + Lc + Ld - k * 65536) (Zb + Zc + Zd - j * 4294967296) := by
  obtain ⟨h32, h16⟩ := h
  obtain ⟨k, hk, ek⟩ := roots3 h16
  obtain ⟨j, hj, ej⟩ := roots3 h32
  refine ⟨k, j, by omega, by omega, ⟨?_, ?_, ?_⟩⟩
  · push_cast; rw [← hb.lo, ← hc.lo, ← hd.lo]; linear_combination ek
  · push_cast; rw [← hb.val, ← hc.val, ← hd.val]; linear_combination ej
  · exact ((hb.cong.add hc.cong).add hd.cong).sub
      (Int.modEq_iff_dvd.mpr ⟨j * 65536 - k, by ring⟩)

/-! ## A word of bits is pinned -/

/-- An integer is zero when it is a multiple of an odd prime p and of 2^16, and below 2^16 p in absolute value. -/
theorem eq_zero_of_dvd_dvd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {D : ℤ} (h1 : (p : ℤ) ∣ D)
    (h16 : (65536 : ℤ) ∣ D) (hb : |D| < p * 65536) : D = 0 := by
  have hc : IsCoprime (p : ℤ) 65536 := by
    rw [Int.isCoprime_iff_gcd_eq_one, show (65536 : ℤ) = ((2 ^ 16 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr h2)
  exact Int.eq_zero_of_abs_lt_dvd (hc.mul_dvd h1 h16) hb

section pin

variable (hp : 7 * 65536 < ringChar F)
include hp

theorem prime_ringChar : (ringChar F).Prime := by
  rcases CharP.char_is_prime_or_zero F (ringChar F) with h | h
  · exact h
  · omega

theorem dvd_of_cast_eq {a b : ℤ} (h : (a : F) = b) : (ringChar F : ℤ) ∣ a - b := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff F (ringChar F)] at h
  exact h

/-- A word with limbs below 2^16 is pinned: its packing is Z.

This needs L in [-6 2^16, 7 2^16) and Z in [-6 2^32, 7 2^32). -/
theorem PW.pin {o : ℕ → F} {L Z : ℤ} (h : PW o L Z) {a0 a1 : ℕ} (ho0 : o 0 = a0) (ho1 : o 1 = a1)
    (ha0 : a0 < 65536) (ha1 : a1 < 65536) (hL : -6 * 65536 ≤ L ∧ L < 7 * 65536)
    (hZ : -6 * 4294967296 ≤ Z ∧ Z < 7 * 4294967296) : (a0 : ℤ) + a1 * 65536 = Z := by
  have hpr := prime_ringChar hp
  have hl := dvd_of_cast_eq hp (a := a0) (b := L) (by rw [← h.lo, ho0]; norm_cast)
  have hlo : (a0 : ℤ) = L := by
    have := Int.eq_zero_of_abs_lt_dvd hl (by rw [abs_lt]; omega)
    omega
  have hv := dvd_of_cast_eq hp (a := a0 + a1 * 65536) (b := Z) (by rw [← h.val, ho0, ho1]; push_cast; ring)
  have h16 : (65536 : ℤ) ∣ (a0 + a1 * 65536) - Z := by
    have := h.cong
    rw [Int.ModEq] at this
    omega
  have := eq_zero_of_dvd_dvd hpr (by omega) hv h16 (by rw [abs_lt]; constructor <;> nlinarith)
  omega

end pin

end Plonky3Lean.Proofs.Sha256Air
