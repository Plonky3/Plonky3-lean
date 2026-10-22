/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Data.Polynomial.Frobenius
public import CompPoly.Fields.Binary.Common
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

/-!
# Rabin's irreducibility test over `GF(2)`, for degree a power of two

A polynomial `P` of degree `2^(k+1)` is irreducible when:

- `P` divides `X^(2^(2^(k+1))) - X`, and
- `P` is coprime to `X^(2^(2^k)) - X`.

The second form states both conditions in `GF(2)[X] / (P)`, with `k` symbolic.
A certificate then never puts a concrete `X^(2^(2^k))` in a polynomial ring, where
unifying two elaborations of that power would evaluate it.
-/

namespace Polynomial

/-- A reducible polynomial of degree `2 m` has an irreducible factor of degree at most `m`. -/
theorem exists_irreducible_factor_le_half {R : Type*} [Field R] (P : R[X]) (m : ℕ)
    (h_deg : P.natDegree = 2 * m) (hm : 0 < m) (h_red : ¬ Irreducible P) :
    ∃ q, Irreducible q ∧ q ∣ P ∧ q.natDegree ≤ m := by
  have h_ne_zero : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at h_deg; omega
  have h_not_unit : ¬ IsUnit P := by
    intro h_unit
    have h0 := natDegree_eq_zero_of_isUnit h_unit
    omega
  obtain ⟨a, b, h_eq, ha, hb⟩ : ∃ a b, P = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff, not_and_or, not_forall] at h_red
    simp only [h_not_unit, not_false_eq_true] at h_red
    push Not at h_red
    simp only [IsEmpty.exists_iff, false_or] at h_red
    obtain ⟨a, b, h_eq, h_nu⟩ := h_red
    exact ⟨a, b, h_eq, h_nu⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at h_eq; exact h_ne_zero h_eq
  have hb0 : b ≠ 0 := by rintro rfl; simp at h_eq; exact h_ne_zero h_eq
  have h_sum : a.natDegree + b.natDegree = 2 * m := by
    rw [← h_deg, h_eq, natDegree_mul ha0 hb0]
  by_cases h_le : a.natDegree ≤ b.natDegree
  · obtain ⟨q, hq, hqa⟩ := WfDvdMonoid.exists_irreducible_factor ha ha0
    exact ⟨q, hq, dvd_trans hqa (Dvd.intro b h_eq.symm),
      le_trans (natDegree_le_of_dvd hqa ha0) (by omega)⟩
  · obtain ⟨q, hq, hqb⟩ := WfDvdMonoid.exists_irreducible_factor hb hb0
    exact ⟨q, hq, dvd_trans hqb (Dvd.intro_left a h_eq.symm),
      le_trans (natDegree_le_of_dvd hqb hb0) (by omega)⟩

/-- Rabin's test over `GF(2)` for a polynomial of degree `2^(k+1)`. -/
theorem irreducible_of_rabin_two_pow (P : (ZMod 2)[X]) (k : ℕ)
    (h_deg : P.natDegree = 2 ^ (k + 1))
    (h_trace : P ∣ X ^ 2 ^ 2 ^ (k + 1) - X)
    (h_cop : IsCoprime P (X ^ 2 ^ 2 ^ k - X)) : Irreducible P := by
  haveI : Fact (Nat.Prime (ringChar (ZMod 2))) := ⟨by rw [ZMod.ringChar_zmod_n]; exact Nat.prime_two⟩
  by_contra h_red
  obtain ⟨q, hq, hqP, hq_deg⟩ := exists_irreducible_factor_le_half P (2 ^ k)
    (by rw [h_deg, pow_succ]; ring) (by positivity) h_red
  have h1 : q.natDegree ∣ 2 ^ (k + 1) :=
    (irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd (R := ZMod 2) (2 ^ (k + 1)) q hq).mp
      (by rw [ZMod.card]; exact dvd_trans hqP h_trace)
  obtain ⟨j, hj, hjq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hjk : j ≤ k := by
    rw [hjq] at hq_deg
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq_deg
  have h2 : q ∣ X ^ 2 ^ 2 ^ k - X := by
    have := (irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd (R := ZMod 2) (2 ^ k) q hq).mpr
      (by rw [hjq]; exact Nat.pow_dvd_pow 2 hjk)
    rwa [ZMod.card] at this
  exact hq.not_isUnit (h_cop.isUnit_of_dvd' hqP h2)

/-- Rabin's test over `GF(2)`, with both conditions in `GF(2)[X] / (P)`:

- `X^(2^(2^(k+1)))` is `X`,
- `X^(2^(2^k)) + X` has an inverse. -/
theorem irreducible_of_rabin_two_pow_mk (P : (ZMod 2)[X]) (k : ℕ)
    (h_deg : P.natDegree = 2 ^ (k + 1))
    (h_trace : AdjoinRoot.mk P X ^ 2 ^ 2 ^ (k + 1) = AdjoinRoot.mk P X)
    (h_cop : ∃ u, AdjoinRoot.mk P u * (AdjoinRoot.mk P X ^ 2 ^ 2 ^ k + AdjoinRoot.mk P X) = 1) :
    Irreducible P := by
  apply irreducible_of_rabin_two_pow P k h_deg
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, h_trace, sub_self]
  · obtain ⟨u, hu⟩ := h_cop
    rw [← map_pow, ← map_add, ← map_mul, ← map_one (AdjoinRoot.mk P), AdjoinRoot.mk_eq_mk] at hu
    obtain ⟨w, hw⟩ := hu
    exact ⟨-w, u, by linear_combination hw - u * X * ZMod2Poly.two_eq_zero⟩

end Polynomial
