module

public import Plonky3Lean.Proofs.Lookup.LogUp
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Fingerprints and the soundness of the bus sum

A tuple is compressed by its fingerprint, and a bus is separated by one more power of beta.

Equal-width tuples have distinct fingerprint polynomials, so distinct messages have distinct denominators.

An unbalanced bus then leaves a nonzero polynomial in (alpha, beta).

Schwartz-Zippel bounds the challenges that hide it.
-/

namespace Plonky3Lean.Proofs.Lookup

open Polynomial Plonky3Lean.Spec.Lookup Finset

set_option linter.unusedSectionVars false

section Fingerprint

variable {R : Type _} [CommRing R]

theorem reverse_getD_cons (x : R) (e : List R) (j : ℕ) :
    (x :: e).reverse.getD j 0 =
      if j < e.length then e.reverse.getD j 0 else if j = e.length then x else 0 := by
  rw [List.reverse_cons]
  split_ifs with h h'
  · exact List.getD_append _ _ _ _ (by simpa using h)
  · subst h'; rw [List.getD_append_right _ _ _ _ (by simp)]; simp
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

/-- Adding a leading entry adds it at the top power. -/
theorem fingerprint_cons (β x : R) (e : List R) :
    fingerprint β (x :: e) = x * β ^ e.length + fingerprint β e := by
  unfold fingerprint
  rw [List.length_cons, sum_range_succ, add_comm]
  congr 1
  · rw [reverse_getD_cons]; simp
  · exact sum_congr rfl fun j hj => by rw [reverse_getD_cons]; simp [mem_range.1 hj]

/-- Horner's rule from an accumulator: a beta^k + fingerprint(e). -/
theorem foldl_horner (β a : R) (e : List R) :
    e.foldl (fun acc x => acc * β + x) a = a * β ^ e.length + fingerprint β e := by
  induction e generalizing a with
  | nil => simp [fingerprint]
  | cons x e ih => rw [List.foldl_cons, ih, fingerprint_cons, List.length_cons, pow_succ]; ring

/-- Horner's rule computes the fingerprint. -/
theorem foldl_horner_zero (β : R) (e : List R) :
    e.foldl (fun acc x => acc * β + x) 0 = fingerprint β e := by
  rw [foldl_horner]; simp

theorem eval_fingerprintPoly (β : R) (e : List R) : (fingerprintPoly e).eval β = fingerprint β e := by
  simp [fingerprintPoly, fingerprint, eval_finsetSum]

/-- Coefficient j of the fingerprint polynomial is entry j from the end. -/
theorem coeff_fingerprintPoly (e : List R) (j : ℕ) : (fingerprintPoly e).coeff j = e.reverse.getD j 0 := by
  simp only [fingerprintPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) fun hj => ?_]
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp at hj ⊢; omega)]; simp

/-- **Injectivity.**

Tuples of one width with equal fingerprint polynomials are equal. -/
theorem fingerprintPoly_inj {e e' : List R} (hl : e.length = e'.length)
    (h : fingerprintPoly e = fingerprintPoly e') : e = e' := by
  have hr : e.reverse = e'.reverse := List.ext_getElem (by simpa using hl) fun j h1 h2 => by
    have := congrArg (·.coeff j) h
    simp only [coeff_fingerprintPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.getD_some] at this
    exact this
  simpa using hr

/-- **The width rule.**

A shorter tuple is a longer one padded with zeros in front.

For example, [x] and [0, x] share every fingerprint. -/
theorem fingerprint_pad (β x : R) : fingerprint β [x] = fingerprint β [0, x] := by
  simp [fingerprint, sum_range_succ]

end Fingerprint

/-! ## The bus polynomial -/

section Bus

variable {K : Type _} [Field K] [DecidableEq K]

/-- The fingerprint as a polynomial in the variable 1 (beta). -/
noncomputable def fingerprintMv (e : List K) : MvPolynomial (Fin 2) K :=
  ∑ j ∈ range e.length, MvPolynomial.C (e.reverse.getD j 0) * MvPolynomial.X 1 ^ j

/-- The denominator as a polynomial in alpha (variable 0) and beta (variable 1). -/
noncomputable def busDenomMv (W bus : ℕ) (e : List K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 + MvPolynomial.C ((bus : K) + 1) * MvPolynomial.X 1 ^ W - fingerprintMv e

theorem eval_busDenomMv (α β : K) (W bus : ℕ) (e : List K) :
    MvPolynomial.eval ![α, β] (busDenomMv W bus e) = busDenom α β W bus e := by
  simp [busDenomMv, fingerprintMv, busDenom, fingerprint, map_sum]

open MvPolynomial in
theorem totalDegree_busDenomMv {W : ℕ} (hW : 1 ≤ W) (bus : ℕ) {e : List K} (he : e.length ≤ W) :
    (busDenomMv W bus e).totalDegree ≤ W := by
  unfold busDenomMv
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · rw [totalDegree_X]; exact hW
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]; exact (totalDegree_pow _ _).trans (by rw [totalDegree_X, mul_one])
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_pow _ _).trans ?_
    rw [totalDegree_X, mul_one]; have := mem_range.1 hj; omega

/-- A key: a bus and a payload. -/
abbrev Key (K : Type _) := ℕ × List K

/-- The cleared bus polynomial: sum_c M_c prod_(c' != c) D_c'. -/
noncomputable def clearedMv (W : ℕ) (G : Finset (Key K)) (M : Key K → K) : MvPolynomial (Fin 2) K :=
  ∑ c ∈ G, MvPolynomial.C (M c) * ∏ c' ∈ G.erase c, busDenomMv W c'.1 c'.2

theorem totalDegree_clearedMv {W : ℕ} (hW : 1 ≤ W) (G : Finset (Key K)) (M : Key K → K)
    (hG : ∀ c ∈ G, c.2.length ≤ W) : (clearedMv W G M).totalDegree ≤ (G.card - 1) * W := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun c hc => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ c' ∈ G.erase c, (busDenomMv W c'.1 c'.2).totalDegree
      ≤ ∑ _c' ∈ G.erase c, W := sum_le_sum fun c' hc' =>
        totalDegree_busDenomMv hW _ (hG c' (mem_of_mem_erase hc'))
    _ = (G.card - 1) * W := by rw [sum_const, card_erase_of_mem hc, smul_eq_mul]

/-- Distinct keys of one width per bus have denominators differing by a nonzero polynomial in beta. -/
theorem denom_diff_ne_zero {W : ℕ} {c c₀ : Key K} (hne : c ≠ c₀) (hc : c.2.length ≤ W)
    (hc₀ : c₀.2.length ≤ W) (hbus : (c.1 : K) = c₀.1 → c.1 = c₀.1)
    (hwidth : c.1 = c₀.1 → c.2.length = c₀.2.length) :
    Polynomial.C ((c.1 : K) - c₀.1) * Polynomial.X ^ W + fingerprintPoly c₀.2 - fingerprintPoly c.2 ≠ 0 := by
  intro h
  by_cases hb : (c.1 : K) = c₀.1
  · have hb' := hbus hb
    rw [hb, sub_self, map_zero, zero_mul, zero_add, sub_eq_zero] at h
    exact hne (Prod.ext hb' (fingerprintPoly_inj (hwidth hb').symm h).symm)
  · have := congrArg (·.coeff W) h
    simp only [coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_fingerprintPoly,
      coeff_zero] at this
    simp only [ite_true] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hc₀),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hc)] at this
    exact hb (by simpa [sub_eq_zero] using this)

/-- **The cleared polynomial is nonzero** when some key has a nonzero net multiplicity. -/
theorem clearedMv_ne_zero {W : ℕ} (G : Finset (Key K)) (M : Key K → K)
    (hG : ∀ c ∈ G, c.2.length ≤ W) (hbus : ∀ c ∈ G, ∀ c' ∈ G, (c.1 : K) = c'.1 → c.1 = c'.1)
    (hwidth : ∀ c ∈ G, ∀ c' ∈ G, c.1 = c'.1 → c.2.length = c'.2.length)
    {c₀ : Key K} (hc₀ : c₀ ∈ G) (hM : M c₀ ≠ 0) : clearedMv W G M ≠ 0 := by
  -- Substitute alpha = fingerprint(e_0) - (b_0 + 1) beta^W, which kills every term but c_0's.
  let φ : MvPolynomial (Fin 2) K →ₐ[K] K[X] :=
    MvPolynomial.aeval ![fingerprintPoly c₀.2 - Polynomial.C ((c₀.1 : K) + 1) * Polynomial.X ^ W,
      Polynomial.X]
  have hφ : ∀ c : Key K, φ (busDenomMv W c.1 c.2) =
      Polynomial.C ((c.1 : K) - c₀.1) * Polynomial.X ^ W + fingerprintPoly c₀.2 - fingerprintPoly c.2 := by
    intro c
    simp [φ, busDenomMv, fingerprintMv, fingerprintPoly, map_sum]
    ring
  intro h0
  have := congrArg φ h0
  rw [map_zero, clearedMv, map_sum, sum_eq_single_of_mem c₀ hc₀ fun c hc hcne => by
    rw [map_mul, map_prod, prod_eq_zero (mem_erase.2 ⟨Ne.symm hcne, hc₀⟩) (by rw [hφ]; simp), mul_zero],
    map_mul, map_prod, MvPolynomial.aeval_C, Polynomial.algebraMap_eq] at this
  refine (mul_eq_zero.1 this).elim (fun h => hM (Polynomial.C_eq_zero.1 h)) fun h => ?_
  obtain ⟨c, hc, h⟩ := prod_eq_zero_iff.1 h
  have hc' := mem_erase.1 hc
  rw [hφ] at h
  exact denom_diff_ne_zero hc'.1 (hG c hc'.2) (hG c₀ hc₀) (hbus c hc'.2 c₀ hc₀)
    (hwidth c hc'.2 c₀ hc₀) h

end Bus

end Plonky3Lean.Proofs.Lookup
