module

public import Plonky3Lean.Proofs.UniStark.Semantics
public import Plonky3Lean.Proofs.Commit.Domain
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.MvPolynomial.Tower

@[expose] public section

/-!
# The constraint polynomial and its quotient

On the coset s H, the STARK's univariate assignment takes the STARK's row values.

So on a trace that satisfies the STARK's relation, the combined constraint polynomial vanishes on s H.

The vanishing polynomial Z then divides it, and the quotient is C_alpha s^n / Z, of degree deg C_alpha - n.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark

/-! ## Evaluating the assignment -/

section eval

variable {F K : Type _} [Field F] [Field K] [Algebra F K]

theorem getD_map_zero {α β : Type _} [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0) (l : List α)
    (i : ℕ) : (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [← hf, List.getD_map]

/-- Evaluating a substituted constraint is evaluating the constraint at the evaluated polynomials. -/
theorem eval_aeval (σ : Var → K[X]) (c : MvPolynomial Var F) (x : K) :
    (MvPolynomial.aeval σ c).eval x = MvPolynomial.aeval (fun v => (σ v).eval x) c := by
  have := congrArg (· c)
    (MvPolynomial.comp_aeval (R := F) (f := σ) ((Polynomial.aeval x).restrictScalars F))
  simpa using this

/-- The combined polynomial at x is the combination of the constraint values at x. -/
theorem eval_combinedPoly (α : K) (σ : Var → K[X]) (C : List (MvPolynomial Var F)) (x : K) :
    (combinedPoly α σ C).eval x =
      combine α (C.map (MvPolynomial.aeval fun v => (σ v).eval x)) := by
  simp only [combinedPoly, combine, eval_finsetSum, eval_mul, eval_C, eval_aeval, List.length_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_map_zero _ (map_zero _)]

/-- The Lagrange basis of a coset maps to the Lagrange basis of the image coset. -/
theorem lagrange_map (f : F →+* K) (s ω : F) (k : ℕ) (i : Fin (2 ^ k)) :
    (lagrange s ω k i).map f = lagrange (f s) (f ω) k i := by
  simp [lagrange, Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod, cosetPoints,
    map_inv₀]

end eval

/-! ## The assignment on the coset -/

section coset

variable {F : Type _} [Field F]

theorem eval_lagrange_node {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    (j : Fin (2 ^ k)) {i : ℕ} (hi : i < 2 ^ k) :
    (lagrange s ω k j).eval (s * ω ^ i) = if i = j.val then 1 else 0 := by
  classical
  have hinj : Set.InjOn (cosetPoints s ω k) (univ : Finset (Fin (2 ^ k))) :=
    (Plonky3Lean.Proofs.Commit.cosetPoints_injective hω hs).injOn
  have hx : s * ω ^ i = cosetPoints s ω k ⟨i, hi⟩ := rfl
  rw [hx, lagrange]
  split_ifs with h
  · obtain rfl : (⟨i, hi⟩ : Fin (2 ^ k)) = j := Fin.ext h
    exact Lagrange.eval_basis_self hinj (mem_univ _)
  · exact Lagrange.eval_basis_of_ne (fun e => h (congrArg Fin.val e).symm) (mem_univ _)

/-- On point s omega^i of the coset, the STARK's assignment takes the STARK's values on row i of a trace it interpolates. -/
theorem eval_starkAssign {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ k) {main prep : ℕ → F[X]} {pub : ℕ → F}
    {periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ k, ∀ c, (main c).eval (s * ω ^ i) = T.main i c)
    (hprep : ∀ i < 2 ^ k, ∀ c, (prep c).eval (s * ω ^ i) = T.prep i c)
    (hpub : ∀ j, pub j = T.pub j)
    (hper : ∀ i < 2 ^ k, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    {i : ℕ} (hi : i < 2 ^ k) (v : Var) :
    (starkAssign s ω k main prep pub periodic v).eval (s * ω ^ i) = starkRowEnv T ω i v := by
  have hnext : ω * (s * ω ^ i) = s * ω ^ ((i + 1) % 2 ^ k) := by
    rw [hω.eq_orderOf, pow_mod_orderOf]; ring
  have hlt : (i + 1) % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  rcases v with ⟨o, c⟩ | ⟨o, c⟩ | j | j | _ | _ | _
  · fin_cases o
    · simp [starkAssign, starkRowEnv, rowEnv, hmain i hi]
    · simp [starkAssign, starkRowEnv, rowEnv, eval_comp, hnext, hmain _ hlt, hT]
  · fin_cases o
    · simp [starkAssign, starkRowEnv, rowEnv, hprep i hi]
    · simp [starkAssign, starkRowEnv, rowEnv, eval_comp, hnext, hprep _ hlt, hT]
  · simp [starkAssign, starkRowEnv, rowEnv, hpub]
  · simp [starkAssign, starkRowEnv, rowEnv, hper i hi]
  · simp only [starkAssign, starkRowEnv, eval_mul, eval_C, eval_lagrange_node hω hs _ hi, hT]
    split_ifs <;> simp_all
  · simp only [starkAssign, starkRowEnv, eval_mul, eval_C, eval_lagrange_node hω hs _ hi, hT]
    split_ifs <;> simp_all
  · simp only [starkAssign, starkRowEnv, eval_mul, eval_C, eval_sub, eval_X, hT]
    field_simp

end coset

/-! ## Divisibility by the vanishing polynomial -/

section vanishing

variable {K : Type _} [Field K]

/-- A polynomial that vanishes on every point of the coset is a multiple of its vanishing polynomial. -/
theorem vanishing_dvd {s ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) {p : K[X]}
    (hp : ∀ i < 2 ^ k, p.eval (s * ω ^ i) = 0) : vanishing s ω k ∣ p := by
  classical
  rw [vanishing, Lagrange.nodal]
  have hinj := Plonky3Lean.Proofs.Commit.cosetPoints_injective hω hs
  refine Finset.prod_dvd_of_coprime (fun i _ j _ hij => pairwise_coprime_X_sub_C hinj hij)
    fun i _ => dvd_iff_isRoot.mpr ?_
  exact hp i i.isLt

/-- The quotient the prover commits to: s^n C_alpha / Z, for the monic vanishing polynomial Z. -/
noncomputable def quotientPoly (s ω : K) (k : ℕ) (P : K[X]) : K[X] :=
  C (s ^ 2 ^ k) * (P /ₘ vanishing s ω k)

theorem vanishing_monic (s ω : K) (k : ℕ) : (vanishing s ω k).Monic := Lagrange.nodal_monic

theorem natDegree_vanishing (s ω : K) (k : ℕ) : (vanishing s ω k).natDegree = 2 ^ k := by
  simp [vanishing, Lagrange.natDegree_nodal]

/-- When Z divides P, off the coset the quotient is s^n P / Z. -/
theorem eval_quotientPoly {s ω : K} {k : ℕ} {P : K[X]} (hdvd : vanishing s ω k ∣ P) {x : K}
    (hx : (vanishing s ω k).eval x ≠ 0) :
    (quotientPoly s ω k P).eval x = s ^ 2 ^ k * (P.eval x / (vanishing s ω k).eval x) := by
  obtain ⟨r, rfl⟩ := hdvd
  rw [quotientPoly, mul_divByMonic_cancel_left _ (vanishing_monic s ω k), eval_mul, eval_C, eval_mul]
  field_simp

/-- A combined polynomial below (c + 1) n has a quotient below c n, for c >= 1. -/
theorem degree_quotientPoly_lt {s ω : K} {k c : ℕ} (hc : 1 ≤ c) {P : K[X]}
    (hP : P.natDegree < (c + 1) * 2 ^ k) : (quotientPoly s ω k P).degree < (c * 2 ^ k : ℕ) := by
  refine degree_le_natDegree.trans_lt ?_
  rw [Nat.cast_lt]
  refine (natDegree_C_mul_le _ _).trans_lt ?_
  rw [natDegree_divByMonic _ (vanishing_monic s ω k), natDegree_vanishing]
  have h1 : 0 < c * 2 ^ k := Nat.mul_pos hc (by positivity)
  rw [add_mul, one_mul] at hP
  generalize c * 2 ^ k = N at h1 hP ⊢
  omega

end vanishing

/-! ## A satisfying trace gives a polynomial quotient -/

section satisfying

variable {F K : Type _} [Field F] [Field K] [Algebra F K]

theorem combine_eq_zero (α : K) {vs : List K} (h : ∀ v ∈ vs, v = 0) : combine α vs = 0 :=
  Finset.sum_eq_zero fun i hi => by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi), h _ (List.getElem_mem _), mul_zero]

/-- The STARK's assignment, with its polynomials read in the extension. -/
noncomputable def starkAssignK (s ω : F) (k : ℕ) (main prep : ℕ → F[X]) (pub : ℕ → F)
    (periodic : ℕ → F[X]) (v : Var) : K[X] :=
  (starkAssign s ω k main prep pub periodic v).map (algebraMap F K)

/-- On a trace that satisfies the STARK's relation, the vanishing polynomial divides the combined polynomial. -/
theorem vanishing_dvd_combinedPoly {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ k) {main prep : ℕ → F[X]} {pub : ℕ → F}
    {periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ k, ∀ c, (main c).eval (s * ω ^ i) = T.main i c)
    (hprep : ∀ i < 2 ^ k, ∀ c, (prep c).eval (s * ω ^ i) = T.prep i c)
    (hpub : ∀ j, pub j = T.pub j)
    (hper : ∀ i < 2 ^ k, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    {C : List (MvPolynomial Var F)} (hsat : SatisfiesStark C T ω) (α : K) :
    vanishing (algebraMap F K s) (algebraMap F K ω) k ∣
      combinedPoly α (starkAssignK s ω k main prep pub periodic) C := by
  refine vanishing_dvd (hω.map_of_injective (algebraMap F K).injective)
    ((_root_.map_ne_zero _).mpr hs) fun i hi => ?_
  rw [eval_combinedPoly]
  refine combine_eq_zero α fun v hv => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  have henv : (fun v => (starkAssignK (K := K) s ω k main prep pub periodic v).eval
      (algebraMap F K s * algebraMap F K ω ^ i)) = algebraMap F K ∘ starkRowEnv T ω i := by
    funext v
    rw [starkAssignK, ← map_pow, ← map_mul, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval,
      eval_starkAssign hω hs hT hmain hprep hpub hper hi v, Function.comp_apply]
  rw [henv, MvPolynomial.aeval_algebraMap_apply]
  simpa using hsat i (hT ▸ hi) c hc

end satisfying

end Plonky3Lean.Proofs.UniStark
