module

public import Plonky3Lean.Spec.Bus
public import Plonky3Lean.Proofs.MultilinearUtil.Unique
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Ring.NNRat

@[expose] public section

/-!
# The grand-product identity and its soundness count

Two lists of tuples of 2^m slots have equal grand-product polynomials exactly when they are permutations of each other.

The proof views the product as a polynomial in the offset over the ring of polynomials in the point.

That ring is a domain, so a product of linear factors determines its roots with multiplicity.

The multilinear extension of a tuple of 2^m slots determines the tuple.

Unequal multisets of at most N tuples then agree on at most max(1, m) N |K|^m of the |K|^(m + 1) challenges, by Schwartz-Zippel.
-/

namespace Plonky3Lean.Proofs.Bus

open Plonky3Lean.Spec.Bus Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  MvPolynomial Finset

variable {K : Type _} [Field K]

/-- The table of a polynomial on the cube: the values at the vertices 0 to 2^m - 1. -/
noncomputable def cubeValues (m : ℕ) (p : MvPolynomial (Fin m) K) : List K :=
  (List.range (2 ^ m)).map fun b => eval (vertexFn m b) p

/-- A tuple of 2^m slots is the table of its multilinear extension. -/
theorem cubeValues_mlePoly {m : ℕ} {t : List K} (ht : t.length = 2 ^ m) :
    cubeValues m (mlePoly t m) = t :=
  List.ext_getElem (by simp [cubeValues, ht]) fun b hb hb' => by
    simp only [cubeValues, List.getElem_map, List.getElem_range]
    rw [eval_mlePoly_vertex t (by simpa [cubeValues] using hb), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hb', Option.getD_some]

theorem finSuccEquiv_fingerprintPoly (m : ℕ) (t : List K) :
    finSuccEquiv K m (fingerprintPoly m t) = Polynomial.C (mlePoly t m) := by
  have h : ((finSuccEquiv K m : _ →ₐ[K] _).comp (rename Fin.succ)) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (Polynomial (MvPolynomial (Fin m) K)) :=
    algHom_ext fun i => by simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h (mlePoly t m)

theorem finSuccEquiv_productPoly (m : ℕ) (ts : List (List K)) :
    finSuccEquiv K m (productPoly m ts) =
      ((ts.map (mlePoly · m) : Multiset _).map fun a => Polynomial.X - Polynomial.C a).prod := by
  simp [productPoly, map_list_prod, finSuccEquiv_fingerprintPoly, finSuccEquiv_X_zero,
    Function.comp_def]

/-- **The multiset identity.** Tuples of 2^m slots have equal grand-product polynomials exactly when the two lists are permutations of each other. -/
theorem productPoly_eq_iff {m : ℕ} {ts ss : List (List K)} (hts : ∀ t ∈ ts, t.length = 2 ^ m)
    (hss : ∀ s ∈ ss, s.length = 2 ^ m) : productPoly m ts = productPoly m ss ↔ ts.Perm ss := by
  refine ⟨fun h => ?_, fun h => (h.map _).prod_eq⟩
  have hroots := congrArg Polynomial.roots (congrArg (finSuccEquiv K m) h)
  simp only [finSuccEquiv_productPoly, Polynomial.roots_multiset_prod_X_sub_C,
    Multiset.coe_eq_coe] at hroots
  have back : ∀ l : List (List K), (∀ t ∈ l, t.length = 2 ^ m) →
      (l.map (mlePoly · m)).map (cubeValues m) = l := fun l hl => by
    rw [List.map_map]
    exact (List.map_congr_left fun t ht => cubeValues_mlePoly (hl t ht)).trans (List.map_id _)
  simpa only [back ts hts, back ss hss] using hroots.map (cubeValues m)

/-! ## Evaluation and degree -/

theorem eval_fingerprintPoly {m : ℕ} (t : List K) (γ : K) (r : Fin m → K) :
    eval (Fin.cons γ r) (fingerprintPoly m t) = fingerprint t (List.ofFn r) := by
  rw [fingerprintPoly, eval_rename]
  exact eval_mlePoly t r

/-- At the offset gamma and the point r, the product polynomial is the grand product. -/
theorem eval_productPoly {m : ℕ} (ts : List (List K)) (γ : K) (r : Fin m → K) :
    eval (Fin.cons γ r) (productPoly m ts) = grandProduct γ (List.ofFn r) ts := by
  simp [productPoly, grandProduct, map_list_prod, eval_fingerprintPoly, Function.comp_def]
  rfl

theorem totalDegree_mlePoly_le (t : List K) (m : ℕ) : (mlePoly t m).totalDegree ≤ m := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i : Fin m, (if b.testBit (m - 1 - i) then X i else (1 - X i : MvPolynomial (Fin m) K)).totalDegree
      ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => by
        split
        · exact (totalDegree_X i).le
        · exact (totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_X i).le)
    _ = m := by simp

theorem totalDegree_productPoly_le (m : ℕ) (ts : List (List K)) :
    (productPoly m ts).totalDegree ≤ max 1 m * ts.length := by
  refine (totalDegree_list_prod _).trans ?_
  rw [List.map_map, mul_comm, ← smul_eq_mul]
  conv_rhs => rw [← List.length_map (f := totalDegree ∘ fun t => X 0 - fingerprintPoly m t)]
  refine List.sum_le_length_nsmul _ _ fun d hd => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hd
  refine (totalDegree_sub _ _).trans (max_le_max (totalDegree_X _).le ?_)
  exact (totalDegree_rename_le _ _).trans (totalDegree_mlePoly_le t m)

/-! ## The soundness count -/

/-- **Schwartz-Zippel** over the offset and the point: a nonzero polynomial of total degree d vanishes on at most d |K|^m of the |K|^(m + 1) challenges. -/
theorem card_roots_le [Fintype K] [DecidableEq K] {m : ℕ} {P : MvPolynomial (Fin (m + 1)) K}
    (hP : P ≠ 0) :
    #{x : K × (Fin m → K) | eval (Fin.cons x.1 x.2) P = 0} ≤
      P.totalDegree * Fintype.card K ^ m := by
  have hsz := schwartz_zippel_totalDegree hP (univ : Finset K)
  set R := #{f ∈ Fintype.piFinset fun _ : Fin (m + 1) => (univ : Finset K) | eval f P = 0}
  have hq : (0 : ℚ≥0) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [card_univ, div_le_div_iff₀ (by positivity) hq] at hsz
  have hR : R ≤ P.totalDegree * Fintype.card K ^ m := by
    have : (R : ℚ≥0) * Fintype.card K ≤ (P.totalDegree * Fintype.card K ^ m) * Fintype.card K := by
      calc (R : ℚ≥0) * Fintype.card K ≤ P.totalDegree * (Fintype.card K : ℚ≥0) ^ (m + 1) := hsz
        _ = _ := by ring
    exact_mod_cast le_of_mul_le_mul_right this hq
  refine le_trans (card_le_card_of_injOn (fun x => Fin.cons x.1 x.2) ?_ ?_) hR
  · intro x hx; simp_all
  · intro x _ y _ h
    exact Prod.ext (by simpa using congrFun h 0) (funext fun i => by simpa using congrFun h i.succ)

/-- **Soundness of the grand product.** Two lists of at most N tuples of 2^m slots, not permutations of each other, have equal grand products on at most max(1, m) N |K|^m of the |K|^(m + 1) pairs of an offset and a point. -/
theorem card_bad_challenges_le [Fintype K] [DecidableEq K] {m N : ℕ} {ts ss : List (List K)}
    (hts : ∀ t ∈ ts, t.length = 2 ^ m) (hss : ∀ s ∈ ss, s.length = 2 ^ m) (hperm : ¬ ts.Perm ss)
    (hN : ts.length ≤ N) (hN' : ss.length ≤ N) :
    #{x : K × (Fin m → K) | grandProduct x.1 (List.ofFn x.2) ts = grandProduct x.1 (List.ofFn x.2) ss}
      ≤ max 1 m * N * Fintype.card K ^ m := by
  have hP : productPoly m ts - productPoly m ss ≠ 0 :=
    sub_ne_zero.2 (mt (productPoly_eq_iff hts hss).1 hperm)
  have hdeg : (productPoly m ts - productPoly m ss).totalDegree ≤ max 1 m * N :=
    (totalDegree_sub _ _).trans (max_le
      ((totalDegree_productPoly_le m ts).trans (Nat.mul_le_mul_left _ hN))
      ((totalDegree_productPoly_le m ss).trans (Nat.mul_le_mul_left _ hN')))
  refine le_trans (card_le_card fun x hx => ?_) ((card_roots_le hP).trans
    (Nat.mul_le_mul_right _ hdeg))
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  rw [map_sub, eval_productPoly, eval_productPoly, hx, sub_self]

end Plonky3Lean.Proofs.Bus
