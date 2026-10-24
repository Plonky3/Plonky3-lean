module

public import Plonky3Lean.Proofs.MultiStark.Ext
public import Plonky3Lean.Proofs.Sumcheck.Prover

@[expose] public section

/-!
# The fraction tree

The fractional sum-check of Papini and Haböck (eprint 2023/1284), Section 3.

Each level of the tree adds the two halves of the level below.

Two quantities do not move from level to level:

- the product of the denominators
- the sum of the fractions, while no denominator vanishes.

So the root is (0, d) with d nonzero exactly when every leaf denominator is nonzero and the leaves sum to zero.

One layer of the reduction is a sum-check over the polynomial

```text
    g(X) = eq(rho, X) * (d1(X) n0(X) + d0(X) n1(X) + lambda d0(X) d1(X))
```

Here n0, d0 are the extensions of the low half of the level below, and n1, d1 of the high half.

Its cube sum is the batched claim N(rho) + lambda D(rho) of the level above.

Its degree in each variable is 3.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Plonky3Lean.Spec.Sumcheck MvPolynomial Finset

variable {K : Type _} [Field K]

/-! ## Levels -/

theorem fracLevel_top (t : ℕ → K × K) {n k : ℕ} (h : n ≤ k) : fracLevel t n k = t := by
  rw [fracLevel]; simp [h]

theorem fracLevel_step (t : ℕ → K × K) {n k : ℕ} (h : k < n) (x : ℕ) :
    fracLevel t n k x = addFrac (fracLevel t n (k + 1) x) (fracLevel t n (k + 1) (2 ^ k + x)) := by
  rw [fracLevel]; simp [show ¬ n ≤ k by omega]

/-- The product of the denominators is the same at every level. -/
theorem prod_den_level (t : ℕ → K × K) (n : ℕ) : ∀ d k, k + d = n →
    ∏ x ∈ range (2 ^ k), (fracLevel t n k x).2 = ∏ x ∈ range (2 ^ n), (t x).2
  | 0, k, h => by
    obtain rfl : n = k := (by omega)
    rw [fracLevel_top t le_rfl]
  | d + 1, k, h => by
    rw [← prod_den_level t n d (k + 1) (by omega), pow_succ, mul_two, prod_range_add,
      ← prod_mul_distrib]
    exact prod_congr rfl fun x _ => by rw [fracLevel_step t (by omega)]; rfl

/-- With every leaf denominator nonzero, every denominator of every level is nonzero. -/
theorem den_level_ne_zero (t : ℕ → K × K) {n : ℕ} (ht : ∀ x < 2 ^ n, (t x).2 ≠ 0) {k : ℕ}
    (hk : k ≤ n) {x : ℕ} (hx : x < 2 ^ k) : (fracLevel t n k x).2 ≠ 0 := by
  have h := prod_den_level t n (n - k) k (by omega)
  have hne : ∏ x ∈ range (2 ^ n), (t x).2 ≠ 0 :=
    prod_ne_zero_iff.mpr fun x hx => ht x (mem_range.mp hx)
  rw [← h] at hne
  exact prod_ne_zero_iff.mp hne x (mem_range.mpr hx)

/-- With every leaf denominator nonzero, the sum of the fractions is the same at every level. -/
theorem sum_frac_level (t : ℕ → K × K) {n : ℕ} (ht : ∀ x < 2 ^ n, (t x).2 ≠ 0) : ∀ d k, k + d = n →
    ∑ x ∈ range (2 ^ k), (fracLevel t n k x).1 / (fracLevel t n k x).2 =
      ∑ x ∈ range (2 ^ n), (t x).1 / (t x).2
  | 0, k, h => by
    obtain rfl : n = k := (by omega)
    rw [fracLevel_top t le_rfl]
  | d + 1, k, h => by
    rw [← sum_frac_level t ht d (k + 1) (by omega), pow_succ, mul_two, sum_range_add,
      ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hx := mem_range.mp hx
    have h0 := den_level_ne_zero t ht (k := k + 1) (by omega) (x := x) (by rw [pow_succ]; omega)
    have h1 := den_level_ne_zero t ht (k := k + 1) (by omega) (x := 2 ^ k + x)
      (by rw [pow_succ]; omega)
    rw [fracLevel_step t (by omega), addFrac, div_add_div _ _ h0 h1]
    ring_nf

/-- **The root.**

The root is a zero numerator over a nonzero denominator exactly when two things hold:

- every leaf denominator is nonzero
- the leaves sum to zero. -/
theorem root_iff (t : ℕ → K × K) (n : ℕ) :
    (fracLevel t n 0 0).1 = 0 ∧ (fracLevel t n 0 0).2 ≠ 0 ↔
      (∀ x < 2 ^ n, (t x).2 ≠ 0) ∧ ∑ x ∈ range (2 ^ n), (t x).1 / (t x).2 = 0 := by
  have hprod := prod_den_level t n n 0 (by omega)
  simp only [pow_zero, range_one, prod_singleton] at hprod
  have hden : (fracLevel t n 0 0).2 ≠ 0 ↔ ∀ x < 2 ^ n, (t x).2 ≠ 0 := by
    rw [hprod, prod_ne_zero_iff]; simp
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ⟨?_, hden.mpr h1⟩⟩
  · have ht := hden.mp h2
    refine ⟨ht, ?_⟩
    have hs := sum_frac_level t ht n 0 (by omega)
    simp only [pow_zero, range_one, sum_singleton, h1, zero_div] at hs
    exact hs.symm
  · have hs := sum_frac_level t h1 n 0 (by omega)
    simp only [pow_zero, range_one, sum_singleton, h2] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right (hden.mpr h1)

/-! ## One layer -/

/-- The batched claim of a level is the extension of the batched sum of its two children. -/
theorem batch_level (t : ℕ → K × K) {n k : ℕ} (hk : k < n) (lam : K) (ρ : List K) :
    rowExt (fun x => (fracLevel t n k x).1) ρ + lam * rowExt (fun x => (fracLevel t n k x).2) ρ =
      rowExt (fun x => (fracLevel t n (k + 1) (2 ^ k + x)).2 * (fracLevel t n (k + 1) x).1 +
        (fracLevel t n (k + 1) x).2 * (fracLevel t n (k + 1) (2 ^ k + x)).1 +
        lam * (fracLevel t n (k + 1) x).2 * (fracLevel t n (k + 1) (2 ^ k + x)).2) ρ := by
  unfold rowExt
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by simp only [fracLevel_step t hk, addFrac]; ring

/-- The claim update: the extension at (b, r) is the line through the two halves at r. -/
theorem ext_cons_line (f : ℕ → K) (b : K) (r : List K) :
    rowExt f (b :: r) =
      rowExt f r + b * (rowExt (fun x => f (2 ^ r.length + x)) r - rowExt f r) := by
  rw [ext_cons]; ring

/-! ## The layer polynomial -/

/-- The table of f on the k-cube. -/
def cubeList (f : ℕ → K) (k : ℕ) : List K := (List.range (2 ^ k)).map f

/-- The sum-check polynomial of one layer, over k variables. -/
noncomputable def layerPoly (k : ℕ) (ρ : List K) (lam : K) (n0 d0 n1 d1 : ℕ → K) :
    MvPolynomial (Fin k) K :=
  mlePoly (eqTable ρ) k * (mlePoly (cubeList d1 k) k * mlePoly (cubeList n0 k) k +
    mlePoly (cubeList d0 k) k * mlePoly (cubeList n1 k) k +
    C lam * mlePoly (cubeList d0 k) k * mlePoly (cubeList d1 k) k)

theorem mle_map_mul_right' (a : K) (f r : List K) : mle (f.map (· * a)) r = mle f r * a := by
  simp only [mle, sum_mul, getD_map_mul_right]
  exact sum_congr rfl fun _ _ => by ring

/-- The extension of the table of eq(p, .) is eq(p, .). -/
theorem mle_eqTable' : ∀ (p y : List K), p.length = y.length → mle (eqTable p) y = eq p y
  | [], [], _ => by simp
  | c :: p, a :: y, h => by
    have h' : p.length = y.length := by simpa using h
    have hl : ((eqTable p).map (· * (1 - c))).length = 2 ^ y.length := by simp [h']
    rw [mle_cons, eqTable_cons, List.take_left' hl, List.drop_left' (by simpa using hl),
      mle_map_mul_right', mle_map_mul_right', mle_eqTable' p y h', eq_cons]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem individualDegreeLE_layerPoly (k : ℕ) (ρ : List K) (lam : K) (n0 d0 n1 d1 : ℕ → K) :
    IndividualDegreeLE (layerPoly k ρ lam n0 d0 n1 d1) 3 := fun i => by
  have hm := fun (f : List K) => mlePoly_isMultilinear f k i
  unfold layerPoly
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (hm _) ((degreeOf_add_le _ _ _).trans (max_le
    ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_)) ?_))).trans (by norm_num : 1 + 2 ≤ 3)
  · exact (degreeOf_mul_le _ _ _).trans (add_le_add (hm _) (hm _))
  · exact (degreeOf_mul_le _ _ _).trans (add_le_add (hm _) (hm _))
  · refine (degreeOf_mul_le _ _ _).trans (add_le_add ((degreeOf_mul_le _ _ _).trans ?_) (hm _))
    rw [degreeOf_C, zero_add]; exact hm _

/-- At a point r, the layer polynomial is eq(rho, r) times the batched sum of the children there. -/
theorem eval_layerPoly {k : ℕ} {ρ : List K} (hρ : ρ.length = k) (lam : K) (n0 d0 n1 d1 : ℕ → K)
    (r : Fin k → K) :
    eval r (layerPoly k ρ lam n0 d0 n1 d1) = eq ρ (List.ofFn r) *
      (rowExt d1 (List.ofFn r) * rowExt n0 (List.ofFn r) +
        rowExt d0 (List.ofFn r) * rowExt n1 (List.ofFn r) +
        lam * rowExt d0 (List.ofFn r) * rowExt d1 (List.ofFn r)) := by
  simp only [layerPoly, cubeList, map_mul, map_add, eval_C, ← ext_eq_eval_mlePoly]
  rw [eval_mlePoly, mle_eqTable' ρ _ (by simp [hρ])]

variable [DecidableEq K]

/-- The cube sum of the layer polynomial is the extension at rho of the batched sum of the children. -/
theorem cubeSum_layerPoly {k : ℕ} {ρ : List K} (hρ : ρ.length = k) (lam : K) (n0 d0 n1 d1 : ℕ → K) :
    cubeSum (layerPoly k ρ lam n0 d0 n1 d1) =
      rowExt (fun x => d1 x * n0 x + d0 x * n1 x + lam * d0 x * d1 x) ρ := by
  subst hρ
  rw [cubeSum, Plonky3Lean.Proofs.Sumcheck.sum_cube_eq_sum_vertex]
  refine sum_congr rfl fun x hx => ?_
  have hx := mem_range.mp hx
  have hl : ∀ f : ℕ → K, (cubeList f ρ.length).getD x 0 = f x := fun f => by
    simp [cubeList, List.getD_eq_getElem?_getD, hx]
  simp only [layerPoly, map_mul, map_add, eval_C, eval_mlePoly_vertex _ hx, hl]
  simp [eqTable, List.getD_eq_getElem?_getD, hx]

end Plonky3Lean.Proofs.MultiStark
