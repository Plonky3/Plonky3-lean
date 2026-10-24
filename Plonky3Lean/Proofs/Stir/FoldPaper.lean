module

public import Plonky3Lean.Proofs.Stir.FoldAlgebra
public import Plonky3Lean.Spec.Stir

@[expose] public section

/-!
# The fold on subgroup coordinates is Definition 4.8 on the coset

On L = s <omega>, the points whose k-th power is (s omega^j)^k are s omega^(j + l M), l < k, for N = k M.

Interpolate at those points and evaluate at gamma.

This is interpolating at omega^(j + l M) and evaluating at gamma / s.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- Interpolating at the image of the nodes is interpolating at the nodes. -/
theorem interpolate_image {k : ℕ} {v : ℕ → K} (hv : Set.InjOn v (range k : Set ℕ)) (f : K → K) :
    Lagrange.interpolate ((range k).image v) id f = Lagrange.interpolate (range k) v (f ∘ v) := by
  refine Lagrange.eq_interpolate_of_eval_eq _ hv ?_ fun i hi => ?_
  · have := Lagrange.degree_interpolate_lt (s := (range k).image v) (v := id) f
      (Set.injOn_id _)
    rwa [card_image_of_injOn hv] at this
  · exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (mem_image_of_mem v hi)

/-- Scaling every node by s and evaluating at gamma is evaluating the unscaled interpolant at gamma / s. -/
theorem eval_interpolate_scale {k : ℕ} {v : ℕ → K} (hv : Set.InjOn v (range k : Set ℕ)) {s : K}
    (hs : s ≠ 0) (r : ℕ → K) (γ : K) :
    (Lagrange.interpolate (range k) (fun l => s * v l) r).eval γ =
      (Lagrange.interpolate (range k) v r).eval (γ / s) := by
  set Q := Lagrange.interpolate (range k) v r
  have hsv : Set.InjOn (fun l => s * v l) (range k : Set ℕ) := fun a ha b hb h =>
    hv ha hb (mul_left_cancel₀ hs h)
  have hQ : Q.comp (C s⁻¹ * X) = Lagrange.interpolate (range k) (fun l => s * v l) r := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hsv ?_ fun i hi => ?_
    · have hdeg := Lagrange.degree_interpolate_lt r hv
      by_cases hQ0 : Q = 0
      · simp only [hQ0, zero_comp]; exact hdeg.trans_le' (by simp)
      · have hlin : (C s⁻¹ * X).natDegree = 1 := by
          rw [natDegree_C_mul_X _ (inv_ne_zero hs)]
        rw [degree_eq_natDegree (fun h => hQ0 ?_)]
        · rw [natDegree_comp, hlin, mul_one, ← degree_eq_natDegree hQ0]; exact hdeg
        · exact (comp_eq_zero_iff.1 h).elim id fun ⟨_, h2⟩ => by
            have := congrArg natDegree h2; simp [hlin] at this
    · simp only [eval_comp, eval_mul, eval_C, eval_X, inv_mul_cancel_left₀ hs]
      exact Lagrange.eval_interpolate_at_node r hv hi
  rw [← hQ, eval_comp]; simp [div_eq_inv_mul]

/-- The points of s <omega> whose k-th power is (s omega^j)^k: s omega^(j + l M) for l < k. -/
theorem fiber_eq {ω s : K} {k M n : ℕ} (hω : IsPrimitiveRoot ω (2 ^ n)) (hN : k * M = 2 ^ n)
    (hs : s ≠ 0) {j : ℕ} (hj : j < M) :
    (cosetSet s ω n).filter (fun x => x ^ k = (s * ω ^ j) ^ k) =
      (range k).image fun l => s * ω ^ (j + l * M) := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    simp only [h, zero_mul] at hN; exact absurd hN.symm (by positivity)
  have hM : 0 < M := by omega
  have hζ : IsPrimitiveRoot (ω ^ k) M := by
    have := hω.pow_of_dvd (p := k) hk.ne' ⟨M, hN.symm⟩
    rwa [← hN, Nat.mul_div_cancel_left _ hk] at this
  have hred : ∀ i, (ω ^ k) ^ i = (ω ^ k) ^ (i % M) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i M, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  ext x
  simp only [cosetSet, mem_filter, mem_image, mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hx⟩
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul] at hx
    have h1 := mul_left_cancel₀ (pow_ne_zero _ hs) hx
    rw [hred i, hred j] at h1
    have h2 := hζ.pow_inj (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) h1
    rw [Nat.mod_eq_of_lt hj] at h2
    refine ⟨i / M, ?_, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    · rw [← h2, Nat.mod_add_div' i M]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨⟨j + l * M, ?_, rfl⟩, ?_⟩
    · rw [← hN]; nlinarith
    · rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, add_mul, pow_add, mul_assoc l, mul_comm M k, hN,
        mul_comm l, pow_mul ω (2 ^ n), hω.pow_eq_one, one_pow, mul_one]

/-- Take any f with value c_i at s omega^i.

The fold of arity k at index j and challenge gamma / s is Fold(f, k, gamma) at (s omega^j)^k.

This is Definition 4.8. -/
theorem foldIdx_eq_fold {ω s : K} {k M n : ℕ} (hω : IsPrimitiveRoot ω (2 ^ n)) (hN : k * M = 2 ^ n)
    (hs : s ≠ 0) (c : List K) (f : K → K) (hf : ∀ i < 2 ^ n, f (s * ω ^ i) = c.getD i 0)
    {j : ℕ} (hj : j < M) (γ : K) :
    foldIdx ω c M k j (γ / s) = Spec.Stir.fold (cosetSet s ω n) f k γ ((s * ω ^ j) ^ k) := by
  have hidx : ∀ l < k, j + l * M < 2 ^ n := fun l hl => by rw [← hN]; nlinarith
  have hv : Set.InjOn (fun l => ω ^ (j + l * M)) (range k : Set ℕ) := by
    intro a ha b hb h
    have := hω.pow_inj (hidx a (mem_range.1 ha)) (hidx b (mem_range.1 hb)) h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < M) (by omega)
  have hsv : Set.InjOn (fun l => s * ω ^ (j + l * M)) (range k : Set ℕ) := fun a ha b hb h =>
    hv ha hb (mul_left_cancel₀ hs h)
  unfold Spec.Stir.fold
  rw [fiber_eq hω hN hs hj, interpolate_image hsv, foldIdx]
  rw [← eval_interpolate_scale hv hs]
  congr 1
  refine Lagrange.interpolate_eq_of_values_eq_on _ _ fun l hl => ?_
  simp [hf _ (hidx l (mem_range.1 hl))]

/-- Take any f with value r_l at s omega^(j + l M).

Interpolate the fiber values r_l at omega^(j + l M) and evaluate at gamma / s.

The result is Fold(f, k, gamma) at (s omega^j)^k. -/
theorem interp_fiber_eq_fold {ω s : K} {k M n : ℕ} (hω : IsPrimitiveRoot ω (2 ^ n))
    (hN : k * M = 2 ^ n) (hs : s ≠ 0) (r : ℕ → K) (f : K → K)
    {j : ℕ} (hj : j < M) (hf : ∀ l < k, f (s * ω ^ (j + l * M)) = r l) (γ : K) :
    (Lagrange.interpolate (range k) (fun l => ω ^ (j + l * M)) r).eval (γ / s) =
      Spec.Stir.fold (cosetSet s ω n) f k γ ((s * ω ^ j) ^ k) := by
  have hidx : ∀ l < k, j + l * M < 2 ^ n := fun l hl => by rw [← hN]; nlinarith
  have hv : Set.InjOn (fun l => ω ^ (j + l * M)) (range k : Set ℕ) := by
    intro a ha b hb h
    have := hω.pow_inj (hidx a (mem_range.1 ha)) (hidx b (mem_range.1 hb)) h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < M) (by omega)
  have hsv : Set.InjOn (fun l => s * ω ^ (j + l * M)) (range k : Set ℕ) := fun a ha b hb h =>
    hv ha hb (mul_left_cancel₀ hs h)
  unfold Spec.Stir.fold
  rw [fiber_eq hω hN hs hj, interpolate_image hsv, ← eval_interpolate_scale hv hs]
  congr 1
  refine Lagrange.interpolate_eq_of_values_eq_on _ _ fun l hl => ?_
  simp [hf _ (mem_range.1 hl)]

end Plonky3Lean.Proofs.Stir
