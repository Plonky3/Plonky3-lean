module

public import P3Sumcheck
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# The prefix round kernel

The tiled loop with its tail computes the two sums over the half-split:

```text
    h(0)   = sum_{i < N/2} w[i] f[i]
    h(inf) = sum_{i < N/2} (w[N/2 + i] - w[i]) (f[N/2 + i] - f[i])
```
-/

namespace Plonky3Lean.Proofs.Sumcheck

open Finset p3_sumcheck.strategy.mirror

variable {A : Type _} [Field A]

theorem foldl_round_reduce (g : ℕ → A × A) (init : A × A) :
    ∀ m, (List.range m).foldl (fun acc j => round_reduce acc (g j)) init =
      (init.1 + ∑ j ∈ range m, (g j).1, init.2 + ∑ j ∈ range m, (g j).2)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_round_reduce g init m]
    simp [round_reduce, sum_range_succ, add_assoc]

theorem foldl_round_step (e0 e1 w0 w1 : ℕ → A) (init : A × A) :
    ∀ m, (List.range m).foldl (fun acc t => round_step acc (e0 t) (e1 t) (w0 t) (w1 t)) init =
      (init.1 + ∑ t ∈ range m, w0 t * e0 t, init.2 + ∑ t ∈ range m, (w1 t - w0 t) * (e1 t - e0 t))
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_round_step e0 e1 w0 w1 init m]
    simp [round_step, sum_range_succ, add_assoc]

theorem sum_tiles {M : Type _} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∀ m, ∑ j ∈ range m, ∑ t ∈ range k, f (j * k + t) = ∑ i ∈ range (m * k), f i
  | 0 => by simp
  | m + 1 => by rw [sum_range_succ, sum_tiles f k m, Nat.succ_mul, sum_range_add]

/-- Entry t of tile j of the first half is entry jK + t of the list. -/
theorem getD_tile_lo (l : List A) {half j t : ℕ} (ht : t < K) (hj : j * K + t < half) :
    (((l.take half).drop (j * K)).take K).getD t 0 = l.getD (j * K + t) 0 := by
  simp [List.getD_eq_getElem?_getD, ht, hj]

/-- Entry t of tile j of the second half is entry half + jK + t of the list. -/
theorem getD_tile_hi (l : List A) {half j t : ℕ} (ht : t < K) :
    (((l.drop half).drop (j * K)).take K).getD t 0 = l.getD (half + (j * K + t)) 0 := by
  simp [List.getD_eq_getElem?_getD, ht, add_assoc]

theorem getD_zipWith_sub {a b : List A} {i : ℕ} (ha : i < a.length) (hb : i < b.length) :
    (List.zipWith (· - ·) a b).getD i 0 = a.getD i 0 - b.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]

/-- The prefix round kernel gives the constant term and the leading coefficient over the half-split.

This holds for equal even lengths. -/
theorem sumcheck_coefficients_prefix_eq (evals weights : List A) (hl : evals.length = weights.length)
    (he : evals.length % 2 = 0) :
    sumcheck_coefficients_prefix evals weights =
      some (∑ i ∈ range (evals.length / 2), weights.getD i 0 * evals.getD i 0,
        ∑ i ∈ range (evals.length / 2), (weights.getD (evals.length / 2 + i) 0 - weights.getD i 0) *
          (evals.getD (evals.length / 2 + i) 0 - evals.getD i 0)) := by
  unfold sumcheck_coefficients_prefix
  have hc : ¬(evals.length ≠ weights.length ∨ evals.length % 2 ≠ 0) := by omega
  simp only [hc, ↓reduceIte]
  rw [foldl_round_reduce, foldl_round_step]
  have hel : evals.length = 2 * (evals.length / 2) := by omega
  have hwl : weights.length = 2 * (evals.length / 2) := by omega
  generalize evals.length / 2 = half at hel hwl ⊢
  have hs {M : Type _} [AddCommMonoid M] (f : ℕ → M) :
      ∑ i ∈ range half, f i = ∑ j ∈ range (half / K), ∑ t ∈ range K, f (j * K + t) +
        ∑ t ∈ range (half - half / K * K), f (half / K * K + t) := by
    rw [sum_tiles, ← sum_range_add, Nat.add_sub_cancel' (Nat.div_mul_le_self half K)]
  have hK : ∀ j ∈ range (half / K), ∀ t ∈ range K, j * K + t < half := fun j hj t ht => by
    have h1 := Nat.div_mul_le_self half K
    have h2 : (j + 1) * K ≤ half / K * K := Nat.mul_le_mul_right K (mem_range.mp hj)
    rw [add_mul, one_mul] at h2
    have := mem_range.mp ht
    omega
  have htail : ∀ t ∈ range (half - half / K * K), half / K * K + t < half := fun t ht => by
    have := mem_range.mp ht; omega
  have hlen {l : List A} (hl : l.length = 2 * half) {j t : ℕ} (hjt : j * K + t < half) (ht : t < K) :
      t < (((l.drop half).drop (j * K)).take K).length ∧ t < (((l.take half).drop (j * K)).take K).length := by
    simp only [List.length_take, List.length_drop]; omega
  simp only [chunk_round_step, mixed_dot_product, round_reduce, zero_add, Option.some.injEq,
    Prod.mk.injEq]
  constructor
  · rw [hs]
    congr 1
    · refine sum_congr rfl fun j hj => sum_congr rfl fun t ht => ?_
      rw [getD_tile_lo _ (mem_range.mp ht) (hK j hj t ht), getD_tile_lo _ (mem_range.mp ht) (hK j hj t ht)]
    · refine sum_congr rfl fun t ht => ?_
      simp [List.getD_eq_getElem?_getD, htail t ht]
  · rw [hs]
    congr 1
    · refine sum_congr rfl fun j hj => sum_congr rfl fun t ht => ?_
      have hjt := hK j hj t ht
      have ht' := mem_range.mp ht
      obtain ⟨hw1, hw2⟩ := hlen hwl hjt ht'
      obtain ⟨he1, he2⟩ := hlen hel hjt ht'
      rw [getD_zipWith_sub hw1 hw2, getD_zipWith_sub he1 he2, getD_tile_lo _ ht' hjt, getD_tile_lo _ ht' hjt, getD_tile_hi _ ht', getD_tile_hi _ ht']
    · refine sum_congr rfl fun t ht => ?_
      simp [List.getD_eq_getElem?_getD, htail t ht]

end Plonky3Lean.Proofs.Sumcheck
