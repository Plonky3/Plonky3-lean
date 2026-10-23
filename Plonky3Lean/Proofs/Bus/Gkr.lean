module

public import P3Bus
public import Plonky3Lean.Proofs.MultilinearUtil.Unique

@[expose] public section

/-!
# The product-tree reduction: schedule and padding

A tree of height h is reduced root first.

An odd tree starts with one binary layer; every other layer contracts two levels:

```text
    h = 2k       (4, 0), (4, 2), ..., (4, 2k - 2)
    h = 2k + 1   (2, 0), (4, 1), (4, 3), ..., (4, 2k - 1)
```

Each pair is a layer's arity and its number of sumcheck rounds.

The leaves past the explicit prefix are ones, and the verifier evaluates their indicator at a point by a binary threshold:

```text
    padding(n, r) = sum_(n <= i < 2^h) eq(i, r)
```
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.product.mirror Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Finset

set_option linter.unusedSectionVars false

/-! ## The schedule -/

theorem layersLoop_even (h : ℕ) : ∀ (k p : ℕ),
    layersLoop h p (2 * k) = (List.range k).map fun j => (4, p + 2 * j)
  | 0, p => by simp [layersLoop]
  | k + 1, p => by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, layersLoop]
    have harity : (if 2 * k + 1 + 1 = h ∧ (2 * k + 1 + 1) % 2 = 1 then 2 else 4) = 4 := by
      rw [ite_eq_right (by omega)]
    simp only [harity, show Nat.log2 4 = 2 by decide, show 2 * k + 1 + 1 - 2 = 2 * k by omega,
      layersLoop_even h k (p + 2), List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def]
    intro _ _; omega

/-- **The schedule.** An even height contracts two levels per layer; an odd height starts with one binary layer. -/
theorem layers_eq (s : ProductGkrShape) :
    s.layers = if s.log_height % 2 = 0 then
        (List.range (s.log_height / 2)).map fun j => (4, 2 * j)
      else (2, 0) :: (List.range (s.log_height / 2)).map fun j => (4, 1 + 2 * j) := by
  unfold ProductGkrShape.layers
  split
  · rw [show s.log_height = 2 * (s.log_height / 2) by omega, layersLoop_even]
    simp
  · rw [show s.log_height = 2 * (s.log_height / 2) + 1 by omega, layersLoop]
    rw [ite_eq_left (by omega)]
    simp only [show Nat.log2 2 = 1 by decide, show 2 * (s.log_height / 2) + 1 - 1 =
      2 * (s.log_height / 2) by omega, layersLoop_even, zero_add,
      show (2 * (s.log_height / 2) + 1) / 2 = s.log_height / 2 by omega]

/-- Every layer contracts log_2 of its arity, so the branches add up to the height. -/
theorem layers_branches (s : ProductGkrShape) :
    (s.layers.map fun l => Nat.log2 l.1).sum = s.log_height := by
  rw [layers_eq]
  have h4 : Nat.log2 4 = 2 := by decide
  have h2 : Nat.log2 2 = 1 := by decide
  split <;> simp [Function.comp_def, h4, h2, List.map_const', List.sum_replicate] <;> omega

/-- There are ceil(h / 2) layers, and none exactly when the height is zero. -/
theorem layers_length (s : ProductGkrShape) : s.layers.length = (s.log_height + 1) / 2 := by
  rw [layers_eq]; split <;> simp <;> omega

/-! ## The identity padding -/

section Padding

variable {F : Type _} [Field F]

/-- The sum of eq(i, r) over the first n vertices. -/
def prefixEq (r : List F) (n : ℕ) : F := ∑ i ∈ range n, eq (vertex r.length i) r

theorem sum_low (c : F) (r : List F) (n : ℕ) (hn : n ≤ 2 ^ r.length) :
    ∑ i ∈ range n, eq (vertex (r.length + 1) i) (c :: r) = (1 - c) * prefixEq r n := by
  unfold prefixEq
  rw [mul_sum]
  exact sum_congr rfl fun i hi => by
    rw [vertex_low (by simp at hi; omega : i < 2 ^ r.length)]; simp

theorem sum_high (c : F) (r : List F) (n : ℕ) (hn : n ≤ 2 ^ r.length) :
    ∑ i ∈ range n, eq (vertex (r.length + 1) (2 ^ r.length + i)) (c :: r) = c * prefixEq r n := by
  unfold prefixEq
  rw [mul_sum]
  exact sum_congr rfl fun i hi => by
    rw [vertex_high (by simp at hi; omega : i < 2 ^ r.length)]; simp

theorem prefixEq_full (r : List F) : prefixEq r (2 ^ r.length) = 1 := by
  induction r with
  | nil => simp [prefixEq, vertex]
  | cons c r ih =>
    unfold prefixEq
    rw [List.length_cons, pow_succ, mul_two, sum_range_add, sum_low c r _ le_rfl,
      sum_high c r _ le_rfl, ih]
    ring

/-- Fixing the top coordinate: a prefix either stops in the lower half, or covers it. -/
theorem prefixEq_cons (c : F) (r : List F) {n : ℕ} (hn : n ≤ 2 ^ (r.length + 1)) :
    prefixEq (c :: r) n = if 2 ^ r.length ≤ n then (1 - c) + c * prefixEq r (n - 2 ^ r.length)
      else (1 - c) * prefixEq r n := by
  unfold prefixEq
  rw [List.length_cons]
  split
  · rw [show n = 2 ^ r.length + (n - 2 ^ r.length) by omega, sum_range_add,
      Nat.add_sub_cancel_left, sum_low c r _ le_rfl, sum_high c r _ (by rw [pow_succ] at hn; omega),
      prefixEq_full]
    simp [prefixEq]
  · rw [sum_low c r _ (by omega)]; rfl

theorem eq_vertex_cons (c : F) (r : List F) {n : ℕ} (hn : n < 2 ^ (r.length + 1)) :
    eq (vertex (r.length + 1) n) (c :: r) = if 2 ^ r.length ≤ n then
      c * eq (vertex r.length (n - 2 ^ r.length)) r else (1 - c) * eq (vertex r.length n) r := by
  split
  · rw [show n = 2 ^ r.length + (n - 2 ^ r.length) by omega,
      vertex_high (by omega : n - 2 ^ r.length < 2 ^ r.length), Nat.add_sub_cancel_left]
    simp
  · rw [vertex_low (by omega)]; simp

/-- The step of the verifier's threshold fold. -/
def padStep (n L : ℕ) (acc : F × F) (cb : F × ℕ) : F × F :=
  if (n >>> (L - 1 - cb.2)) % 2 = 1 then (acc.1 + acc.2 * (1 - cb.1), acc.2 * cb.1)
  else (acc.1, acc.2 * (1 - cb.1))

/-- **The threshold fold.** Over the coordinates from index k, it adds the mass of the vertices below the low bits of n, scaled by the running eq. -/
theorem foldl_padStep (n L : ℕ) : ∀ (l : List F) (k : ℕ) (b e : F), k + l.length = L →
    (l.zipIdx k).foldl (padStep n L) (b, e) =
      (b + e * prefixEq l (n % 2 ^ l.length), e * eq (vertex l.length (n % 2 ^ l.length)) l)
  | [], k, b, e, _ => by simp [prefixEq, vertex, Nat.mod_one]
  | c :: rest, k, b, e, hk => by
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hshift : L - 1 - k = rest.length := by simp at hk; omega
    have hmod : n % 2 ^ (rest.length + 1) =
        n % 2 ^ rest.length + 2 ^ rest.length * (n / 2 ^ rest.length % 2) :=
      Nat.mod_pow_succ
    have hlt : n % 2 ^ rest.length < 2 ^ rest.length := Nat.mod_lt _ (by positivity)
    have hbit : n >>> rest.length % 2 = n / 2 ^ rest.length % 2 := by rw [Nat.shiftRight_eq_div_pow]
    rw [foldl_padStep n L rest (k + 1) _ _ (by simp at hk; omega)]
    simp only [List.length_cons]
    rw [prefixEq_cons c rest (Nat.le_of_lt (Nat.mod_lt _ (by positivity))),
      eq_vertex_cons c rest (Nat.mod_lt _ (by positivity)), hmod]
    unfold padStep
    simp only [hshift, hbit]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ rest.length) with h | h
    · simp only [h, mul_zero, add_zero, zero_ne_one, ite_false,
        show ¬ 2 ^ rest.length ≤ n % 2 ^ rest.length by omega]
      congr 1 <;> ring
    · simp only [h, mul_one, ite_true, show 2 ^ rest.length ≤ n % 2 ^ rest.length + 2 ^ rest.length
        by omega, Nat.add_sub_cancel]
      congr 1 <;> ring

/-- **The identity padding.** On a point of the statement's dimension and a prefix that fits, the verifier's threshold evaluation is the sum of eq(i, r) over the padded addresses. -/
theorem identity_padding_evaluation_eq (s : ProductGkrShape) (n : ℕ) (point : List F)
    (hp : point.length = s.log_height) (hn : n ≤ 2 ^ s.log_height) :
    s.identity_padding_evaluation n point =
      some (∑ i ∈ Ico n (2 ^ s.log_height), eq (vertex s.log_height i) point) := by
  have hsplit : ∑ i ∈ Ico n (2 ^ s.log_height), eq (vertex s.log_height i) point =
      1 - prefixEq point n := by
    have := prefixEq_full point
    unfold prefixEq at this ⊢
    rw [hp] at this ⊢
    rw [← this, ← sum_range_add_sum_Ico _ hn]; ring
  unfold ProductGkrShape.identity_padding_evaluation
  rw [hsplit, ite_eq_right (by omega), ite_eq_right (by omega)]
  split
  · rename_i h; subst h
    rw [← hp, prefixEq_full]; simp
  · rename_i h
    have hf := foldl_padStep (F := F) n point.length point 0 0 1 (by simp)
    unfold padStep at hf
    rw [hf, zero_add, one_mul, Nat.mod_eq_of_lt (by rw [hp]; omega)]

/-- The evaluation panics exactly on a point of the wrong dimension or a prefix longer than the table. -/
theorem identity_padding_evaluation_panics (s : ProductGkrShape) (n : ℕ) (point : List F) :
    s.identity_padding_evaluation n point = none ↔
      point.length ≠ s.log_height ∨ 2 ^ s.log_height < n := by
  unfold ProductGkrShape.identity_padding_evaluation
  by_cases h1 : point.length = s.log_height
  · by_cases h2 : 2 ^ s.log_height < n
    · simp [h1, h2]
    · simp only [h1, ne_eq, not_true_eq_false, ite_false, gt_iff_lt, h2, false_or, iff_false]
      split <;> simp
  · simp [h1]

end Padding

end Plonky3Lean.Proofs.Bus
