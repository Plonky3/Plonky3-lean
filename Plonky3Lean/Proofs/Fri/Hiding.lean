module

public import P3Fri.Hiding
public import Plonky3Lean.Proofs.Fri.Matrix
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The hiding PCS

The randomized commitment keeps the trace on the even rows of the doubled domain.

The quotient mask adds r(X) v(X) to a chunk, for v the chunk domain's vanishing polynomial.

The masks of all chunks cancel in the recombination the STARK verifier computes.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.hiding_pcs.mirror Polynomial Finset

variable {K : Type} [Field K]

/-- The randomized commitment keeps the trace on the even rows: entry c of row 2 i, at width w + r, is entry c of row i of the trace. -/
theorem randomize_even_row (v : List K) {w r h : ℕ} (hw : 0 < w) (hv : v.length = h * w) (rnd : List K)
    (hrnd : h * (w + 2 * r) ≤ rnd.length) {i c : ℕ} (hi : i < h) (hc : c < w) :
    (randomize v w r rnd).1.getD (2 * i * (w + r) + c) 0 = v.getD (i * w + c) 0 := by
  have hh : v.length / w = h := by rw [hv, Nat.mul_div_cancel _ hw]
  have hf : ∀ j < h, ((v.drop (j * w)).take w ++ (rnd.drop (j * (w + 2 * r))).take (w + 2 * r)).length =
      2 * (w + r) := by
    intro j hj
    simp only [List.length_append, List.length_take, List.length_drop]
    have h1 : w ≤ v.length - j * w := by rw [hv]; have := Nat.mul_le_mul_right w (show j + 1 ≤ h by omega); rw [Nat.succ_mul] at this; omega
    have h2 : w + 2 * r ≤ rnd.length - j * (w + 2 * r) := by
      have := Nat.mul_le_mul_right (w + 2 * r) (show j + 1 ≤ h by omega); rw [Nat.succ_mul] at this; omega
    rw [min_eq_left h1, min_eq_left h2]; ring
  simp only [randomize, withRandomCols, hh]
  rw [show 2 * i * (w + r) + c = i * (2 * (w + r)) + c by ring,
    getD_flatMap_blocks _ _ h hf i c hi (by omega)]
  have hlen : ((v.drop (i * w)).take w).length = w := by
    simp only [List.length_take, List.length_drop, hv]
    have := Nat.mul_le_mul_right w (show i + 1 ≤ h by omega); rw [Nat.succ_mul] at this; omega
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hc, List.getElem?_drop]

theorem getD_set' (l : List K) (i k : ℕ) (x : K) (hi : i < l.length) :
    (l.set i x).getD k 0 = if i = k then x else l.getD k 0 := by
  rcases eq_or_ne i k with rfl | hik
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hik, hik]

/-- What pair (i, j) of the mask adds at position k. -/
def maskDelta (g p : K) (h w : ℕ) (rv : List K) (k : ℕ) (e : ℕ × ℕ) : K :=
  (if e.1 * w + e.2 = k then -(g ^ e.1 * rv.getD (e.1 * w + e.2) 0) else 0) +
    (if (h + e.1) * w + e.2 = k then p * (g ^ e.1 * rv.getD (e.1 * w + e.2) 0) else 0)

/-- The mask's effect, pair by pair: each pair (i, j) moves its two positions by -g^i r_(i,j) and p g^i r_(i,j). -/
theorem maskCoeffs_foldl (g p : K) (h w : ℕ) (rv : List K) :
    ∀ (l : List (ℕ × ℕ)) (c : List K), (∀ e ∈ l, (h + e.1) * w + e.2 < c.length ∧ e.1 * w + e.2 < c.length) →
      ∀ k, (l.foldl (fun c e =>
        let m := g ^ e.1 * rv.getD (e.1 * w + e.2) 0
        let c := c.set (e.1 * w + e.2) (c.getD (e.1 * w + e.2) 0 - m)
        c.set ((h + e.1) * w + e.2) (c.getD ((h + e.1) * w + e.2) 0 + p * m)) c).getD k 0 =
        c.getD k 0 + (l.map (maskDelta g p h w rv k)).sum
  | [], c, _, k => by simp
  | e :: l, c, hl, k => by
    rw [List.foldl_cons, maskCoeffs_foldl g p h w rv l _ (fun e' he' => by
      simpa using hl e' (List.mem_cons_of_mem _ he')) k]
    obtain ⟨h1, h2⟩ := hl e List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    generalize (l.map (maskDelta g p h w rv k)).sum = S
    simp only [maskDelta]
    rw [getD_set' _ _ _ _ (by rw [List.length_set]; exact h1), getD_set' _ _ _ _ h2,
      getD_set' _ _ _ _ h2]
    split_ifs with h3 h4 h5 h5 h4 <;> (try subst h3) <;> (try rw [h4]) <;> (try rw [← h5]) <;>
      first | contradiction | ring

theorem sum_map_range'' {M : Type _} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range'' f n,
      Finset.sum_range_succ]; simp

theorem sum_pairs {M : Type _} [AddCommMonoid M] (h w : ℕ) (F : ℕ × ℕ → M) :
    (((List.range h).flatMap fun i => (List.range w).map fun j => (i, j)).map F).sum =
      ∑ i ∈ range h, ∑ j ∈ range w, F (i, j) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp only [List.flatMap_singleton, List.map_map]
    exact congrArg _ (sum_map_range'' (fun j => F (h, j)) w)

theorem div_mod_unique {w i j i' j' : ℕ} (hj : j < w) (hj' : j' < w) (h : i' * w + j' = i * w + j) :
    i' = i ∧ j' = j := by
  have h1 : (i' * w + j') / w = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj', zero_add]
  have h2 : (i * w + j) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
  have hi : i' = i := by rw [← h1, h, h2]
  subst hi; exact ⟨rfl, by omega⟩

/-- The quotient mask on coefficients: in column j, coefficient i < h loses g^i r_(i,j), and coefficient h + i gains p g^i r_(i,j). -/
theorem maskCoeffs_getD (g p : K) {h w : ℕ} (rv coeffs : List K) (hlen : 2 * h * w ≤ coeffs.length)
    {i j : ℕ} (hi : i < 2 * h) (hj : j < w) :
    (maskCoeffs g p h w rv coeffs).getD (i * w + j) 0 = coeffs.getD (i * w + j) 0 +
      (if i < h then -(g ^ i * rv.getD (i * w + j) 0) else 0) +
      (if h ≤ i then p * (g ^ (i - h) * rv.getD ((i - h) * w + j) 0) else 0) := by
  rw [maskCoeffs, maskCoeffs_foldl g p h w rv _ coeffs ?_, sum_pairs, add_assoc]
  · congr 1
    simp only [maskDelta, Finset.sum_add_distrib]
    congr 1
    · by_cases hih : i < h
      · rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
        · simp [hih]
        · intro j' _ hj'; simp only [ite_eq_right_iff]; intro h'; exact absurd (div_mod_unique hj (by
            simp at *; omega) h').2 hj'
        · intro h'; simp at h'; omega
        · intro i' _ hi'; refine Finset.sum_eq_zero fun j' hj' => ?_
          simp only [ite_eq_right_iff]; intro h'; exact absurd (div_mod_unique hj (by simpa using hj') h').1 hi'
        · intro h'; simp at h'; omega
      · simp only [hih, ↓reduceIte]
        refine Finset.sum_eq_zero fun i' hi' => Finset.sum_eq_zero fun j' hj' => ?_
        simp only [ite_eq_right_iff]; intro h'
        have := (div_mod_unique hj (by simpa using hj') h').1; simp at hi'; omega
    · by_cases hih : h ≤ i
      · rw [Finset.sum_eq_single (i - h), Finset.sum_eq_single j]
        · simp [hih, show h + (i - h) = i by omega]
        · intro j' _ hj'; simp only [ite_eq_right_iff]; intro h'
          exact absurd (div_mod_unique hj (by simp at *; omega) h').2 hj'
        · intro h'; simp at h'; omega
        · intro i' _ hi'; refine Finset.sum_eq_zero fun j' hj' => ?_
          simp only [ite_eq_right_iff]; intro h'
          have := (div_mod_unique hj (by simpa using hj') h').1; omega
        · intro h'; simp at h'; omega
      · simp only [hih, ↓reduceIte]
        refine Finset.sum_eq_zero fun i' hi' => Finset.sum_eq_zero fun j' hj' => ?_
        simp only [ite_eq_right_iff]; intro h'
        have := (div_mod_unique hj (by simpa using hj') h').1; omega
  · intro e he
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at he
    obtain ⟨i', hi', j', hj', rfl⟩ := he
    dsimp only
    constructor
    · have : (h + i') * w + j' < (2 * h) * w := by
        have := Nat.mul_le_mul_right w (show h + i' + 1 ≤ 2 * h by omega); rw [Nat.succ_mul] at this; omega
      omega
    · have : i' * w + j' < (2 * h) * w := by
        have := Nat.mul_le_mul_right w (show i' + 1 ≤ 2 * h by omega); rw [Nat.succ_mul] at this; omega
      omega

/-- Column j of the masked chunk, as a polynomial on coefficients, gains r(X) (p X^h - 1), for r with coefficients g^i r_(i,j). -/
theorem maskCoeffs_column (g p x : K) {h w : ℕ} (rv coeffs : List K) (hlen : 2 * h * w ≤ coeffs.length)
    {j : ℕ} (hj : j < w) :
    ∑ i ∈ range (2 * h), (maskCoeffs g p h w rv coeffs).getD (i * w + j) 0 * x ^ i =
      ∑ i ∈ range (2 * h), coeffs.getD (i * w + j) 0 * x ^ i +
        (∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i) * (p * x ^ h - 1) := by
  rw [Finset.sum_congr rfl fun i hi => by
    rw [maskCoeffs_getD g p rv coeffs hlen (Finset.mem_range.1 hi) hj]]
  have hA : ∑ i ∈ range (2 * h), (if i < h then -(g ^ i * rv.getD (i * w + j) 0) else 0) * x ^ i =
      -∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i := by
    rw [show 2 * h = h + h by ring, Finset.sum_range_add, ← Finset.sum_neg_distrib]
    have e1 : ∑ i ∈ range h, (if i < h then -(g ^ i * rv.getD (i * w + j) 0) else 0) * x ^ i =
        ∑ i ∈ range h, -(g ^ i * rv.getD (i * w + j) 0 * x ^ i) :=
      Finset.sum_congr rfl fun i hi => by simp only [Finset.mem_range] at hi; simp [hi, neg_mul]
    have e2 : ∑ i ∈ range h, (if h + i < h then -(g ^ (h + i) * rv.getD ((h + i) * w + j) 0) else 0) *
        x ^ (h + i) = 0 := Finset.sum_eq_zero fun i _ => by simp
    rw [e1, e2, add_zero]
  have hB : ∑ i ∈ range (2 * h), (if h ≤ i then p * (g ^ (i - h) * rv.getD ((i - h) * w + j) 0) else 0) * x ^ i =
      (∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i) * (p * x ^ h) := by
    rw [show 2 * h = h + h by ring, Finset.sum_range_add, Finset.sum_mul]
    have e1 : ∑ i ∈ range h, (if h ≤ i then p * (g ^ (i - h) * rv.getD ((i - h) * w + j) 0) else 0) *
        x ^ i = 0 := Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi; simp [show ¬ h ≤ i by omega]
    have e2 : ∑ i ∈ range h, (if h ≤ h + i then p * (g ^ (h + i - h) * rv.getD ((h + i - h) * w + j) 0)
        else 0) * x ^ (h + i) = ∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i * (p * x ^ h) :=
      Finset.sum_congr rfl fun i _ => by simp only [show h ≤ h + i by omega, ↓reduceIte,
        Nat.add_sub_cancel_left, pow_add]; ring
    rw [e1, e2, zero_add]
  simp only [add_mul, Finset.sum_add_distrib, hA, hB]
  ring

/-- The masks cancel in the recombination: with weights c_i prod_(j != i) v_j, the chunk masks v_i R_i sum to zero when the last chunk's mask is minus the sum of the others scaled by c_i / c_last. -/
theorem masks_cancel {d : ℕ} (c v : Fin (d + 1) → K) (R : Fin d → K) (hc : c (Fin.last d) ≠ 0) :
    ∑ i : Fin (d + 1), (c i * ∏ j ∈ univ.erase i, v j) *
      (v i * Fin.lastCases (-∑ i : Fin d, c i.castSucc / c (Fin.last d) * R i) R i) = 0 := by
  have hprod : ∀ i : Fin (d + 1), (∏ j ∈ univ.erase i, v j) * v i = ∏ j, v j := fun i =>
    Finset.prod_erase_mul _ _ (mem_univ i)
  calc ∑ i : Fin (d + 1), (c i * ∏ j ∈ univ.erase i, v j) *
        (v i * Fin.lastCases (-∑ i : Fin d, c i.castSucc / c (Fin.last d) * R i) R i)
      = (∏ j, v j) * ∑ i : Fin (d + 1), c i * Fin.lastCases (-∑ i : Fin d, c i.castSucc / c (Fin.last d) * R i) R i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hprod i]; ring
    _ = 0 := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
        have e : ∀ i : Fin d, c (Fin.last d) * (c i.castSucc / c (Fin.last d) * R i) = c i.castSucc * R i :=
          fun i => by field_simp
        rw [mul_neg, Finset.mul_sum, Finset.sum_congr rfl fun i _ => e i, add_neg_cancel, mul_zero]

omit [Field K] in
/-- The verifier's merge undoes the prover's split: hidden values of the configured count rejoin the public ones. -/
theorem merge_split {k : ℕ} (z : K) (vals : List K) (hk : k ≤ vals.length) :
    mergePoint k ⟨z, (splitPoint k vals).1⟩ (splitPoint k vals).2 = some ⟨z, vals⟩ := by
  simp [mergePoint, splitPoint, show vals.length - (vals.length - k) = k by omega]

omit [Field K] in
/-- The verifier's merge rejects exactly a hidden part of the wrong count. -/
theorem mergePoint_eq_none (k : ℕ) (pt : p3_commit.pcs.univariate.mirror.PointOpening K) (rand : List K) :
    mergePoint k pt rand = none ↔ rand.length ≠ k := by
  unfold mergePoint; split_ifs with h <;> simp [h]

/-- The three hiding budgets read the same mask height: the trace height N at commit, the LDE height 2 N 2^b without its blowup at opening, and half the doubled domain at verification. -/
theorem mask_heights_agree (N b : ℕ) (hb : b < 64) :
    lde_mask_height b (2 * N * 2 ^ b) = N ∧ (2 * N) / 2 = N := by
  simp [lde_mask_height, hb, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ b)]

end Plonky3Lean.Proofs.Fri
