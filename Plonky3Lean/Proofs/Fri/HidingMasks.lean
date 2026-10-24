module

public import Plonky3Lean.Proofs.Fri.Hiding

@[expose] public section

/-!
# The quotient masks and the chunk count

The hiding commitment masks d quotient chunks, one per evaluation it receives.

It also receives a chunk count n from its caller, and never checks n = d.

It draws random blocks for chunks 0 to d - 2 and a zero block for chunk d - 1.

Then it balances chunk n - 1 against the chunks before it.

```text
    v_i     = r_i                                        i != n - 1
    v_(n-1) = r_(n-1) - sum_(j < n-1) (c_j / c_(n-1)) r_j
    r_(d-1) = 0
```

The recombination sees the masks through sum_i c_i v_i, coefficient by coefficient.

- When n = d, that sum is zero for every draw.
- When n < d, it is the nonzero form sum_(n-1 <= i < d-1) c_i r_i, so the masks do not cancel.
- When n > d, reading c_(n-1) panics.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.hiding_pcs.mirror Finset

variable {K : Type} [Field K]

/-! ## The balancing loop -/

omit [Field K] in
theorem length_foldl_set (f : List K → ℕ → ℕ) (g : List K → ℕ → K) :
    ∀ (l : List ℕ) (A : List K), (l.foldl (fun acc k => acc.set (f acc k) (g acc k)) A).length = A.length
  | [], _ => rfl
  | k :: l, A => by rw [List.foldl_cons, length_foldl_set f g l, List.length_set]

/-- One pass of the loop subtracts m times block src from block base.

Block src lies before block base, so the pass never reads a value it wrote. -/
theorem balance_block (A : List K) (base src : ℕ) (m : K) :
    ∀ n, base + n ≤ A.length → src + n ≤ base → ∀ p,
      ((List.range n).foldl (fun acc k => acc.set (base + k) (acc.getD (base + k) 0 - acc.getD (src + k) 0 * m))
        A).getD p 0 =
      if base ≤ p ∧ p < base + n then A.getD p 0 - A.getD (src + (p - base)) 0 * m else A.getD p 0 := by
  intro n
  induction n with
  | zero => intro _ _ p; simp
  | succ n ih =>
    intro hlen hsrc p
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl := length_foldl_set (fun _ k => base + k)
      (fun acc k => acc.getD (base + k) 0 - acc.getD (src + k) 0 * m) (List.range n) A
    rw [getD_set' _ _ _ _ (by rw [hl]; omega), ih (by omega) (by omega), ih (by omega) (by omega),
      ih (by omega) (by omega)]
    by_cases hp : base + n = p
    · subst hp
      have h1 : ¬ (base ≤ src + n ∧ src + n < base + n) := by omega
      have h2 : base ≤ base + n ∧ base + n < base + (n + 1) := by omega
      simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left, lt_self_iff_false, and_false, and_self]
    · by_cases hin : base ≤ p ∧ p < base + n
      · simp only [hp, hin, show base ≤ p ∧ p < base + (n + 1) from ⟨hin.1, by omega⟩, and_self, ↓reduceIte]
      · simp only [hp, hin, show ¬ (base ≤ p ∧ p < base + (n + 1)) by omega, ↓reduceIte]

/-- The balancing loop leaves every block but the last chunk's, and subtracts the scaled blocks from it. -/
theorem lastMask_getD (mul : List K) (hw : ℕ) (rv : List K) (last : ℕ) (hJ : mul.length ≤ last)
    (hl : last * hw + hw ≤ rv.length) (p : ℕ) :
    (lastMask mul hw rv last).getD p 0 =
      if last * hw ≤ p ∧ p < last * hw + hw then
        rv.getD p 0 - ∑ j ∈ range mul.length, rv.getD (j * hw + (p - last * hw)) 0 * mul.getD j 0
      else rv.getD p 0 := by
  have key : ∀ J ≤ mul.length, ∀ p, ((List.range J).foldl (fun acc j =>
      (List.range hw).foldl (fun acc k =>
        acc.set (last * hw + k) (acc.getD (last * hw + k) 0 - acc.getD (j * hw + k) 0 * mul.getD j 0)) acc)
      rv).getD p 0 =
      if last * hw ≤ p ∧ p < last * hw + hw then
        rv.getD p 0 - ∑ j ∈ range J, rv.getD (j * hw + (p - last * hw)) 0 * mul.getD j 0
      else rv.getD p 0 := by
    intro J
    induction J with
    | zero => intro _ p; simp
    | succ J ih =>
      intro hJm p
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : last * hw + hw ≤ ((List.range J).foldl (fun acc j =>
          (List.range hw).foldl (fun acc k =>
            acc.set (last * hw + k) (acc.getD (last * hw + k) 0 - acc.getD (j * hw + k) 0 * mul.getD j 0)) acc)
          rv).length := by
        have : ∀ (l : List ℕ) (A : List K), (l.foldl (fun acc j =>
            (List.range hw).foldl (fun acc k =>
              acc.set (last * hw + k) (acc.getD (last * hw + k) 0 - acc.getD (j * hw + k) 0 * mul.getD j 0)) acc)
            A).length = A.length := by
          intro l
          induction l with
          | nil => intro A; rfl
          | cons j l ihl => intro A; rw [List.foldl_cons, ihl, length_foldl_set]
        rw [this]; exact hl
      have hsrc : J * hw + hw ≤ last * hw := by
        have := Nat.mul_le_mul_right hw (show J + 1 ≤ last by omega); rw [Nat.succ_mul] at this; exact this
      rw [balance_block _ (last * hw) (J * hw) _ hw hlen hsrc p, ih (by omega)]
      by_cases hin : last * hw ≤ p ∧ p < last * hw + hw
      · rw [ih (by omega)]
        have hout : ¬ (last * hw ≤ J * hw + (p - last * hw) ∧ J * hw + (p - last * hw) < last * hw + hw) := by
          omega
        simp only [hin, hout, and_self, ↓reduceIte, sum_range_succ, sub_sub]
      · simp only [hin, ↓reduceIte]
  exact key _ le_rfl p

/-! ## The masks, chunk by chunk -/

/-- The random value of chunk i at position k: zero for the last evaluation. -/
def draw (d hw : ℕ) (rnd : List K) (i k : ℕ) : K := if i < d - 1 then rnd.getD (i * hw + k) 0 else 0

theorem maskDraws_getD {d hw : ℕ} (rnd : List K) (hrnd : (d - 1) * hw ≤ rnd.length) {i k : ℕ} (hi : i < d)
    (hk : k < hw) : (maskDraws d hw rnd).getD (i * hw + k) 0 = draw d hw rnd i k := by
  have htake : (rnd.take ((d - 1) * hw)).length = (d - 1) * hw := by simp [hrnd]
  unfold maskDraws draw
  split_ifs with hid
  · have : i * hw + k < (d - 1) * hw := by
      have := Nat.mul_le_mul_right hw (show i + 1 ≤ d - 1 by omega); rw [Nat.succ_mul] at this; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt this]
  · have hi' : i = d - 1 := by omega
    subst hi'
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), htake, Nat.add_sub_cancel_left]
    simp [hk]

variable [DecidableEq K]

/-- The masks the commitment computes, chunk by chunk, when n lies between 2 and the evaluation count d.

Chunk n - 1 is balanced against the chunks before it, and every other chunk keeps its draw. -/
theorem quotientMaskValues_getD (cis : List K) {n hw : ℕ} (rnd : List K) (h1 : 1 < n) (hn : n ≤ cis.length)
    (hc : cis.getD (n - 1) 0 ≠ 0) (hrnd : (cis.length - 1) * hw ≤ rnd.length) :
    ∃ v, quotientMaskValues cis n hw rnd = some v ∧ ∀ i < cis.length, ∀ k < hw,
      v.getD (i * hw + k) 0 = if i = n - 1 then
        draw cis.length hw rnd i k -
          ∑ j ∈ range (n - 1), draw cis.length hw rnd j k * (cis.getD j 0 / cis.getD (n - 1) 0)
      else draw cis.length hw rnd i k := by
  have hget : cis[n - 1]? = some (cis.getD (n - 1) 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega)
  refine ⟨_, by
    simp only [quotientMaskValues, show ¬ n ≤ 1 by omega, hget, ↓reduceIte, Option.bind_eq_bind]
    dsimp only [Option.bind]
    simp only [hc, ↓reduceIte]
    rfl,
    fun i hi k hk => ?_⟩
  have hlen : (maskDraws cis.length hw rnd).length = cis.length * hw := by
    simp only [maskDraws, List.length_append, List.length_take, List.length_replicate, min_eq_left hrnd]
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hl : (n - 1) * hw + hw ≤ (maskDraws cis.length hw rnd).length := by
    rw [hlen, ← Nat.succ_mul]; exact Nat.mul_le_mul_right hw (by omega)
  rw [lastMask_getD _ hw _ (n - 1) (by simp) hl, maskDraws_getD rnd hrnd hi hk]
  by_cases hin : i = n - 1
  · subst hin
    simp only [show (n - 1) * hw ≤ (n - 1) * hw + k ∧ (n - 1) * hw + k < (n - 1) * hw + hw from
      ⟨by omega, by omega⟩, and_self, ↓reduceIte, List.length_map, List.length_range]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [show j * hw + ((n - 1) * hw + k - (n - 1) * hw) = j * hw + k by omega,
      maskDraws_getD rnd hrnd (by simp at hj; omega) hk]
    simp [List.getD_eq_getElem?_getD, mem_range.1 hj, div_eq_mul_inv]
  · have hout : ¬ ((n - 1) * hw ≤ i * hw + k ∧ i * hw + k < (n - 1) * hw + hw) := by
      rintro ⟨h1, h2⟩
      apply hin
      rcases Nat.lt_or_ge i (n - 1) with h | h
      · have := Nat.mul_le_mul_right hw (show i + 1 ≤ n - 1 by omega); rw [Nat.succ_mul] at this; omega
      · rcases Nat.eq_or_lt_of_le h with h | h
        · exact h.symm
        · have := Nat.mul_le_mul_right hw (show n - 1 + 1 ≤ i by omega); rw [Nat.succ_mul] at this; omega
    simp only [hin, hout, ↓reduceIte]

/-- The commitment panics on n of at most 1, and on n past the evaluation count. -/
theorem quotientMaskValues_eq_none (cis : List K) (n hw : ℕ) (rnd : List K) (h : n ≤ 1 ∨ cis.length < n) :
    quotientMaskValues cis n hw rnd = none := by
  by_cases h1 : n ≤ 1
  · simp [quotientMaskValues, h1]
  · have h2 : cis[n - 1]? = none := List.getElem?_eq_none (by omega)
    simp only [quotientMaskValues, h1, h2, ↓reduceIte]
    rfl

/-! ## Cancellation -/

/-- The masks' weighted sum at position k: sum_i c_i v_i. -/
def maskResidual (cis v : List K) (hw k : ℕ) : K :=
  ∑ i ∈ range cis.length, cis.getD i 0 * v.getD (i * hw + k) 0

/-- The weighted sum of the masks is the sum of c_i r_i over the chunks from n - 1 on. -/
theorem maskResidual_eq (cis : List K) {n hw : ℕ} (rnd : List K) (h1 : 1 < n) (hn : n ≤ cis.length)
    (hc : cis.getD (n - 1) 0 ≠ 0) (hrnd : (cis.length - 1) * hw ≤ rnd.length) {v : List K}
    (hv : quotientMaskValues cis n hw rnd = some v) {k : ℕ} (hk : k < hw) :
    maskResidual cis v hw k = ∑ i ∈ Ico (n - 1) cis.length, cis.getD i 0 * draw cis.length hw rnd i k := by
  obtain ⟨v', hv', hspec⟩ := quotientMaskValues_getD cis rnd h1 hn hc hrnd
  obtain rfl := Option.some.inj (hv.symm.trans hv')
  unfold maskResidual
  rw [sum_congr rfl fun i hi => by rw [hspec i (mem_range.1 hi) k hk]]
  have hsplit : ∀ i ∈ range cis.length, cis.getD i 0 * (if i = n - 1 then
      draw cis.length hw rnd i k - ∑ j ∈ range (n - 1), draw cis.length hw rnd j k * (cis.getD j 0 / cis.getD (n - 1) 0)
      else draw cis.length hw rnd i k) = cis.getD i 0 * draw cis.length hw rnd i k -
      (if i = n - 1 then cis.getD (n - 1) 0 *
        ∑ j ∈ range (n - 1), draw cis.length hw rnd j k * (cis.getD j 0 / cis.getD (n - 1) 0) else 0) := by
    intro i _
    split_ifs with h
    · subst h; ring
    · ring
  have hR := sum_range_add_sum_Ico (fun i => cis.getD i 0 * draw cis.length hw rnd i k)
    (show n - 1 ≤ cis.length by omega)
  have e3 : cis.getD (n - 1) 0 * ∑ j ∈ range (n - 1), draw cis.length hw rnd j k * (cis.getD j 0 / cis.getD (n - 1) 0) =
      ∑ j ∈ range (n - 1), cis.getD j 0 * draw cis.length hw rnd j k := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by field_simp
  rw [sum_congr rfl hsplit, sum_sub_distrib, sum_ite_eq' (range cis.length) (n - 1)]
  simp only [show n - 1 ∈ range cis.length from mem_range.2 (by omega), ↓reduceIte]
  linear_combination -hR - e3

/-- When the chunk count is the evaluation count, the masks cancel for every draw. -/
theorem maskResidual_eq_zero (cis : List K) {hw : ℕ} (rnd : List K) (h1 : 1 < cis.length)
    (hc : cis.getD (cis.length - 1) 0 ≠ 0) (hrnd : (cis.length - 1) * hw ≤ rnd.length) {v : List K}
    (hv : quotientMaskValues cis cis.length hw rnd = some v) {k : ℕ} (hk : k < hw) :
    maskResidual cis v hw k = 0 := by
  rw [maskResidual_eq cis rnd h1 le_rfl hc hrnd hv hk, Nat.Ico_pred_singleton (by omega), sum_singleton]
  simp [draw]

/-- When the chunk count falls short of the evaluation count, some draw leaves the masks uncancelled.

Every constant is nonzero, as on disjoint chunks. -/
theorem maskResidual_ne_zero (cis : List K) {n hw : ℕ} (h1 : 1 < n) (hn : n < cis.length) (hw0 : 0 < hw)
    (hc : ∀ i < cis.length, cis.getD i 0 ≠ 0) :
    ∃ rnd : List K, (cis.length - 1) * hw ≤ rnd.length ∧ ∃ v, quotientMaskValues cis n hw rnd = some v ∧
      maskResidual cis v hw 0 ≠ 0 := by
  -- Draw 1 at position 0 of chunk n - 1, and 0 everywhere else.
  set rnd : List K := (List.range ((cis.length - 1) * hw)).map fun p => if p = (n - 1) * hw then 1 else 0
  have hrnd : (cis.length - 1) * hw ≤ rnd.length := by simp [rnd]
  obtain ⟨v, hv, -⟩ := quotientMaskValues_getD cis rnd h1 hn.le (hc _ (by omega)) hrnd
  refine ⟨rnd, hrnd, v, hv, ?_⟩
  rw [maskResidual_eq cis rnd h1 hn.le (hc _ (by omega)) hrnd hv hw0]
  have hd : ∀ i ∈ Ico (n - 1) cis.length, draw cis.length hw rnd i 0 = if i = n - 1 then 1 else 0 := by
    intro i hi
    simp only [mem_Ico] at hi
    unfold draw
    split_ifs with hid hin hin
    · subst hin
      have : (n - 1) * hw < (cis.length - 1) * hw := Nat.mul_lt_mul_of_pos_right (by omega) hw0
      simp [rnd, List.getD_eq_getElem?_getD, this]
    · have hlt : i * hw < (cis.length - 1) * hw := Nat.mul_lt_mul_of_pos_right hid hw0
      have hne : i * hw ≠ (n - 1) * hw := fun e => hin (Nat.eq_of_mul_eq_mul_right hw0 e)
      simp [rnd, List.getD_eq_getElem?_getD, hlt, hne]
    · omega
    · rfl
  rw [sum_congr rfl fun i hi => by rw [hd i hi],
    sum_eq_single_of_mem (n - 1) (by simp; omega) fun j _ hj => by simp [hj]]
  simpa using hc _ (by omega)

end Plonky3Lean.Proofs.Fri
