module

public import Plonky3Lean.Proofs.Lookup.Soundness

@[expose] public section

/-!
# The running-sum encoding

Each lookup column of an AIR is pinned on every row by U f = V, the fraction cleared of its denominators.

The accumulator column starts at 0, adds each row's fractions, and ends at the committed terminal.

The terminals of all AIRs sum to zero.

Satisfied constraints with nonzero denominators then make the bus sum vanish.

An honest trace satisfies them whenever its denominators are nonzero.
-/

namespace Plonky3Lean.Proofs.Lookup

open Plonky3Lean.Spec.Lookup Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K]

/-! ## One row -/

/-- With nonzero denominators, V = U sum_i m_i / d_i. -/
theorem numerator_eq_of_ne_zero {terms : List (K × K)}
    (h : ∀ i < terms.length, den terms i ≠ 0) :
    numerator terms = denominator terms * fracSum terms := by
  unfold numerator denominator fracSum
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_prod_erase _ _ hi]
  field_simp [h i (mem_range.1 hi)]

/-- With nonzero denominators, the pin holds exactly for the fraction sum. -/
theorem pinned_iff {terms : List (K × K)} (h : ∀ i < terms.length, den terms i ≠ 0) (f : K) :
    Pinned terms f ↔ f = fracSum terms := by
  unfold Pinned
  rw [numerator_eq_of_ne_zero h]
  exact mul_right_inj' (prod_ne_zero_iff.2 fun i hi => h i (mem_range.1 hi))

/-- Two vanishing denominators leave the fraction free: every value satisfies the pin. -/
theorem pinned_of_two_zero {terms : List (K × K)} {i j : ℕ} (hij : i ≠ j)
    (hi : i < terms.length) (hj : j < terms.length) (hdi : den terms i = 0)
    (hdj : den terms j = 0) (f : K) : Pinned terms f := by
  unfold Pinned numerator denominator
  rw [prod_eq_zero (mem_range.2 hi) hdi, zero_mul]
  refine (sum_eq_zero fun k hk => ?_).symm
  by_cases hk' : k = i
  · subst hk'; rw [prod_eq_zero (mem_erase.2 ⟨Ne.symm hij, mem_range.2 hj⟩) hdj, mul_zero]
  · rw [prod_eq_zero (mem_erase.2 ⟨Ne.symm hk', mem_range.2 hi⟩) hdi, mul_zero]

/-- One vanishing denominator with zero multiplicity also leaves the fraction free. -/
theorem pinned_of_zero_mul {terms : List (K × K)} {i : ℕ} (hi : i < terms.length)
    (hdi : den terms i = 0) (hmi : mul terms i = 0) (f : K) : Pinned terms f := by
  unfold Pinned numerator denominator
  rw [prod_eq_zero (mem_range.2 hi) hdi, zero_mul]
  refine (sum_eq_zero fun k hk => ?_).symm
  by_cases hk' : k = i
  · subst hk'; rw [hmi, zero_mul]
  · rw [prod_eq_zero (mem_erase.2 ⟨Ne.symm hk', mem_range.2 hi⟩) hdi, mul_zero]

/-- One vanishing denominator with a nonzero multiplicity, the others nonzero, satisfies no pin: an honest prover fails. -/
theorem not_pinned_of_one_zero {terms : List (K × K)} {i : ℕ} (hi : i < terms.length)
    (hdi : den terms i = 0) (hmi : mul terms i ≠ 0)
    (hrest : ∀ j < terms.length, j ≠ i → den terms j ≠ 0) (f : K) : ¬ Pinned terms f := by
  unfold Pinned numerator denominator
  rw [prod_eq_zero (mem_range.2 hi) hdi, zero_mul, sum_eq_single_of_mem i (mem_range.2 hi) fun k hk hki => by
    rw [prod_eq_zero (mem_erase.2 ⟨Ne.symm hki, mem_range.2 hi⟩) hdi, mul_zero]]
  refine fun h => (mul_ne_zero hmi (prod_ne_zero_iff.2 fun j hj => ?_)) h.symm
  exact hrest j (mem_range.1 (mem_of_mem_erase hj)) (ne_of_mem_erase hj)

/-- **The honest fraction is pinned** whenever every denominator with a nonzero multiplicity is nonzero.

This covers the prover's zero-multiplicity skip: such a term adds 0 / d = 0. -/
theorem pinned_fracSum {terms : List (K × K)}
    (h : ∀ i < terms.length, mul terms i ≠ 0 → den terms i ≠ 0) : Pinned terms (fracSum terms) := by
  by_cases hall : ∀ i < terms.length, den terms i ≠ 0
  · exact (pinned_iff hall _).2 rfl
  · push Not at hall
    obtain ⟨i, hi, h0⟩ := hall
    exact pinned_of_zero_mul hi h0 (by_contra fun hm => h i hi hm h0) _

/-! ## One AIR -/

/-- The constrained accumulator holds the sum of the rows before it. -/
theorem acc_eq_sum {t : RunningSum K} {n w : ℕ} (h : t.Constrained n w) :
    ∀ r, r < n → t.acc r = ∑ r' ∈ range r, t.rowSum w r'
  | 0, _ => by simp [h.first]
  | r + 1, hr => by rw [h.transition r hr, acc_eq_sum h r (by omega), sum_range_succ]

/-- **The terminal is the sum over the trace.** -/
theorem terminal_eq_sum {t : RunningSum K} {n w : ℕ} (h : t.Constrained n w) (hn : 0 < n) :
    t.terminal = ∑ r ∈ range n, t.rowSum w r := by
  rw [h.last, acc_eq_sum h (n - 1) (by omega), ← sum_range_succ, Nat.sub_add_cancel hn]

/-- On one row, the terminal is that row's fractions. -/
theorem terminal_eq_height_one {t : RunningSum K} {w : ℕ} (h : t.Constrained 1 w) :
    t.terminal = t.rowSum w 0 := by
  rw [terminal_eq_sum h one_pos, sum_range_one]

/-- The honest columns: the accumulator is the sum of the rows before it, the terminal the sum of all. -/
def honest (frac : ℕ → ℕ → K) (n w : ℕ) : RunningSum K where
  acc r := ∑ r' ∈ range r, ∑ c ∈ range w, frac r' c
  frac := frac
  terminal := ∑ r ∈ range n, ∑ c ∈ range w, frac r c

/-- **Completeness.** The honest columns satisfy the accumulator constraints on every nonempty trace. -/
theorem honest_constrained (frac : ℕ → ℕ → K) {n : ℕ} (hn : 0 < n) (w : ℕ) :
    (honest frac n w).Constrained n w where
  first := by simp [honest]
  transition r _ := by simp [honest, RunningSum.rowSum, sum_range_succ]
  last := by
    simp only [honest, RunningSum.rowSum]
    rw [← sum_range_succ, Nat.sub_add_cancel hn]

/-! ## Every AIR together -/

/-- The messages of one AIR: its height, its lookup columns, and the messages each column folds on each row. -/
structure AirMessages (K : Type _) where
  height : ℕ
  width : ℕ
  msgs : ℕ → ℕ → List (Key K × K)

/-- The (d, m) pairs of a row of a column, d the domain-separated denominator of the message. -/
def AirMessages.terms (a : AirMessages K) (α β : K) (W r c : ℕ) : List (K × K) :=
  (a.msgs r c).map fun p => (busDenom α β W p.1.1 p.1.2, p.2)

/-- Every message of an AIR, row by row and column by column. -/
def AirMessages.all (a : AirMessages K) : List (Key K × K) :=
  ((List.range a.height).flatMap fun r => (List.range a.width).flatMap fun c => a.msgs r c)

/-- The verifier accepts the permutation columns of every AIR: each is pinned and constrained, and the terminals sum to zero. -/
def Accepts (α β : K) (W : ℕ) (airs : List (AirMessages K)) (cols : ℕ → RunningSum K) : Prop :=
  (∀ i (h : i < airs.length), 0 < airs[i].height ∧ (cols i).Constrained airs[i].height airs[i].width ∧
    ∀ r < airs[i].height, ∀ c < airs[i].width, Pinned (airs[i].terms α β W r c) ((cols i).frac r c)) ∧
  ∑ i ∈ range airs.length, (cols i).terminal = 0

theorem den_terms {a : AirMessages K} {α β : K} {W r c i : ℕ} (hi : i < (a.msgs r c).length) :
    den (a.terms α β W r c) i = busDenom α β W (a.msgs r c)[i].1.1 (a.msgs r c)[i].1.2 := by
  simp [den, AirMessages.terms, List.getD_eq_getElem?_getD, hi]

/-- A list sum as a sum over positions. -/
theorem list_sum_map_eq_sum_range {α M : Type _} [AddCommMonoid M] (l : List α) (g : α → M) (d : α) :
    (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

theorem fracSum_terms (a : AirMessages K) (α β : K) (W r c : ℕ) :
    fracSum (a.terms α β W r c) = busSum α β W (a.msgs r c) := by
  unfold fracSum busSum AirMessages.terms
  rw [list_sum_map_eq_sum_range _ _ ((0, []), 0), List.length_map]
  refine sum_congr rfl fun i hi => ?_
  simp [mul, den, List.getD_eq_getElem?_getD, mem_range.1 hi]

theorem busSum_append (α β : K) (W : ℕ) (l l' : List (Key K × K)) :
    busSum α β W (l ++ l') = busSum α β W l + busSum α β W l' := by
  simp [busSum]

theorem busSum_flatMap {ι : Type _} (α β : K) (W : ℕ) (l : List ι) (f : ι → List (Key K × K)) :
    busSum α β W (l.flatMap f) = (l.map fun i => busSum α β W (f i)).sum := by
  induction l with
  | nil => simp [busSum]
  | cons i l ih => rw [List.flatMap_cons, busSum_append, ih, List.map_cons, List.sum_cons]

theorem list_sum_map_range {M : Type _} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i ∈ range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem busSum_all (a : AirMessages K) (α β : K) (W : ℕ) :
    busSum α β W a.all = ∑ r ∈ range a.height, ∑ c ∈ range a.width, busSum α β W (a.msgs r c) := by
  simp only [AirMessages.all, busSum_flatMap, list_sum_map_range]

/-- The messages of every AIR. -/
def allMessages (airs : List (AirMessages K)) : List (Key K × K) := airs.flatMap AirMessages.all

theorem mem_allMessages {airs : List (AirMessages K)} {p : Key K × K} :
    p ∈ allMessages airs ↔ ∃ i, ∃ h : i < airs.length, ∃ r < airs[i].height, ∃ c < airs[i].width,
      p ∈ airs[i].msgs r c := by
  simp only [allMessages, AirMessages.all, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, r, hr, c, hc, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ⟨i, hi, r, hr, c, hc, hp⟩
  · rintro ⟨i, hi, r, hr, c, hc, hp⟩; exact ⟨_, List.getElem_mem hi, r, hr, c, hc, hp⟩

/-- **Satisfied constraints imply the bus relation.** When the verifier accepts and no denominator vanishes, the sum of m / d over every message of every AIR is zero. -/
theorem busSum_eq_zero_of_accepts {α β : K} {W : ℕ} {airs : List (AirMessages K)}
    {cols : ℕ → RunningSum K} (h : Accepts α β W airs cols)
    (hD : ∀ p ∈ allMessages airs, busDenom α β W p.1.1 p.1.2 ≠ 0) :
    busSum α β W (allMessages airs) = 0 := by
  rw [← h.2, allMessages, busSum_flatMap]
  rw [show (airs.map fun a => busSum α β W a.all).sum =
      ∑ i ∈ range airs.length, busSum α β W (airs.getD i ⟨0, 0, fun _ _ => []⟩).all from
    list_sum_map_eq_sum_range _ _ _]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  obtain ⟨hn, hc, hp⟩ := h.1 i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, busSum_all,
    terminal_eq_sum hc hn]
  refine sum_congr rfl fun r hr => sum_congr rfl fun c hcw => ?_
  have hden : ∀ j < (airs[i].terms α β W r c).length, den (airs[i].terms α β W r c) j ≠ 0 := by
    intro j hj
    have hj' : j < (airs[i].msgs r c).length := by simpa [AirMessages.terms] using hj
    rw [den_terms hj']
    exact hD _ (mem_allMessages.2 ⟨i, hi, r, mem_range.1 hr, c, mem_range.1 hcw, List.getElem_mem hj'⟩)
  rw [← fracSum_terms, ← (pinned_iff hden _).1 (hp r (mem_range.1 hr) c (mem_range.1 hcw))]

open Classical in
/-- **Soundness of the AIR encoding.** For an unbalanced set of messages, the challenge pairs at which some permutation columns are accepted number at most N (W + 1) |K|, for N messages.

The columns may be chosen after the challenges. -/
theorem card_accepting_le [Fintype K] [DecidableEq K] (airs : List (AirMessages K)) {W : ℕ}
    (hW : 1 ≤ W) (hlen : ∀ p ∈ allMessages airs, p.1.2.length ≤ W)
    (hbus : ∀ p ∈ allMessages airs, ∀ q ∈ allMessages airs, (p.1.1 : K) = q.1.1 → p.1.1 = q.1.1)
    (hwidth : ∀ p ∈ allMessages airs, ∀ q ∈ allMessages airs, p.1.1 = q.1.1 →
      p.1.2.length = q.1.2.length)
    (hunbal : ¬ Balanced (allMessages airs)) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 W airs cols}
      ≤ (allMessages airs).length * (W + 1) * Fintype.card K := by
  refine le_trans (card_le_card fun x hx => ?_) (card_bad_challenges_le _ hW hlen hbus hwidth hunbal)
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨cols, hacc⟩ := hx
  by_cases hD : ∃ p ∈ allMessages airs, busDenom x.1 x.2 W p.1.1 p.1.2 = 0
  · exact Or.inl hD
  · simp only [not_exists, not_and] at hD
    exact Or.inr (busSum_eq_zero_of_accepts hacc hD)

end Plonky3Lean.Proofs.Lookup
