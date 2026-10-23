module

public import Plonky3Lean.Proofs.Lookup.Gadget
public import Plonky3Lean.Proofs.Air.Semantics

@[expose] public section

/-!
# The lookup constraints on a row

On the debug builder of one row, the transcribed fraction pin asserts U f - V, and the accumulator asserts its three selector-gated equations.

Over every row of a trace, the constraints hold exactly when the columns form a constrained running sum and every fraction is pinned.
-/

namespace Plonky3Lean.Proofs.Lookup

open Plonky3Lean.Spec.Lookup Finset p3_lookup.mirror p3_air.symbolic.mirror p3_air.builder.mirror
  p3_air.air.mirror Plonky3Lean.Proofs.Air

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [DecidableEq F] {K : Type} [Field K] [Algebra F K] [DecidableEq K]

/-- The debug permutation builder of one row: the debug extension builder, the extension field, and the permutation window, challenges and values. -/
def rowPermBuilder (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
    (periodic : List F) (perm : RowWindow K) (randomness values : List K) :
    PermBuilder F F K DebugState where
  toExtensionBuilder := debugExtBuilder main preprocessed pv first last trans periodic
  ext := fieldOps K
  ext_of := algebraMap F K
  permutation _ := perm
  permutation_randomness _ := randomness
  permutation_values _ := values

/-- Failures only grow. -/
theorem failures_assert_zero {T : Type _} [Zero T] [DecidableEq T] (s : DebugState) (x : T) :
    ∃ l, (s.assert_zero x).failures = s.failures ++ l := by
  unfold DebugState.assert_zero; split_ifs <;> simp

theorem foldl_exclusive (xs : List ((K × K) × K)) (a b c : K) :
    xs.foldl (fun (st : K × K × K) x => (st.1 + x.1.1 * x.2, st.2.1 + x.1.1 * x.1.2, st.2.2 + x.1.1))
      (a, b, c) =
      (a + (xs.map fun x => x.1.1 * x.2).sum, b + (xs.map fun x => x.1.1 * x.1.2).sum,
        c + (xs.map fun x => x.1.1).sum) := by
  induction xs generalizing a b c with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih]; simp [add_assoc]

/-- **The exclusive fold**: N = sum_k f_k m_k and D = sum_k f_k t_k + 1 - sum_k f_k, over the branches (f_k, t_k, m_k). -/
theorem compute_exclusive_terms_field (flags : List K) (elements : List (List K)) (mults : List K)
    (α β : K) (hf : flags.length = elements.length) (hm : mults.length = elements.length) :
    let xs := (flags.zip (elements.map fun e => α - fingerprint β e)).zip mults
    compute_exclusive_terms (fieldOps K) flags elements mults α β =
      some ((xs.map fun x => x.1.1 * x.2).sum,
        (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum)) := by
  intro xs
  unfold compute_exclusive_terms
  rw [combine_elements_field]
  have h1 : (flags.zip (elements.map fun e => α - fingerprint β e)).length = mults.length := by
    simp [hf, hm]
  simp only [zip_eq, List.length_map, hf, ite_true, h1, Option.bind_eq_bind, Option.bind_some]
  simp only [fieldOps]
  rw [foldl_exclusive]; simp [xs]

/-- With exactly one active branch, the column holds that branch: N = m_j and D = t_j. -/
theorem exclusive_one_hot (xs : List ((K × K) × K)) {j : ℕ} (hj : j < xs.length)
    (hflag : ∀ k (h : k < xs.length), xs[k].1.1 = if k = j then 1 else 0) :
    (xs.map fun x => x.1.1 * x.2).sum = xs[j].2 ∧
      (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum) = xs[j].1.2 := by
  have key : ∀ g : (K × K) × K → K, (xs.map fun x => x.1.1 * g x).sum = g xs[j] := by
    intro g
    rw [list_sum_map_eq_sum_range _ _ ((0, 0), 0), sum_eq_single_of_mem j (mem_range.2 hj)]
    · simp [List.getD_eq_getElem?_getD, hj, hflag j hj]
    · intro k hk hkj
      simp [List.getD_eq_getElem?_getD, mem_range.1 hk, hflag k (mem_range.1 hk), hkj]
  refine ⟨key (·.2), ?_⟩
  have := key fun _ => 1
  simp only [mul_one] at this
  rw [key (·.1.2), this, sub_self, add_zero]

/-- With no active branch, the column holds zero: N = 0 and D = 1. -/
theorem exclusive_none (xs : List ((K × K) × K)) (hflag : ∀ x ∈ xs, x.1.1 = 0) :
    (xs.map fun x => x.1.1 * x.2).sum = 0 ∧
      (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum) = 1 := by
  have h0 : ∀ g : (K × K) × K → K, (xs.map fun x => x.1.1 * g x).sum = 0 := fun g =>
    List.sum_eq_zero fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; rw [hflag x hx, zero_mul]
  refine ⟨h0 (·.2), ?_⟩
  have := h0 fun _ => 1
  simp only [mul_one] at this
  rw [h0 (·.1.2), this]; ring

theorem length_of_mapM_some {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; simp [h.symm]
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, _, l'', hl, rfl⟩ := h
    simp [length_of_mapM_some hl]

section Row

variable (main preprocessed : RowWindow F) (pv : List F) (first last trans : F) (periodic : List F)
  (perm : RowWindow K) (randomness values : List K) (s : DebugState)

/-- **The additive fraction pin on a row** asserts U f - V, for the resolved tuples and multiplicities and the lookup's challenges. -/
theorem eval_fraction_additive (lookup : Lookup F) (hflags : lookup.flags = none)
    (hlen : lookup.elements.length = lookup.multiplicities.length) {ev : List (List K)} {mv : List K}
    (hev : lookup.elements.mapM (fun exprs => exprs.mapM fun e =>
      (resolve (debugBuilder main preprocessed pv first last trans periodic) s e).map
        (algebraMap F K)) = some ev)
    (hmv : lookup.multiplicities.mapM (fun e =>
      (resolve (debugBuilder main preprocessed pv first last trans periodic) s e).map
        (algebraMap F K)) = some mv)
    {α β f : K} (hα : randomness[2 * lookup.column]? = some α)
    (hβ : randomness[2 * lookup.column + 1]? = some β) (hf : perm.current[lookup.column + 1]? = some f) :
    eval_fraction (rowPermBuilder main preprocessed pv first last trans periodic perm randomness values)
      s lookup =
      some (s.assert_zero (denominator (rowTerms ev mv α β) * f - numerator (rowTerms ev mv α β))) := by
  have hevl := length_of_mapM_some hev
  have hmvl := length_of_mapM_some hmv
  have hr : ¬ randomness.length < 2 * (lookup.column + 1) := by
    have := (List.getElem?_eq_some_iff.1 hβ).1; omega
  unfold eval_fraction
  simp only [rowPermBuilder, debugExtBuilder]
  simp only [hlen, ne_eq, not_true_eq_false, ite_false, hev, hmv, hflags, Option.getD_none,
    List.mapM_nil, Option.bind_eq_bind, Option.bind_some, hr, hα, hβ, hf]
  rw [compute_combined_sum_terms_field _ _ _ _ (by omega)]
  rfl

end Row

/-! ## The accumulator -/

theorem failures_assert_zero_eq {T : Type _} [Zero T] [DecidableEq T] (s : DebugState) (x : T) :
    (s.assert_zero x).failures = s.failures ++ if x ≠ 0 then [⟨s.row_index, s.constraint_index⟩] else [] := by
  unfold DebugState.assert_zero; split_ifs <;> simp

theorem row_index_assert_zero {T : Type _} [Zero T] [DecidableEq T] (s : DebugState) (x : T) :
    (s.assert_zero x).row_index = s.row_index := rfl

/-- Three assertions in a row leave the failures unchanged exactly when each value is zero. -/
theorem failures_three {T : Type _} [Zero T] [DecidableEq T] (s : DebugState) (x y z : T) :
    (((s.assert_zero x).assert_zero y).assert_zero z).failures = s.failures ↔
      x = 0 ∧ y = 0 ∧ z = 0 := by
  simp [failures_assert_zero_eq]

/-- The permutation window of row r of n: rows r and r + 1 mod n of the columns P. -/
def permWindow (P : ℕ → ℕ → K) (n width r : ℕ) : RowWindow K :=
  ⟨(List.range width).map (P r), (List.range width).map (P ((r + 1) % n))⟩

theorem foldlM_row_sum (g : Lookup F → Option K) (P : ℕ → K) (l' : List (Lookup F)) (a : K)
    (hl : ∀ l ∈ l', g l = some (P (l.column + 1))) :
    l'.foldlM (fun sum (l : Lookup F) => (g l).bind fun v => some (sum + v)) a =
      some (a + (l'.map fun l => P (l.column + 1)).sum) := by
  induction l' generalizing a with
  | nil => simp
  | cons x l' ih =>
    simp only [List.foldlM_cons, hl x List.mem_cons_self, Option.bind_some, Option.bind_eq_bind]
    rw [ih _ fun l hl' => hl l (List.mem_cons_of_mem _ hl')]
    simp [add_assoc]

theorem sum_columns (P : ℕ → K) (lookups : List (Lookup F))
    (hcol : ∀ i (h : i < lookups.length), lookups[i].column = i) :
    (lookups.map fun l => P (l.column + 1)).sum = ∑ c ∈ range lookups.length, P (c + 1) := by
  rw [list_sum_map_eq_sum_range _ _ ⟨.Local, [], [], 0, 0, none⟩]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, hi, hcol i hi]

section AccRow

variable (main preprocessed : RowWindow F) (pv : List F) (first last trans : F) (periodic : List F)
  (randomness values : List K) (s : DebugState)

/-- **The accumulator on a row** asserts acc = 0 through the first-row selector, acc' = acc + row sum through the transition selector, and terminal = acc + row sum through the last-row selector. -/
theorem eval_accumulator_row (P : ℕ → ℕ → K) (n r : ℕ) (lookups : List (Lookup F))
    (hcol : ∀ i (h : i < lookups.length), lookups[i].column = i) (T : K) :
    ∃ s', eval_accumulator (rowPermBuilder main preprocessed pv first last trans periodic
      (permWindow P n (lookups.length + 1) r) randomness values) s lookups T = some s' ∧
      (s'.failures = s.failures ↔
        P r 0 * algebraMap F K first = 0 ∧
        (P ((r + 1) % n) 0 - P r 0 - ∑ c ∈ range lookups.length, P r (c + 1)) *
          algebraMap F K trans = 0 ∧
        (T - P r 0 - ∑ c ∈ range lookups.length, P r (c + 1)) * algebraMap F K last = 0) := by
  have hmem : ∀ l ∈ lookups, l.column < lookups.length := fun l hl => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl; rw [hcol i hi]; exact hi
  have hsum := foldlM_row_sum (F := F)
    (fun l => Option.map (P r) (List.range (lookups.length + 1))[l.column + 1]?) (P r) lookups 0
    fun l hl => by rw [List.getElem?_range (by have := hmem l hl; omega)]; rfl
  rw [sum_columns (P r) lookups hcol, zero_add] at hsum
  unfold eval_accumulator
  simp only [rowPermBuilder, permWindow, List.length_map, List.length_range,
    show lookups.length + 1 > lookups.length by omega, not_true_eq_false, ite_false,
    List.getElem?_map, List.getElem?_range (show 0 < lookups.length + 1 by omega), Option.map_some,
    Option.bind_eq_bind, Option.bind_some]
  simp only [fieldOps, Option.pure_def]
  rw [hsum, Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  simp only [ExtensionBuilder.when, debugExtBuilder]
  exact failures_three _ _ _ _

end AccRow

/-- The running sum read from permutation columns: column 0 is the accumulator, column c + 1 the fraction of lookup c. -/
def columnsOf (P : ℕ → ℕ → K) (T : K) : RunningSum K := ⟨fun r => P r 0, fun r c => P r (c + 1), T⟩

/-- **The accumulator over a trace.** On a trace of n >= 1 rows, the accumulator constraints pass on every row exactly when the columns form a constrained running sum. -/
theorem accumulator_trace_iff (main preprocessed : ℕ → RowWindow F) (pv : List F)
    (periodic : ℕ → List F) (randomness values : List K) (s : ℕ → DebugState)
    (P : ℕ → ℕ → K) {n : ℕ} (hn : 0 < n) (lookups : List (Lookup F))
    (hcol : ∀ i (h : i < lookups.length), lookups[i].column = i) (T : K) :
    (∀ r < n, ∃ s', eval_accumulator (rowPermBuilder (main r) (preprocessed r) pv
      (if r = 0 then 1 else 0) (if r = n - 1 then 1 else 0) (if r ≠ n - 1 then 1 else 0)
      (periodic r) (permWindow P n (lookups.length + 1) r) randomness values) (s r) lookups T =
        some s' ∧ s'.failures = (s r).failures) ↔
      (columnsOf P T).Constrained n lookups.length := by
  have row := fun r => eval_accumulator_row (main r) (preprocessed r) pv (if r = 0 then 1 else 0)
    (if r = n - 1 then 1 else 0) (if r ≠ n - 1 then 1 else 0) (periodic r) randomness values (s r) P
    n r lookups hcol T
  have pass : ∀ r, (∃ s', eval_accumulator (rowPermBuilder (main r) (preprocessed r) pv
      (if r = 0 then 1 else 0) (if r = n - 1 then 1 else 0) (if r ≠ n - 1 then 1 else 0)
      (periodic r) (permWindow P n (lookups.length + 1) r) randomness values) (s r) lookups T =
        some s' ∧ s'.failures = (s r).failures) ↔ _ := fun r => by
    obtain ⟨s', h1, h2⟩ := row r
    exact ⟨fun ⟨t, ht, ht'⟩ => h2.1 (Option.some.inj (h1.symm.trans ht) ▸ ht'),
      fun h => ⟨s', h1, h2.2 h⟩⟩
  simp only [pass]
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_, ?_⟩
    · have := (h 0 hn).1; simpa [columnsOf] using this
    · have := (h r (by omega)).2.1
      simp only [show r ≠ n - 1 by omega, ne_eq, not_false_eq_true, ite_true, map_one,
        mul_one, sub_eq_zero, Nat.mod_eq_of_lt hr] at this
      simp only [columnsOf, RunningSum.rowSum]; rw [← this]; ring
    · have := (h (n - 1) (by omega)).2.2
      simp only [ite_true, map_one, mul_one, sub_eq_zero] at this
      simp only [columnsOf, RunningSum.rowSum]; rw [← this]; ring
  · intro hc r hr
    refine ⟨?_, ?_, ?_⟩
    · by_cases h0 : r = 0
      · subst h0; simpa [columnsOf] using hc.first
      · simp [h0]
    · by_cases hl : r = n - 1
      · simp [hl]
      · have := hc.transition r (by omega)
        simp only [columnsOf, RunningSum.rowSum] at this
        simp [hl, Nat.mod_eq_of_lt (show r + 1 < n by omega), this]
    · by_cases hl : r = n - 1
      · subst hl; have := hc.last
        simp only [columnsOf, RunningSum.rowSum] at this
        simp [this]
      · simp [hl]

end Plonky3Lean.Proofs.Lookup
