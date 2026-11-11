module

public import P3MultiStark.Mirror.Security
public import P3MultiStark.Mirror.Zerocheck
public import Plonky3Lean.Proofs.MultiStark.Zerocheck
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The AIR terms p3-security charges are the zerocheck's soundness error

p3-security charges four terms for the AIR reduction:

```text
    constraint-batching   (k - 1) / q
    air-batching          (A - 1) / q
    zerocheck             m / (q - 1)
    constraint-sumcheck   m (d + 1) / q
```

The first three bound the zerocheck's own error, proved by counting draws.

The last is the sumcheck's, at the round degree the verifier runs.

That degree is one more than the degree charged.

The verifier and the accounting agree on it.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.security.mirror Plonky3Lean.Spec.MultiStark Finset

/-! ## The round degree -/

theorem foldl_max_eq (ds : List ℕ) (a : ℕ) : ds.foldl max a = max a (ds.foldl max 0) := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (max 0 d)]; omega

/-- **The verifier's round degree is the charged degree plus one.**

With or without a bus, the verifier's sumcheck has exactly the degree p3-security charges for. -/
theorem round_degree_eq (ds : List ℕ) (bus : Option ℕ) :
    p3_multi_stark.zerocheck.mirror.round_degree ds bus = charged_degree ds bus + 1 := by
  cases bus <;> simp [p3_multi_stark.zerocheck.mirror.round_degree, charged_degree]; omega

/-- The variables charged are the zerocheck point's: the largest arity, or the lookup reduction's. -/
theorem num_variables_ge (heights : List ℕ) (lookup : Option ℕ) :
    ∀ h ∈ heights, h ≤ num_variables heights lookup := by
  intro h hh
  simp only [num_variables]
  suffices ∀ a, h ≤ heights.foldl max a from (this 0).trans (le_max_left _ _)
  induction heights with
  | nil => simp at hh
  | cons d ds ih =>
    intro a
    rcases List.mem_cons.mp hh with rfl | hh
    · rw [List.foldl_cons, foldl_max_eq]; omega
    · exact ih hh _

/-! ## The zerocheck terms -/

/-- A term's error as a rational: its numerator over the field's order, or one less. -/
def Term.value (q : ℕ) (t : Term) : ℚ :=
  t.numerator / match t.denominator with | .Field => (q : ℚ) | .NonZero => (q - 1 : ℚ)

theorem sum_filter_ne_zero (q : ℕ) : ∀ (l : List Term),
    ((l.filter (·.numerator ≠ 0)).map (Term.value q)).sum = (l.map (Term.value q)).sum
  | [] => rfl
  | t :: l => by
    have ih := sum_filter_ne_zero q l
    rw [List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    · rename_i h
      rw [ih, List.map_cons, List.sum_cons]
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        not_not] at h
      simp [Term.value, h]

/-- The three terms that bound the zerocheck, before the sumcheck's. -/
def zerocheckTerms (p : AirParams) : List Term :=
  (air_terms p).filter (·.label ≠ "constraint-sumcheck")

theorem sum_zerocheckTerms (q : ℕ) (p : AirParams) :
    ((zerocheckTerms p).map (Term.value q)).sum =
      ((p.max_num_constraints - 1 : ℕ) : ℚ) / q + ((p.num_instances - 1 : ℕ) : ℚ) / q +
        (p.num_variables : ℚ) / (q - 1) := by
  unfold zerocheckTerms air_terms
  rw [List.filter_filter]
  have : ∀ l : List Term, (l.filter fun t => decide (t.label ≠ "constraint-sumcheck") &&
      decide (t.numerator ≠ 0)) = (l.filter (·.label ≠ "constraint-sumcheck")).filter
        (·.numerator ≠ 0) := fun l => by rw [List.filter_filter]; congr; funext t; simp [Bool.and_comm]
  rw [this, sum_filter_ne_zero]
  simp [Term.value, List.filter]
  ring

/-- **The charged terms bound the zerocheck.**

Take an unsatisfied batch of A instances over at most m variables, with at most k constraints each.

Its zerocheck sum is zero on a fraction of the q^2 (q - 1)^m draws.

That fraction is at most the sum of three terms p3-security charges:

- constraint batching
- air batching
- zerocheck. -/
theorem zerocheck_error_le_terms {K : Type _} [Field K] [Fintype K] [DecidableEq K]
    {batch : List (Instance K)} (hsat : ¬ Satisfied batch) {m k : ℕ}
    (hm : ∀ A ∈ batch, A.log_height ≤ m) (hk : ∀ A ∈ batch, A.constraints.length ≤ k) (d : ℕ) :
    (#{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0} : ℚ) /
      ((Fintype.card K : ℚ) ^ 2 * ((Fintype.card K - 1 : ℕ) : ℚ) ^ m) ≤
      ((zerocheckTerms ⟨batch.length, k, m, d⟩).map (Term.value (Fintype.card K))).sum := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hq0 : (0 : ℚ) < Fintype.card K := by exact_mod_cast (by omega : 0 < Fintype.card K)
  have hq1 : (0 : ℚ) < ((Fintype.card K - 1 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 0 < Fintype.card K - 1)
  have hcast : (Fintype.card K : ℚ) - 1 = ((Fintype.card K - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hq.le, Nat.cast_one]
  rw [sum_zerocheckTerms, hcast, div_le_iff₀ (by positivity)]
  have h := card_zerocheck_eq_zero_le hsat hm hk
  have hb : (#{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0} : ℚ) ≤
      ((k - 1) * (Fintype.card K * (Fintype.card K - 1) ^ m) +
        Fintype.card K * ((batch.length - 1) * (Fintype.card K - 1) ^ m) +
        Fintype.card K * (Fintype.card K * (m * (Fintype.card K - 1) ^ (m - 1))) : ℕ) := by
    exact_mod_cast h
  refine hb.trans (le_of_eq ?_)
  push_cast
  rcases m with _ | m
  · field_simp; ring
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

end Plonky3Lean.Proofs.MultiStark
