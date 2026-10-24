module

public import P3BatchStark.Assumptions.Mirror.Check
public import Plonky3Lean.Proofs.Lookup.RunningSum
public import Plonky3Lean.Spec.UniStark
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# The debug checker and the selectors in a lookup count

The checker panics on a preprocessed or permutation trace of another height.

Otherwise it passes exactly when every row's AIR and lookup constraints pass with the 0/1 selectors.

The prover's permutation trace also reads the 0/1 selectors.

The STARK evaluates the Lagrange selectors instead.

A lookup count that reads a selector therefore has two consequences:

- the honest fraction m / d, with m the 0/1 value, meets the STARK's pin only where both values agree
- on row 0 the transition selector is 1 - omega^(n-1) in the STARK and 1 in the checker.

So the honest proof fails on row 0.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.checker.mirror p3_air.air.mirror p3_air.builder.mirror p3_lookup.mirror
  Plonky3Lean.Spec.Lookup Plonky3Lean.Spec.UniStark Plonky3Lean.Spec.Air

section Checker

variable {F : Type} [Field F] [DecidableEq F] [Inhabited F] {K : Type} [Field K] [Algebra F K]
  [DecidableEq K]

theorem forM_option_eq_some {α : Type} (l : List α) (f : α → Option Unit) :
    forM l f = some () ↔ ∀ x ∈ l, f x = some () := by
  induction l with
  | nil => simp
  | cons a l ih =>
    show (f a >>= fun _ => l.forM f) = _ ↔ _
    rcases hfa : f a with _ | u
    · simp [hfa]
    · simpa [hfa] using ih

/-- **The checker.**

With traces of one height, it passes exactly when every row's AIR and lookup constraints evaluate cleanly.

Cleanly means without panicking and without a failure.

With traces of another height it panics. -/
theorem check_constraints_eq_some (air : Air F) (main : Mat F) (prep : Option (Mat F)) (perm : Mat K)
    (ch vals : List K) (pv : List F) (lookups : List (Lookup F)) :
    p3_batch_stark.checker.mirror.check_constraints air main prep perm ch vals pv lookups = some () ↔
      (∀ p ∈ prep, p.height = main.height) ∧ perm.height = main.height ∧
      ∀ r < main.height, ∃ s, eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r)
        (DebugState.new r) lookups = some s ∧ s.failures = [] := by
  -- The row loop passes exactly when every row passes.
  have key : ((List.range main.height).forM fun r => do
      let s ← eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r) (DebugState.new r) lookups
      if s.failures ≠ [] then none else pure ()) = some () ↔
      ∀ r < main.height, ∃ s, eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r)
        (DebugState.new r) lookups = some s ∧ s.failures = [] := by
    refine (forM_option_eq_some _ _).trans (forall_congr' fun r => ?_)
    rw [List.mem_range]
    refine imp_congr_right fun _ => ?_
    rcases eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r) (DebugState.new r) lookups
      with _ | s
    · simp
    · by_cases hs : s.failures = [] <;> simp [hs]
  unfold p3_batch_stark.checker.mirror.check_constraints
  by_cases hp : ∀ q ∈ prep, q.height = main.height
  · have hp' : (prep.map fun q => decide (q.height ≠ main.height)).getD false = false := by
      rcases prep with _ | q <;> simp_all
    by_cases hm : perm.height = main.height
    · simp only [hp', Bool.false_eq_true, ↓reduceIte, hm, ne_eq, not_true_eq_false]
      exact key.trans ⟨fun h => ⟨hp, trivial, h⟩, fun h => h.2.2⟩
    · simp [hm]
  · have hp' : (prep.map fun q => decide (q.height ≠ main.height)).getD false = true := by
      rcases prep with _ | q <;> simp_all
    simp only [hp', ↓reduceIte]
    exact iff_of_false (by simp) fun h => hp h.1

end Checker

section Selectors

variable {K : Type _} [Field K]

/-- With a nonzero denominator d, the fraction m / d is pinned for the count c exactly when c = m. -/
theorem pin_single_iff {d c m : K} (hd : d ≠ 0) : Pinned [(d, c)] (m / d) ↔ c = m := by
  rw [Plonky3Lean.Proofs.Lookup.pinned_iff (by simp [den, hd])]
  simp [fracSum, mul, den]
  constructor
  · intro h; field_simp at h; exact h.symm
  · rintro rfl; rfl

/-- **The honest fraction under the STARK's selectors.**

Take a count reading a selector v on row i.

The prover's fraction m / d, with m the 0/1 value, meets the STARK's pin exactly when the two values agree. -/
theorem selector_count_pinned_iff (T : Instance K) (ω : K) (i : ℕ) (v : Var) {d : K} (hd : d ≠ 0) :
    Pinned [(d, starkRowEnv T ω i v)] (rowEnv T i v / d) ↔ starkRowEnv T ω i v = rowEnv T i v :=
  pin_single_iff hd

/-- **The transition selector on row 0.**

On a trace of n >= 2 rows, the STARK evaluates it to 1 - omega^(n-1), never 1.

So a count reading it pins no honest fraction on row 0. -/
theorem transition_row0_ne (T : Instance K) {ω : K} (hω : IsPrimitiveRoot ω T.height) (hn : 2 ≤ T.height)
    {d : K} (hd : d ≠ 0) :
    starkRowEnv T ω 0 .isTransition ≠ rowEnv T 0 .isTransition ∧
      ¬ Pinned [(d, starkRowEnv T ω 0 .isTransition)] (rowEnv T 0 .isTransition / d) := by
  have hne : starkRowEnv T ω 0 .isTransition ≠ rowEnv T 0 .isTransition := by
    have h0 : ω ≠ 0 := hω.ne_zero (by omega)
    have hne0 : (0 : ℕ) ≠ T.height - 1 := by omega
    simp only [starkRowEnv, rowEnv, pow_zero, hne0, ↓reduceIte]
    intro h
    exact pow_ne_zero _ h0 (by linear_combination -h)
  exact ⟨hne, fun h => hne ((selector_count_pinned_iff T ω 0 _ hd).1 h)⟩

/-- The first-row selector on row 0 is n in the STARK and 1 in the checker. -/
theorem first_row0 (T : Instance K) (ω : K) :
    starkRowEnv T ω 0 .isFirstRow = T.height ∧ rowEnv T 0 .isFirstRow = 1 := by
  simp [starkRowEnv, rowEnv]

end Selectors

end Plonky3Lean.Proofs.BatchStark
