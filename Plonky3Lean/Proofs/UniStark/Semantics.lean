module

public import Plonky3Lean.Spec.UniStark
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The STARK's selectors are not 0/1

On row i, a selector of the STARK is zero exactly where the 0/1 selector is zero.

So a constraint that is a product of selectors times a selector-free polynomial vanishes on the same rows either way.

A constraint that adds two selector-filtered terms does not: the two terms are weighted differently.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Plonky3Lean.Spec.Air Plonky3Lean.Spec.UniStark

variable {F : Type _} [Field F]

/-- The STARK and the reference semantics agree on every variable that is not a selector. -/
theorem starkRowEnv_of_not_selector (T : Instance F) (ω : F) (i : ℕ) {v : Var}
    (hv : ¬ IsSelector v) : starkRowEnv T ω i v = rowEnv T i v := by
  cases v <;> simp_all [IsSelector, starkRowEnv]

/-- On a row of the trace, a selector of the STARK vanishes exactly where the 0/1 selector does. -/
theorem starkRowEnv_eq_zero_iff {T : Instance F} {ω : F} (hω : IsPrimitiveRoot ω T.height)
    (hn : (T.height : F) ≠ 0) {i : ℕ} (hi : i < T.height) {v : Var} (hv : IsSelector v) :
    starkRowEnv T ω i v = 0 ↔ rowEnv T i v = 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  cases v <;> simp only [IsSelector] at hv
  · by_cases h : i = 0 <;> simp [starkRowEnv, rowEnv, h, hn]
  · by_cases h : i = T.height - 1 <;> simp [starkRowEnv, rowEnv, h, hn, hω0]
  · have : ω ^ i = ω ^ (T.height - 1) ↔ i = T.height - 1 := ⟨hω.pow_inj hi (by omega), fun h => h ▸ rfl⟩
    simp [starkRowEnv, rowEnv, sub_eq_zero, this]

/-- A constraint in selector form vanishes on a row with the STARK's selectors exactly when it does with 0/1 selectors. -/
theorem eval_starkRowEnv_eq_zero_iff {T : Instance F} {ω : F} (hω : IsPrimitiveRoot ω T.height)
    (hn : (T.height : F) ≠ 0) {i : ℕ} (hi : i < T.height) {c : MvPolynomial Var F}
    (hc : SelectorSeparated c) :
    MvPolynomial.eval (starkRowEnv T ω i) c = 0 ↔ MvPolynomial.eval (rowEnv T i) c = 0 := by
  obtain ⟨ss, p, hss, hp, rfl⟩ := hc
  have hpe : MvPolynomial.eval (starkRowEnv T ω i) p = MvPolynomial.eval (rowEnv T i) p :=
    MvPolynomial.eval₂Hom_congr' rfl (fun v hv _ => starkRowEnv_of_not_selector T ω i (hp v hv)) rfl
  simp only [map_mul, map_list_prod, List.map_map, mul_eq_zero, List.prod_eq_zero_iff,
    List.mem_map, Function.comp_apply, MvPolynomial.eval_X, hpe]
  refine or_congr ?_ Iff.rfl
  constructor <;> rintro ⟨s, hs, h⟩ <;> exact ⟨s, hs, by simpa [starkRowEnv_eq_zero_iff hω hn hi (hss s hs)] using h⟩

/-- On constraints in selector form, the STARK's relation is the AIR's. -/
theorem satisfiesStark_iff {C : List (MvPolynomial Var F)} {T : Instance F} {ω : F}
    (hω : IsPrimitiveRoot ω T.height) (hn : (T.height : F) ≠ 0)
    (hC : ∀ c ∈ C, SelectorSeparated c) : SatisfiesStark C T ω ↔ Satisfies C T :=
  forall₂_congr fun _ hi => forall₂_congr fun c hc => eval_starkRowEnv_eq_zero_iff hω hn hi (hC c hc)

/-! ## Adding two filtered terms -/

/-- The constraint is_first_row a + is_transition b, with a and b the first two columns. -/
noncomputable def firstPlusTransition : MvPolynomial Var F :=
  .X .isFirstRow * .X (.main 0 0) + .X .isTransition * .X (.main 0 1)

/-- A trace of n rows whose two columns are (a, b) on row 0 and zero elsewhere. -/
def rowZeroTrace (n : ℕ) (a b : F) : Instance F where
  height := n
  main i c := if i = 0 then (if c = 0 then a else if c = 1 then b else 0) else 0
  prep _ _ := 0
  pub _ := 0
  periodic _ _ := 0

theorem eval_firstPlusTransition_rowZero {n : ℕ} (hn : 2 ≤ n) (a b ω : F) {i : ℕ} (hi : i < n) :
    MvPolynomial.eval (rowEnv (rowZeroTrace n a b) i) firstPlusTransition =
        (if i = 0 then a + b else 0) ∧
      MvPolynomial.eval (starkRowEnv (rowZeroTrace n a b) ω i) firstPlusTransition =
        (if i = 0 then n * a + (1 - ω ^ (n - 1)) * b else 0) := by
  have h0 : (0 : ℕ) ≠ n - 1 := by omega
  by_cases h : i = 0
  · subst h; simp [firstPlusTransition, rowEnv, starkRowEnv, rowZeroTrace, h0]
  · simp [firstPlusTransition, rowEnv, starkRowEnv, rowZeroTrace, h]

/-- When (1 - n)^n != 1, the two semantics disagree in both directions.

The trace with (a, b) = (1, -1) on row 0 satisfies the AIR, and the STARK rejects it.

The trace with (a, b) = ((1 - omega^(n-1)) / n, -1) on row 0 satisfies the STARK, and the AIR rejects it. -/
theorem firstPlusTransition_disagree {n : ℕ} (hn : 2 ≤ n) {ω : F} (hω : IsPrimitiveRoot ω n)
    (hn0 : (n : F) ≠ 0) (h : (1 - n : F) ^ n ≠ 1) :
    (Satisfies [firstPlusTransition] (rowZeroTrace (F := F) n 1 (-1)) ∧
      ¬ SatisfiesStark [firstPlusTransition] (rowZeroTrace (F := F) n 1 (-1)) ω) ∧
    (SatisfiesStark [firstPlusTransition] (rowZeroTrace n ((1 - ω ^ (n - 1)) / n) (-1)) ω ∧
      ¬ Satisfies [firstPlusTransition] (rowZeroTrace n ((1 - ω ^ (n - 1)) / n) (-1))) := by
  have hne : ω ^ (n - 1) ≠ 1 - n := by
    intro he
    apply h
    rw [← he, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hpos : 0 < n := by omega
  simp only [Satisfies, SatisfiesStark, List.mem_singleton, forall_eq]
  refine ⟨⟨fun i hi => ?_, fun hs => ?_⟩, ⟨fun i hi => ?_, fun hs => ?_⟩⟩
  · rw [(eval_firstPlusTransition_rowZero hn _ _ ω hi).1]; simp
  · have := hs 0 hpos
    rw [(eval_firstPlusTransition_rowZero hn _ _ ω hpos).2] at this
    exact hne (by simp at this; linear_combination this)
  · rw [(eval_firstPlusTransition_rowZero hn _ _ ω hi).2]
    split_ifs
    · field_simp; ring
    · rfl
  · have := hs 0 hpos
    rw [(eval_firstPlusTransition_rowZero hn _ _ ω hpos).1] at this
    simp only [ite_true] at this
    field_simp at this
    exact hne (by linear_combination -this)

end Plonky3Lean.Proofs.UniStark
