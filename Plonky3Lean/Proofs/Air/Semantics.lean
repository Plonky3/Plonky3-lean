module

public import Plonky3Lean.Proofs.Air.Check

@[expose] public section

/-!
# What the builder combinators mean

The selector form of an AIR and its domain form describe the same traces.

On the debug builder, each combinator accepts exactly the values its name promises.

Resolving a symbolic expression on the debug builder evaluates the polynomial it denotes.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Domains and selectors -/

/-- On a row of the trace, a domain's selector is 1 on the domain and 0 off it. -/
theorem eval_selector (T : Instance F) {i : ℕ} (hi : i < T.height) (d : Domain) :
    MvPolynomial.eval (rowEnv T i) d.selector = if d.Contains T.height i then 1 else 0 := by
  have h1 : i = T.height - 1 ↔ i + 1 = T.height := by omega
  have h2 : i + 1 < T.height ↔ ¬ i + 1 = T.height := by omega
  cases d <;> simp [Domain.selector, Domain.Contains, rowEnv, h1, h2, ite_not]

/-- The selector form and the domain form of an AIR describe the same traces. -/
theorem satisfies_selector_iff (C : List (Constraint F)) (T : Instance F) :
    Satisfies (C.map fun c => c.domain.selector * c.poly) T ↔ SatisfiesOn C T := by
  simp only [Satisfies, SatisfiesOn, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, map_mul]
  constructor
  · intro h c hc i hi hd
    simpa [eval_selector T hi, hd] using h i hi c hc
  · intro h i hi c hc
    rw [eval_selector T hi]
    split_ifs with hd
    · simp [h c hc i hi hd]
    · simp

/-- On a trace of one row, a transition constraint asks nothing. -/
theorem transition_vacuous_of_height_one (p : MvPolynomial Var F) (T : Instance F)
    (h : T.height = 1) : SatisfiesOn [⟨.transition, p⟩] T := by
  simp [SatisfiesOn, Domain.Contains, h]

/-- On a trace of no rows, every constraint holds, even a nonzero constant. -/
theorem satisfies_of_height_zero (C : List (MvPolynomial Var F)) (T : Instance F)
    (h : T.height = 0) : Satisfies C T := by
  simp [Satisfies, h]

/-- A nonzero constant constraint fails on every trace with a row. -/
theorem not_satisfies_const {c : F} (hc : c ≠ 0) (T : Instance F) (h : 0 < T.height) :
    ¬ Satisfies [MvPolynomial.C c] T := by
  simp only [Satisfies, List.mem_singleton, forall_eq, MvPolynomial.eval_C, not_forall]
  exact ⟨0, h, hc⟩

/-- The next row of the last row is row 0. -/
theorem rowEnv_next_last (T : Instance F) (h : 0 < T.height) (c : ℕ) :
    rowEnv T (T.height - 1) (.main 1 c) = T.main 0 c := by
  simp [rowEnv, Nat.sub_add_cancel h]

/-! ## The debug builder's combinators -/

section debug

variable (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
  (periodic : List F) (s : DebugState)

/-- The debug builder of one row. -/
abbrev dbg : AirBuilder F F DebugState := debugBuilder main preprocessed pv first last trans periodic

theorem assert_zero_failures {T : Type _} [Zero T] [DecidableEq T] (x : T) :
    (s.assert_zero x).failures = s.failures ↔ x = 0 := by
  by_cases hx : x = 0 <;> simp [DebugState.assert_zero, hx]

/-- The debug builder accepts exactly zero. -/
theorem dbg_assert_zero (x : F) :
    ((dbg main preprocessed pv first last trans periodic).assert_zero s x).failures = s.failures ↔
      x = 0 :=
  assert_zero_failures s x

/-- Through a condition, it accepts x exactly when the condition or x is zero. -/
theorem dbg_when (c x : F) :
    (((dbg main preprocessed pv first last trans periodic).when c).assert_zero s x).failures =
      s.failures ↔ c = 0 ∨ x = 0 := by
  simp [AirBuilder.when, debugBuilder, assert_zero_failures]

/-- Through two conditions, it accepts x exactly when one of them or x is zero. -/
theorem dbg_when_when (c d x : F) :
    ((((dbg main preprocessed pv first last trans periodic).when c).when d).assert_zero s
      x).failures = s.failures ↔ c = 0 ∨ d = 0 ∨ x = 0 := by
  simp [AirBuilder.when, debugBuilder, assert_zero_failures]

/-- Where a and b differ, it asks x to be zero. -/
theorem dbg_when_ne (a b x : F) :
    (((dbg main preprocessed pv first last trans periodic).when_ne a b).assert_zero s
      x).failures = s.failures ↔ (a ≠ b → x = 0) := by
  simp [AirBuilder.when_ne, AirBuilder.when, debugBuilder, assert_zero_failures, sub_eq_zero,
    or_iff_not_imp_left]

/-- It accepts x and y as equal exactly when they are. -/
theorem dbg_assert_eq (x y : F) :
    ((dbg main preprocessed pv first last trans periodic).assert_eq s x y).failures =
      s.failures ↔ x = y := by
  simp [AirBuilder.assert_eq, debugBuilder, assert_zero_failures, sub_eq_zero]

/-- It accepts x as one exactly when it is. -/
theorem dbg_assert_one (x : F) :
    ((dbg main preprocessed pv first last trans periodic).assert_one s x).failures =
      s.failures ↔ x = 1 := by
  simp [AirBuilder.assert_one, debugBuilder, assert_zero_failures, sub_eq_zero]

/-- It accepts x as boolean exactly when x is 0 or 1. -/
theorem dbg_assert_bool (x : F) :
    ((dbg main preprocessed pv first last trans periodic).assert_bool s x).failures =
      s.failures ↔ x = 0 ∨ x = 1 := by
  simp [AirBuilder.assert_bool, AirBuilder.bool_check, debugBuilder, assert_zero_failures,
    sub_eq_zero]

theorem foldl_assert_zero_failures {T : Type _} [Zero T] [DecidableEq T] (xs : List T)
    (s : DebugState) : ∃ L, (xs.foldl DebugState.assert_zero s).failures = s.failures ++ L ∧
      (L = [] ↔ ∀ x ∈ xs, x = 0) := by
  induction xs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
    obtain ⟨L, hL, hL0⟩ := ih (s.assert_zero x)
    by_cases hx : x = 0 <;>
      refine ⟨_, by simpa [DebugState.assert_zero, hx] using hL, ?_⟩ <;> simp [hx, hL0]

/-- Asserting a list from a state records no failure exactly when every value is zero. -/
theorem dbg_assert_zeros (xs : List F) :
    ((dbg main preprocessed pv first last trans periodic).assert_zeros s xs).failures =
      s.failures ↔ ∀ x ∈ xs, x = 0 := by
  obtain ⟨L, hL, hL0⟩ := foldl_assert_zero_failures xs s
  change (xs.foldl DebugState.assert_zero s).failures = s.failures ↔ _
  rw [hL, List.append_right_eq_self, hL0]

end debug

section rows

variable [Inhabited F] (air : Air F) (M : Mat F) (pv : List F) (s : DebugState)

/-- On row i of the check, the first-row filter asks x to vanish on row 0 only. -/
theorem row_when_first_row (i : ℕ) (x : F) :
    ((((rowBuilder air M pv i).when_first_row s)).assert_zero s x).failures = s.failures ↔
      (i = 0 → x = 0) := by
  simp [AirBuilder.when_first_row, AirBuilder.when, rowBuilder, debugBuilder, assert_zero_failures]

/-- On row i of the check, the last-row filter asks x to vanish on row n - 1 only. -/
theorem row_when_last_row (i : ℕ) (x : F) :
    ((((rowBuilder air M pv i).when_last_row s)).assert_zero s x).failures = s.failures ↔
      (i = M.height - 1 → x = 0) := by
  simp [AirBuilder.when_last_row, AirBuilder.when, rowBuilder, debugBuilder, assert_zero_failures]

/-- On row i of the check, the transition filter asks x to vanish on every row but n - 1. -/
theorem row_when_transition (i : ℕ) (x : F) :
    ((((rowBuilder air M pv i).when_transition s)).assert_zero s x).failures = s.failures ↔
      (i ≠ M.height - 1 → x = 0) := by
  simp [AirBuilder.when_transition, AirBuilder.when, rowBuilder, debugBuilder,
    assert_zero_failures]

/-- On a trace of one row, the transition filter accepts anything. -/
theorem row_when_transition_height_one (x : F) (h : M.height = 1) :
    ((((rowBuilder air M pv 0).when_transition s)).assert_zero s x).failures = s.failures := by
  simp [row_when_transition, h]

/-- The transition window of size at most 2 is the transition selector, and a larger one panics. -/
theorem row_is_transition_window (i size : ℕ) :
    (rowBuilder air M pv i).is_transition_window s size =
      if size ≤ 2 then some (if i ≠ M.height - 1 then 1 else 0) else none := by
  simp [AirBuilder.is_transition_window, rowBuilder, debugBuilder]

end rows

/-! ## Extension assertions -/

section ext

variable {EF : Type} [Field EF] [Algebra F EF] [DecidableEq EF]
  (main preprocessed : RowWindow F) (pv : List F) (first last trans : F) (periodic : List F)
  (s : DebugState)

/-- The debug extension builder of one row. -/
abbrev dbgExt : ExtensionBuilder F F EF DebugState :=
  debugExtBuilder main preprocessed pv first last trans periodic

/-- The debug builder accepts exactly zero in the extension. -/
theorem dbgExt_assert_zero_ext (x : EF) :
    ((dbgExt main preprocessed pv first last trans periodic).assert_zero_ext s x).failures =
      s.failures ↔ x = 0 :=
  assert_zero_failures s x

/-- Through a base condition, it accepts an extension value exactly when the condition or the value is zero. -/
theorem dbgExt_when (c : F) (x : EF) :
    (((dbgExt main preprocessed pv first last trans periodic).when c).assert_zero_ext s
      x).failures = s.failures ↔ c = 0 ∨ x = 0 := by
  simp [ExtensionBuilder.when, debugExtBuilder, assert_zero_failures, or_comm]

/-- It accepts two extension values as equal exactly when they are. -/
theorem dbgExt_assert_eq_ext (x y : EF) :
    ((dbgExt main preprocessed pv first last trans periodic).assert_eq_ext s x y).failures =
      s.failures ↔ x = y := by
  simp [ExtensionBuilder.assert_eq_ext, debugExtBuilder, assert_zero_failures, sub_eq_zero]

/-- It accepts an extension value as one exactly when it is. -/
theorem dbgExt_assert_one_ext (x : EF) :
    ((dbgExt main preprocessed pv first last trans periodic).assert_one_ext s x).failures =
      s.failures ↔ x = 1 := by
  simp [ExtensionBuilder.assert_one_ext, ExtensionBuilder.assert_eq_ext, debugExtBuilder,
    assert_zero_failures, sub_eq_zero]

end ext

/-! ## Resolving on the debug builder -/

/-- The values of the variables a debug builder of one row holds.

An entry past a window reads 0. -/
def windowEnv (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
    (periodic : List F) : Var → F
  | .main 0 c => main.current.getD c 0
  | .main 1 c => main.next.getD c 0
  | .prep 0 c => preprocessed.current.getD c 0
  | .prep 1 c => preprocessed.next.getD c 0
  | .pub j => pv.getD j 0
  | .periodic j => periodic.getD j 0
  | .isFirstRow => first
  | .isLastRow => last
  | .isTransition => trans

/-- Every variable leaf names offset 0 or 1 and an entry the debug builder holds. -/
def InScope (main preprocessed : RowWindow F) (pv periodic : List F) :
    SymbolicExpression F → Prop
  | .Leaf (.Variable v) =>
    match v.entry with
    | .Main 0 => v.index < main.current.length
    | .Main 1 => v.index < main.next.length
    | .Preprocessed 0 => v.index < preprocessed.current.length
    | .Preprocessed 1 => v.index < preprocessed.next.length
    | .Public => v.index < pv.length
    | .Periodic => v.index < periodic.length
    | _ => False
  | .Leaf _ => True
  | .Add x y _ | .Sub x y _ | .Mul x y _ =>
    InScope main preprocessed pv periodic x ∧ InScope main preprocessed pv periodic y
  | .Neg x _ => InScope main preprocessed pv periodic x

/-- Resolving an expression in scope on the debug builder evaluates the polynomial it denotes. -/
theorem resolve_debugBuilder (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
    (periodic : List F) (s : DebugState) (e : SymbolicExpression F)
    (he : InScope main preprocessed pv periodic e) :
    resolve (debugBuilder main preprocessed pv first last trans periodic) s e =
      some (MvPolynomial.eval (windowEnv main preprocessed pv first last trans periodic)
        (toPoly e)) := by
  induction e with
  | Leaf a =>
    rcases a with ⟨⟨_ | _ | o⟩ | ⟨_ | _ | o⟩ | _ | _, j⟩ | _ | _ | _ | c <;>
      simp_all [InScope, resolve, toPoly, SymbolicExpr.denote, leafPoly, varPoly, windowEnv,
        debugBuilder, AirBuilder.is_transition_window, List.getD_eq_getElem?_getD]
  | Add x y _ hx hy | Sub x y _ hx hy | Mul x y _ hx hy =>
    simp_all [InScope, resolve, toPoly, SymbolicExpr.denote, debugBuilder]
  | Neg x _ hx => simp_all [InScope, resolve, toPoly, SymbolicExpr.denote, debugBuilder]

/-! ## Boundary cells on a one-row trace -/

/-- The declaration accepts column 0 on the first row and on the last row, bound to two public values. -/
theorem validate_first_last_same_column :
    validate [⟨0, .First, 0⟩, ⟨0, .Last, 1⟩] 1 2 = .ok () := rfl

/-- On a trace of one row those two cells are the same cell. -/
theorem row_first_last_height_one (c j k : ℕ) :
    BoundaryPublic.row ⟨c, .First, j⟩ 1 = BoundaryPublic.row ⟨c, .Last, k⟩ 1 := rfl

end Plonky3Lean.Proofs.Air
