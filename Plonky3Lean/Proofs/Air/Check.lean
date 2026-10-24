module

public import Plonky3Lean.Proofs.Air.Builder

@[expose] public section

/-!
# The debug constraint checker accepts exactly the satisfying traces

At row i, the debug builder sees the values of the variables on row i of the trace.

So, on a parametric AIR, it asserts the values of the AIR's constraint polynomials at row i.

It records a failure exactly for the nonzero ones.

The checker therefore accepts a trace exactly when:

- its shape checks pass
- every constraint polynomial vanishes on every row.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air

variable {F : Type} [Field F] [DecidableEq F] [Inhabited F]

/-! ## Lists and loops -/

theorem forall₂_range_map {α β : Type _} {R : α → β → Prop} {f : ℕ → α} {l : List β} {w : ℕ}
    (hl : l.length = w) (h : ∀ c (hc : c < w), R (f c) (l[c]'(hl ▸ hc))) :
    List.Forall₂ R ((List.range w).map f) l := by
  subst hl
  rw [List.forall₂_iff_get]
  exact ⟨by simp, fun c h₁ _ => by simpa using h c (by simpa using h₁)⟩

theorem except_forM_eq_ok {α ε : Type _} (l : List α) (f : α → Except ε Unit) :
    l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => simp [List.forM, pure, Except.pure]
  | cons a l ih =>
    simp only [List.forM]
    rcases h : f a with e | ⟨⟩
    · simp [h, bind, Except.bind]
    · simpa [h, bind, Except.bind] using ih

/-! ## The debug state -/

/-- Asserting a list of values from a state. -/
def assertAll (s : DebugState) (vals : List F) : DebugState := vals.foldl DebugState.assert_zero s

theorem assertAll_failures_eq_nil (s : DebugState) (vals : List F) :
    (assertAll s vals).failures = [] ↔ s.failures = [] ∧ ∀ v ∈ vals, v = 0 := by
  induction vals generalizing s with
  | nil => simp [assertAll]
  | cons v vals ih =>
    simp only [assertAll, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hv : v = 0 <;> simp [DebugState.assert_zero, hv]

/-! ## Matrices -/

theorem Mat.length_row {M : Mat F} {i : ℕ} (hi : i < M.height) : (M.row i).length = M.width := by
  unfold Mat.height at hi
  split_ifs at hi with hw
  · simp at hi
  · have : (i + 1) * M.width ≤ M.values.length :=
      (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hw)).mp hi
    simp only [Mat.row, List.length_take, List.length_drop]
    rw [min_eq_left]
    rw [Nat.add_mul, one_mul] at this
    omega

theorem Mat.next_lt {n i : ℕ} (hi : i < n) : (i + 1) % n < n := Nat.mod_lt _ (by omega)

/-! ## The trace as an instance -/

/-- The trace, preprocessed trace, public values and periodic columns of a check, as an instance. -/
def instOf (air : Air F) (M : Mat F) (pv : List F) : Instance F where
  height := M.height
  main i c := (M.row i).getD c 0
  prep i c := ((air.preprocessed_trace.map (·.row i)).getD []).getD c 0
  pub j := pv.getD j 0
  periodic j r := (air.periodic_values r).getD j 0

/-- The widths the checker relies on all match the AIR:

- the trace width
- the preprocessed width
- the public values
- the periodic columns. -/
structure Shapes (air : Air F) (M : Mat F) (pv : List F) : Prop where
  main_width : M.width = air.width
  prep_width : ∀ P, air.preprocessed_trace = some P → P.width = air.preprocessed_width
  prep_none : air.preprocessed_trace = none → air.preprocessed_width = 0
  pub : pv.length = air.num_public_values
  periodic : air.periodic_columns.length = air.num_periodic_columns

/-- The preprocessed trace, when present, has the trace's height. -/
def PrepHeight (air : Air F) (M : Mat F) : Prop :=
  ∀ P, air.preprocessed_trace = some P → P.height = M.height

/-! ## One row -/

theorem getElem?_getD {l : List F} {c : ℕ} (h : c < l.length) : l[c]?.getD 0 = l[c] := by
  simp [h]

/-- At row i, the polynomial builder and the debug builder are related by evaluation on row i. -/
theorem builderRel_poly_row {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv)
    (hp : PrepHeight air M) {i : ℕ} (hi : i < M.height) :
    BuilderRel (polyBuilder (AirLayout.from_air air)) (rowBuilder air M pv i)
      (fun p v => MvPolynomial.eval (rowEnv (instOf air M pv) i) p = v)
      (fun ps st => st = assertAll (DebugState.new i)
        (ps.map (MvPolynomial.eval (rowEnv (instOf air M pv) i)))) where
  add h h' := by subst h h'; simp [polyBuilder, rowBuilder, debugBuilder]
  sub h h' := by subst h h'; simp [polyBuilder, rowBuilder, debugBuilder]
  mul h h' := by subst h h'; simp [polyBuilder, rowBuilder, debugBuilder]
  neg h := by subst h; simp [polyBuilder, rowBuilder, debugBuilder]
  const c := by simp [polyBuilder, rowBuilder, debugBuilder]
  main_current _ := by
    show List.Forall₂ _ _ (M.row i)
    refine forall₂_range_map (by rw [Mat.length_row hi, hs.main_width]; rfl) fun c hc => ?_
    simpa [rowEnv, instOf] using getElem?_getD _
  main_next _ := by
    show List.Forall₂ _ _ (M.row ((i + 1) % M.height))
    refine forall₂_range_map
      (by rw [Mat.length_row (Mat.next_lt hi), hs.main_width]; rfl) fun c hc => ?_
    simpa [rowEnv, instOf] using getElem?_getD _
  preprocessed_current _ := by
    rcases hP : air.preprocessed_trace with _ | P
    · simp [polyBuilder, rowBuilder, debugBuilder, AirLayout.from_air, hs.prep_none hP, hP]
    · simp only [rowBuilder, debugBuilder, hP, rowPair]
      refine forall₂_range_map (by
        rw [Mat.length_row (hp P hP ▸ hi), hs.prep_width P hP]; rfl) fun c hc => ?_
      simpa [rowEnv, instOf, hP] using getElem?_getD _
  preprocessed_next _ := by
    rcases hP : air.preprocessed_trace with _ | P
    · simp [polyBuilder, rowBuilder, debugBuilder, AirLayout.from_air, hs.prep_none hP, hP]
    · simp only [rowBuilder, debugBuilder, hP, rowPair]
      refine forall₂_range_map (by
        rw [Mat.length_row (by rw [hp P hP]; exact Mat.next_lt hi), hs.prep_width P hP]; rfl)
        fun c hc => ?_
      simpa [rowEnv, instOf, hP] using getElem?_getD _
  public_values _ := by
    show List.Forall₂ _ _ pv
    refine forall₂_range_map (by simp [hs.pub, AirLayout.from_air]) fun c hc => ?_
    simpa [rowEnv, instOf] using getElem?_getD _
  periodic_values _ := by
    show List.Forall₂ _ _ (air.periodic_values i)
    refine forall₂_range_map (by simp [Air.periodic_values, hs.periodic, AirLayout.from_air])
      fun c hc => ?_
    simpa [rowEnv, instOf] using getElem?_getD _
  is_first_row _ := by simp [polyBuilder, rowBuilder, debugBuilder, rowEnv, instOf]
  is_last_row _ := by simp [polyBuilder, rowBuilder, debugBuilder, rowEnv, instOf]
  is_transition _ := by
    simp only [polyBuilder, rowBuilder, debugBuilder, MvPolynomial.eval_X, rowEnv, instOf]
    split_ifs <;> simp_all
  assert_zero h h' := by
    subst h h'
    simp [polyBuilder, rowBuilder, debugBuilder, assertAll, List.foldl_append]
  window := rfl

/-- At row i, the debug builder asserts the values of the constraint polynomials on row i. -/
theorem eval_rowBuilder {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv)
    (hp : PrepHeight air M) {i : ℕ} (hi : i < M.height) :
    air.eval (rowBuilder air M pv i) (DebugState.new i) =
      assertAll (DebugState.new i)
        ((constraints air).map (MvPolynomial.eval (rowEnv (instOf air M pv) i))) :=
  air.parametric _ _ _ _ (builderRel_poly_row hs hp hi) [] _ rfl

/-- At row i, the debug builder records no failure exactly when every constraint vanishes there. -/
theorem rowBuilder_ok_iff {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv)
    (hp : PrepHeight air M) {i : ℕ} (hi : i < M.height) :
    (air.eval (rowBuilder air M pv i) (DebugState.new i)).failures = [] ↔
      ∀ c ∈ constraints air, MvPolynomial.eval (rowEnv (instOf air M pv) i) c = 0 := by
  rw [eval_rowBuilder hs hp hi, assertAll_failures_eq_nil]
  simp [DebugState.new]

/-! ## The whole check -/

/-- Every periodic column has a power-of-two length that divides the height. -/
def PeriodicShapes (air : Air F) (height : ℕ) : Prop :=
  ∀ col ∈ air.periodic_columns,
    (col.length ≠ 0 ∧ 2 ^ Nat.log 2 col.length = col.length) ∧ height % col.length = 0

theorem assert_periodic_column_shapes_ok (air : Air F) (height : ℕ) :
    assert_periodic_column_shapes air height = .ok () ↔ PeriodicShapes air height := by
  unfold assert_periodic_column_shapes PeriodicShapes
  rw [except_forM_eq_ok]
  refine forall₂_congr fun col _ => ?_
  by_cases h1 : col.length ≠ 0 ∧ 2 ^ Nat.log 2 col.length = col.length <;>
    by_cases h2 : height % col.length = 0 <;> simp_all [bind, Except.bind, pure, Except.pure]

/-- The checker accepts exactly when:

- the preprocessed height matches
- the periodic shapes are valid
- every boundary cell holds its public value
- the trace satisfies the AIR's constraint polynomials. -/
theorem check_constraints_ok_iff {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv) :
    check_constraints air M pv = .ok () ↔
      PrepHeight air M ∧ PeriodicShapes air M.height ∧
        boundary_io_mismatches air M pv = .ok [] ∧ Satisfies (constraints air) (instOf air M pv) := by
  by_cases hp : PrepHeight air M
  · have hrows : (List.range M.height).forM (fun row_index =>
        if (air.eval (rowBuilder air M pv row_index) (DebugState.new row_index)).failures ≠ [] then
          (throw "constraints not satisfied" : Except String Unit) else pure PUnit.unit) = .ok () ↔
        Satisfies (constraints air) (instOf air M pv) := by
      rw [except_forM_eq_ok]
      simp only [Satisfies, List.mem_range]
      refine forall₂_congr fun i hi => ?_
      rw [← rowBuilder_ok_iff hs hp hi]
      by_cases h : (air.eval (rowBuilder air M pv i) (DebugState.new i)).failures = [] <;>
        simp [h, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    unfold check_constraints
    rw [← hrows, ← assert_periodic_column_shapes_ok]
    rcases hper : assert_periodic_column_shapes air M.height with e | ⟨⟩ <;>
      rcases hb : boundary_io_mismatches air M pv with e' | bs <;>
      rcases hP : air.preprocessed_trace with _ | P <;>
      simp [hper, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
        Except.pure] <;> split_ifs <;> simp_all [PrepHeight]
  · obtain ⟨P, hP, hne⟩ : ∃ P, air.preprocessed_trace = some P ∧ P.height ≠ M.height := by
      simpa [PrepHeight] using hp
    unfold check_constraints
    simp [hp, hP, hne, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

end Plonky3Lean.Proofs.Air
