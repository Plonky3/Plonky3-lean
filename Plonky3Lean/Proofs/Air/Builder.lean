module

public import Plonky3Lean.Proofs.Air.Symbolic

@[expose] public section

/-!
# The symbolic builder denotes the polynomial builder

The polynomial builder is the reference semantics of an AIR.

Its expressions are polynomials in the variables of a row, and it records each asserted polynomial.

On any parametric AIR, the symbolic builder records expressions that denote exactly those polynomials.

They are also well formed, so their cached degree multiples are the ones the walk recomputes.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air
open SymbolicExpr

variable {F : Type} [Field F] [DecidableEq F]

/-- Entrywise relation of two maps of one list. -/
theorem forall₂_map_map {α β γ : Type _} {R : β → γ → Prop} {f : α → β} {g : α → γ} {l : List α}
    (h : ∀ x ∈ l, R (f x) (g x)) : List.Forall₂ R (l.map f) (l.map g) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr h

/-- The polynomial builder: the variables of the window, and a state that records each asserted polynomial. -/
noncomputable def polyBuilder (layout : AirLayout) :
    AirBuilder F (MvPolynomial Var F) (List (MvPolynomial Var F)) where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := MvPolynomial.C
  main _ := ⟨(List.range layout.main_width).map (.X <| .main 0 ·),
    (List.range layout.main_width).map (.X <| .main 1 ·)⟩
  preprocessed _ := ⟨(List.range layout.preprocessed_width).map (.X <| .prep 0 ·),
    (List.range layout.preprocessed_width).map (.X <| .prep 1 ·)⟩
  is_first_row _ := .X .isFirstRow
  is_last_row _ := .X .isLastRow
  is_transition _ := .X .isTransition
  assert_zero s x := s ++ [x]
  public_values _ := (List.range layout.num_public_values).map (.X <| .pub ·)
  periodic_values _ := (List.range layout.num_periodic_columns).map (.X <| .periodic ·)

/-- The constraint polynomials of an AIR: what its evaluation asserts on the polynomial builder. -/
noncomputable def constraints (air : Air F) : List (MvPolynomial Var F) :=
  air.eval (polyBuilder (AirLayout.from_air air)) []

/-- The symbolic builder and the polynomial builder are related by denotation. -/
theorem builderRel_symbolic_poly (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (polyBuilder layout)
      (fun e p => toPoly e = p) (fun s t => s.map toPoly = t) where
  add h h' := by subst h h'; exact denote_sym_add leafDen_leafPoly _ _
  sub h h' := by subst h h'; exact denote_sym_sub leafDen_leafPoly _ _
  mul h h' := by subst h h'; exact denote_sym_mul leafDen_leafPoly _ _
  neg h := by subst h; exact denote_sym_neg leafDen_leafPoly _
  const c := by simp [symbolicBuilder, polyBuilder, toPoly, leafDen_leafPoly, MvPolynomial.algebraMap_eq]
  main_current _ := forall₂_map_map fun _ _ => rfl
  main_next _ := forall₂_map_map fun _ _ => rfl
  preprocessed_current _ := forall₂_map_map fun _ _ => rfl
  preprocessed_next _ := forall₂_map_map fun _ _ => rfl
  public_values _ := forall₂_map_map fun _ _ => rfl
  periodic_values _ := forall₂_map_map fun _ _ => rfl
  is_first_row _ := rfl
  is_last_row _ := rfl
  is_transition _ := rfl
  assert_zero h h' := by subst h h'; simp [symbolicBuilder, polyBuilder]
  window := rfl

/-- What the symbolic builder records denotes what the polynomial builder records. -/
theorem symbolic_toPoly (air : Air F) (layout : AirLayout) :
    (air.eval (symbolicBuilder layout) []).map toPoly = air.eval (polyBuilder layout) [] :=
  air.parametric _ _ _ _ (builderRel_symbolic_poly layout) [] [] rfl

/-- The symbolic builder is related to itself by equality of well-formed expressions. -/
theorem builderRel_symbolic_wf (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (symbolicBuilder layout)
      (fun e e' => e = e' ∧ WF e) (fun s t => s = t ∧ ∀ c ∈ s, WF c) where
  add h h' := by obtain ⟨rfl, h⟩ := h; obtain ⟨rfl, h'⟩ := h'; exact ⟨rfl, wf_sym_add h h'⟩
  sub h h' := by obtain ⟨rfl, h⟩ := h; obtain ⟨rfl, h'⟩ := h'; exact ⟨rfl, wf_sym_sub h h'⟩
  mul h h' := by obtain ⟨rfl, h⟩ := h; obtain ⟨rfl, h'⟩ := h'; exact ⟨rfl, wf_sym_mul h h'⟩
  neg h := by obtain ⟨rfl, h⟩ := h; exact ⟨rfl, wf_sym_neg h⟩
  const _ := ⟨rfl, trivial⟩
  main_current _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  main_next _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  preprocessed_current _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  preprocessed_next _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  public_values _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  periodic_values _ := forall₂_map_map fun _ _ => ⟨rfl, trivial⟩
  is_first_row _ := ⟨rfl, trivial⟩
  is_last_row _ := ⟨rfl, trivial⟩
  is_transition _ := ⟨rfl, trivial⟩
  assert_zero h h' := by
    obtain ⟨rfl, hs⟩ := h; obtain ⟨rfl, h'⟩ := h'
    exact ⟨rfl, by simpa [symbolicBuilder, or_imp, forall_and] using ⟨hs, h'⟩⟩
  window := rfl

/-- Every expression the symbolic builder records is well formed. -/
theorem symbolic_wf (air : Air F) (layout : AirLayout) :
    ∀ c ∈ air.eval (symbolicBuilder layout) [], WF c :=
  (air.parametric _ _ _ _ (builderRel_symbolic_wf layout) [] [] ⟨rfl, by simp⟩).2

/-- With the AIR's own layout, the layout check passes and the constraints are what the symbolic builder records. -/
theorem get_symbolic_constraints_from_air (air : Air F) :
    get_symbolic_constraints air (AirLayout.from_air air) =
      .ok (air.eval (symbolicBuilder (AirLayout.from_air air)) []) := by
  simp [get_symbolic_constraints, AirLayout.validate_against_air, AirLayout.from_air]; rfl

/-- The symbolic constraints of an AIR denote its constraint polynomials. -/
theorem get_symbolic_constraints_toPoly (air : Air F) :
    ((get_symbolic_constraints air (AirLayout.from_air air)).map (·.map toPoly)) =
      .ok (constraints air) := by
  rw [get_symbolic_constraints_from_air]
  exact congrArg Except.ok (symbolic_toPoly air _)

end Plonky3Lean.Proofs.Air
