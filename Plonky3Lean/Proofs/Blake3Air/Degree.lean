module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Degree

@[expose] public section

/-!
# The constraint degrees of the BLAKE3 AIRs

Every symbolic constraint of the prime-field AIR has degree multiple at most 3, its hint.

Every symbolic constraint of the characteristic-2 AIR has degree multiple at most 2, its hint.

Neither reads a selector.

A builder over pairs of naturals bounds the degree multiple and the transition count.

- A sum takes the larger bound.
- A product adds them.
- A constant has degree 0.

Its bounds dominate those of the symbolic builder.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir SymbolicExpr

variable {F : Type} [Field F] [DecidableEq F]

/-- Bounds of (degree multiple, transition count), with constants of degree 0.

The state records whether every assertion so far is bounded by (d, 0). -/
def topBuilderD (d : ℕ) (layout : AirLayout) : AirBuilder F (ℕ × ℕ) Bool where
  add p q := (max p.1 q.1, max p.2 q.2)
  sub p q := (max p.1 q.1, max p.2 q.2)
  mul p q := (p.1 + q.1, p.2 + q.2)
  neg p := p
  const _ := (0, 0)
  main _ := ⟨(List.range layout.main_width).map fun _ => (1, 0),
    (List.range layout.main_width).map fun _ => (1, 0)⟩
  preprocessed _ := ⟨(List.range layout.preprocessed_width).map fun _ => (1, 0),
    (List.range layout.preprocessed_width).map fun _ => (1, 0)⟩
  is_first_row _ := (1, 0)
  is_last_row _ := (1, 0)
  is_transition _ := (0, 1)
  assert_zero s p := s && decide (p.1 ≤ d ∧ p.2 = 0)
  public_values _ := (List.range layout.num_public_values).map fun _ => (0, 0)
  periodic_values _ := (List.range layout.num_periodic_columns).map fun _ => (1, 0)

theorem builderRel_topD (d : ℕ) (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (topBuilderD d layout) Bounded
      (fun es b => b = true → ∀ e ∈ es, e.degree_multiple ≤ d ∧ transitionCount e = 0) where
  add h h' := ⟨wf_sym_add h.1 h'.1, (dw_sym_add (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_add tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  sub h h' := ⟨wf_sym_sub h.1 h'.1, (dw_sym_sub (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_sub tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  mul h h' := ⟨wf_sym_mul h.1 h'.1, (dw_sym_mul (fun _ => rfl) _ _).trans (add_le_add h.2.1 h'.2.1),
    (dw_sym_mul tc_const _ _).trans (add_le_add h.2.2 h'.2.2)⟩
  neg h := ⟨wf_sym_neg h.1, (dw_sym_neg (fun _ => rfl) _).trans h.2.1,
    (dw_sym_neg tc_const _).trans h.2.2⟩
  const c := ⟨wf_const c, (dw_const_leaf (fun _ => rfl) c).le, (dw_const_leaf tc_const c).le⟩
  main_current _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  main_next _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  preprocessed_current _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  preprocessed_next _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  public_values _ := forall₂_map_map fun _ _ => ⟨trivial, Nat.zero_le _, le_rfl⟩
  periodic_values _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  is_first_row _ := ⟨trivial, le_rfl, le_rfl⟩
  is_last_row _ := ⟨trivial, le_rfl, le_rfl⟩
  is_transition _ := ⟨trivial, le_rfl, le_rfl⟩
  assert_zero {es} {b} {e} {p} hq he := by
    intro hb
    simp only [topBuilderD, Bool.and_eq_true, decide_eq_true_eq] at hb
    intro e' he'
    rcases List.mem_append.mp he' with h | h
    · exact hq hb.1 e' h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨he.1.degree_multiple_eq ▸ he.2.1.trans hb.2.1, Nat.le_zero.mp (hb.2.2 ▸ he.2.2)⟩
  window := rfl

theorem getD_map_range_const {α : Type} (n i : ℕ) (a b : α) :
    ((List.range n).map fun _ => a).getD i b = if i < n then a else b := by
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

/-- When the bounding builder accepts an AIR, every constraint has degree multiple at most d and no selector. -/
theorem bounded_of_topD (d : ℕ) (air : Air F)
    (h : air.eval (topBuilderD d (AirLayout.from_air air)) true = true) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      e.degree_multiple ≤ d ∧ transitionCount e = 0 :=
  air.parametric _ _ _ _ (builderRel_topD d _) [] true (by simp) h

/-- The largest constraint degree of an AIR whose constraints have degree multiple at most d. -/
theorem max_degree_le {air : Air F} {d : ℕ}
    (hper : (AirLayout.from_air air).num_periodic_columns = 0)
    (hb : ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [], e.degree_multiple ≤ d)
    (n : ℕ) : ∃ D, get_max_constraint_degree air (AirLayout.from_air air) n = .ok D ∧ D ≤ d := by
  have hfold : ∀ l : List ℕ, (∀ x ∈ l, x ≤ d) → l.foldr max 0 ≤ d := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons]; simp_all
  refine ⟨((air.eval (symbolicBuilder (AirLayout.from_air air)) []).map
    SymbolicExpr.degree_multiple).foldr max 0, ?_, hfold _ ?_⟩
  · simp [get_max_constraint_degree, get_symbolic_constraints_from_air, hper, bind, Except.bind,
      pure, Except.pure]
  · simp only [List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    exact hb e he

/-! ## Checking the bound in pieces

The bounding builder's state is a conjunction, so a run from b is b and the run from true.

So the run of a long evaluation splits into the runs of its steps, each checked on its own.
-/

/-- The bounding builder related to itself: a state b && s on the left of s. -/
theorem builderRel_and (d : ℕ) (layout : AirLayout) (b : Bool) :
    BuilderRel (topBuilderD (F := F) d layout) (topBuilderD d layout) Eq
      (fun s₁ s₂ => s₁ = (b && s₂)) where
  add h h' := by subst h h'; rfl
  sub h h' := by subst h h'; rfl
  mul h h' := by subst h h'; rfl
  neg h := by subst h; rfl
  const _ := rfl
  main_current _ := List.forall₂_refl _
  main_next _ := List.forall₂_refl _
  preprocessed_current _ := List.forall₂_refl _
  preprocessed_next _ := List.forall₂_refl _
  public_values _ := List.forall₂_refl _
  periodic_values _ := List.forall₂_refl _
  is_first_row _ := rfl
  is_last_row _ := rfl
  is_transition _ := rfl
  assert_zero hs h := by subst hs h; simp [topBuilderD, Bool.and_assoc]
  window := rfl

/-- A step of the bounding builder's run: from b && s it reaches b && its run from s. -/
def Lin (f : Bool → Bool) : Prop := ∀ b s, f (b && s) = (b && f s)

theorem Lin.eq {f : Bool → Bool} (hf : Lin f) (s : Bool) : f s = (s && f true) := by
  simpa using hf s true

/-- The quotient of an AIR with degree hint d, no periodic column, and constraints of degree multiple at most d.

Its sizing gives 2^L chunks with L = log_2 ceil (max(d, 2) - 1).

Every constraint polynomial fits them. -/
theorem quotient_fits_of_bounded [Inhabited F] {air : Air F} {d : ℕ} (hhint : air.max_constraint_degree = some d)
    (hb : ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      e.degree_multiple ≤ d ∧ transitionCount e = 0)
    (hper : (AirLayout.from_air air).num_periodic_columns = 0) {n : ℕ} (hn : 1 ≤ n)
    {σ : Plonky3Lean.Spec.Air.Var → Polynomial F} {periods : List ℕ}
    (hσ : Plonky3Lean.Spec.Air.DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    get_log_quotient_degree air (AirLayout.from_air air) n 0 = .ok (log2_ceil_usize (max d 2 - 1)) ∧
      ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
        Plonky3Lean.Spec.Air.FitsChunks n (2 ^ log2_ceil_usize (max d 2 - 1))
          (Plonky3Lean.Spec.Air.constraintPoly σ (toPoly e)) := by
  obtain ⟨D, hD, hDd⟩ := max_degree_le hper (fun e he => (hb e he).1) n
  have hL : get_log_quotient_degree air (AirLayout.from_air air) n 0 =
      .ok (log2_ceil_usize (max d 2 - 1)) := by
    simp only [get_log_quotient_degree, hD, hhint, bind, Except.bind, pure, Except.pure,
      Option.getD_some]
    rw [show max (max D d + 0) 2 = max d 2 by omega]
    rfl
  exact ⟨hL, quotient_fits_fast hn hper hL hσ hp fun e he => (hb e he).2.le.trans (Nat.zero_le 1)⟩

end Plonky3Lean.Proofs.Blake3Air
