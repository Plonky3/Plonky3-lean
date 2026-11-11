module

public import Plonky3Lean.Proofs.KeccakAir.Parametric
public import Plonky3Lean.Proofs.Air.Degree

@[expose] public section

/-!
# The constraint degrees of the Keccak-f AIR

Every symbolic constraint of the AIR has degree multiple at most 3.

It also has at most one transition selector along a product.

A builder over pairs of naturals bounds both: a sum takes the larger bound, a product adds them.

Its bounds dominate those of the symbolic builder, and on the AIR they are at most (3, 1).
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror
open Plonky3Lean.Proofs.Air SymbolicExpr

variable {F : Type} [Field F] [DecidableEq F]

/-! ## The simplifying operators do not raise a walk -/

section walk

variable {f : BaseLeaf F → ℕ} (hf : ∀ c, f (.Constant c) = 0)
include hf

theorem dw_const_leaf (c : F) :
    (Leaf (SymLeaf.from_const c) : SymbolicExpression F).degree_with f = 0 := hf c

theorem dw_sym_neg (x : SymbolicExpression F) : x.sym_neg.degree_with f ≤ x.degree_with f := by
  unfold sym_neg
  split
  · rw [dw_const_leaf hf]; exact Nat.zero_le _
  · exact le_rfl

theorem dw_sym_add (x y : SymbolicExpression F) :
    (x.sym_add y).degree_with f ≤ max (x.degree_with f) (y.degree_with f) := by
  unfold sym_add
  split
  · rw [dw_const_leaf hf]; exact Nat.zero_le _
  · split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
    · exact le_rfl

theorem dw_sym_sub (x y : SymbolicExpression F) :
    (x.sym_sub y).degree_with f ≤ max (x.degree_with f) (y.degree_with f) := by
  unfold sym_sub
  split
  · rw [dw_const_leaf hf]; exact Nat.zero_le _
  · split_ifs
    · exact (dw_sym_neg hf y).trans (le_max_right _ _)
    · exact le_max_left _ _
    · exact le_rfl

theorem dw_sym_mul (x y : SymbolicExpression F) :
    (x.sym_mul y).degree_with f ≤ x.degree_with f + y.degree_with f := by
  unfold sym_mul
  split
  · rw [dw_const_leaf hf]; exact Nat.zero_le _
  · split_ifs
    · rw [dw_const_leaf hf]; exact Nat.zero_le _
    · exact Nat.le_add_left _ _
    · exact Nat.le_add_right _ _
    · exact le_rfl

end walk

/-! ## The bounding builder -/

/-- Bounds of (degree multiple, transition count): sums take the larger bound, products add them.

The base bounds:

- every cell and constant: (1, 0)
- the boundary selectors: (1, 0)
- the transition selector: (0, 1).

The state records whether every assertion so far is bounded by (3, 1). -/
def topBuilder (layout : AirLayout) : AirBuilder F (ℕ × ℕ) Bool where
  add p q := (max p.1 q.1, max p.2 q.2)
  sub p q := (max p.1 q.1, max p.2 q.2)
  mul p q := (p.1 + q.1, p.2 + q.2)
  neg p := p
  const _ := (1, 0)
  main _ := ⟨(List.range layout.main_width).map fun _ => (1, 0),
    (List.range layout.main_width).map fun _ => (1, 0)⟩
  preprocessed _ := ⟨(List.range layout.preprocessed_width).map fun _ => (1, 0),
    (List.range layout.preprocessed_width).map fun _ => (1, 0)⟩
  is_first_row _ := (1, 0)
  is_last_row _ := (1, 0)
  is_transition _ := (0, 1)
  assert_zero s p := s && decide (p.1 ≤ 3 ∧ p.2 ≤ 1)
  public_values _ := (List.range layout.num_public_values).map fun _ => (1, 0)
  periodic_values _ := (List.range layout.num_periodic_columns).map fun _ => (1, 0)

/-- An expression is well formed and bounded by the pair. -/
def Bounded (e : SymbolicExpression F) (p : ℕ × ℕ) : Prop :=
  WF e ∧ e.degree_with SymLeaf.degree_multiple ≤ p.1 ∧ transitionCount e ≤ p.2

theorem tc_const (c : F) : (fun l : BaseLeaf F => match l with | .IsTransition => 1 | _ => 0)
    (.Constant c) = 0 := rfl

theorem builderRel_top (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (topBuilder layout) Bounded
      (fun es b => b = true → ∀ e ∈ es, e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1) where
  add h h' := ⟨wf_sym_add h.1 h'.1, (dw_sym_add (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_add tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  sub h h' := ⟨wf_sym_sub h.1 h'.1, (dw_sym_sub (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_sub tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  mul h h' := ⟨wf_sym_mul h.1 h'.1, (dw_sym_mul (fun _ => rfl) _ _).trans (add_le_add h.2.1 h'.2.1),
    (dw_sym_mul tc_const _ _).trans (add_le_add h.2.2 h'.2.2)⟩
  neg h := ⟨wf_sym_neg h.1, (dw_sym_neg (fun _ => rfl) _).trans h.2.1,
    (dw_sym_neg tc_const _).trans h.2.2⟩
  const c := ⟨wf_const c, Nat.zero_le _, Nat.zero_le _⟩
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
    simp only [topBuilder, Bool.and_eq_true, decide_eq_true_eq] at hb
    intro e' he'
    rcases List.mem_append.mp he' with h | h
    · exact hq hb.1 e' h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨he.1.degree_multiple_eq ▸ he.2.1.trans hb.2.1, he.2.2.trans hb.2.2⟩
  window := rfl

/-- Suppose the bounding builder accepts an AIR.

Then every symbolic constraint has degree multiple at most 3.

It also has at most one transition selector along a product. -/
theorem bounded_of_top (air : Air F) (h : air.eval (topBuilder (AirLayout.from_air air)) true = true) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  air.parametric _ _ _ _ (builderRel_top _) [] true (by simp) h

theorem getD_map_const {α β : Type} (l : List α) (a : β) (i : ℕ) :
    (l.map fun _ => a).getD i a = a := by
  induction l generalizing i with
  | nil => simp
  | cons x l ih => cases i <;> simp_all

/-- The bounding builder accepts the Keccak-f AIR over the field. -/
abbrev TopOk (F : Type) [Field F] : Prop :=
  (keccakAir (F := F)).eval (topBuilder (AirLayout.from_air (keccakAir (F := F)))) true = true

section bounds

variable (htop : TopOk F)
include htop

/-- Every symbolic constraint of the Keccak-f AIR has degree multiple at most 3.

It also has at most one transition selector along a product. -/
theorem keccak_constraints_bounded :
    ∀ e ∈ (keccakAir (F := F)).eval (symbolicBuilder (AirLayout.from_air (keccakAir (F := F)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  bounded_of_top _ htop

/-- The largest constraint degree is at most 3. -/
theorem keccak_max_degree_le (n : ℕ) : ∃ D,
    get_max_constraint_degree (keccakAir (F := F)) (AirLayout.from_air (keccakAir (F := F))) n = .ok D ∧
      D ≤ 3 := by
  have hfold : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 3) → l.foldr max 0 ≤ 3 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons]; simp_all
  refine ⟨(((keccakAir (F := F)).eval (symbolicBuilder (AirLayout.from_air (keccakAir (F := F))))
    []).map SymbolicExpr.degree_multiple).foldr max 0, ?_, hfold _ ?_⟩
  · simp only [get_max_constraint_degree, get_symbolic_constraints_from_air]
    rfl
  · simp only [List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    exact (keccak_constraints_bounded htop e he).1

/-- The quotient sizing gives at most 2^1 chunks, and every constraint polynomial fits them. -/
theorem keccak_quotient_fits [Inhabited F] {n : ℕ} (hn : 1 ≤ n) {σ : Plonky3Lean.Spec.Air.Var → Polynomial F}
    {periods : List ℕ} (hσ : Plonky3Lean.Spec.Air.DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    ∃ L ≤ 1, get_log_quotient_degree (keccakAir (F := F)) (AirLayout.from_air (keccakAir (F := F))) n 0 =
        .ok L ∧
      ∀ e ∈ (keccakAir (F := F)).eval (symbolicBuilder (AirLayout.from_air (keccakAir (F := F)))) [],
        Plonky3Lean.Spec.Air.FitsChunks n (2 ^ L) (Plonky3Lean.Spec.Air.constraintPoly σ (toPoly e)) := by
  obtain ⟨D, hD, hD3⟩ := keccak_max_degree_le htop n
  have hL : get_log_quotient_degree (keccakAir (F := F)) (AirLayout.from_air (keccakAir (F := F))) n 0 =
      .ok (log2_ceil_usize (max (max D 0) 2 - 1)) := by
    simp only [get_log_quotient_degree, hD, bind, Except.bind, pure, Except.pure]
    rfl
  refine ⟨_, log2_ceil_le ?_, hL, quotient_fits_fast hn (by rfl) hL hσ hp
    fun e he => (keccak_constraints_bounded htop e he).2⟩
  have : max (max D 0) 2 - 1 ≤ 2 := by omega
  exact this

end bounds

end Plonky3Lean.Proofs.KeccakAir
