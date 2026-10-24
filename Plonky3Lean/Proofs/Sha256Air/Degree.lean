module

public import Plonky3Lean.Proofs.Sha256Air.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Binary.Degree
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Mersenne31.Basic

@[expose] public section

/-!
# The constraint degrees of the SHA-256 AIRs

A builder over pairs of naturals bounds the degree multiple and the transition count of every constraint.

A sum takes the larger bound, a product adds them, and a constant is bounded by 0.

- Over a prime field, every constraint has degree multiple at most 3, the declared bound.
- Over a field of characteristic 2, every constraint has degree multiple at most 2, the declared bound.
- No constraint reads a transition selector.

The bounding builder checks this by evaluation over BabyBear, KoalaBear, Goldilocks, Mersenne31 and GF(2).
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror
open Plonky3Lean.Proofs.Air SymbolicExpr
open Plonky3Lean.Proofs.KeccakAir (Bounded dw_sym_add dw_sym_sub dw_sym_mul dw_sym_neg tc_const
  getD_map_const)
open Plonky3Lean.Proofs.KeccakAir.Binary (length_constraints countBuilder)

variable {F : Type} [Field F] [DecidableEq F]

/-- Bounds of (degree multiple, transition count), checking every assertion against (d, 0). -/
def topBuilder (d : ℕ) (layout : AirLayout) : AirBuilder F (ℕ × ℕ) Bool where
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
  assert_zero s p := decide (p.1 ≤ d ∧ p.2 = 0) && s
  public_values _ := (List.range layout.num_public_values).map fun _ => (0, 0)
  periodic_values _ := (List.range layout.num_periodic_columns).map fun _ => (1, 0)

theorem builderRel_top (d : ℕ) (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (topBuilder d layout) Bounded
      (fun es b => b = true → ∀ e ∈ es, e.degree_multiple ≤ d ∧ transitionCount e = 0) where
  add h h' := ⟨wf_sym_add h.1 h'.1, (dw_sym_add (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_add tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  sub h h' := ⟨wf_sym_sub h.1 h'.1, (dw_sym_sub (fun _ => rfl) _ _).trans (max_le_max h.2.1 h'.2.1),
    (dw_sym_sub tc_const _ _).trans (max_le_max h.2.2 h'.2.2)⟩
  mul h h' := ⟨wf_sym_mul h.1 h'.1, (dw_sym_mul (fun _ => rfl) _ _).trans (add_le_add h.2.1 h'.2.1),
    (dw_sym_mul tc_const _ _).trans (add_le_add h.2.2 h'.2.2)⟩
  neg h := ⟨wf_sym_neg h.1, (dw_sym_neg (fun _ => rfl) _).trans h.2.1,
    (dw_sym_neg tc_const _).trans h.2.2⟩
  const c := ⟨wf_const c, le_rfl, le_rfl⟩
  main_current _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  main_next _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  preprocessed_current _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  preprocessed_next _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  public_values _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  periodic_values _ := forall₂_map_map fun _ _ => ⟨trivial, le_rfl, le_rfl⟩
  is_first_row _ := ⟨trivial, le_rfl, le_rfl⟩
  is_last_row _ := ⟨trivial, le_rfl, le_rfl⟩
  is_transition _ := ⟨trivial, le_rfl, le_rfl⟩
  assert_zero {es} {b} {e} {p} hq he := by
    intro hb
    simp only [topBuilder, Bool.and_eq_true, decide_eq_true_eq] at hb
    intro e' he'
    rcases List.mem_append.mp he' with h | h
    · exact hq hb.2 e' h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨he.1.degree_multiple_eq ▸ he.2.1.trans hb.1.1, Nat.le_zero.mp (hb.1.2 ▸ he.2.2)⟩
  window := rfl

/-- When the bounding builder accepts an AIR, its constraints are bounded.

Each has degree multiple at most d and no transition selector. -/
theorem bounded_of_top {d : ℕ} (air : Air F)
    (h : air.eval (topBuilder d (AirLayout.from_air air)) true = true) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      e.degree_multiple ≤ d ∧ transitionCount e = 0 :=
  air.parametric _ _ _ _ (builderRel_top d _) [] true (by simp) h

/-- The bounding builder accepts the AIR over a prime field at degree 3. -/
abbrev TopOk (F : Type) [Field F] : Prop :=
  (sha256Air (F := F)).eval (topBuilder 3 (AirLayout.from_air (sha256Air (F := F)))) true = true

theorem getD_map_const' {α β : Type} (l : List α) (a d : β) (i : ℕ) :
    (l.map fun _ => a).getD i d = if i < l.length then a else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · exact List.getD_eq_default _ _ (by simpa using h)

/-- Unfold the bounding builder's run to a closed computation and evaluate it. -/
macro "top_tac" : tactic => `(tactic| (
  simp only [TopOk, sha256Air, eval, topBuilder, getD_map_const', List.length_range, AirLayout.from_air]
  decide +kernel))

theorem top_babyBear : TopOk BabyBear.Field := by top_tac
theorem top_koalaBear : TopOk KoalaBear.Field := by top_tac
theorem top_goldilocks : TopOk Goldilocks.Field := by top_tac
theorem top_mersenne31 : TopOk Mersenne31.Field := by top_tac

section bounds

variable (htop : TopOk F)
include htop

/-- Over a prime field, each constraint has degree multiple at most 3.

No constraint reads a transition selector. -/
theorem constraints_bounded :
    ∀ e ∈ (sha256Air (F := F)).eval (symbolicBuilder (AirLayout.from_air (sha256Air (F := F)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  bounded_of_top _ htop

/-- The largest constraint degree is at most 3. -/
theorem max_degree_le (n : ℕ) : ∃ D,
    get_max_constraint_degree (sha256Air (F := F)) (AirLayout.from_air (sha256Air (F := F))) n = .ok D ∧
      D ≤ 3 := by
  have hfold : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 3) → l.foldr max 0 ≤ 3 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons]; simp_all
  refine ⟨(((sha256Air (F := F)).eval (symbolicBuilder (AirLayout.from_air (sha256Air (F := F))))
    []).map SymbolicExpr.degree_multiple).foldr max 0, ?_, hfold _ ?_⟩
  · simp only [get_max_constraint_degree, get_symbolic_constraints_from_air]
    rfl
  · simp only [List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    exact (constraints_bounded htop e he).1

/-- The quotient sizing gives 2 chunks, and every constraint polynomial fits them. -/
theorem quotient_fits [Inhabited F] {n : ℕ} (hn : 1 ≤ n) {σ : Plonky3Lean.Spec.Air.Var → Polynomial F}
    {periods : List ℕ} (hσ : Plonky3Lean.Spec.Air.DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    get_log_quotient_degree (sha256Air (F := F)) (AirLayout.from_air (sha256Air (F := F))) n 0 =
        .ok 1 ∧
      ∀ e ∈ (sha256Air (F := F)).eval (symbolicBuilder (AirLayout.from_air (sha256Air (F := F)))) [],
        Plonky3Lean.Spec.Air.FitsChunks n (2 ^ 1) (Plonky3Lean.Spec.Air.constraintPoly σ (toPoly e)) := by
  obtain ⟨D, hD, hD3⟩ := max_degree_le htop n
  have hL : get_log_quotient_degree (sha256Air (F := F)) (AirLayout.from_air (sha256Air (F := F))) n 0 =
      .ok 1 := by
    simp only [get_log_quotient_degree, hD, bind, Except.bind, pure, Except.pure]
    simp only [sha256Air, Option.getD_some, show max (max D 3 + 0) 2 - 1 = 2 by omega]
    rfl
  exact ⟨hL, quotient_fits_fast hn (by rfl) hL hσ hp
    fun e he => by rw [(constraints_bounded htop e he).2]; exact Nat.zero_le _⟩

end bounds

/-! ## The AIR over a field of characteristic 2 -/

/-- The bounding builder accepts the characteristic-2 AIR at degree 2. -/
abbrev TopOkB (F : Type) [Field F] (cb : Bool) : Prop :=
  (binaryAir (F := F) cb).eval (topBuilder 2 (AirLayout.from_air (binaryAir (F := F) cb))) true = true

theorem top_binary_gf2 (cb : Bool) : TopOkB (ZMod 2) cb := by
  cases cb <;>
  · simp only [TopOkB, binaryAir, binary.eval, topBuilder, getD_map_const', List.length_range,
      AirLayout.from_air]
    decide +kernel

/-- In characteristic 2, each constraint has degree multiple at most 2.

No constraint reads a transition selector. -/
theorem binary_constraints_bounded {cb : Bool} (htop : TopOkB F cb) :
    ∀ e ∈ (binaryAir (F := F) cb).eval (symbolicBuilder (AirLayout.from_air (binaryAir (F := F) cb))) [],
      e.degree_multiple ≤ 2 ∧ transitionCount e = 0 :=
  bounded_of_top _ htop

/-- Over GF(2), the characteristic-2 AIR asserts exactly the number of constraints it reports. -/
theorem binary_num_constraints (cb : Bool) :
    some ((binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) []).length =
      binary.num_constraints cb := by
  rw [length_constraints]
  cases cb <;>
  · simp only [binaryAir, binary.eval, countBuilder, getD_map_const, AirLayout.from_air]
    decide +kernel

/-- Over BabyBear, the AIR over a prime field asserts 8096 constraints. -/
theorem num_constraints :
    ((sha256Air (F := BabyBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := BabyBear.Field)))) []).length =
      8096 := by
  rw [length_constraints]
  simp only [sha256Air, eval, countBuilder, getD_map_const, AirLayout.from_air]
  decide +kernel

end Plonky3Lean.Proofs.Sha256Air
