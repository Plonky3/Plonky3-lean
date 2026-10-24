module

public import P3UniStark
public import Plonky3Lean.Spec.UniStark
public import Plonky3Lean.Proofs.Air.Semantics
public import Mathlib.RingTheory.MvPolynomial.Tower

@[expose] public section

/-!
# The two constraint folders compute the same combination

The verifier folds each asserted value into acc alpha + x, which is Horner's rule.

The prover collects the base values.

It dots them with the powers of alpha, one basis coordinate at a time.

On a parametric AIR both give sum_i alpha^(m - 1 - i) C_i, with the constraints in emission order.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_uni_stark.folder.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.UniStark Plonky3Lean.Proofs.Air

/-! ## The combination -/

section combine

variable {K : Type _} [Field K]

theorem combine_nil (α : K) : combine α [] = 0 := by simp [combine]

theorem combine_append_singleton (α : K) (vs : List K) (v : K) :
    combine α (vs ++ [v]) = combine α vs * α + v := by
  simp only [combine, List.length_append, List.length_singleton, Finset.sum_range_succ,
    Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    rw [List.getD_append _ _ _ _ hi, mul_right_comm, ← pow_succ]
    congr 2
    omega
  · simp

/-- Horner's rule from an accumulator a: the fold is a alpha^m plus the combination. -/
theorem foldl_horner (α a : K) (vs : List K) :
    vs.foldl (fun acc x => acc * α + x) a = a * α ^ vs.length + combine α vs := by
  induction vs using List.reverseRecOn generalizing a with
  | nil => simp [combine_nil]
  | append_singleton vs v ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, combine_append_singleton,
      List.length_append, List.length_singleton, pow_succ]
    ring

end combine

/-! ## The verifier's folder -/

section verifier

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- The rows, public values and periodic values have the widths the AIR declares. -/
structure WindowShapes {E P : Type} (air : Air F) (main preprocessed : RowWindow E) (pv : List P)
    (periodic : List E) : Prop where
  main_current : main.current.length = air.width
  main_next : main.next.length = air.width
  prep_current : preprocessed.current.length = air.preprocessed_width
  prep_next : preprocessed.next.length = air.preprocessed_width
  pub : pv.length = air.num_public_values
  periodic : periodic.length = air.num_periodic_columns

/-- An assignment of the AIR's variables that a window holds.

It covers every entry the AIR can read, and the three selectors. -/
structure Holds {E : Type} [Zero E] (air : Air F) (env : Var → E) (main preprocessed : RowWindow E)
    (pv periodic : List E) (first last trans : E) : Prop where
  shapes : WindowShapes air main preprocessed pv periodic
  main_current : ∀ c < air.width, main.current.getD c 0 = env (.main 0 c)
  main_next : ∀ c < air.width, main.next.getD c 0 = env (.main 1 c)
  prep_current : ∀ c < air.preprocessed_width, preprocessed.current.getD c 0 = env (.prep 0 c)
  prep_next : ∀ c < air.preprocessed_width, preprocessed.next.getD c 0 = env (.prep 1 c)
  pub : ∀ j < air.num_public_values, pv.getD j 0 = env (.pub j)
  periodic : ∀ j < air.num_periodic_columns, periodic.getD j 0 = env (.periodic j)
  first : first = env .isFirstRow
  last : last = env .isLastRow
  trans : trans = env .isTransition

/-- A window holds the assignment that reads it. -/
theorem holds_windowEnv {E : Type} [Field E] {air : Air F} {main preprocessed : RowWindow E}
    {pv periodic : List E} (hs : WindowShapes air main preprocessed pv periodic) (first last trans : E) :
    Holds air (windowEnv main preprocessed pv first last trans periodic) main preprocessed pv periodic
      first last trans :=
  ⟨hs, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, rfl, rfl, rfl⟩

theorem forall₂_window {E : Type} [Zero E] {R : MvPolynomial Var F → E → Prop} {w : ℕ}
    {l : List E} (hl : l.length = w) {f : ℕ → MvPolynomial Var F}
    (h : ∀ c < w, R (f c) (l.getD c 0)) : List.Forall₂ R ((List.range w).map f) l :=
  forall₂_range_map hl fun c hc => by
    have := h c hc
    rwa [List.getD_eq_getElem _ _ (hl ▸ hc)] at this

/-- The polynomial builder and the verifier's folder are related by evaluation.

The evaluation is at an assignment the opened values hold. -/
theorem builderRel_verifier {air : Air F} {env : Var → K} {main preprocessed : RowWindow K}
    {pv : List F} {periodic : List K} {first last trans : K}
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans) (α : K) :
    BuilderRel (polyBuilder (AirLayout.from_air air))
      (verifierFolder main preprocessed pv periodic first last trans α)
      (fun p v => MvPolynomial.aeval env p = v)
      (fun ps acc => acc = combine α (ps.map (MvPolynomial.aeval env))) where
  add h h' := by subst h h'; simp [polyBuilder, verifierFolder]
  sub h h' := by subst h h'; simp [polyBuilder, verifierFolder]
  mul h h' := by subst h h'; simp [polyBuilder, verifierFolder]
  neg h := by subst h; simp [polyBuilder, verifierFolder]
  const c := by simp [polyBuilder, verifierFolder]
  main_current _ := forall₂_window h.shapes.main_current fun c hc => by
    rw [h.main_current c hc]; simp
  main_next _ := forall₂_window h.shapes.main_next fun c hc => by
    rw [h.main_next c hc]; simp
  preprocessed_current _ := forall₂_window h.shapes.prep_current fun c hc => by
    rw [h.prep_current c hc]; simp
  preprocessed_next _ := forall₂_window h.shapes.prep_next fun c hc => by
    rw [h.prep_next c hc]; simp
  public_values _ := forall₂_window (by simpa [verifierFolder, AirLayout.from_air] using h.shapes.pub)
    fun c hc => by simpa [verifierFolder] using (h.pub c hc).symm
  periodic_values _ := forall₂_window h.shapes.periodic fun c hc => by
    rw [h.periodic c hc]; simp
  is_first_row _ := by simp [polyBuilder, verifierFolder, h.first]
  is_last_row _ := by simp [polyBuilder, verifierFolder, h.last]
  is_transition _ := by simp [polyBuilder, verifierFolder, h.trans]
  assert_zero h h' := by
    subst h h'
    simp [polyBuilder, verifierFolder, combine_append_singleton]
  window := rfl

/-- The verifier's accumulator is the combination of the constraint polynomials at the opened values. -/
theorem verifier_accumulator {air : Air F} {env : Var → K} {main preprocessed : RowWindow K}
    {pv : List F} {periodic : List K} {first last trans : K}
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans) (α : K) :
    air.eval (verifierFolder main preprocessed pv periodic first last trans α) 0 =
      combine α ((constraints air).map (MvPolynomial.aeval env)) :=
  air.parametric _ _ _ _ (builderRel_verifier h α) [] 0 (by simp [combine_nil])

end verifier

/-! ## The prover's folder -/

section prover

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- The polynomial builder and the prover's folder are related by evaluation.

The evaluation is at an assignment the row holds. -/
theorem builderRel_prover {air : Air F} {env : Var → F} {main preprocessed : RowWindow F}
    {pv periodic : List F} {first last trans : F}
    (h : Holds air env main preprocessed pv periodic first last trans) :
    BuilderRel (polyBuilder (AirLayout.from_air air))
      (proverFolder main preprocessed pv periodic first last trans)
      (fun p v => MvPolynomial.eval env p = v)
      (fun ps st => st = ps.map (MvPolynomial.eval env)) where
  add h h' := by subst h h'; simp [polyBuilder, proverFolder]
  sub h h' := by subst h h'; simp [polyBuilder, proverFolder]
  mul h h' := by subst h h'; simp [polyBuilder, proverFolder]
  neg h := by subst h; simp [polyBuilder, proverFolder]
  const c := by simp [polyBuilder, proverFolder]
  main_current _ := forall₂_window h.shapes.main_current fun c hc => by
    rw [h.main_current c hc]; simp
  main_next _ := forall₂_window h.shapes.main_next fun c hc => by
    rw [h.main_next c hc]; simp
  preprocessed_current _ := forall₂_window h.shapes.prep_current fun c hc => by
    rw [h.prep_current c hc]; simp
  preprocessed_next _ := forall₂_window h.shapes.prep_next fun c hc => by
    rw [h.prep_next c hc]; simp
  public_values _ := forall₂_window (by simpa [proverFolder, AirLayout.from_air] using h.shapes.pub)
    fun c hc => by simpa [proverFolder] using (h.pub c hc).symm
  periodic_values _ := forall₂_window h.shapes.periodic fun c hc => by
    rw [h.periodic c hc]; simp
  is_first_row _ := by simp [polyBuilder, proverFolder, h.first]
  is_last_row _ := by simp [polyBuilder, proverFolder, h.last]
  is_transition _ := by simp [polyBuilder, proverFolder, h.trans]
  assert_zero h h' := by subst h h'; simp [polyBuilder, proverFolder]
  window := rfl

/-- The prover's folder collects the values of the constraint polynomials on the row, in emission order. -/
theorem prover_constraints {air : Air F} {env : Var → F} {main preprocessed : RowWindow F}
    {pv periodic : List F} {first last trans : F}
    (h : Holds air env main preprocessed pv periodic first last trans) :
    air.eval (proverFolder main preprocessed pv periodic first last trans) [] =
      (constraints air).map (MvPolynomial.eval env) :=
  air.parametric _ _ _ _ (builderRel_prover h) [] [] rfl

/-- The symbolic builder records one base constraint per constraint polynomial. -/
theorem get_constraint_layout_from_air (air : Air F) :
    get_constraint_layout air (AirLayout.from_air air) =
      .ok ⟨List.range (constraints air).length, []⟩ := by
  have h := congrArg List.length (symbolic_toPoly air (AirLayout.from_air air))
  rw [List.length_map] at h
  rw [constraints, ← h]
  simp [get_constraint_layout, AirLayout.validate_against_air, AirLayout.from_air]
  rfl

theorem mapM_some_of {α β : Type _} (l : List α) (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ l, f x = some (g x)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem sum_map_range {M : Type _} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem batched_linear_combination_range {R A : Type} [CommRing R] [AddCommMonoid A] [Module R A]
    (values : List A) (f : ℕ → R) :
    batched_linear_combination values ((List.range values.length).map f) =
      some (∑ j ∈ Finset.range values.length, f j • values.getD j 0) := by
  have hz : values.zip ((List.range values.length).map f) =
      (List.range values.length).map fun j => (values.getD j 0, f j) :=
    List.ext_getElem (by simp) fun j h₁ h₂ => by
      simp only [List.length_map, List.length_range] at h₂
      simp [h₂]
  simp [batched_linear_combination, hz, ← sum_map_range]
  rfl

/-- The prover's combination, with the powers the layout decomposes, is that of the embedded values. -/
theorem finalize_decompose {D : ℕ} (B : Module.Basis (Fin D) F K) (α : K) (base : List F) :
    finalize_constraints B
        (ConstraintLayout.decompose_alpha B ⟨List.range base.length, []⟩ α).1
        (ConstraintLayout.decompose_alpha B ⟨List.range base.length, []⟩ α).2 base [] =
      some (combine α (base.map (algebraMap F K))) := by
  set n := base.length
  set c : Fin D → F := fun d => ∑ j ∈ Finset.range n, B.repr (α ^ (n - 1 - j)) d • base.getD j 0
  have hpow : ∀ j ∈ List.range n,
      (((List.range n).map (α ^ ·)).reverse).getD j 0 = α ^ (n - 1 - j) := by
    intro j hj
    have hj := List.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_reverse]
    simp
  have hcoeff : ∀ d ∈ List.range D, batched_linear_combination base
      ((ConstraintLayout.decompose_alpha B ⟨List.range n, []⟩ α).1.getD d []) =
        some (if h : d < D then c ⟨d, h⟩ else 0) := by
    intro d hd
    have hd := List.mem_range.mp hd
    simp only [hd, ↓reduceDIte]
    rw [ConstraintLayout.decompose_alpha, List.getD_eq_getElem _ _ (by simpa using hd)]
    simp only [List.getElem_map, List.getElem_finRange, ConstraintLayout.total_constraints,
      List.length_range, List.length_nil, add_zero]
    rw [List.map_congr_left fun j hj => by rw [hpow j hj], batched_linear_combination_range]
    rfl
  have hext : (ConstraintLayout.decompose_alpha B ⟨List.range n, []⟩ α).2 = [] := rfl
  rw [finalize_constraints, mapM_some_of _ _ _ hcoeff, hext]
  simp only [batched_linear_combination, List.length_nil, List.zip_nil_left, List.map_nil,
    List.sum_nil, ite_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def, add_zero]
  congr 1
  have hget : ∀ d : Fin D, ((List.range D).map fun d => if h : d < D then c ⟨d, h⟩ else 0).getD d 0 =
      c d := fun d => by rw [List.getD_eq_getElem _ _ (by simp)]; simp
  simp only [hget, c, combine, List.length_map, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show (base.map (algebraMap F K)).getD j 0 = algebraMap F K (base.getD j 0) by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases base[j]? <;> simp]
  calc ∑ d : Fin D, (B.repr (α ^ (n - 1 - j)) d • base.getD j 0) • B d
      = base.getD j 0 • ∑ d : Fin D, B.repr (α ^ (n - 1 - j)) d • B d := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun d _ => by rw [smul_eq_mul, mul_comm, mul_smul]
    _ = α ^ (n - 1 - j) * algebraMap F K (base.getD j 0) := by
        rw [B.sum_repr, Algebra.smul_def, mul_comm]

/-- The two folders weight the constraints with the same powers of alpha, in the same order.

On a row whose values embed in the verifier's, the prover's combination is the verifier's accumulator. -/
theorem prover_eq_verifier {D : ℕ} (B : Module.Basis (Fin D) F K) {air : Air F} {env : Var → F}
    {main preprocessed : RowWindow F} {pv periodic : List F} {first last trans : F}
    (hp : Holds air env main preprocessed pv periodic first last trans)
    {mainK preprocessedK : RowWindow K} {periodicK : List K} {firstK lastK transK : K}
    (hv : Holds air (algebraMap F K ∘ env) mainK preprocessedK (pv.map (algebraMap F K)) periodicK
      firstK lastK transK) (α : K) :
    ∃ l, get_constraint_layout air (AirLayout.from_air air) = .ok l ∧
      finalize_constraints B (l.decompose_alpha B α).1 (l.decompose_alpha B α).2
        (air.eval (proverFolder main preprocessed pv periodic first last trans) []) [] =
      some (air.eval (verifierFolder mainK preprocessedK pv periodicK firstK lastK transK α) 0) := by
  refine ⟨_, get_constraint_layout_from_air air, ?_⟩
  rw [prover_constraints hp, verifier_accumulator hv]
  have := finalize_decompose B α ((constraints air).map (MvPolynomial.eval env))
  rw [List.length_map] at this
  rw [this, List.map_map]
  congr 2
  refine List.map_congr_left fun c _ => ?_
  simp [MvPolynomial.aeval_algebraMap_apply]

end prover


end Plonky3Lean.Proofs.UniStark
