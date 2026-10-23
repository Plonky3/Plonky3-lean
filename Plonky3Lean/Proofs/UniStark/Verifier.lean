module

public import Plonky3Lean.Proofs.UniStark.Recompose
public import Plonky3Lean.Proofs.Commit.Selectors

@[expose] public section

/-!
# The constraint check at the out-of-domain point

The check panics exactly when zeta lies on the trace domain, where the selectors divide by zero.

Off the domain, on the honest openings of a trace that satisfies the STARK's relation, the fold times 1 / Z(zeta) is the quotient at zeta.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_air.builder.mirror p3_air.air.mirror p3_uni_stark.folder.mirror p3_uni_stark.verifier.mirror
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Air

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K] (G : Gen K)

/-- The check panics exactly when zeta lies on the trace domain, for an AIR without boundary cells. -/
theorem verify_constraints_none_iff (hV : GenValid G) (air : Air F)
    (hb : air.public_boundary_io = []) (trace_local trace_next : List K)
    (pl pn : Option (List K)) (periodic : List K) (pv : List F) (c : Coset G) (ζ α q : K) :
    verify_constraints G air trace_local trace_next pl pn periodic pv c ζ α q = none ↔
      InCoset c.shift c.subgroup_generator c.log_size ζ := by
  rw [← selectors_at_point_none G hV c ζ]
  simp only [verify_constraints, hb, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases Coset.selectors_at_point G c ζ with _ | sels
  · simp
  · simp only [Option.bind_eq_bind, Option.bind_some, reduceCtorEq, iff_false]
    split_ifs <;> simp

/-- When the check returns, it accepts exactly when both preprocessed rows have one width and the fold times the inverse vanishing value is the quotient. -/
theorem verify_constraints_ok_iff (air : Air F) (trace_local trace_next : List K)
    (pl pn : Option (List K)) (periodic : List K) (pv : List F) (c : Coset G) (ζ α q : K)
    (r : Except VerificationError Unit)
    (h : verify_constraints G air trace_local trace_next pl pn periodic pv c ζ α q = some r) :
    r = .ok () ↔ ∃ sels, Coset.selectors_at_point G c ζ = some sels ∧
      (pl.map List.length).getD 0 = (pn.map List.length).getD 0 ∧
      air.eval (verifierFolder ⟨trace_local, trace_next⟩ (preprocessedWindow pl pn) pv periodic
        sels.is_first_row sels.is_last_row sels.is_transition α) 0 * sels.inv_vanishing = q := by
  unfold verify_constraints at h
  by_cases hb : air.public_boundary_io = []
  · rcases hs : Coset.selectors_at_point G c ζ with _ | sels
    · simp [hb, hs] at h
    · simp only [hb, hs, ne_eq, not_true_eq_false, ↓reduceIte, Option.bind_eq_bind,
        Option.bind_some] at h
      by_cases h1 : (pl.map List.length).getD 0 = (pn.map List.length).getD 0 <;>
        simp only [h1, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
      · split_ifs at h with h2 <;> cases (Option.some.inj h) <;> simp_all
      · cases (Option.some.inj h); simp_all
  · simp [hb] at h

/-- The shape checks accept exactly when every documented shape holds. -/
theorem check_shape_ok_iff (air : Air F) (opens zk : Bool) (D n bits : ℕ) (pv : List F)
    (tl : List K) (tn : Option (List K)) (qcs : List (List K)) (r : Option (List K)) (rc : Bool)
    (w : F) :
    check_shape air opens zk D n bits pv tl tn qcs r rc w = .ok () ↔
      r.isSome = zk ∧ rc = zk ∧ pv.length = air.num_public_values ∧
      (if opens then ∃ v, tn = some v ∧ v.length = air.width else tn = none) ∧
      tl.length = air.width ∧ qcs.length = n ∧ (∀ qc ∈ qcs, qc.length = D) ∧
      (∀ x ∈ r, x.length = D) ∧ (bits = 0 → w = 0) := by
  unfold check_shape
  by_cases h1 : r.isSome ≠ zk ∨ rc ≠ zk
  · simp only [h1, ↓reduceIte]
    simp only [ne_eq] at h1
    constructor
    · intro h; cases h
    · rintro ⟨ha, hb, -⟩; tauto
  · simp only [h1, ↓reduceIte]
    push Not at h1
    obtain ⟨ha, hb⟩ := h1
    cases opens <;> rcases tn with _ | v <;>
      simp only [ha, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] <;>
      split_ifs <;> simp_all <;>
      (intro a b c hr; rename_i h; obtain ⟨x, hx, hn⟩ := h a b c; exact absurd (hr x hx) hn)

/-- Once zeta passes the domain check, the selectors at zeta do not panic. -/
theorem check_ood_point_ok (hV : GenValid G) (c : Coset G) (ζ : K)
    (h : check_ood_point G c ζ = .ok ()) : (Coset.selectors_at_point G c ζ).isSome := by
  rw [Option.isSome_iff_ne_none, Ne, selectors_at_point_none G hV c ζ,
    ← vanishing_poly_at_point_eq_zero G hV c ζ]
  intro h0
  simp [check_ood_point, h0, throw, throwThe, MonadExceptOf.throw] at h

/-- The honest opening of row o of the trace at zeta: column c of the assignment, evaluated at zeta. -/
noncomputable def openRow (σ : Var → K[X]) (row : ℕ → Var) (w : ℕ) (ζ : K) : List K :=
  (List.range w).map fun c => (σ (row c)).eval ζ

theorem getD_openRow (σ : Var → K[X]) (row : ℕ → Var) {w c : ℕ} (hc : c < w) (ζ : K) :
    (openRow σ row w ζ).getD c 0 = (σ (row c)).eval ζ := by
  simp [openRow, List.getD_eq_getElem?_getD, hc]

/-- Completeness of the check at zeta.

Take a trace that satisfies the STARK's relation on the subgroup s H, interpolated by the trace polynomials.

On the honest openings of the trace at zeta, with zeta off s H, the check accepts the quotient s^n C_alpha / Z at zeta. -/
theorem verify_constraints_complete (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) {s ω : F}
    (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]} {pv : List F}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpv : pv.length = air.num_public_values)
    (hsat : SatisfiesStark (constraints air) T ω) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) (α : K) {pl pn : Option (List K)}
    (hpre : (pl = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 0) air.preprocessed_width ζ) ∧
      pn = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 1) air.preprocessed_width ζ)) ∨
      (pl = none ∧ pn = none ∧ air.preprocessed_width = 0)) :
    verify_constraints G air
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
      pl pn
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) .periodic
        air.num_periodic_columns ζ) pv c ζ α
      ((quotientPoly c.shift c.subgroup_generator c.log_size
        (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
          (constraints air))).eval ζ) = some (.ok ()) := by
  set σ := starkAssignK (K := K) s ω c.log_size main prep (pv.getD · 0) periodic with hσ
  have hsel := selectors_at_point_some G hV h2 c ζ hζ
  have hZ : (vanishing c.shift c.subgroup_generator c.log_size).eval ζ ≠ 0 := by
    rw [eval_vanishing G hV, sub_ne_zero]
    exact fun h => hζ ((inCoset_iff (prim G hV c) c.shift_ne_zero).mpr h)
  have hdvd : vanishing c.shift c.subgroup_generator c.log_size ∣
      combinedPoly α σ (constraints air) := by
    rw [hcs, hcg]
    exact vanishing_dvd_combinedPoly hω hs hT hmain hprep (fun j => (hpub j)) hper hsat α
  -- The window the folder sees holds the assignment at zeta.
  have hw : preprocessedWindow pl pn = ⟨openRow σ (.prep 0) air.preprocessed_width ζ,
      openRow σ (.prep 1) air.preprocessed_width ζ⟩ := by
    rcases hpre with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h0⟩
    · rfl
    · simp [preprocessedWindow, openRow, h0]
  have hlen : (pl.map List.length).getD 0 = (pn.map List.length).getD 0 := by
    rcases hpre with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ <;> simp [openRow]
  have hholds : Holds air (fun v => (σ v).eval ζ)
      ⟨openRow σ (.main 0) air.width ζ, openRow σ (.main 1) air.width ζ⟩
      ⟨openRow σ (.prep 0) air.preprocessed_width ζ, openRow σ (.prep 1) air.preprocessed_width ζ⟩
      (pv.map (algebraMap F K)) (openRow σ .periodic air.num_periodic_columns ζ)
      ((2 ^ c.log_size : K) * (lagrange c.shift c.subgroup_generator c.log_size 0).eval ζ)
      ((2 ^ c.log_size : K) * c.subgroup_generator *
        (lagrange c.shift c.subgroup_generator c.log_size (lastIdx c.log_size)).eval ζ)
      ((ζ - cosetPoints c.shift c.subgroup_generator c.log_size (lastIdx c.log_size)) / c.shift) := {
    shapes := ⟨by simp [openRow], by simp [openRow], by simp [openRow], by simp [openRow],
      by simp [hpv], by simp [openRow]⟩
    main_current := fun _ h => getD_openRow σ _ h ζ
    main_next := fun _ h => getD_openRow σ _ h ζ
    prep_current := fun _ h => getD_openRow σ _ h ζ
    prep_next := fun _ h => getD_openRow σ _ h ζ
    pub := fun j _ => by
      rw [getD_map_zero _ (map_zero _)]
      simp [hσ, starkAssignK, starkAssign]
    periodic := fun _ h => getD_openRow σ _ h ζ
    first := by simp [hσ, starkAssignK, starkAssign, lagrange_map, hcs, hcg, map_ofNat]
    last := by
      simp [hσ, starkAssignK, starkAssign, lagrange_map, hcs, hcg, map_ofNat]
      exact Or.inl rfl
    trans := by
      simp only [hσ, starkAssignK, starkAssign, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_C, eval_sub, eval_X, map_inv₀,
        map_mul, map_pow, cosetPoints, lastIdx, hcs, hcg, Polynomial.map_pow, eval_pow]
      rw [div_eq_inv_mul] }
  have hfold := verifier_accumulator hholds α
  rw [← eval_combinedPoly] at hfold
  simp only [verify_constraints, hb, ne_eq, not_true_eq_false, ↓reduceIte, hsel,
    Option.bind_eq_bind, Option.bind_some, hlen, hw, hfold, eval_quotientPoly hdvd hZ]
  simp only [div_eq_mul_inv]
  ring_nf
  simp

end Plonky3Lean.Proofs.UniStark
