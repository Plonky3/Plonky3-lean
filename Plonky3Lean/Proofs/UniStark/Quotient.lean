module

public import Plonky3Lean.Proofs.UniStark.Verifier

@[expose] public section

/-!
# The prover's quotient values

At point x_i of the quotient coset, the prover folds the constraints on rows i and i + 2^(log |Q| - log n) of the extended trace.

Those rows hold the trace polynomials at x_i and at omega x_i.

The selectors are p3-commit's, so the value is C_alpha(x_i) / (x_i^n - 1).

On a satisfying trace that is the quotient polynomial at x_i.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_air.builder.mirror p3_air.air.mirror p3_uni_stark.folder.mirror p3_uni_stark.prover.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Air

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K] (G : Gen F)

/-- The selector vectors on the quotient coset hold the STARK's selector polynomials at each point, and 1 / Z. -/
theorem selector_entries (hV : GenValid G) (hN : GenNested G) (h2 : (2 : F) ≠ 0)
    {td qd : Coset G} (h1 : td.shift = 1) (hle : td.log_size ≤ qd.log_size)
    (hdisj : qd.shift ^ 2 ^ qd.log_size ≠ 1) {sel : LagrangeSelectors (List F)}
    (hsel : Coset.selectors_on_coset G td qd = some sel) {m : ℕ} (hm : m < 2 ^ qd.log_size)
    (main prep periodic : ℕ → F[X]) (pub : ℕ → F) :
    let σ := starkAssign td.shift td.subgroup_generator td.log_size main prep pub periodic
    let x := qd.shift * qd.subgroup_generator ^ m
    sel.is_first_row.getD m 0 = (σ .isFirstRow).eval x ∧
      sel.is_last_row.getD m 0 = (σ .isLastRow).eval x ∧
      sel.is_transition.getD m 0 = (σ .isTransition).eval x ∧
      sel.inv_vanishing.getD m 0 =
        td.shift ^ 2 ^ td.log_size / (vanishing td.shift td.subgroup_generator td.log_size).eval x := by
  intro σ x
  have hat := selectors_on_coset_at_point G hV hN h1 hle hdisj hsel m hm
  have hx : ¬ InCoset td.shift td.subgroup_generator td.log_size x := fun h =>
    absurd hat (by rw [(selectors_at_point_none G hV td x).mpr h]; simp)
  rw [selectors_at_point_some G hV h2 td x hx, Option.some.injEq, LagrangeSelectors.mk.injEq] at hat
  obtain ⟨e1, e2, e3, e4⟩ := hat
  refine ⟨e1 ▸ ?_, e2 ▸ ?_, e3 ▸ ?_, e4.symm⟩
  · simp [σ, starkAssign]
  · simp [σ, starkAssign]; exact Or.inl rfl
  · simp [σ, starkAssign, cosetPoints, lastIdx, div_eq_inv_mul]

theorem getD_wrappingRow (m : p3_commit.pcs.univariate.mirror.Mat F) {r c : ℕ} (hc : c < m.width) :
    (wrappingRow m r).getD c 0 = m.entry (r % m.height) ⟨c, hc⟩ := by
  simp [wrappingRow, List.getD_eq_getElem?_getD, hc]

/-- The quotient's values on the quotient coset.

Take the extended trace and preprocessed trace at the points x_i of the quotient coset, and a periodic table that reads each periodic polynomial at x_i.

Then the value at x_i is C_alpha(x_i) s^n / Z(x_i), for the trace subgroup's selectors. -/
theorem quotient_values_eq {D : ℕ} (B : Module.Basis (Fin D) F K) (hV : GenValid G)
    (hN : GenNested G) (h2 : (2 : F) ≠ 0) (air : Air F) {pv : List F}
    (hpv : pv.length = air.num_public_values) {td qd : Coset G} (h1 : td.shift = 1)
    (hle : td.log_size ≤ qd.log_size) (hdisj : qd.shift ^ 2 ^ qd.log_size ≠ 1)
    {tq : p3_commit.pcs.univariate.mirror.Mat F} {pq : Option (p3_commit.pcs.univariate.mirror.Mat F)}
    {main prep periodic : ℕ → F[X]} {t : PeriodicLdeTable F}
    (htw : tq.width = air.width) (hth : tq.height = 2 ^ qd.log_size)
    (htrace : ∀ i < 2 ^ qd.log_size, ∀ j : Fin tq.width,
      tq.entry i j = (main j).eval (qd.shift * qd.subgroup_generator ^ i))
    (hpq : match pq with
      | none => air.preprocessed_width = 0
      | some p => p.width = air.preprocessed_width ∧ p.height = 2 ^ qd.log_size ∧
          ∀ i < 2 ^ qd.log_size, ∀ j : Fin p.width,
            p.entry i j = (prep j).eval (qd.shift * qd.subgroup_generator ^ i))
    (hper : build_periodic_lde_table G air.periodic_columns td qd = some t)
    (hte : t.is_empty = true → air.num_periodic_columns = 0)
    (htw' : t.is_empty = false → t.width = air.num_periodic_columns)
    (htg : ∀ i, ∀ j < air.num_periodic_columns,
      t.get i j = some ((periodic j).eval (qd.shift * qd.subgroup_generator ^ i))) (α : K) :
    quotient_values G B air pv (AirLayout.from_air air) td qd tq pq α =
      some ((List.range (2 ^ qd.log_size)).map fun i =>
        combine α ((constraints air).map fun c => algebraMap F K (MvPolynomial.eval
          (fun v => (starkAssign td.shift td.subgroup_generator td.log_size main prep (pv.getD · 0)
            periodic v).eval (qd.shift * qd.subgroup_generator ^ i)) c)) *
        algebraMap F K (td.shift ^ 2 ^ td.log_size /
          (vanishing td.shift td.subgroup_generator td.log_size).eval
            (qd.shift * qd.subgroup_generator ^ i))) := by
  obtain ⟨sel, hsel⟩ : ∃ sel, Coset.selectors_on_coset G td qd = some sel :=
    ⟨_, selectors_on_coset_eq G hV hN h1 hle hdisj⟩
  set σ := starkAssign td.shift td.subgroup_generator td.log_size main prep (pv.getD · 0) periodic
    with hσ
  set ns := 2 ^ (qd.log_size - td.log_size) with hns
  -- The row i + ns of the quotient coset is omega x_i, for omega the trace generator.
  have hgen : td.subgroup_generator = qd.subgroup_generator ^ ns := by
    have := gen_sub G hN qd.log_size_le (Nat.sub_le qd.log_size td.log_size)
    rwa [Nat.sub_sub_self hle] at this
  have hnext : ∀ i, qd.shift * qd.subgroup_generator ^ ((i + ns) % 2 ^ qd.log_size) =
      td.subgroup_generator * (qd.shift * qd.subgroup_generator ^ i) := by
    intro i
    rw [(prim G hV qd).eq_orderOf, pow_mod_orderOf, hgen, pow_add]
    ring
  -- The periodic values at each point.
  have hP : ∀ i, ∃ P : List F, (if t.is_empty then some [] else
      (List.range t.width).mapM (t.get i)) = some P ∧ P.length = air.num_periodic_columns ∧
      ∀ j < air.num_periodic_columns,
        P.getD j 0 = (periodic j).eval (qd.shift * qd.subgroup_generator ^ i) := by
    intro i
    cases he : t.is_empty
    · have hw := htw' he
      refine ⟨_, mapM_some_of _ _ (fun j => (periodic j).eval (qd.shift * qd.subgroup_generator ^ i))
        fun j hj => htg i j (hw ▸ List.mem_range.mp hj), by simp [hw], fun j hj => ?_⟩
      simp [List.getD_eq_getElem?_getD, hw, hj]
    · exact ⟨[], rfl, (hte he).symm ▸ rfl, fun j hj => absurd hj (by rw [hte he]; omega)⟩
  -- The value at one point, for any periodic values that read the periodic polynomials there.
  have key : ∀ i < 2 ^ qd.log_size, ∀ P : List F, P.length = air.num_periodic_columns →
      (∀ j < air.num_periodic_columns,
        P.getD j 0 = (periodic j).eval (qd.shift * qd.subgroup_generator ^ i)) →
      (finalize_constraints B
        (ConstraintLayout.decompose_alpha B ⟨List.range (constraints air).length, []⟩ α).1
        (ConstraintLayout.decompose_alpha B ⟨List.range (constraints air).length, []⟩ α).2
        (air.eval (proverFolder ⟨wrappingRow tq i, wrappingRow tq (i + ns)⟩
          (match (generalizing := false) pq with
            | some p => ⟨wrappingRow p i, wrappingRow p (i + ns)⟩
            | none => ⟨[], []⟩)
          pv P (sel.is_first_row.getD i 0) (sel.is_last_row.getD i 0)
          (sel.is_transition.getD i 0)) []) []).bind
        (fun q => pure (q * algebraMap F K (sel.inv_vanishing.getD i 0))) =
      some (combine α ((constraints air).map fun c => algebraMap F K (MvPolynomial.eval
          (fun v => (σ v).eval (qd.shift * qd.subgroup_generator ^ i)) c)) *
        algebraMap F K (td.shift ^ 2 ^ td.log_size /
          (vanishing td.shift td.subgroup_generator td.log_size).eval
            (qd.shift * qd.subgroup_generator ^ i))) := by
    intro i hi P hPl hPg
    obtain ⟨e1, e2, e3, e4⟩ := selector_entries G hV hN h2 h1 hle hdisj hsel hi main prep periodic
      (pv.getD · 0)
    have hmod : i % 2 ^ qd.log_size = i := Nat.mod_eq_of_lt hi
    have hrow : ∀ (m : p3_commit.pcs.univariate.mirror.Mat F) (f : ℕ → F[X]),
        m.height = 2 ^ qd.log_size →
        (∀ i < 2 ^ qd.log_size, ∀ j : Fin m.width,
          m.entry i j = (f j).eval (qd.shift * qd.subgroup_generator ^ i)) →
        ∀ c (hc : c < m.width),
          (wrappingRow m i).getD c 0 = (f c).eval (qd.shift * qd.subgroup_generator ^ i) ∧
          (wrappingRow m (i + ns)).getD c 0 =
            ((f c).comp (C td.subgroup_generator * X)).eval (qd.shift * qd.subgroup_generator ^ i) := by
      intro m f hmh hme c hc
      refine ⟨?_, ?_⟩
      · rw [getD_wrappingRow m hc, hmh, hmod, hme i hi]
      · rw [getD_wrappingRow m hc, hmh, hme _ (Nat.mod_lt _ (by positivity)), hnext, eval_comp]
        simp
    have hholds : Holds air (fun v => (σ v).eval (qd.shift * qd.subgroup_generator ^ i))
        ⟨wrappingRow tq i, wrappingRow tq (i + ns)⟩
        (match (generalizing := false) pq with
          | some p => ⟨wrappingRow p i, wrappingRow p (i + ns)⟩
          | none => ⟨[], []⟩)
        pv P (sel.is_first_row.getD i 0) (sel.is_last_row.getD i 0) (sel.is_transition.getD i 0) := by
      rcases pq with _ | p
      · exact {
          shapes := ⟨by simp [wrappingRow, htw], by simp [wrappingRow, htw], by simp [hpq],
            by simp [hpq], hpv, hPl⟩
          main_current := fun c hc => (hrow tq main hth htrace c (htw ▸ hc)).1
          main_next := fun c hc => (hrow tq main hth htrace c (htw ▸ hc)).2
          prep_current := fun c hc => absurd hc (by simp [hpq])
          prep_next := fun c hc => absurd hc (by simp [hpq])
          pub := fun j _ => by simp [hσ, starkAssign]
          periodic := fun j hj => hPg j hj
          first := e1
          last := e2
          trans := e3 }
      · obtain ⟨hpw, hph, hpe⟩ := hpq
        exact {
          shapes := ⟨by simp [wrappingRow, htw], by simp [wrappingRow, htw],
            by simp [wrappingRow, hpw], by simp [wrappingRow, hpw], hpv, hPl⟩
          main_current := fun c hc => (hrow tq main hth htrace c (htw ▸ hc)).1
          main_next := fun c hc => (hrow tq main hth htrace c (htw ▸ hc)).2
          prep_current := fun c hc => (hrow p prep hph hpe c (hpw ▸ hc)).1
          prep_next := fun c hc => (hrow p prep hph hpe c (hpw ▸ hc)).2
          pub := fun j _ => by simp [hσ, starkAssign]
          periodic := fun j hj => hPg j hj
          first := e1
          last := e2
          trans := e3 }
    have hfin := finalize_decompose B α
      ((constraints air).map (MvPolynomial.eval fun v => (σ v).eval (qd.shift * qd.subgroup_generator ^ i)))
    rw [List.length_map] at hfin
    rw [prover_constraints hholds, hfin, e4, List.map_map]
    rfl
  unfold quotient_values
  simp only [hsel, get_constraint_layout_from_air, hper, Except.toOption, Option.bind_eq_bind,
    Option.bind_some, not_lt.mpr hle, ite_false]
  refine mapM_some_of _ _ _ fun i hi => ?_
  have hi := List.mem_range.mp hi
  obtain ⟨P, hPe, hPl, hPg⟩ := hP i
  cases he : t.is_empty <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hPe ⊢
  · rw [hPe, Option.bind_some]
    exact key i hi P hPl hPg
  · cases (Option.some.inj hPe)
    exact key i hi [] hPl hPg

end Plonky3Lean.Proofs.UniStark
