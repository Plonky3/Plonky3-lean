module

public import Plonky3Lean.Proofs.Stir.Newton
public import Plonky3Lean.Proofs.Stir.QueryFold

@[expose] public section

/-!
# The verifier's shape checks and the query loop

The answer polynomial is accepted with at most one coefficient per point, and none only when there is no point.

The compact encoding interpolates the points itself, and rejects repeated points instead of panicking.

The query loop keeps the first answer of each repeated index, so the points it records are distinct.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_stir.verifier.mirror p3_dft.mirror
open Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

theorem throw_ne_pure {α : Type} (e : StirError) (a : α) : (throw e : VM α) ≠ pure a := by
  intro h; cases h

/-- The sent answer polynomial is accepted with at most max coefficients, and an empty list only when max = 0. -/
theorem check_ans_length_ok (round : ℕ) (ans : List EF) (max : ℕ) :
    check_ans_length round ans max = pure () ↔ ans.length ≤ max ∧ (ans ≠ [] ∨ max = 0) := by
  unfold check_ans_length
  split_ifs with h1 h2
  · simp only [throw_ne_pure, false_iff, not_and]; intro h; omega
  · obtain ⟨rfl, h⟩ := h2
    simp only [throw_ne_pure, false_iff]; simp; omega
  · simp only [true_iff]
    refine ⟨by omega, ?_⟩
    by_cases he : ans = []
    · exact Or.inr (by by_contra hm; exact h2 ⟨he, by omega⟩)
    · exact Or.inl he

/-- The compact encoding on distinct points rebuilds the interpolant, and never panics. -/
theorem resolve_compact_eq (round : ℕ) (points values : List EF) (hlen : points.length = values.length)
    (hnd : points.Nodup) (hne : points ≠ []) :
    ∃ cs, resolve_ans_polynomial round true [] points values = pure cs ∧
      coeffPoly cs = Lagrange.interpolate (range points.length) (fun i => points.getD i 0)
        (fun i => values.getD i 0) := by
  obtain ⟨cs, hcs, hp⟩ := interpolate_poly_eq points values hlen hnd hne
  refine ⟨cs, ?_, hp⟩
  have hdup : ¬ (List.range values.length).any (fun i => (points.take i).contains (points.getD i 0)) := by
    simp only [List.any_eq_true, List.mem_range, List.contains_iff_mem, not_exists, not_and]
    intro i hi hmem
    rw [← hlen] at hi
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
    rw [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at hje
    simp only [List.length_take] at hj
    have := (hnd.getElem_inj_iff).1 hje
    omega
  simp only [resolve_ans_polynomial, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_true_eq_false, hlen, false_or, hdup, liftO, hcs]
  rfl

theorem nodup_of_not_any (points : List EF)
    (h : ¬ (List.range points.length).any (fun i => (points.take i).contains (points.getD i 0))) :
    points.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj heq
  apply h
  simp only [List.any_eq_true, List.mem_range, List.contains_iff_mem]
  refine ⟨j, hj, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [List.getElem?_eq_getElem (hij.trans hj), List.getElem?_eq_getElem hj, Option.some.injEq] at heq
  rw [← heq]
  exact List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩

theorem check_ans_length_run (round : ℕ) (ans : List EF) (max : ℕ) :
    (check_ans_length round ans max).run.isSome := by
  unfold check_ans_length; split_ifs <;> rfl

/-- Resolving the answer polynomial never panics: every malformed answer polynomial is an error. -/
theorem resolve_ans_polynomial_no_panic (round : ℕ) (compact : Bool) (transmitted points values : List EF) :
    (resolve_ans_polynomial round compact transmitted points values).run.isSome := by
  unfold resolve_ans_polynomial
  cases compact
  · simp only [Bool.not_false, ↓reduceIte, check_ans_length]
    split_ifs <;> rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · rfl
    · rfl
    · push Not at h2
      obtain ⟨hlen, hany⟩ := h2
      have hnd := nodup_of_not_any points (by simpa using hany)
      by_cases hne : points = []
      · subst hne
        have : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
        subst this; rfl
      · obtain ⟨cs, hcs, -⟩ := interpolate_poly_eq points values hlen hnd hne
        simp [liftO, hcs]

/-- An invariant every successful step keeps holds after a successful loop. -/
theorem foldlM_inv {σ : Type} (P : σ → Prop) (step : σ → ℕ → VM σ) :
    ∀ (l : List ℕ), (∀ s q s', q ∈ l → P s → step s q = pure s' → P s') →
      ∀ (init r : σ), P init → l.foldlM step init = pure r → P r := by
  intro l
  induction l with
  | nil => intro _ init r h hr; cases hr; exact h
  | cons q l ih' =>
    intro hstep init r h hr
    have ih := ih' fun s q' s' hq => hstep s q' s' (List.mem_cons_of_mem _ hq)
    rw [List.foldlM_cons] at hr
    rcases hs : (step init q).run with _ | (e | s)
    · have : step init q = ExceptT.mk none := by rw [← hs]; rfl
      rw [this] at hr; cases hr
    · have : step init q = ExceptT.mk (some (Except.error e)) := by rw [← hs]; rfl
      rw [this] at hr; cases hr
    · have : step init q = pure s := by
        show step init q = ExceptT.mk (some (Except.ok s)); rw [← hs]; rfl
      rw [this] at hr
      exact ih s r (hstep _ _ _ (by simp) h this) hr

/-- Bind in VM through a step that succeeded. -/
theorem bind_eq_pure {α β : Type} {x : VM α} {f : α → VM β} {b : β} (h : x >>= f = pure b) :
    ∃ a, x = pure a ∧ f a = pure b := by
  rcases hx : x.run with _ | (e | a)
  · have : x = ExceptT.mk none := by rw [← hx]; rfl
    rw [this] at h; cases h
  · have : x = ExceptT.mk (some (Except.error e)) := by rw [← hx]; rfl
    rw [this] at h; cases h
  · have : x = pure a := by show x = ExceptT.mk (some (Except.ok a)); rw [← hx]; rfl
    exact ⟨a, this, by rw [this] at h; exact h⟩

/-- The query loop records each distinct index once, its point at the index, and one answer per point. -/
theorem fold_queries_seen (G : Gen F) (round : ℕ) (fold_shift : F) (fold_log_domain current_log_domain : ℕ)
    (arity : ℕ) (current_shift : F) (fold_beta : EF) (prev_ctx : Option (VirtualRoundContext EF))
    (query_indices : List ℕ) (round_rows : List (List EF)) (st : QueryState F EF)
    (h : fold_queries G round fold_shift fold_log_domain current_log_domain arity current_shift fold_beta
      prev_ctx query_indices round_rows = pure st) :
    st.seen.Nodup ∧
      st.query_points = st.seen.map (fun j => algebraMap F EF fold_shift *
        algebraMap F EF (G.gen fold_log_domain ^ j)) ∧
      (∀ j ∈ st.seen, j ∈ query_indices) ∧ st.query_answers.length = st.seen.length := by
  unfold fold_queries at h
  obtain ⟨fold_gen, hfg, h⟩ := bind_eq_pure h
  obtain ⟨domain_gen, -, h⟩ := bind_eq_pure h
  have hfg' : fold_gen = G.gen fold_log_domain := by
    unfold liftO Gen.get at hfg; split_ifs at hfg <;> cases hfg; rfl
  subst hfg'
  refine foldlM_inv (fun st : QueryState F EF => st.seen.Nodup ∧
      st.query_points = st.seen.map (fun j => algebraMap F EF fold_shift *
        algebraMap F EF (G.gen fold_log_domain ^ j)) ∧
      (∀ j ∈ st.seen, j ∈ query_indices) ∧ st.query_answers.length = st.seen.length) _ _ ?_ _ _
    ⟨List.nodup_nil, rfl, by simp, rfl⟩ h
  intro s q s' hq ⟨h1, h2, h3, h4⟩ hs'
  obtain ⟨fv, -, hs'⟩ := bind_eq_pure hs'
  have hq' := List.mem_range.1 hq
  have hj : ((query_indices.zip round_rows)[q]).1 ∈ query_indices :=
    (List.of_mem_zip (List.getElem_mem hq')).1
  have hsome : (query_indices.zip round_rows)[q]? = some ((query_indices.zip round_rows)[q]) :=
    List.getElem?_eq_getElem hq'
  simp only [hsome] at hs'
  generalize (query_indices.zip round_rows)[q] = pr at hs' hj
  obtain ⟨j, row⟩ := pr
  dsimp only at hs' hj
  by_cases hn : j ∈ s.seen
  · rw [ite_eq_right (not_not.2 hn)] at hs'
    cases hs'; exact ⟨h1, h2, h3, h4⟩
  · rw [ite_eq_left hn] at hs'
    cases hs'
    refine ⟨h1.append (List.nodup_singleton _) (by simpa using hn), by simp [h2], fun j' hjm => ?_,
      by simp [h4]⟩
    rcases List.mem_append.1 hjm with hjm | hjm
    · exact h3 j' hjm
    · rw [List.mem_singleton.1 hjm]; exact hj

theorem mapM_pure {α β : Type} (f : α → VM β) :
    ∀ l : List α, (∀ x ∈ l, ∃ b, f x = pure b) → ∃ bs, l.mapM f = pure bs := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons x l ih =>
    intro h
    obtain ⟨b, hb⟩ := h x (by simp)
    obtain ⟨bs, hbs⟩ := ih fun y hy => h y (by simp [hy])
    exact ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl⟩

/-- Every draw is in the sorted, deduplicated index list the source answers. -/
theorem mem_unique_of_mem (indices : List ℕ) {j : ℕ} (hj : j ∈ indices) :
    j ∈ (indices.mergeSort (· ≤ ·)).dedup := by
  rw [List.mem_dedup, List.mem_mergeSort]; exact hj

/-- Laying the external fibers out in draw order never panics when the source does not. -/
theorem external_fibers_no_panic (indices : List ℕ) (arity : ℕ) (round : Option ℕ)
    (source : List ℕ → VM (List (List EF))) (hsrc : ∀ l, (source l).run.isSome) :
    (external_fibers_in_draw_order indices arity round source).run.isSome := by
  unfold external_fibers_in_draw_order
  dsimp only
  rcases hs : (source (indices.mergeSort (· ≤ ·)).dedup).run with _ | (e | fibers)
  · have := hsrc (indices.mergeSort (· ≤ ·)).dedup; rw [hs] at this; cases this
  · have : source (indices.mergeSort (· ≤ ·)).dedup = ExceptT.mk (some (Except.error e)) := by
      rw [← hs]; rfl
    rw [this]; rfl
  · have : source (indices.mergeSort (· ≤ ·)).dedup = pure fibers := by
      show _ = ExceptT.mk (some (Except.ok fibers)); rw [← hs]; rfl
    rw [this, pure_bind]
    split_ifs
    · rfl
    · split
      · rfl
      · obtain ⟨bs, hbs⟩ := mapM_pure (fun j => match ((indices.mergeSort (· ≤ ·)).dedup).idxOf? j with
          | some pos => (pure (fibers.getD pos []) : VM (List EF))
          | none => panic) indices (fun j hj => by
            obtain ⟨pos, hpos⟩ : ∃ pos, ((indices.mergeSort (· ≤ ·)).dedup).idxOf? j = some pos :=
              Option.isSome_iff_exists.1 (List.isSome_idxOf?.2 (mem_unique_of_mem indices hj))
            exact ⟨fibers.getD pos [], by simp only [hpos]⟩)
        erw [hbs]; rfl

end Plonky3Lean.Proofs.Stir
