module

public import Plonky3Lean.Proofs.Whir.Complete

@[expose] public section

/-!
# The verifier never panics

On a consistent configuration and a Merkle scheme that accepts only rows of the stated width, every proof gives an answer: an acceptance or an error.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.mirror p3_sumcheck.constraints.mirror p3_whir.mirror p3_whir.transcript.mirror
open p3_multilinear_util.point.mirror Plonky3Lean.Proofs.Sumcheck

set_option linter.unusedSectionVars false

variable {F EF Com MP : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The Merkle scheme accepts only rows of the stated width. -/
def Widths (m : Mmcs F EF Com MP) : Prop :=
  (∀ root dims idx rows pf, m.verifyBase root dims idx rows pf = true → ∀ r ∈ rows, r.length = dims.2) ∧
    ∀ root dims idx rows pf, m.verifyExt root dims idx rows pf = true → ∀ r ∈ rows, r.length = dims.2

variable (E : Env F EF Com MP)

theorem verify_merkle_proof_widths (hw : Widths E.mmcs) {openings : QueryOpenings F EF MP} {root : Com}
    {idx : List ℕ} {dims : ℕ × ℕ} {t : ℕ} {answers : List (List EF)}
    (h : verify_merkle_proof E openings root idx dims t = .ok answers) : ∀ a ∈ answers, a.length = dims.2 := by
  unfold verify_merkle_proof at h
  split at h
  · split_ifs at h with h1 h2
    cases h
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    simpa using hw.1 _ _ _ _ _ h2 r hr
  · split_ifs at h with h1 h2
    cases h
    exact hw.2 _ _ _ _ _ h2
  · cases h

/-- On rows of 2^k values and k < 64 challenges, the folds never panic. -/
theorem folds_some (thr w T : ℕ) (r : List EF) (hr : r.length < 64) :
    ∀ answers : List (List EF), (∀ a ∈ answers, a.length = 2 ^ r.length) →
      ∃ v, answers.mapM (fun a => (p3_multilinear_util.poly.mirror.Poly.new a).bind
        fun p => p3_multilinear_util.split_eq.mirror.Poly.eval_ext thr w T p r) = some v
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
    obtain ⟨v, hv⟩ := folds_some thr w T r hr as fun b hb => h b (by simp [hb])
    have ha := h a (by simp)
    exact ⟨mle a r :: v, by simp [List.mapM_cons, Poly_new_pow a ha, poly_eval_ext_eq thr w T a r hr ha, hv]⟩

/-- The STIR phase never panics, when the challenges match the fold width and the generator exists; an accepted statement has the round's variable count. -/
theorem stir_some (hw : Widths E.mmcs) (c : WhirConfig) (openings : QueryOpenings F EF MP) (pw : F)
    (params : RoundConfig) (root : Com) (r : List EF) (t : ℕ) (h : List (Step F EF))
    (hs : (c.site t).isSome) (hk : params.folding_factor = r.length) (h64 : r.length < 64)
    (hg : params.log_folded_domain_size ≤ E.adicity) :
    ∃ res, verify_stir_challenges E c openings pw params root r t h = some res ∧
      ∀ stir h', res = .ok (stir, h') → stir.num_variables = params.num_variables := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  simp only [verify_stir_challenges, hs, Option.bind_eq_bind, Option.bind_some]
  split
  · exact ⟨_, rfl, fun _ _ h => by cases h⟩
  · split
    · exact ⟨_, rfl, fun _ _ h => by cases h⟩
    · next answers hm =>
      obtain ⟨v, hv⟩ := folds_some E.thr E.w E.T r h64 answers fun a ha => by
        rw [verify_merkle_proof_widths E hw hm a ha, hk]
      rw [hv]
      simp only [Option.bind_some, two_adic_generator, hg, ↓reduceIte]
      exact ⟨_, rfl, fun stir h' he => by cases he; rfl⟩

/-- An accepted sumcheck returns one challenge per round. -/
theorem verify_rounds_length (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F) (h : List (Step F EF))
    (c : EF) (N pow : ℕ) (basis : Basis) {rs : List EF} {c' : EF} {h' : List (Step F EF)}
    (hok : verify_rounds S evals wits h c N pow basis = .ok (rs, c', h')) : rs.length = N := by
  rw [verify_rounds_eq] at hok
  by_cases h1 : evals.length = N
  · by_cases h2 : wits.length = if 0 < pow then N else 0
    · simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte] at hok
      revert hok
      split
      · intro hok; cases hok
      · intro hok
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        rw [← hok.1]
        simp
    · simp [h1, h2] at hok
  · simp [h1] at hok

/-- The final weight never panics when every constraint fits the end of the point. -/
theorem eval_constraints_poly_some (r : List EF) :
    ∀ cs : List (Constraint F EF), (∀ c ∈ cs, c.num_variables ≤ r.length ∧
      ∀ s ∈ c.statements, s.Dim c.num_variables) →
      ∃ v, VariableOrder.Prefix.eval_constraints_poly cs r = some v := by
  intro cs h
  have hval : ∀ (c : Constraint F EF) (y : List EF), (∀ s ∈ c.statements, s.Fits y) → ∃ v, constraintValue c y = some v := by
    intro c y hc
    suffices ∀ (l : List (Statements F EF)) (acc : EF × ℕ), (∀ s ∈ l, s.Fits y) →
        ∃ v, l.foldlM (fun (acc : EF × ℕ) (s : Statements F EF) => do
          let w ← s.weights_at y
          pure (acc.1 + dot w (powers c.challenge (c.initial_power + acc.2) w.length), acc.2 + s.len)) acc = some v by
      obtain ⟨v, hv⟩ := this c.statements (0, 0) hc
      exact ⟨v.1, by rw [constraintValue, hv]; rfl⟩
    intro l
    induction l with
    | nil => exact fun acc _ => ⟨acc, rfl⟩
    | cons s l ih =>
      intro acc hl
      obtain ⟨v, hv⟩ := ih (acc.1 + dot (s.weights y) (powers c.challenge (c.initial_power + acc.2)
        (s.weights y).length), acc.2 + s.len) fun t ht => hl t (by simp [ht])
      exact ⟨v, by rw [List.foldlM_cons, Statements.weights_at_eq (hl s (by simp))]; exact hv⟩
  have hm : ∃ vs, cs.mapM (fun c => (subpoint r.reverse c.num_variables).bind fun sub =>
      constraintValue c sub.reverse) = some vs := by
    induction cs with
    | nil => exact ⟨[], rfl⟩
    | cons c cs ih =>
      obtain ⟨vs, hvs⟩ := ih fun t ht => h t (by simp [ht])
      obtain ⟨hn, hd⟩ := h c (by simp)
      have hsub : subpoint r.reverse c.num_variables = some (r.drop (r.length - c.num_variables)).reverse := by
        simp [subpoint, hn, List.take_reverse]
      obtain ⟨v, hv⟩ := hval c (r.drop (r.length - c.num_variables)) fun s hs => by
        have := hd s hs
        cases s with
        | Eq s => exact fun p hp => by rw [this p hp, List.length_drop]; omega
        | Select s => trivial
      exact ⟨v :: vs, by simp [List.mapM_cons, hsub, hv, hvs]⟩
  obtain ⟨vs, hvs⟩ := hm
  exact ⟨vs.sum, by simp only [VariableOrder.eval_constraints_poly, Option.bind_eq_bind, hvs]; rfl⟩

theorem expand_points (S : WSponge F EF) (nv : ℕ) (ys : List EF) (h : List (Step F EF)) :
    ∀ k, ∀ p ∈ ((List.range k).foldl (fun (acc : List (List EF) × List (Step F EF)) i =>
        let z := S.sample acc.2
        let point := Point.expand_from_univariate z nv
        (acc.1 ++ [point], acc.2 ++ [.challenge, .message [ys.getD i 0]])) ([], h)).1, p.length = nv
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact expand_points S nv ys h k p hp
    · simp only [List.mem_singleton] at hp
      simp [hp, expand_from_univariate_eq]

/-- A parsed round's out-of-domain statement has the round's variable count, and so does each of its points. -/
theorem parse_with_round_dims (rp : WhirRoundProof F EF Com MP) (nv s t : ℕ) (h : List (Step F EF))
    {root : Com} {ood : EqStatement EF} {h' : List (Step F EF)}
    (hp : parse_with_round E rp nv s t h = .ok (root, ood, h')) :
    ood.num_variables = nv ∧ ∀ p ∈ ood.points, p.length = nv := by
  unfold parse_with_round at hp
  rcases hc : rp.commitment with _ | r
  · simp [hc, throw, throwThe, MonadExceptOf.throw] at hp
  · simp only [hc] at hp
    split_ifs at hp with hl
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl, -⟩ := hp
    exact ⟨rfl, expand_points E.S nv rp.ood_answers _ s⟩

variable (c : WhirConfig)

/-- The shape of the verifier's loop state after t rounds: the last challenges have the fold width, and every constraint fits the end of the challenges to come. -/
def SInv (t : ℕ) (st : LoopState F EF Com) : Prop :=
  (∃ r, st.randomness.getLast? = some r ∧ r.length = kAt c t) ∧
    ∀ con ∈ st.constraints, con.num_variables ≤ st.randomness.flatten.length + nvAt c t ∧
      ∀ s ∈ con.statements, s.Dim con.num_variables

theorem sumcheck_length {data : SumcheckData F EF} {h : List (Step F EF)} {cl : EF} {N pow : ℕ}
    {rs : List EF} {cl' : EF} {h' : List (Step F EF)}
    (hok : sumcheck E data h cl N pow = .ok (rs, cl', h')) : rs.length = N := by
  unfold sumcheck at hok
  rcases hv : verify_rounds E.S.toSponge data.1 data.2 h cl N pow .Evaluation with e | ⟨rs', cl'', h''⟩
  · simp [hv, Except.mapError] at hok
  · simp only [hv, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact verify_rounds_length _ _ _ _ _ _ _ _ hv

/-- One verifier round never panics, on any proof, and keeps the shape. -/
theorem roundStep_some {n : ℕ} (hv : Valid c n E.adicity) (hw : Widths E.mmcs) (proof : WhirProof F EF Com MP)
    (hn : proof.rounds.length = c.n_rounds) {t : ℕ} (ht : t < c.n_rounds) (st : LoopState F EF Com)
    (hs : SInv c t st) :
    ∃ res, roundStep E c proof st t = some res ∧ ∀ st', res = .ok st' → SInv c (t + 1) st' := by
  obtain ⟨⟨r, hr, hrl⟩, hcons⟩ := hs
  obtain ⟨rp, hrp⟩ : ∃ rp, proof.rounds[t]? = some rp := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hk1 : c.round_folding_factor (t + 1) = some (c.folding_schedule.getD (t + 1) 0) := by
    simp only [WhirConfig.round_folding_factor, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by have := hv.schedule; omega), Option.getD_some]
  simp only [roundStep, queried_lt c ht, hrp, Option.bind_eq_bind, Option.bind_some]
  split
  · exact ⟨_, rfl, fun _ h => by cases h⟩
  · next root ood h1 hparse =>
    obtain ⟨hon, hop⟩ := parse_with_round_dims E rp _ _ t _ hparse
    simp only [hr, Option.bind_some]
    obtain ⟨res, hres, hstir⟩ := stir_some E hw c rp.openings rp.pow_witness (queried c t) st.prev r t h1
      (hv.sites t ht.le) (by rw [hrl, kAt, hv.folding t ht.le]) (by rw [hrl, kAt]; exact hv.small t ht.le)
      (hv.adicity t ht.le)
    rw [hres]
    simp only [Option.bind_some]
    split
    · exact ⟨_, rfl, fun _ h => by cases h⟩
    · next stir h2 =>
      have hsn := hstir stir h2 rfl
      rw [new_with_existing_claim_eq _ _ _ (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro _ (rfl | rfl)
        · rfl
        · show stir.num_variables = ood.num_variables; rw [hsn, hon])]
      simp only [Option.bind_some, hk1]
      split
      · exact ⟨_, rfl, fun _ h => by cases h⟩
      · next rs cl h3 hsc =>
        refine ⟨_, rfl, fun st' h => ?_⟩
        cases h
        have hrs := sumcheck_length E hsc
        have hvars : nvAt c t = nvAt c (t + 1) + c.folding_schedule.getD (t + 1) 0 := hv.vars t ht
        refine ⟨⟨rs, by simp, hrs⟩, fun con hc => ?_⟩
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨h1, h2⟩ := hcons con hc
          refine ⟨?_, h2⟩
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
          omega
        · simp only [List.mem_singleton] at hc
          subst hc
          refine ⟨?_, ?_⟩
          · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
              List.length_append]
            show ood.num_variables ≤ _
            rw [hon]
            have : (queried c t).num_variables = nvAt c t := rfl
            omega
          · simp only [List.mem_cons, List.mem_nil_iff, or_false]
            rintro _ (rfl | rfl)
            · exact fun p hp => by rw [hop p hp, hon]
            · trivial

theorem loop_some {n : ℕ} (hv : Valid c n E.adicity) (hw : Widths E.mmcs) (proof : WhirProof F EF Com MP)
    (hn : proof.rounds.length = c.n_rounds) (st0 : LoopState F EF Com) (h0 : SInv c 0 st0) :
    ∀ t ≤ c.n_rounds, ∃ res, (List.range t).foldlM (loopStep E c proof) (.ok st0) = some res ∧
      ∀ st, res = .ok st → SInv c t st
  | 0, _ => ⟨_, rfl, fun st h => by cases h; exact h0⟩
  | t + 1, ht => by
    obtain ⟨res, hres, hinv⟩ := loop_some hv hw proof hn st0 h0 t (by omega)
    rw [List.range_succ, List.foldlM_append, hres]
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.bind_some]
    rcases res with e | st
    · exact ⟨_, rfl, fun _ h => by cases h⟩
    · obtain ⟨res', hres', hinv'⟩ := roundStep_some E c hv hw proof hn (show t < c.n_rounds by omega) st (hinv st rfl)
      simp only [loopStep, hres', Option.bind_some]
      exact ⟨res', rfl, hinv'⟩

/-- The verifier never panics: on a consistent configuration, a layout of the polynomial's variable count and a Merkle scheme that checks row widths, every proof is accepted or rejected with an error. -/
theorem verify_some {n : ℕ} (hv : Valid c n E.adicity) (hw : Widths E.mmcs)
    (hlay : ∀ α, (E.initial α).num_variables = n ∧ ∀ s ∈ (E.initial α).statements, s.Dim n)
    (seed : Step F EF) (proof : WhirProof F EF Com MP) (commitment : Com) (h : List (Step F EF)) :
    (verify E c seed proof commitment h).isSome := by
  unfold verify
  by_cases hn' : proof.rounds.length = c.n_rounds
  swap
  · simp [hn']
  simp only [hn', ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · rfl
  by_cases hp : c.final_round_config.pow_bits = 0 ∧ proof.final_pow_witness ≠ 0
  · simp [hp]
  by_cases hs : c.final_sumcheck_rounds = 0 ∧ proof.final_sumcheck.isSome
  · simp [hp, hs]
  simp only [hp, hs, ↓reduceIte]
  have hk0 : c.round_folding_factor 0 = some (c.folding_schedule.getD 0 0) := by
    simp only [WhirConfig.round_folding_factor, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by have := hv.schedule; omega), Option.getD_some]
  simp only [p3_whir.mirror.replay, hk0, Option.bind_eq_bind, Option.bind_some]
  split
  · rfl
  · next rs0 cl h1 hsc =>
    have h0 : SInv c 0 ⟨[E.initial (E.S.sample (h ++ [seed] ++ [E.layoutSeed]))], [rs0], commitment, cl, h1⟩ := by
      obtain ⟨hnv, hd⟩ := hlay (E.S.sample (h ++ [seed] ++ [E.layoutSeed]))
      refine ⟨⟨rs0, rfl, sumcheck_length E hsc⟩, fun con hc => ?_⟩
      simp only [List.mem_singleton] at hc
      subst hc
      refine ⟨?_, fun s hs => hnv ▸ hd s hs⟩
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, sumcheck_length E hsc, hnv]
      have := hv.vars0
      unfold nvAt
      omega
    obtain ⟨res, hres, hinv⟩ := loop_some E c hv hw proof hn' _ h0 c.n_rounds le_rfl
    rcases res with e | st
    · rw [hres]; rfl
    · rw [hres]
      simp only [Option.bind_some]
      obtain ⟨⟨r, hr, hrl⟩, hcons⟩ := hinv st rfl
      split
      · rfl
      · next fin hfin =>
        by_cases hlen : fin.length = 2 ^ c.final_round_config.num_variables
        swap
        · simp [hlen]
        simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, hr, Option.bind_some]
        have hqN : queried c c.n_rounds = c.final_round_config := by simp [queried]
        obtain ⟨res2, hres2, -⟩ := stir_some E hw c proof.final_openings proof.final_pow_witness (queried c c.n_rounds)
          st.prev r c.n_rounds (st.h ++ [.message fin]) (hv.sites _ le_rfl) (by rw [hrl, kAt, hv.folding _ le_rfl])
          (by rw [hrl, kAt]; exact hv.small _ le_rfl) (hv.adicity _ le_rfl)
        rw [hqN] at hres2
        rw [hres2]
        simp only [Option.bind_some]
        split
        · rfl
        · next stir h2 =>
          split
          · rfl
          · generalize hx : (if 0 < c.final_sumcheck_rounds then
                (verify_final_sumcheck_rounds E.S.toSponge proof.final_sumcheck h2 st.claimed
                  c.final_sumcheck_rounds c.final_folding_pow_bits .Evaluation).mapError VerifierError.Sumcheck
              else pure ([], st.claimed, h2)) = x
            have hrf : ∀ rf cl' h', x = .ok (rf, cl', h') → rf.length = c.final_sumcheck_rounds := by
              intro rf cl' h' hxe
              subst hxe
              by_cases hR : 0 < c.final_sumcheck_rounds
              · simp only [hR, ↓reduceIte] at hx
                unfold verify_final_sumcheck_rounds at hx
                simp only [show ¬ c.final_sumcheck_rounds = 0 from by omega, ↓reduceIte] at hx
                rcases hd : proof.final_sumcheck with _ | ⟨ev, ws⟩
                · simp [hd, throw, throwThe, MonadExceptOf.throw, Except.mapError] at hx
                · simp only [hd] at hx
                  rcases hv' : verify_rounds E.S.toSponge ev ws h2 st.claimed c.final_sumcheck_rounds
                    c.final_folding_pow_bits .Evaluation with e | ⟨rs', cl'', h''⟩
                  · simp [hv', Except.mapError] at hx
                  · simp only [hv', Except.mapError, Except.ok.injEq, Prod.mk.injEq] at hx
                    rw [← hx.1]
                    exact verify_rounds_length _ _ _ _ _ _ _ _ hv'
              · simp only [hR, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hx
                rw [← hx.1]
                simp; omega
            rcases x with e | ⟨rf, cl', h'⟩
            · rfl
            · have hrl' := hrf rf cl' h' rfl
              have hfinal := hv.final
              have hnvN : nvAt c c.n_rounds = c.final_sumcheck_rounds := by
                rw [nvAt, hqN, hfinal.1]
              obtain ⟨wv, hwv⟩ := eval_constraints_poly_some (st.randomness ++ [rf]).flatten st.constraints
                fun con hc => by
                  obtain ⟨h1, h2⟩ := hcons con hc
                  refine ⟨?_, h2⟩
                  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
                    List.length_append]
                  omega
              have hpe : p3_multilinear_util.split_eq.mirror.Poly.eval_ext E.thr E.w E.T fin rf = some (mle fin rf) :=
                poly_eval_ext_eq _ _ _ _ _ (by omega) (by rw [hlen, hrl', hfinal.1])
              simp only [hwv, hpe, Option.bind_some]
              split <;> rfl

end Plonky3Lean.Proofs.Whir
