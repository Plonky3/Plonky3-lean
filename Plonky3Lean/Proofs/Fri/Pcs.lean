module

public import Plonky3Lean.Proofs.Fri.Robust
public import P3Fri.PcsVerify

@[expose] public section

/-!
# The PCS verifier: where it panics

The only panics left are the challenger's assertions on a grinding difficulty.

A difficulty b > 0 panics unless b < 64 and 2^b < p, for the field order p.

The claims replay never rejects, since its description comes from the same claims.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.transcript.mirror p3_fri.mirror p3_fri.config.mirror p3_fri.verifier.mirror
open p3_commit.pcs.univariate.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

/-! ## The grinding check -/

section grind

variable {K Com S : Type _}

/-- A difficulty the challenger accepts: zero, or below 64 bits with 2^b < p. -/
def PowSafe (p b : ℕ) : Prop := b = 0 ∨ (b < 64 ∧ 2 ^ b < p)

instance (p b : ℕ) : Decidable (PowSafe p b) := by unfold PowSafe; infer_instance

theorem sample_bits_isSome (sp : Sponge K Com S) (s : S) (b : ℕ) :
    (sample_bits sp s b).isSome ↔ b < 64 ∧ 2 ^ b < sp.order := by
  unfold sample_bits; split_ifs with h <;> simp <;> omega

/-- The grinding check panics exactly at an unsafe difficulty. -/
theorem check_witness_isSome (sp : Sponge K Com S) (s : S) (b : ℕ) (w : K) :
    (check_witness sp s b w).isSome ↔ PowSafe sp.order b := by
  unfold check_witness PowSafe
  split_ifs with h
  · simp [h]
  · simp [Option.isSome_map, sample_bits_isSome, h]

/-! ## The FRI transcript -/

theorem commit_round_run_isSome (sp : Sponge K Com S) (shape : FriShape) (s : S) (cw : Com × K)
    (h : PowSafe sp.order shape.commit_pow_bits) : (commit_round sp shape s cw).run.isSome := by
  unfold commit_round
  split_ifs with hb
  · obtain ⟨⟨ok, s'⟩, he⟩ := Option.isSome_iff_exists.1
      ((check_witness_isSome sp (sp.observe_commitment s cw.1) _ cw.2).2 h)
    simp only [ExceptT.run, ExceptT.lift, he]
    cases ok <;> rfl
  · rfl

theorem foldlM_run_isSome {ε α β : Type _} {f : β → α → ExceptT ε Option β} (hf : ∀ b a, (f b a).run.isSome) :
    ∀ (l : List α) (b : β), (l.foldlM f b).run.isSome
  | [], _ => rfl
  | a :: l, b => by
    rw [List.foldlM_cons]
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hf b a)
    simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at hr ⊢
    rw [hr]
    rcases r with e | b'
    · rfl
    · exact foldlM_run_isSome hf l b'

theorem check_witness_eq_none (sp : Sponge K Com S) (s : S) (b : ℕ) (w : K) :
    check_witness sp s b w = none ↔ ¬ PowSafe sp.order b := by
  rw [← check_witness_isSome, Option.not_isSome_iff_eq_none]

theorem commit_round_run_eq_none (sp : Sponge K Com S) (shape : FriShape) (s : S) (cw : Com × K)
    (h : ¬ PowSafe sp.order shape.commit_pow_bits) : (commit_round sp shape s cw).run = none := by
  have hb : 0 < shape.commit_pow_bits := by unfold PowSafe at h; omega
  unfold commit_round
  simp only [hb, ↓reduceIte, ExceptT.run, ExceptT.lift, (check_witness_eq_none _ _ _ _).2 h]
  rfl

/-- The commit rounds panic exactly when the counts match, some round exists, and the commit difficulty is unsafe. -/
theorem commit_rounds_run_eq_none (sp : Sponge K Com S) (shape : FriShape) (s : S) (coms : List Com)
    (ws : List K) :
    (commit_rounds sp shape s coms ws).run = none ↔
      coms.length = shape.log_arities.length ∧ ws.length = shape.log_arities.length ∧
        shape.log_arities ≠ [] ∧ ¬ PowSafe sp.order shape.commit_pow_bits := by
  unfold commit_rounds
  by_cases hc : coms.length ≠ shape.log_arities.length
  · simp only [hc, ne_eq, false_and, iff_false]; exact Option.some_ne_none _
  by_cases hw : ws.length ≠ shape.log_arities.length
  · simp only [hc, hw, ↓reduceIte, ne_eq, false_and, and_false, iff_false]; exact Option.some_ne_none _
  push Not at hc hw
  simp only [hc, hw, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
  by_cases hs : PowSafe sp.order shape.commit_pow_bits
  · simp only [hs, not_true_eq_false, and_false, iff_false]
    rw [← Option.not_isSome_iff_eq_none, not_not]
    exact foldlM_run_isSome (fun b a => by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (commit_round_run_isSome sp shape b.2 a hs)
      simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at hr ⊢
      rw [hr]; rcases r <;> rfl) _ _
  simp only [hs, not_false_eq_true, and_true]
  rcases hl : shape.log_arities with _ | ⟨a, L⟩
  · rw [hl] at hc hw
    rw [List.length_eq_zero_iff.1 hc]
    simp
  · rw [hl] at hc hw
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one hc
    obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_length_eq_add_one hw
    simp only [List.zip_cons_cons, List.foldlM_cons, reduceCtorEq, not_false_eq_true, iff_true]
    simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    have := commit_round_run_eq_none sp shape s (c, w) hs
    simp only [ExceptT.run] at this
    rw [this]; rfl

theorem bind_run_isSome {ε α β : Type _} {m : ExceptT ε Option α} {k : α → ExceptT ε Option β}
    (hm : m.run.isSome) (hk : ∀ a, (k a).run.isSome) : (m >>= k).run.isSome := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hm
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at hr ⊢
  rw [hr]; rcases r with e | a
  · rfl
  · exact hk a

theorem lift_sample_isSome {ε : Type _} (sp : Sponge K Com S) (b : ℕ) (hb : b < 64 ∧ 2 ^ b < sp.order) (t : S) :
    (ExceptT.lift (sample_bits sp t b) : ExceptT ε Option (ℕ × S)).run.isSome := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((sample_bits_isSome sp t b).2 hb)
  simp [ExceptT.run, ExceptT.lift, ExceptT.mk, hr]

/-- The query phase panics exactly when the final polynomial has its length, a witness is given,
and the query difficulty is unsafe.

This needs the index width to be safe, as every reachable shape has it. -/
theorem query_phase_run_eq_none (sp : Sponge K Com S) (shape : FriShape) (s : S) (fp : List K) (w : Option K)
    (hi : shape.index_bits < 64 ∧ 2 ^ shape.index_bits < sp.order) :
    (query_phase sp shape s fp w).run = none ↔
      shape.final_poly_len = fp.length ∧ w.isSome ∧ ¬ PowSafe sp.order shape.query_pow_bits := by
  unfold query_phase
  by_cases hl : shape.final_poly_len ≠ fp.length
  · simp only [hl, ne_eq, false_and, iff_false]; exact Option.some_ne_none _
  push Not at hl
  simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
  by_cases hs : PowSafe sp.order shape.query_pow_bits
  · simp only [hs, not_true_eq_false, and_false, iff_false]
    rw [← Option.not_isSome_iff_eq_none, not_not]
    have hidx : ∀ s2 : S, ((List.range shape.num_queries).foldlM (fun (acc : List ℕ × S) (_ : ℕ) => do
        let r ← (ExceptT.lift (sample_bits sp acc.2 shape.index_bits) : ExceptT TranscriptFailure Option (ℕ × S))
        pure (acc.1 ++ [r.1], r.2)) ([], s2)).run.isSome := fun s2 =>
      foldlM_run_isSome (fun acc _ => bind_run_isSome (lift_sample_isSome sp _ hi _) fun _ => rfl) _ _
    split_ifs with hb
    · rcases w with _ | w
      · rfl
      · obtain ⟨⟨ok, s'⟩, he⟩ := Option.isSome_iff_exists.1
          ((check_witness_isSome sp (sp.observe_values s fp) _ w).2 hs)
        refine bind_run_isSome (by simp [ExceptT.run, ExceptT.lift, ExceptT.mk, he]) fun _ => ?_
        split_ifs
        · exact hidx _
        · rfl
    · exact hidx _
  have hb : 0 < shape.query_pow_bits := by unfold PowSafe at hs; omega
  simp only [hs, not_false_eq_true, and_true, hb, ↓reduceIte]
  rcases w with _ | w
  · simp only [Option.isSome_none, Bool.false_eq_true, iff_false]; exact Option.some_ne_none _
  · simp only [Option.isSome_some, iff_true]
    simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift,
      (check_witness_eq_none _ _ _ _).2 hs]
    rfl

/-- The batching phase panics exactly when a witness is given and the batching difficulty is unsafe. -/
theorem batch_phase_run_eq_none (sp : Sponge K Com S) (shape : PcsShape) (s : S) (w : Option K) :
    (batch_phase sp shape s w).run = none ↔ w.isSome ∧ ¬ PowSafe sp.order shape.batch_pow_bits := by
  unfold batch_phase
  by_cases hs : PowSafe sp.order shape.batch_pow_bits
  · simp only [hs, not_true_eq_false, and_false, iff_false]
    rw [← Option.not_isSome_iff_eq_none, not_not]
    split_ifs with hb
    · rcases w with _ | w
      · rfl
      · obtain ⟨⟨ok, s'⟩, he⟩ := Option.isSome_iff_exists.1 ((check_witness_isSome sp s _ w).2 hs)
        refine bind_run_isSome (by simp [ExceptT.run, ExceptT.lift, ExceptT.mk, he]) fun _ => ?_
        split_ifs <;> rfl
    · rfl
  have hb : 0 < shape.batch_pow_bits := by unfold PowSafe at hs; omega
  simp only [hs, not_false_eq_true, and_true, hb, ↓reduceIte]
  rcases w with _ | w
  · simp only [Option.isSome_none, Bool.false_eq_true, iff_false]; exact Option.some_ne_none _
  · simp only [Option.isSome_some, iff_true]
    simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift,
      (check_witness_eq_none _ _ _ _).2 hs]
    rfl

theorem foldlM_claimed (sp : Sponge K Com S) (D : List ℕ) :
    ∀ (l : List (PointOpening K)) (k : ℕ) (s : S),
      (∀ i (h : i < l.length), D[k + i]? = some (l[i].values.length)) →
      (l.zipIdx k).foldlM (fun st e => do
        match D[e.2]? with
        | none => (ExceptT.lift none : ExceptT PcsTranscriptFailure Option S)
        | some n =>
          if n ≠ e.1.values.length then
            throw (PcsTranscriptFailure.ClaimedEvaluationCount e.2 n e.1.values.length)
          pure (sp.observe_values st e.1.values)) s =
        pure (l.foldl (fun st p => sp.observe_values st p.values) s)
  | [], _, _, _ => rfl
  | p :: l, k, s, hD => by
    have h0 := hD 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [List.zipIdx_cons, List.foldlM_cons, h0]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.foldl_cons]
    exact foldlM_claimed sp D l (k + 1) _ fun i h => by
      have := hD (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, show k + (i + 1) = k + 1 + i by omega] at this

/-- The claims replay never rejects and never panics.

Its description is built from the same claims, so every point has its described count. -/
theorem claimed_openings_from_claims {C D : Type _} (sp : Sponge K Com S) (params : FriParameters) (s : S)
    (claims : List (CommitmentOpening K C D)) :
    claimed_openings sp (PcsShape.from_claims params claims) s claims =
      pure ((claims.flatMap fun c => c.matrices.flatMap fun m => m.points).foldl
        (fun st p => sp.observe_values st p.values) s) := by
  unfold claimed_openings
  have hD : (PcsShape.from_claims params claims).claimed_evaluation_counts.flatten.flatten =
      (claims.flatMap fun c => c.matrices.flatMap fun m => m.points).map (·.values.length) := by
    induction claims with
    | nil => rfl
    | cons c cs ih =>
      simp only [PcsShape.from_claims, List.map_cons, List.flatten_cons, List.flatMap_cons, List.map_append,
        List.flatten_append] at ih ⊢
      rw [ih]; congr 1
      induction c.matrices <;> simp_all
  rw [hD]
  exact foldlM_claimed sp _ _ 0 s fun i h => by simp [List.getElem?_eq_getElem h]

end grind

/-! ## The FRI verifier -/

section fri

variable {K : Type} [Field K] [DecidableEq K]

/-- The checks before the FRI transcript all pass, with schedule L:

- the instance is not vacuous
- the tallest height lies within the adicity
- the schedule exists and is L
- the proof's lengths match the schedule and the parameters
- the witnesses of zero difficulty are zero. -/
structure FriPre {C Com MP IMP : Type} (G : Gen K) (params : FriParameters) (claims : List (Claim G C))
    (proof : FriProof K Com MP IMP) (L : List ℕ) : Prop where
  queries : params.num_queries ≠ 0
  blowup : params.log_blowup ≠ 0
  arity : params.max_log_arity ≠ 0
  matrices : claims.all (·.matrices = []) = false
  height : (inputLogHeights params.log_blowup claims).headD 0 ≤ G.adicity
  schedule : fold_schedule (inputLogHeights params.log_blowup claims)
    (params.log_blowup + params.log_final_poly_len) params.max_log_arity = some L
  openings : proof.commit_phase_openings.length = L.length
  siblings : (proof.commit_phase_openings.zip L).find? (fun e =>
      e.1.sibling_values.length ≠ params.num_queries ∨ e.1.sibling_values.any (·.length ≠ 2 ^ e.2 - 1)) = none
  canonical : check_canonical_pow_witnesses params proof = true
  final : proof.final_poly.length = params.final_poly_len

/-- The FRI transcript at schedule L. -/
abbrev txAt {C Com S : Type} (G : Gen K) (mkTx : FriShape → VerifierTx K Com S) (params : FriParameters)
    (claims : List (Claim G C)) (L : List ℕ) : VerifierTx K Com S :=
  mkTx (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))

/-- The FRI verifier panics exactly when its checks pass up to the transcript, and then:

- the commit rounds panic, or
- they return, and the query phase panics. -/
theorem verify_fri_panics_iff (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (g : K) {C S : Type}
    (fmmcs immcs : MmcsOps K) (mkTx : FriShape → VerifierTx K fmmcs.Commitment S) (params : FriParameters)
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) :
    ¬ Total (verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha) ↔
      ∃ L, FriPre G params claims proof L ∧
        (((txAt G mkTx params claims L).commit_rounds s proof.commit_phase_commits
            proof.commit_pow_witnesses).run = none ∨
        ∃ r, ((txAt G mkTx params claims L).commit_rounds s proof.commit_phase_commits
            proof.commit_pow_witnesses).run = some (.ok r) ∧
          ((txAt G mkTx params claims L).query_phase r.2 proof.final_poly
            (some proof.query_pow_witness)).run = none) := by
  unfold verify_fri
  constructor
  · intro hnt
    by_contra hno
    apply hnt
    by_cases h1 : params.num_queries = 0
    · simp only [h1, ↓reduceIte, throw_bind']; exact total_throw _
    by_cases h2' : params.log_blowup = 0
    · simp only [h1, h2', ↓reduceIte, throw_bind']; exact total_throw _
    by_cases h3 : params.max_log_arity = 0
    · simp only [h1, h2', h3, ↓reduceIte, throw_bind']; exact total_throw _
    by_cases h4 : claims.all (·.matrices = []) = true
    · simp only [h1, h2', h3, h4, ↓reduceIte, throw_bind']; exact total_throw _
    by_cases hbig : G.adicity < (inputLogHeights params.log_blowup claims).headD 0
    · simp only [h1, h2', h3, h4, hbig, ↓reduceIte, throw_bind', Bool.false_eq_true]; exact total_throw _
    have hok := (le_headD_inputLogHeights params.log_blowup claims).resolve_right hbig
    push Not at hbig
    obtain ⟨L, hL⟩ : ∃ L, fold_schedule (inputLogHeights params.log_blowup claims)
        (params.log_blowup + params.log_final_poly_len) params.max_log_arity = some L := by
      rcases hfs : fold_schedule (inputLogHeights params.log_blowup claims)
        (params.log_blowup + params.log_final_poly_len) params.max_log_arity with _ | L
      · rw [fold_schedule_eq_none] at hfs
        rcases hfs with hfs | hfs
        · exact absurd (inputLogHeights_isChain _ claims) hfs
        · exact absurd hfs.1 h3
      · exact ⟨L, rfl⟩
    simp only [h1, h2', h3, h4, ↓reduceIte, Bool.false_eq_true, not_lt.2 hbig, lift, hL, lift_some_bind,
      pure_bind]
    refine total_ite (fun _ => total_throw _) fun h5 => ?_
    split
    · exact total_ite (fun _ => total_throw _) fun _ => total_throw _
    rename_i hfind
    refine total_ite (fun _ => total_throw _) fun h6 => ?_
    refine total_ite (fun _ => total_throw _) fun h7 => ?_
    have hpre : FriPre G params claims proof L :=
      ⟨h1, h2', h3, by simpa using h4, hbig, hL, by simpa using h5, hfind, by simpa using h6, by simpa using h7⟩
    have hc : ((txAt G mkTx params claims L).commit_rounds s proof.commit_phase_commits
        proof.commit_pow_witnesses).run ≠ none := fun h => hno ⟨L, hpre, Or.inl h⟩
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hc
    dsimp only [txAt, ExceptT.run] at hr
    simp only [ExceptT.run, hr, lift_some_bind]
    rcases r with f | r1
    · exact total_throw _
    have hq : ((txAt G mkTx params claims L).query_phase r1.2 proof.final_poly
        (some proof.query_pow_witness)).run ≠ none := fun h => hno ⟨L, hpre, Or.inr ⟨r1, hr, h⟩⟩
    obtain ⟨q, hq'⟩ := Option.ne_none_iff_exists'.1 hq
    dsimp only [txAt, ExceptT.run] at hq'
    simp only [hq', lift_some_bind]
    rcases q with f | r2
    · exact total_throw _
    refine total_bind (open_inputs_total (ME := fmmcs.Error) G g immcs _ _ _ _ _ claims commit_of hok)
      fun ro _ => ?_
    refine total_bind (total_mapM (fun e => checkQuery_total G hV h2 _ _ _ _ _ hbig e) _) fun rec _ => ?_
    exact total_bind (total_foldlM (fun lc e => checkRound_total fmmcs rec lc e) _ _) fun _ _ => total_pure _
  · rintro ⟨L, hp, hpan⟩
    simp only [hp.queries, hp.blowup, hp.arity, hp.matrices, ↓reduceIte, Bool.false_eq_true,
      not_lt.2 hp.height, lift, hp.schedule, lift_some_bind, pure_bind, hp.openings, ne_eq,
      not_true_eq_false, hp.siblings, hp.canonical, hp.final]
    have hnone : ∀ {α β : Type} (k : α → Res fmmcs.Error immcs.Error β),
        ¬ Total (ExceptT.lift none >>= k) := fun k h => by
      rw [lift_none_bind] at h; simp [Total, ExceptT.lift, ExceptT.mk] at h
    rcases hpan with h | ⟨r, hr, hq⟩
    · dsimp only [txAt, ExceptT.run] at h
      simp only [ExceptT.run, h]
      exact hnone _
    · dsimp only [txAt, ExceptT.run] at hr hq
      simp only [ExceptT.run, hr, lift_some_bind, hq]
      exact hnone _

/-- The concrete FRI transcript never panics at a reachable shape, when:

- both of its difficulties are safe
- 2^h < p for the adicity h, with h < 64. -/
theorem verifierTx_total {Com S : Type} (sp : Sponge K Com S) (params : FriParameters) (G : Gen K)
    (hc : PowSafe sp.order params.commit_proof_of_work_bits) (hq : PowSafe sp.order params.query_proof_of_work_bits)
    (hG : G.adicity < 64 ∧ 2 ^ G.adicity < sp.order) (L : List ℕ) (H : ℕ) (hH : H ≤ G.adicity) :
    TxTotal (verifierTx sp (FriShape.with_schedule params L H)) := by
  refine ⟨fun s c w => ?_, fun s f w => ?_⟩
  · rw [← Option.ne_none_iff_isSome]
    intro h
    exact ((commit_rounds_run_eq_none sp _ s c w).1 h).2.2.2 hc
  · rw [← Option.ne_none_iff_isSome]
    intro h
    have hi : H < 64 ∧ 2 ^ H < sp.order :=
      ⟨by omega, lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hH) hG.2⟩
    exact ((query_phase_run_eq_none sp _ s f w hi).1 h).2.2 hq

end fri

/-! ## The PCS verifier -/

section pcs

variable {K : Type} [Field K] [DecidableEq K]

open p3_fri.two_adic_pcs.mirror

/-- The sponge after the claims replay. -/
def claimedState {C D Com S : Type} (sp : Sponge K Com S) (claims : List (CommitmentOpening K C D)) (s : S) : S :=
  (claims.flatMap fun c => c.matrices.flatMap fun m => m.points).foldl (fun st p => sp.observe_values st p.values) s

/-- The PCS verifier never panics when:

- the three difficulties are safe for the field order p
- 2^h < p for the adicity h, with h < 64. -/
theorem verify_total (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (g : K) {C S : Type}
    (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S) (params : FriParameters)
    (claims : List (Claim G C)) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment)
    (hb : PowSafe sp.order params.batch_proof_of_work_bits)
    (hc : PowSafe sp.order params.commit_proof_of_work_bits) (hq : PowSafe sp.order params.query_proof_of_work_bits)
    (hG : G.adicity < 64 ∧ 2 ^ G.adicity < sp.order) :
    Total (verify G g fmmcs immcs sp params claims proof s commit_of) := by
  unfold verify
  refine total_ite (fun _ => total_throw _) fun _ => ?_
  dsimp only
  rw [claimed_openings_from_claims]
  simp only [ExceptT.run_pure, Option.pure_def, lift, lift_some_bind, pure_bind]
  have hbt : (batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness)).run ≠ none := fun h =>
    ((batch_phase_run_eq_none _ _ _ _).1 h).2 hb
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hbt
  dsimp only [claimedState, ExceptT.run] at hr
  simp only [hr]
  rcases r with f | ⟨α, s2⟩
  · exact total_throw _
  exact verify_fri_total G hV h2 g fmmcs immcs _ params
    (fun L H hH => verifierTx_total sp params G hc hq hG L H hH) proof s2 claims commit_of α

/-- The PCS verifier panics exactly when the witnesses of zero difficulty are zero and one of these holds:

- the batching difficulty is unsafe, or
- the batching grind passes, the FRI checks before its transcript pass with schedule L, and either
  - some round exists, the round counts match, and the commit difficulty is unsafe, or
  - the commit rounds return and the query difficulty is unsafe.

This holds when 2^h < p for the adicity h, with h < 64. -/
theorem verify_panics_iff (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (g : K) {C S : Type}
    (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S) (params : FriParameters)
    (claims : List (Claim G C)) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) (hG : G.adicity < 64 ∧ 2 ^ G.adicity < sp.order) :
    ¬ Total (verify G g fmmcs immcs sp params claims proof s commit_of) ↔
      check_canonical_pow_witnesses params proof = true ∧
        (¬ PowSafe sp.order params.batch_proof_of_work_bits ∨
          ∃ α s2, (batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
              (some proof.batch_pow_witness)).run = some (.ok (α, s2)) ∧
            ∃ L, FriPre G params claims proof L ∧
              ((proof.commit_phase_commits.length = L.length ∧ proof.commit_pow_witnesses.length = L.length ∧
                  L ≠ [] ∧ ¬ PowSafe sp.order params.commit_proof_of_work_bits) ∨
                (∃ r, (commit_rounds sp (FriShape.with_schedule params L
                    ((inputLogHeights params.log_blowup claims).headD 0)) s2 proof.commit_phase_commits
                    proof.commit_pow_witnesses).run = some (.ok r) ∧
                  ¬ PowSafe sp.order params.query_proof_of_work_bits))) := by
  have hfri : ∀ α s2, ¬ Total (verify_fri G g fmmcs immcs (verifierTx sp) params proof s2 claims commit_of α) ↔
      ∃ L, FriPre G params claims proof L ∧
        ((proof.commit_phase_commits.length = L.length ∧ proof.commit_pow_witnesses.length = L.length ∧
            L ≠ [] ∧ ¬ PowSafe sp.order params.commit_proof_of_work_bits) ∨
          (∃ r, (commit_rounds sp (FriShape.with_schedule params L
              ((inputLogHeights params.log_blowup claims).headD 0)) s2 proof.commit_phase_commits
              proof.commit_pow_witnesses).run = some (.ok r) ∧
            ¬ PowSafe sp.order params.query_proof_of_work_bits)) := by
    intro α s2
    rw [verify_fri_panics_iff G hV h2 g fmmcs immcs _ params proof s2 claims commit_of α]
    refine exists_congr fun L => and_congr_right fun hp => or_congr ?_ (exists_congr fun r => and_congr_right fun _ => ?_)
    · exact commit_rounds_run_eq_none sp _ s2 _ _
    · have hi : (inputLogHeights params.log_blowup claims).headD 0 < 64 ∧
          2 ^ (inputLogHeights params.log_blowup claims).headD 0 < sp.order :=
        ⟨by have := hp.height; omega,
          lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hp.height) hG.2⟩
      rw [txAt, verifierTx, query_phase_run_eq_none sp _ _ _ _ hi]
      simp [FriShape.with_schedule, hp.final]
  unfold verify
  by_cases hcan : check_canonical_pow_witnesses params proof = true
  swap
  · simp only [hcan, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, throw_bind', false_and, iff_false,
      not_not]
    exact total_throw _
  simp only [hcan, not_true_eq_false, ↓reduceIte, true_and]
  rw [claimed_openings_from_claims]
  simp only [ExceptT.run_pure, Option.pure_def, lift, lift_some_bind, pure_bind]
  rw [show (claims.flatMap fun c => c.matrices.flatMap fun m => m.points).foldl
    (fun st p => sp.observe_values st p.values) s = claimedState sp claims s from rfl]
  have hbn : (batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness)).run = none ↔ ¬ PowSafe sp.order params.batch_proof_of_work_bits := by
    rw [batch_phase_run_eq_none]; simp [PcsShape.from_claims]
  rcases hr : (batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness)).run with _ | (f | ⟨α, s2⟩)
  · simp only [ExceptT.run, lift_none_bind, hbn.1 hr, not_false_eq_true, true_or, iff_true]
    simp [Total, ExceptT.lift, ExceptT.mk]
  · have hs : PowSafe sp.order params.batch_proof_of_work_bits := by
      by_contra hn; rw [hbn.2 hn] at hr; cases hr
    simp only [ExceptT.run, lift_some_bind, hs, not_true_eq_false, false_or, throw_bind', Option.some.injEq,
      reduceCtorEq, false_and, exists_false, iff_false, not_not]
    exact total_throw _
  · have hs : PowSafe sp.order params.batch_proof_of_work_bits := by
      by_contra hn; rw [hbn.2 hn] at hr; cases hr
    simp only [ExceptT.run, lift_some_bind, hs, not_true_eq_false, false_or, Option.some.injEq,
      Except.ok.injEq, Prod.mk.injEq]
    rw [hfri]
    constructor
    · exact fun h => ⟨α, s2, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h

end pcs

end Plonky3Lean.Proofs.Fri
