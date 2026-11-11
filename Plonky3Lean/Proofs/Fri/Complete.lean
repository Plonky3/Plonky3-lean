module

public import Plonky3Lean.Proofs.Fri.Chain
public import Plonky3Lean.Proofs.Fri.Pcs
public import Plonky3Lean.Proofs.Fri.Reduce

@[expose] public section

/-!
# Completeness of the verifier

An honest proof is accepted.

The honest rounds are a chain of codewords, each folded from the one before.

A shorter input joins the chain where the fold reaches its height.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror p3_fri.config.mirror p3_fri.transcript.mirror Plonky3Lean.Proofs.Dft
open p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

theorem mapM_eq_pure_map' {ε α β : Type _} {f : α → ExceptT ε Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = pure (g x)) → l.mapM f = pure (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, pure_bind,
      mapM_eq_pure_map' l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- A fold whose step at index i subtracts w of its item returns the start less the sum of w. -/
theorem foldlM_sub {ε α : Type _} (f : ℕ → α × ℕ → ExceptT ε Option ℕ) (w : α → ℕ) :
    ∀ (l : List α) (k0 h : ℕ), (∀ a i, (a, i) ∈ l.zipIdx k0 →
        f (h - ((l.take (i - k0)).map w).sum) (a, i) = pure (h - ((l.take (i - k0)).map w).sum - w a)) →
      (l.zipIdx k0).foldlM f h = pure (h - (l.map w).sum)
  | [], _, h, _ => by simp
  | a :: l, k0, h, hf => by
    have h0 := hf a k0 (by simp)
    simp only [Nat.sub_self, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] at h0
    rw [List.zipIdx_cons, List.foldlM_cons, h0, pure_bind,
      foldlM_sub f w l (k0 + 1) (h - w a) fun b i hi => by
        have hi' := (List.mem_zipIdx hi).1
        have := hf b i (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hi)
        rw [show i - k0 = (i - (k0 + 1)) + 1 by omega, List.take_succ_cons, List.map_cons,
          List.sum_cons, Nat.sub_add_eq, Nat.sub_add_eq] at this
        simpa [Nat.sub_add_eq] using this]
    simp [Nat.sub_add_eq]

/-- The recorded group index and row of round k, at the query's index. -/
theorem recordedOf_getD : ∀ (rs : List (Rd K)) (idx k : ℕ) (hk : k < rs.length),
    (recordedOf rs idx).getD k (0, []) =
      (idx / 2 ^ ((rs.take (k + 1)).map Rd.a).sum,
        rowList rs[k].w rs[k].a (idx / 2 ^ ((rs.take (k + 1)).map Rd.a).sum))
  | [], _, _, hk => absurd hk (by simp)
  | r :: rs, idx, 0, _ => by simp [recordedOf]
  | r :: rs, idx, k + 1, hk => by
    simp only [recordedOf, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ]
    rw [recordedOf_getD rs _ k (by simpa using hk), Nat.div_div_eq_div_mul, ← pow_add]

/-- The group indices of round k: every query index shifted down by the arities through round k. -/
def roundGroups (rs : List (Rd K)) (indices : List ℕ) (k : ℕ) : List ℕ :=
  indices.map (· / 2 ^ ((rs.take (k + 1)).map Rd.a).sum)

/-- Completeness of the FRI verifier.

Take a proof whose checks before the transcript pass with schedule L, and a transcript that accepts it.

Take global rounds whose challenges, arities and siblings are the proof's.

Take input checks that return, for every query, the first word's value and the rolled-in inputs.

Take, for every query, an honest chain of codewords through these rounds.

Take a final polynomial that agrees with the final word.

Take a commit-phase scheme that accepts the honest rows.

Then the verifier accepts. -/
theorem verify_fri_complete (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    {C S : Type} (fmmcs immcs : MmcsOps K) (mkTx : FriShape → VerifierTx K fmmcs.Commitment S)
    (params : FriParameters) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) (hG : G.adicity < 64)
    {L : List ℕ} (hpre : FriPre G params claims proof L) {H : ℕ}
    (hH : (inputLogHeights params.log_blowup claims).headD 0 = H)
    (rs : List (Rd K)) (wF : List K) (P : K[X]) (hL : rs.map Rd.a = L)
    {s1 s2 : S} {indices : List ℕ}
    (hc : (txAt G mkTx params claims L).commit_rounds s proof.commit_phase_commits proof.commit_pow_witnesses =
      pure (rs.map Rd.β, s1))
    (hq : (txAt G mkTx params claims L).query_phase s1 proof.final_poly (some proof.query_pow_witness) =
      pure (indices, s2))
    (hsv : proof.commit_phase_openings.map (·.sibling_values) = rs.map Rd.sv)
    (hHf : H - totalA rs = params.log_blowup + params.log_final_poly_len)
    (hopen : open_inputs' G g fmmcs immcs params.log_blowup H indices proof.input_openings alpha claims commit_of =
      pure (indices.map fun i => (H, (nextWord rs wF).getD i 0) :: rolls rs H i))
    (hchain : ∀ q i, indices[q]? = some i → HonestChain G q H i rs wF P)
    (hfinal : ∀ j < 2 ^ (H - totalA rs), horner proof.final_poly (G.gen H ^ bitRev H j) = wF.getD j 0)
    (hmmcs : ∀ k (hk : k < rs.length) (c : fmmcs.Commitment) (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      proof.commit_phase_commits[k]? = some c → proof.commit_phase_openings[k]? = some o →
      fmmcs.verify_multi_batch c [(2 ^ rs[k].a, 2 ^ (H - ((rs.take (k + 1)).map Rd.a).sum))]
        (roundGroups rs indices k) ((roundGroups rs indices k).map fun t => [rowList rs[k].w rs[k].a t])
        o.opening_proof = .ok ()) :
    verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha = pure () := by
  subst hH hL
  have hc' : ((txAt G mkTx params claims (rs.map Rd.a)).commit_rounds s proof.commit_phase_commits
      proof.commit_pow_witnesses).run = some (.ok (rs.map Rd.β, s1)) := by rw [hc]; rfl
  have hq' : ((txAt G mkTx params claims (rs.map Rd.a)).query_phase s1 proof.final_poly
      (some proof.query_pow_witness)).run = some (.ok (indices, s2)) := by rw [hq]; rfl
  dsimp only [txAt, ExceptT.run] at hc' hq'
  unfold verify_fri
  simp only [hpre.queries, hpre.blowup, hpre.arity, hpre.matrices, ↓reduceIte, Bool.false_eq_true,
    not_lt.2 hpre.height, lift, hpre.schedule, lift_some_bind, pure_bind, hpre.openings, ne_eq,
    not_true_eq_false, hpre.siblings, hpre.canonical, hpre.final]
  set H := (inputLogHeights params.log_blowup claims).headD 0 with hHdef
  have hrec : ((indices.zip (indices.map fun i => (H, (nextWord rs wF).getD i 0) :: rolls rs H i)).zipIdx).mapM
      (checkQuery (ME := fmmcs.Error) (IE := immcs.Error) G (rs.map Rd.β) (rs.map Rd.a)
        (proof.commit_phase_openings.map (·.sibling_values)) proof.final_poly H
        (params.log_blowup + params.log_final_poly_len)) =
      pure (((indices.zip (indices.map fun i => (H, (nextWord rs wF).getD i 0) :: rolls rs H i)).zipIdx).map
        fun e => recordedOf rs e.1.1) := by
    refine mapM_eq_pure_map' _ fun e he => ?_
    obtain ⟨⟨i, ro⟩, q⟩ := e
    obtain ⟨hqlt, he'⟩ := List.mem_zipIdx' he
    simp only [List.length_zip, List.length_map, min_self] at hqlt
    simp only [List.getElem_zip, List.getElem_map, Prod.mk.injEq] at he'
    obtain ⟨hi, hro⟩ := he'
    rw [← hi] at hro
    subst hro
    have hiq : indices[q]? = some i := by rw [List.getElem?_eq_getElem hqlt, hi]
    have hch := hchain q i hiq
    have hok := hch.chainOK G hV hN h2
    have hiH : i < 2 ^ H := by
      cases rs with
      | nil => exact hch.2.2
      | cons r rs => exact hch.2.2.2.2.1
    have hHa : H ≤ G.adicity := hpre.height
    unfold checkQuery
    rw [hsv, fold_query_complete G q i rs wF hok (fun r hr => by
      have := (hok.facts).1; have hr' := List.le_sum_of_mem (List.mem_map_of_mem (f := Rd.a) hr)
      simp only [totalA] at this; omega) hHf]
    have hj : i / 2 ^ totalA rs < 2 ^ (H - totalA rs) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hok.facts.1]; exact hiH
    simp only [pure_bind, lift, gen_get_of_le G hHa, lift_some_bind, hfinal _ hj, ne_eq,
      not_true_eq_false, ↓reduceIte]
  simp only [ExceptT.run, hc', lift_some_bind, hq']
  rw [hopen, pure_bind, hrec, pure_bind]
  set recorded := ((indices.zip (indices.map fun i => (H, (nextWord rs wF).getD i 0) :: rolls rs H i)).zipIdx).map
    fun e => recordedOf rs e.1.1
  set l := proof.commit_phase_commits.zip (proof.commit_phase_openings.zip (rs.map Rd.a)) with hl
  rw [foldlM_sub _ (fun e => e.2.2) l 0 H fun a i hai => ?_, pure_bind]
  obtain ⟨hi, ha⟩ := List.mem_zipIdx' hai
  simp only [Nat.sub_zero] at hi ha ⊢
  have hil : i < rs.length := by
    have : l.length ≤ rs.length := by simp [hl]
    omega
  have htake : (l.take i).map (fun e => e.2.2) = (rs.take i).map Rd.a := by
    refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_take, List.length_take]; omega)
      fun j h1 h2 => ?_
    simp [hl, List.getElem_take, List.getElem_zip]
  obtain ⟨c, o, la⟩ := a
  simp only [hl, List.getElem_zip, List.getElem_map, Prod.mk.injEq] at ha
  obtain ⟨hc, ho, hla⟩ := ha
  rw [htake]
  simp only [hla]
  unfold checkRound
  have hS : ((rs.take (i + 1)).map Rd.a).sum = ((rs.take i).map Rd.a).sum + rs[i].a := by
    rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hil]; simp
  have hrows : recorded.map (fun r => [(r.getD i (0, [])).2]) =
      (recorded.map fun r => (r.getD i (0, [])).1).map fun t => [rowList rs[i].w rs[i].a t] := by
    simp only [recorded, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp]
    rw [recordedOf_getD rs _ i hil]
  have hgroups : recorded.map (fun r => (r.getD i (0, [])).1) = roundGroups rs indices i := by
    simp only [recorded, List.map_map, roundGroups]
    rw [show ((fun r => (r.getD i (0, [])).1) ∘ fun e : (ℕ × List (ℕ × K)) × ℕ => recordedOf rs e.1.1) =
        (· / 2 ^ ((rs.take (i + 1)).map Rd.a).sum) ∘ (Prod.fst ∘ Prod.fst) by
      funext e; simp only [Function.comp_apply]; rw [recordedOf_getD rs _ i hil], ← List.map_map, ← List.map_map, List.zipIdx_map_fst,
      List.map_fst_zip (by simp)]
  dsimp only
  rw [hrows, hgroups, show H - ((rs.take i).map Rd.a).sum - rs[i].a = H - ((rs.take (i + 1)).map Rd.a).sum by
    rw [hS, Nat.sub_sub], hmmcs i hil c o
      (by rw [List.getElem?_eq_getElem (by simp [hl] at hi; omega)]; exact congrArg some hc.symm)
      (by rw [List.getElem?_eq_getElem (by simp [hl] at hi; omega)]; exact congrArg some ho.symm)]

/-- Completeness of the PCS verifier.

Take witnesses that are zero at zero difficulty, a batching grind that passes, and a FRI run that accepts.

Then the PCS verifier accepts. -/
theorem pcs_verify_complete (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
    (sp : Sponge K fmmcs.Commitment S) (params : FriParameters) (claims : List (Claim G C))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) (hcan : check_canonical_pow_witnesses params proof = true) {α : K} {s2 : S}
    (hb : batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness) = pure (α, s2))
    (hfri : verify_fri G g fmmcs immcs (verifierTx sp) params proof s2 claims commit_of α = pure ()) :
    verify G g fmmcs immcs sp params claims proof s commit_of = pure () := by
  have hb' : (batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness)).run = some (.ok (α, s2)) := by rw [hb]; rfl
  dsimp only [claimedState, ExceptT.run] at hb'
  unfold verify
  simp only [hcan, not_true_eq_false, ↓reduceIte]
  rw [claimed_openings_from_claims]
  simp only [ExceptT.run_pure, Option.pure_def, lift, lift_some_bind, pure_bind]
  simp only [ExceptT.run, hb', lift_some_bind]
  exact hfri

/-! ## The input checks on honest openings -/

theorem forM_eq_pure {ε α : Type _} {f : α → ExceptT ε Option PUnit} :
    ∀ (l : List α), (∀ x ∈ l, f x = pure ()) → l.forM f = pure ()
  | [], _ => rfl
  | x :: l, h => by
    show f x >>= (fun _ => l.forM f) = pure ()
    rw [h x List.mem_cons_self, pure_bind, forM_eq_pure l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The dimensions one batch check passes to the scheme.

Each matrix gets its claimed width and its height with the blowup. -/
def batchDims {G : Gen K} {C : Type} (b : ℕ) (c : Claim G C) : List (ℕ × ℕ) :=
  c.matrices.map fun m => ((m.points.headD ⟨0, []⟩).values.length, 2 ^ m.domain.log_size * 2 ^ b)

/-- The indices one batch check passes to the scheme.

Each query index is shifted down to the batch's tallest height. -/
def batchReduced {G : Gen K} {C : Type} (b H : ℕ) (indices : List ℕ) (c : Claim G C) : List ℕ :=
  match (c.matrices.map fun m => 2 ^ m.domain.log_size * 2 ^ b).max? with
  | some h => indices.map (· / 2 ^ (H - Nat.log 2 h))
  | none => indices.map fun _ => 0

/-- One batch's checks pass on an honest opening:

- one opened row set per query, each with one row per matrix
- every matrix opened at some point
- a scheme that accepts the rows at the dimensions and indices the check computes. -/
theorem checkBatch_honest {ME : Type} (G : Gen K) {C : Type} (mmcs : MmcsOps K) (b H : ℕ) (indices : List ℕ)
    (commit_of : C → mmcs.Commitment) (bo : BatchMultiOpening K mmcs.MultiProof) (c : Claim G C)
    (hq : bo.opened_values.length = indices.length)
    (hm : ∀ r ∈ bo.opened_values, r.length = c.matrices.length)
    (hp : ∀ m ∈ c.matrices, m.points ≠ [])
    (hmmcs : mmcs.verify_multi_batch (commit_of c.commitment) (batchDims b c) (batchReduced b H indices c)
      bo.opened_values bo.opening_proof = .ok ()) :
    checkBatch (ME := ME) G mmcs b H indices commit_of (bo, c) = pure () := by
  unfold checkBatch
  have h1 : (bo.opened_values.any fun x => decide (x.length ≠ c.matrices.length)) = false := by
    simp only [List.any_eq_false, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, not_not]
    exact hm
  have h2' : (c.matrices.any fun x => decide (x.points = [])) = false := by
    simpa using hp
  simp only [hq, ne_eq, not_true_eq_false, ↓reduceIte, h1, h2', Bool.false_eq_true]
  split
  · rename_i e he
    exact absurd (he.symm.trans hmmcs) (by simp)
  · rfl

/-- The denominator checks pass when no opening point is a query point. -/
theorem checkDenominators_honest {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (indices : List ℕ)
    (claims : List (Claim G C)) (hHa : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.domain.log_size + b ≤ G.adicity)
    (hz : ∀ index ∈ indices, ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      p.point ≠ xOfQuery G g H index (m.domain.log_size + b)) :
    checkDenominators (ME := ME) (IE := IE) G g b H indices claims = pure () := by
  unfold checkDenominators
  refine forM_eq_pure _ fun index hi => forM_eq_pure _ fun c hc => forM_eq_pure _ fun m hm => ?_
  have hx : queryPoint G g H (m.domain.log_size + b) index =
      some (xOfQuery G g H index (m.domain.log_size + b)) := by
    simp [xOfQuery, queryPoint, gen_get_of_le G (hHa c hc m hm)]
  simp only [lift, hx, lift_some_bind]
  refine forM_eq_pure _ fun p hp => ?_
  simp [sub_eq_zero, hz index hi c hc m hm p hp]

/-- The input checks pass on honest openings, and leave each query's reduction. -/
theorem open_inputs_honest {ME : Type} (G : Gen K) (g : K) {C : Type} (mmcs : MmcsOps K) (b H : ℕ)
    (indices : List ℕ) (input_openings : List (BatchMultiOpening K mmcs.MultiProof)) (α : K)
    (claims : List (Claim G C)) (commit_of : C → mmcs.Commitment)
    (hlen : input_openings.length = claims.length)
    (hbatch : ∀ bc ∈ input_openings.zip claims,
      checkBatch (ME := ME) G mmcs b H indices commit_of bc = pure ())
    (hden : checkDenominators (ME := ME) (IE := mmcs.Error) G g b H indices claims = pure ()) :
    open_inputs (ME := ME) G g mmcs b H indices input_openings α claims commit_of =
      indices.zipIdx.mapM fun e => reduceQuery G g b H α claims
        (input_openings.map fun bo => bo.opened_values.getD e.2 []) e.1 := by
  unfold open_inputs
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, forM_eq_pure _ hbatch, pure_bind, hden]

end Plonky3Lean.Proofs.Fri
