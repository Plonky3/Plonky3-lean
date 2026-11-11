module

public import Plonky3Lean.Proofs.Fri.Query
public import Plonky3Lean.Proofs.Fri.Res

@[expose] public section

/-!
# The verifier never panics

On every proof, transcript and commitment scheme, each verifier step returns a value or a rejection.

The field facts it needs: the generator table is primitive, and 2 is invertible.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror p3_fri.config.mirror Plonky3Lean.Proofs.Dft
open p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-- The fold chain never panics once its shape checks pass.

Every round folds a row of the right length below the adicity. -/
theorem foldlM_foldStep_isSome (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (q : ℕ) :
    ∀ (rounds : List (K × ℕ × List (List K))) (st : ChainState K),
      (∀ r ∈ rounds, 1 ≤ r.2.1 ∧ ∃ s, r.2.2[q]? = some s ∧ s.length = 2 ^ r.2.1 - 1) →
      (rounds.map fun r => r.2.1).sum ≤ st.2.2.1 → st.2.2.1 ≤ G.adicity →
      (rounds.foldlM (foldStep G q) st).isSome
  | [], _, _, _, _ => rfl
  | (β, a, sv) :: rounds, (idx, v, lh, ro, acc), hr, hsum, hla => by
    obtain ⟨ha1, s, hs, hsl⟩ := hr _ List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hsum
    dsimp only at hsum hla ha1 hs hsl
    have hrow : (rebuildRow (2 ^ a) (idx % 2 ^ a) v s).length = 2 ^ a := by simp [rebuildRow]
    obtain ⟨u, hu⟩ : ∃ u, fold_row G (idx / 2 ^ a) (lh - a) a β (rebuildRow (2 ^ a) (idx % 2 ^ a) v s) = some u := by
      rcases hf : fold_row G (idx / 2 ^ a) (lh - a) a β (rebuildRow (2 ^ a) (idx % 2 ^ a) v s) with _ | u
      · rw [fold_row_eq_none G hV h2 ha1] at hf
        rcases hf with hf | hf
        · omega
        · exact absurd hrow hf
      · exact ⟨u, rfl⟩
    rw [List.foldlM_cons]
    simp only [foldStep, hs, hu, Option.bind_eq_bind, Option.bind_some]
    have hrest := fun st' => foldlM_foldStep_isSome G hV h2 q rounds st'
      (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))
    rcases ro with _ | ⟨⟨h1, v1⟩, ro'⟩
    · exact hrest _ (by simp; omega) (by simp; omega)
    · by_cases hh : h1 = lh - a
      · simp only [hh, ↓reduceIte, Option.bind_some]; exact hrest _ (by simp; omega) (by simp; omega)
      · simp only [hh, ↓reduceIte, Option.bind_some]; exact hrest _ (by simp; omega) (by simp; omega)

theorem sum_zip3_le {α β : Type _} : ∀ (l1 : List α) (l2 : List ℕ) (l3 : List β),
    ((List.zip l1 (List.zip l2 l3)).map fun r => r.2.1).sum ≤ l2.sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp
  | _ :: l1, x :: l2, _ :: l3 => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have := sum_zip3_le l1 l2 l3; omega

theorem mem_zip_swap {α β : Type _} {x : α × β} {l1 : List α} {l2 : List β} (h : x ∈ List.zip l1 l2) :
    (x.2, x.1) ∈ List.zip l2 l1 := by
  rw [← List.zip_swap, List.mem_map]; exact ⟨x, h, rfl⟩

/-- The fold chain of a query never panics. -/
theorem fold_query_total {ME IE : Type} (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (q idx : ℕ)
    (betas : List K) (las : List ℕ) (svs : List (List (List K))) (ro : List (ℕ × K)) {H : ℕ} (Hf : ℕ)
    (hH : H ≤ G.adicity) :
    Total (fold_query (ME := ME) (IE := IE) G q idx betas las svs ro H Hf) := by
  unfold fold_query
  by_cases hany : (las.any fun la => decide (la = 0 ∨ 64 ≤ la)) = true
  · simp only [hany, ↓reduceIte, throw_bind']; exact total_throw _
  simp only [hany, Bool.false_eq_true, ↓reduceIte]
  cases hfind : List.find? (badRound q) (svs.zip las) with
  | some e =>
    rcases e with ⟨sv, _⟩
    by_cases hs : sv[q]?.isNone = true
    · simp only [hs, ↓reduceIte, throw_bind']; exact total_throw _
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, throw_bind']; exact total_throw _
  | none =>
  by_cases hsum : H - Hf < las.sum
  · simp only [hsum, ↓reduceIte, throw_bind']; exact total_throw _
  simp only [hsum, ↓reduceIte]
  rcases ro with _ | ⟨⟨lh, v0⟩, ro'⟩
  · simp only [throw_bind']; exact total_throw _
  simp only [pure_bind]
  by_cases hlh : lh ≠ H
  · simp only [hlh, ↓reduceIte, ne_eq, not_false_eq_true, throw_bind']; exact total_throw _
  simp only [hlh, ↓reduceIte]
  have hgood : ∀ r ∈ List.zip betas (List.zip las svs), 1 ≤ r.2.1 ∧ ∃ s, r.2.2[q]? = some s ∧ s.length = 2 ^ r.2.1 - 1 := by
    intro r hr
    have hm : r.2 ∈ List.zip las svs := (List.of_mem_zip hr).2
    have hla : r.2.1 ∈ las := (List.of_mem_zip hm).1
    have hall : ∀ x ∈ las, ¬x = 0 ∧ x < 64 := by simpa using hany
    refine ⟨by have := hall _ hla; omega, ?_⟩
    have hsw := mem_zip_swap hm
    have hb := List.find?_eq_none.1 hfind _ hsw
    simp only [badRound] at hb
    rcases hq : r.2.2[q]? with _ | s
    · simp [hq] at hb
    · simp only [hq] at hb; exact ⟨s, rfl, by simpa using hb⟩
  have hsome := foldlM_foldStep_isSome G hV h2 q (List.zip betas (List.zip las svs)) (idx, v0, H, ro', [])
    hgood (by have := sum_zip3_le betas las svs; dsimp only; omega) hH
  push Not at hlh
  subst hlh
  rcases hfl : List.foldlM (foldStep G q) (idx, v0, lh, ro', []) (betas.zip (las.zip svs)) with _ | res
  · rw [hfl] at hsome; simp at hsome
  obtain ⟨index, folded, log_h, roF, recs⟩ := res
  simp only [lift, lift_some_bind]
  refine total_ite (fun _ => ?_) (fun _ => total_ite (fun _ => ?_) (fun _ => total_pure _))
  · simp only [throw_bind']; exact total_throw _
  · simp only [throw_bind']; exact total_throw _

/-- The claimed heights of every matrix, with the blowup, are within the adicity. -/
def HeightsOK {C : Type} (G : Gen K) (b : ℕ) (claims : List (Claim G C)) : Prop :=
  ∀ c ∈ claims, ∀ m ∈ c.matrices, m.domain.log_size + b ≤ G.adicity

theorem reduceMatrix_total {ME IE : Type} (G : Gen K) (g : K) (b H : ℕ) (α : K) (index : ℕ) (st : RedState K)
    (mr : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K)
    (hm : mr.1.domain.log_size + b ≤ G.adicity) :
    Total (reduceMatrix (ME := ME) (IE := IE) G g b H α index st mr) := by
  obtain ⟨acc, keys, offs⟩ := st
  obtain ⟨m, row⟩ := mr
  unfold reduceMatrix
  dsimp only
  simp only [queryPoint, gen_get_of_le G hm, Option.bind_eq_bind, Option.bind_some, lift, lift_some_bind]
  refine total_bind (total_foldlM (fun st2 p => ?_) _ _) fun _ _ => total_pure _
  split_ifs <;> (try simp only [throw_bind']) <;> first | exact total_throw _ | exact total_pure _

theorem reduceQuery_total {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) (hc : HeightsOK G b claims) :
    Total (reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index) := by
  unfold reduceQuery
  refine total_bind ?_ fun res _ => ?_
  · have hmats : ∀ mr ∈ (claims.zip rows).flatMap (fun cr => cr.1.matrices.zip cr.2),
        mr.1.domain.log_size + b ≤ G.adicity := by
      intro mr hmr
      obtain ⟨cr, hcr, hmr⟩ := List.mem_flatMap.1 hmr
      exact hc cr.1 (List.of_mem_zip hcr).1 mr.1 (List.of_mem_zip hmr).1
    generalize ((claims.zip rows).flatMap fun cr => cr.1.matrices.zip cr.2) = mats at hmats ⊢
    generalize ((((fun _ => (0 : K)), ([] : List ℕ), ladderOffsets (openingPoints b claims)) : RedState K)) = st0
    induction mats generalizing st0 with
    | nil => exact total_pure _
    | cons mr mats ih =>
      rw [List.foldlM_cons]
      exact total_bind (reduceMatrix_total G g b H α index st0 mr (hmats mr List.mem_cons_self))
        fun st1 _ => ih (fun x hx => hmats x (List.mem_cons_of_mem _ hx)) st1
  · obtain ⟨acc, keys, _⟩ := res
    dsimp only
    split_ifs <;> (try simp only [throw_bind']) <;> first | exact total_throw _ | exact total_pure _

theorem checkBatch_total {ME : Type} (G : Gen K) {C : Type} (mmcs : MmcsOps K) (b H : ℕ) (indices : List ℕ)
    (commit_of : C → mmcs.Commitment) (bc : BatchMultiOpening K mmcs.MultiProof × Claim G C) :
    Total (checkBatch (ME := ME) G mmcs b H indices commit_of bc) := by
  obtain ⟨bo, c⟩ := bc
  unfold checkBatch
  dsimp only
  split_ifs <;> (try simp only [throw_bind']) <;> (try exact total_throw _)
  split <;> first | exact total_throw _ | exact total_pure _

theorem checkDenominators_total {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (indices : List ℕ)
    (claims : List (Claim G C)) (hc : HeightsOK G b claims) :
    Total (checkDenominators (ME := ME) (IE := IE) G g b H indices claims) := by
  unfold checkDenominators
  refine total_forM (fun index => total_forM' _ fun c hcm => total_forM' _ fun m hm => ?_) _
  simp only [queryPoint, gen_get_of_le G (hc c hcm m hm), Option.bind_eq_bind, Option.bind_some, lift,
    lift_some_bind]
  exact total_forM (fun p => total_ite (fun _ => total_throw _) (fun _ => total_pure _)) _

theorem open_inputs_total {ME : Type} (G : Gen K) (g : K) {C : Type} (mmcs : MmcsOps K) (b H : ℕ)
    (indices : List ℕ) (input_openings : List (BatchMultiOpening K mmcs.MultiProof)) (α : K)
    (claims : List (Claim G C)) (commit_of : C → mmcs.Commitment) (hc : HeightsOK G b claims) :
    Total (open_inputs (ME := ME) G g mmcs b H indices input_openings α claims commit_of) := by
  unfold open_inputs
  dsimp only
  split_ifs
  · simp only [throw_bind']; exact total_throw _
  refine total_bind (total_forM (fun bc => checkBatch_total G mmcs b H indices commit_of bc) _) fun _ _ => ?_
  refine total_bind (checkDenominators_total (ME := ME) (IE := mmcs.Error) G g b H indices claims hc)
    fun _ _ => ?_
  apply total_mapM
  intro e
  exact reduceQuery_total G g b H α claims _ e.1 hc

/-- The input heights the verifier derives are strictly decreasing. -/
theorem inputLogHeights_isChain {G : Gen K} {C : Type} (b : ℕ) (claims : List (Claim G C)) :
    (inputLogHeights b claims).IsChain (· > ·) := by
  unfold inputLogHeights
  set l := (claims.flatMap fun c => c.matrices.map fun m => m.domain.log_size + b).mergeSort
    (fun a b => decide (b ≤ a))
  have hs : l.Pairwise (fun a b => decide (b ≤ a) = true) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) _
  have hd : l.dedup.Pairwise (fun a b => b ≤ a) := (hs.sublist (List.dedup_sublist l)).imp (by simp)
  exact ((hd.and (List.nodup_dedup l)).imp fun h => lt_of_le_of_ne h.1 (Ne.symm h.2)).isChain

theorem checkQuery_total {ME IE : Type} (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (betas : List K)
    (las : List ℕ) (svs : List (List (List K))) (final_poly : List K) {H : ℕ} (Hf : ℕ) (hH : H ≤ G.adicity)
    (e : (ℕ × List (ℕ × K)) × ℕ) :
    Total (checkQuery (ME := ME) (IE := IE) G betas las svs final_poly H Hf e) := by
  unfold checkQuery
  refine total_bind (fold_query_total G hV h2 _ _ _ _ _ _ Hf hH) fun r _ => ?_
  obtain ⟨folded, di, rec⟩ := r
  simp only [lift, gen_get_of_le G hH, lift_some_bind]
  split_ifs
  · simp only [throw_bind']; exact total_throw _
  · exact total_pure _

theorem checkRound_total {IE : Type} (fmmcs : MmcsOps K) (recorded : List (List (ℕ × List K))) (lc : ℕ)
    (e : (fmmcs.Commitment × CommitPhaseMultiStep K fmmcs.MultiProof × ℕ) × ℕ) :
    Total (checkRound (IE := IE) fmmcs recorded lc e) := by
  obtain ⟨⟨commit, opening, la⟩, round⟩ := e
  unfold checkRound
  dsimp only
  split <;> first | exact total_throw _ | exact total_pure _

theorem le_headD_inputLogHeights {G : Gen K} {C : Type} (b : ℕ) (claims : List (Claim G C)) :
    HeightsOK G b claims ∨ G.adicity < (inputLogHeights b claims).headD 0 := by
  by_cases h : G.adicity < (inputLogHeights b claims).headD 0
  · exact Or.inr h
  refine Or.inl fun c hc m hm => ?_
  have hx : m.domain.log_size + b ∈ inputLogHeights b claims := by
    simp only [inputLogHeights, List.mem_dedup, List.mem_mergeSort, List.mem_flatMap, List.mem_map]
    exact ⟨c, hc, m, hm, rfl⟩
  have hpw := List.pairwise_iff_getElem.1 (List.isChain_iff_pairwise.1 (inputLogHeights_isChain b claims))
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have h0 : 0 < (inputLogHeights b claims).length := by omega
  have : (inputLogHeights b claims)[i] ≤ (inputLogHeights b claims).headD 0 := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Option.getD_some]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact le_rfl
    · exact le_of_lt (hpw 0 i h0 hi hi0)
  omega

/-- A transcript whose two phases never panic. -/
def TxTotal {Com S : Type} (tx : VerifierTx K Com S) : Prop :=
  (∀ s c w, (tx.commit_rounds s c w).run.isSome) ∧ ∀ s f w, (tx.query_phase s f w).run.isSome

theorem total_lift_isSome {ME IE α : Type} {o : Option α} (h : o.isSome) :
    Total (lift o : Res ME IE α) := by
  obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.1 h; exact total_lift_some a

/-- The verifier never panics on a transcript that never panics at the shapes it can build.

This holds on every proof, commitment schemes and claims. -/
theorem verify_fri_total (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (g : K) {C S : Type}
    (fmmcs immcs : MmcsOps K) (mkTx : p3_fri.transcript.mirror.FriShape → VerifierTx K fmmcs.Commitment S)
    (params : FriParameters)
    (htx : ∀ L H, H ≤ G.adicity → TxTotal (mkTx (p3_fri.transcript.mirror.FriShape.with_schedule params L H)))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) :
    Total (verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha) := by
  unfold verify_fri
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
  refine total_ite (fun _ => total_throw _) fun _ => ?_
  split
  · exact total_ite (fun _ => total_throw _) fun _ => total_throw _
  refine total_ite (fun _ => total_throw _) fun _ => ?_
  refine total_ite (fun _ => total_throw _) fun _ => ?_
  refine total_bind (total_lift_isSome ((htx L _ hbig).1 _ _ _)) fun r _ => ?_
  rcases r with f | r1
  · exact total_throw _
  refine total_bind (total_lift_isSome ((htx L _ hbig).2 _ _ _)) fun r _ => ?_
  rcases r with f | r2
  · exact total_throw _
  refine total_bind (open_inputs_total (ME := fmmcs.Error) G g immcs _ _ _ _ _ claims commit_of hok)
    fun ro _ => ?_
  refine total_bind (total_mapM (fun e => checkQuery_total G hV h2 _ _ _ _ _ hbig e) _) fun rec _ => ?_
  exact total_bind (total_foldlM (fun lc e => checkRound_total fmmcs rec lc e) _ _) fun _ _ => total_pure _

end Plonky3Lean.Proofs.Fri
