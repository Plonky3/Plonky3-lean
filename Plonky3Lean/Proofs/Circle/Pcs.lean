module

public import P3Circle.Pcs
public import Plonky3Lean.Proofs.Circle.Res
public import Plonky3Lean.Proofs.Circle.Folding

@[expose] public section

/-!
# p3-circle: the PCS verifier never panics, except at two points

The verifier panics in exactly two places:

- an opening point t with t^2 = -1, which has no point on the circle
- a claimed domain of one row, whose vanishing polynomial v_0 the lambda correction reads.

Everything else returns a value or a rejection.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft
open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_commit.pcs.univariate.mirror
open p3_commit.domain.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_circle.ordering.mirror
open p3_circle.folding.mirror p3_circle.deep_quotient.mirror p3_circle.verifier.mirror p3_circle.pcs.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-! ## The proof shape -/

/-- What an accepted shape check guarantees. -/
structure ShapeOK {Com MP IP : Type} (params : FriParameters) (proof : CircleFriProof K Com MP IP)
    (n : ℕ) : Prop where
  blowup : 1 ≤ params.log_blowup
  commits : proof.commit_phase_commits.length = n
  witnesses : proof.commit_pow_witnesses.length = n
  openings : proof.commit_phase_openings.length = n
  queries : ∀ o ∈ proof.commit_phase_openings, o.sibling_values.length = params.num_queries
  siblings : ∀ o ∈ proof.commit_phase_openings, ∀ s ∈ o.sibling_values, s.length = 1

/-- Close a step that returns or rejects at once. -/
macro "total_leaf" : tactic =>
  `(tactic| first
    | exact total_throw _
    | exact total_pure _
    | (simp only [throw_bind'']; exact total_throw _))

theorem validate_proof_shape_total {ME IE Com MP IP : Type} (params : FriParameters)
    (proof : CircleFriProof K Com MP IP) (n : ℕ) :
    Total (validate_proof_shape (ME := ME) (IE := IE) params proof n) := by
  unfold validate_proof_shape
  repeat' (first | apply total_ite | intro)
  all_goals first
    | total_leaf
    | refine total_bind (total_forM _ fun e _ => ?_) fun _ _ => total_pure _
      repeat' (first | apply total_ite | intro)
      all_goals total_leaf

theorem mem_zip_replicate {α β : Type _} {a : β} {x : α} :
    ∀ {l : List α}, x ∈ l → (x, a) ∈ l.zip (List.replicate l.length a)
  | y :: l, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [List.replicate_succ]
    · simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons]
      exact Or.inr (mem_zip_replicate hx)

theorem validate_proof_shape_spec {ME IE Com MP IP : Type} {params : FriParameters}
    {proof : CircleFriProof K Com MP IP} {n : ℕ} {la : List ℕ}
    (h : validate_proof_shape (ME := ME) (IE := IE) params proof n = pure la) :
    la = List.replicate n 1 ∧ ShapeOK params proof n := by
  unfold validate_proof_shape at h
  simp only [throw_bind'', ite_throw_eq_pure] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨_, hf, hp⟩ := h
  cases pure_inj' hp
  have hall := forM_eq_pure hf
  have h8 : proof.commit_phase_openings.length = n := by simpa using h8
  have hstep : ∀ o ∈ proof.commit_phase_openings, o.sibling_values.length = params.num_queries ∧
      ∀ s ∈ o.sibling_values, s.length = 1 := by
    intro o ho
    have := hall _ (h8 ▸ mem_zip_replicate (a := 1) ho)
    simp only [ite_throw_eq_pure] at this
    obtain ⟨hq, hs, -⟩ := this
    exact ⟨by simpa using hq, by simpa using hs⟩
  exact ⟨rfl, ⟨by omega, by simpa using h4, by simpa using h5, h8, fun o ho => (hstep o ho).1,
    fun o ho => (hstep o ho).2⟩⟩

/-! ## The fold chain -/

/-- A row of two values rebuilt from the running value and one sibling. -/
theorem rebuildRow_two (i : ℕ) (hi : i < 2) (v a : K) :
    rebuildRow 2 i v [a] = some (if i = 0 then [v, a] else [a, v]) := by
  interval_cases i <;> rfl

/-- The fold chain never panics when every round halves, carries one sibling and has a twiddle. -/
theorem foldlM_foldStep_isSome (q : ℕ) (tw : List K) :
    ∀ (rounds : List ((K × ℕ × List (List K)) × ℕ)) (st : ChainState K),
      (∀ r ∈ rounds, r.1.2.1 = 1 ∧ (∃ s, r.1.2.2[q]? = some s ∧ s.length = 1) ∧ r.2 < tw.length) →
      rounds.length ≤ st.2.2.1 → (rounds.foldlM (foldStep q tw) st).isSome
  | [], _, _, _ => rfl
  | ((β, a, sv), round) :: rounds, (idx, v, lh, ro, acc), hr, hlen => by
    obtain ⟨ha, ⟨s, hs, hsl⟩, hround⟩ := hr _ List.mem_cons_self
    obtain ⟨b, rfl⟩ : ∃ b, s = [b] := by
      match s, hsl with
      | [b], _ => exact ⟨b, rfl⟩
    dsimp only at ha hs hround hlen
    subst ha
    simp only [List.length_cons] at hlen
    have hrest := fun st' => foldlM_foldStep_isSome q tw rounds st'
      (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))
    obtain ⟨t, ht⟩ : ∃ t, tw[round]? = some t := ⟨tw[round], by simp [hround]⟩
    rw [List.foldlM_cons]
    rcases ro with _ | ⟨⟨h1, v1⟩, ro'⟩
    all_goals
      simp only [foldStep, hs, rebuildRow_two _ (Nat.mod_lt _ (by norm_num)), pow_one, ht,
        show ¬ lh < 1 by omega, ne_eq, not_true_eq_false, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
    · split_ifs <;> exact hrest _ (by simp; omega)
    · split_ifs <;> exact hrest _ (by simp; omega)

theorem mem_zipIdx_mem {α : Type _} {l : List α} {r : α × ℕ} (h : r ∈ l.zipIdx) :
    r.1 ∈ l ∧ r.2 < l.length := by
  obtain ⟨x, i⟩ := r
  obtain ⟨hi, hx⟩ := List.mem_zipIdx' h
  exact ⟨hx ▸ List.getElem_mem hi, hi⟩

/-- A query's fold chain never panics on a validated proof.

Every round halves and carries one sibling for the query, and each round has its twiddle. -/
theorem fold_query_total {ME IE : Type} (lb q idx : ℕ) (betas : List K) {R : ℕ}
    (svs : List (List (List K))) (ro : List (ℕ × K)) {L : ℕ} (tw : List K)
    (hsv : ∀ sv ∈ svs, ∃ s, sv[q]? = some s ∧ s.length = 1) (htw : tw.length = R) (hRL : R ≤ L) :
    Total (fold_query (ME := ME) (IE := IE) lb q idx betas (List.replicate R 1) svs ro L tw) := by
  unfold fold_query
  have hlen : ((betas.zip ((List.replicate R 1).zip svs)).zipIdx).length ≤ R := by
    simp only [List.length_zipIdx, List.length_zip, List.length_replicate]; omega
  have hsome := foldlM_foldStep_isSome q tw ((betas.zip ((List.replicate R 1).zip svs)).zipIdx)
    (idx, 0, L, ro, []) (fun r hr => by
      obtain ⟨hr1, hr2⟩ := mem_zipIdx_mem hr
      have hm := (List.of_mem_zip hr1).2
      refine ⟨List.eq_of_mem_replicate (List.of_mem_zip hm).1, hsv _ (List.of_mem_zip hm).2, ?_⟩
      simp only [List.length_zip, List.length_replicate] at hr2; omega) (by simpa using hlen.trans hRL)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨_, folded, log_h, ro', recorded⟩ := res
  simp only [lift, hres, lift_some_bind']
  repeat' (first | apply total_ite | intro)
  all_goals total_leaf

variable {G : Gen (K × K)}

/-- The twiddle chain of a query returns one twiddle per round, without panicking. -/
theorem query_twiddles_some (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (t : ℕ) {L R : ℕ}
    (hRL : R + 1 ≤ L) (hG : L + 2 ≤ G.adicity) :
    ∃ tw, query_x_twiddles_inv G t L R = some tw ∧ tw.length = R := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact ⟨[], by simp [query_x_twiddles_inv], rfl⟩
  · exact ⟨_, query_x_twiddles_inv_eq hV h2 t hR hRL hG, by simp⟩

/-- Heights listed strictly decreasing. -/
def Desc (ro : List (ℕ × K)) : Prop := ((ro.zip ro.tail).all fun p => p.2.1 < p.1.1) = true

theorem checkQuery_total {ME IE : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb R : ℕ}
    (betas : List K) (svs : List (List (List K))) (fp : K) (e : (ℕ × List (ℕ × K)) × ℕ)
    (hlb : 1 ≤ lb) (hG : R + lb + 2 ≤ G.adicity)
    (hsv : ∀ sv ∈ svs, ∃ s, sv[e.2]? = some s ∧ s.length = 1) (hro : Desc e.1.2) :
    Total (checkQuery (ME := ME) (IE := IE) G lb betas (List.replicate R 1) svs fp (R + lb) e) := by
  obtain ⟨⟨index, ro⟩, q⟩ := e
  unfold checkQuery
  dsimp only at hro hsv ⊢
  obtain ⟨tw, htw, htwl⟩ := query_twiddles_some hV h2 (index / 2) (L := R + lb) (R := R) (by omega)
    (by omega)
  rw [Desc] at hro
  simp only [hro, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_replicate, lift, htw,
    lift_some_bind']
  refine total_bind (fold_query_total lb q _ betas svs ro tw hsv htwl (by omega)) fun _ _ => ?_
  repeat' (first | apply total_ite | intro)
  all_goals total_leaf

theorem mapInputError_total {ME IE α : Type} {m : ExceptT IE Option α} (h : Total m) :
    Total (mapInputError (ME := ME) m) := by
  rcases m with _ | (e | a)
  · exact absurd h (by simp [Total, ExceptT.run])
  · rfl
  · rfl

theorem mapInputError_eq_pure {ME IE α : Type} {m : ExceptT IE Option α} {a : α}
    (h : mapInputError (ME := ME) m = pure a) : m = pure a := by
  rcases m with _ | (e | b)
  · cases h
  · cases h
  · cases h; rfl

theorem checkRound_total {IE : Type} (fmmcs : MmcsOps K) (rec : List (List (ℕ × List K))) (h : ℕ)
    (e : (fmmcs.Commitment × CommitPhaseMultiStep K fmmcs.MultiProof × ℕ) × ℕ) :
    Total (checkRound (IE := IE) fmmcs rec h e) := by
  obtain ⟨⟨c, o, a⟩, r⟩ := e
  unfold checkRound
  dsimp only
  split <;> total_leaf

/-- The query checks never panic once the proof's shape is validated and the input checks never panic.

The input checks must list each query's openings with strictly decreasing heights. -/
theorem verify_queries_total (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {IE IP : Type} (fmmcs : MmcsOps K)
    (params : FriParameters) (proof : CircleFriProof K fmmcs.Commitment fmmcs.MultiProof IP)
    (betas : List K) (indices : List ℕ) {R : ℕ}
    (open_inputs : List ℕ → IP → ExceptT IE Option (List (List (ℕ × K))))
    (hlb : 1 ≤ params.log_blowup) (hG : R + params.log_blowup + 2 ≤ G.adicity)
    (hq : ∀ o ∈ proof.commit_phase_openings, o.sibling_values.length = params.num_queries)
    (hs : ∀ o ∈ proof.commit_phase_openings, ∀ s ∈ o.sibling_values, s.length = 1)
    (hidx : indices.length ≤ params.num_queries)
    (hopen : Total (open_inputs indices proof.input_openings))
    (hdesc : ∀ out, open_inputs indices proof.input_openings = pure out → ∀ ro ∈ out, Desc ro) :
    Total (verify_queries G fmmcs params proof betas indices (List.replicate R 1) open_inputs) := by
  unfold verify_queries
  simp only [List.sum_replicate, smul_eq_mul, mul_one]
  refine total_bind (mapInputError_total hopen) fun out hout => ?_
  have hout := mapInputError_eq_pure hout
  refine total_bind (total_mapM _ fun e he => ?_) fun _ _ =>
    total_bind (total_foldlM _ _ fun _ _ _ => checkRound_total _ _ _ _) fun _ _ => total_pure _
  obtain ⟨he1, he2⟩ := mem_zipIdx_mem he
  refine checkQuery_total hV h2 betas _ _ e hlb hG (fun sv hsv => ?_) (hdesc out hout _ (List.of_mem_zip he1).2)
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hsv
  have hlt : e.2 < o.sibling_values.length := by
    rw [hq o ho]; simp only [List.length_zip] at he2; omega
  exact ⟨_, List.getElem?_eq_getElem hlt, hs o ho _ (List.getElem_mem hlt)⟩

/-! ## The input checks -/

/-- A point with y = 0 has order at most 2. -/
theorem two_nsmul_eq_zero_of_y {P : C K} (hy : P.y = 0) : 2 • P = 0 := by
  have hx : P.x ^ 2 = 1 := by simpa [hy] using P.eq
  ext
  · rw [C.two_nsmul_x, hx]; norm_num
  · rw [C.two_nsmul_y, hy]; simp

/-- Every point of a standard domain of size at least 2 has y nonzero. -/
theorem twinPoint_standard_y_ne_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (k : ℕ) : (twinPoint (genPt G (n + 1)) (genPt G (n - 1)) k).y ≠ 0 := by
  intro hy
  rw [twinPoint_standard hV hn hG] at hy
  have hord : addOrderOf ((2 * k + 1) • genPt G (n + 1)) = 2 ^ (n + 1) := by
    rw [Nat.Coprime.addOrderOf_nsmul, addOrderOf_genPt hV h2 hG]
    rw [addOrderOf_genPt hV h2 hG]
    exact Nat.Coprime.pow_left _ (by simp)
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero (two_nsmul_eq_zero_of_y hy)
  rw [hord] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  have : 2 ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- What the verifier's no-panic argument needs of the claims:

- every claimed domain has at least 2 rows
- every committed height lies at or below the tallest one, H
- every opening point t has 1 + t^2 nonzero. -/
structure ClaimsOK {Com : Type} (lb H : ℕ) (rounds : List (Claim K Com)) : Prop where
  log_n : ∀ c ∈ rounds, ∀ m ∈ c.matrices, 1 ≤ m.domain.log_n
  height : ∀ c ∈ rounds, ∀ m ∈ c.matrices, m.domain.log_n + lb ≤ H
  points : ∀ c ∈ rounds, ∀ m ∈ c.matrices, ∀ p ∈ m.points, 1 + p.point * p.point ≠ 0

theorem checkBatch_total (immcs : MmcsOps K) {FME : Type} {lb H : ℕ} (indices : List ℕ)
    (bc : BatchMultiOpening K immcs.MultiProof × Claim K immcs.Commitment)
    (hh : ∀ m ∈ bc.2.matrices, m.domain.log_n + lb ≤ H) :
    Total (checkBatch (FME := FME) immcs lb H indices bc) := by
  obtain ⟨bo, c⟩ := bc
  unfold checkBatch
  dsimp only at hh ⊢
  refine total_ite (fun _ => by total_leaf) fun _ => ?_
  refine total_bind (total_mapM _ fun m _ => by split <;> total_leaf) fun dims _ => ?_
  split
  · simp only [pure_bind]; split <;> total_leaf
  · next h hmax =>
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.max?_mem hmax)
    simp only [← pow_add, log2Strict_pow, lift_some_bind', show ¬ H < m.domain.log_n + lb from
      by have := hh m hm; omega, ↓reduceIte, pure_bind]
    split <;> total_leaf

/-- The heights a query's reduction has seen: distinct, above the blowup, at or below H. -/
def KeysOK (lb H : ℕ) (keys : List ℕ) : Prop := keys.Nodup ∧ ∀ k ∈ keys, lb + 1 ≤ k ∧ k ≤ H

/-- The point of a standard domain the verifier reads, at any index. -/
theorem standard_nth_point (hV : CircleGenValid G) {h : ℕ} (hh : 1 ≤ h) (hG : h + 1 ≤ G.adicity) (idx : ℕ) :
    (CircleDomain.standard G h).bind (fun d => CircleDomain.nth_point G d idx) =
      some (ofC (twinPoint (genPt G (h + 1)) (genPt G (h - 1)) idx)) := by
  rw [standard_eq hV h hG, Option.bind_some, nth_point_eq hV h _ hh (by omega)]

theorem reduceMatrix_total {IME FME : Type} (hV : CircleGenValid G) {lb H : ℕ} (αs : List K) (index : ℕ)
    (st : (ℕ → K × K) × List ℕ) (m : MatrixOpening K (CircleDomain K) × List K × (K × K))
    (hn : 1 ≤ m.1.domain.log_n) (hh : m.1.domain.log_n + lb ≤ H) (hG : H + 1 ≤ G.adicity)
    (hpts : ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0) :
    Total (reduceMatrix (IME := IME) (FME := FME) G lb H αs index st m) := by
  obtain ⟨acc, keys⟩ := st
  obtain ⟨mat, row, aw, aw2⟩ := m
  dsimp only at hn hh hpts
  have hpt := standard_nth_point hV (h := mat.domain.log_n + lb) (by omega) (by omega)
    (cfft_permute_index (index / 2 ^ (H - (mat.domain.log_n + lb))) (mat.domain.log_n + lb))
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  unfold reduceMatrix
  dsimp only
  rw [ite_eq_right (by omega), standard_eq hV _ (by omega), lift_some_bind']
  simp only [hpt, lift_some_bind']
  refine total_bind (total_foldlM _ _ fun e p hp => ?_) fun _ _ => total_pure _
  refine total_ite (fun _ => by total_leaf) fun _ => ?_
  rw [from_projective_line_eq, dite_eq_right (hpts p hp), lift_some_bind']
  split <;> total_leaf

theorem reduceMatrix_keys {IME FME : Type} {lb H : ℕ} {αs : List K} {index : ℕ}
    {st st' : (ℕ → K × K) × List ℕ} {m : MatrixOpening K (CircleDomain K) × List K × (K × K)}
    (hn : 1 ≤ m.1.domain.log_n) (hh : m.1.domain.log_n + lb ≤ H)
    (h : reduceMatrix (IME := IME) (FME := FME) G lb H αs index st m = pure st') (hk : KeysOK lb H st.2) :
    KeysOK lb H st'.2 := by
  obtain ⟨acc, keys⟩ := st
  obtain ⟨mat, row, aw, aw2⟩ := m
  dsimp only at hn hh hk
  unfold reduceMatrix at h
  dsimp only at h
  rw [ite_eq_right (by omega)] at h
  rw [bind_eq_pure'] at h
  obtain ⟨d, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨x, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨e, -, h⟩ := h
  cases pure_inj' h
  dsimp only
  split_ifs with hmem
  · exact hk
  · refine ⟨List.nodup_append.mpr ⟨hk.1, List.nodup_singleton _, ?_⟩, fun k hk' => ?_⟩
    · intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; exact fun h => hmem (h ▸ ha)
    · rcases List.mem_append.mp hk' with hk' | hk'
      · exact hk.2 k hk'
      · rw [List.mem_singleton] at hk'; omega

/-- What one batch needs for its reduction never to panic. -/
structure BatchOK {Com MP : Type} (lb H query : ℕ) (e : BatchMultiOpening K MP × Claim K Com × List (K × K)) :
    Prop where
  row : query < e.1.opened_values.length
  pows : e.2.2.length = e.2.1.matrices.length
  log_n : ∀ m ∈ e.2.1.matrices, 1 ≤ m.domain.log_n
  height : ∀ m ∈ e.2.1.matrices, m.domain.log_n + lb ≤ H
  points : ∀ m ∈ e.2.1.matrices, ∀ p ∈ m.points, 1 + p.point * p.point ≠ 0

theorem mem_zipIdx_zip {α β : Type _} {l : List α} {l' : List β} {r : (α × β) × ℕ}
    (h : r ∈ (l.zip l').zipIdx) : r.1.1 ∈ l ∧ r.2 < l.length := by
  obtain ⟨h1, h2⟩ := mem_zipIdx_mem h
  exact ⟨(List.of_mem_zip h1).1, by simp only [List.length_zip] at h2; omega⟩

theorem reduceBatch_total {IME FME Com MP : Type} (hV : CircleGenValid G) {lb H : ℕ} (αs : List K)
    (index query : ℕ) (st : (ℕ → K × K) × List ℕ) (e : BatchMultiOpening K MP × Claim K Com × List (K × K))
    (he : BatchOK lb H query e) (hG : H + 1 ≤ G.adicity) :
    Total (reduceBatch (IME := IME) (FME := FME) G lb H αs index query st e) := by
  obtain ⟨bo, c, pows⟩ := e
  obtain ⟨hrow, hpows, hn, hh, hp⟩ := he
  dsimp only at hrow hpows hn hh hp
  unfold reduceBatch
  simp only [List.getElem?_eq_getElem hrow, lift_some_bind']
  refine total_ite (fun _ => by total_leaf) fun _ => total_foldlM _ _ fun st mr hmr => ?_
  obtain ⟨hm, hi⟩ := mem_zipIdx_zip hmr
  rw [List.getElem?_eq_getElem (by omega), lift_some_bind']
  exact reduceMatrix_total hV αs index st _ (hn _ hm) (hh _ hm) hG (hp _ hm)

theorem reduceBatch_keys {IME FME Com MP : Type} {lb H : ℕ} {αs : List K} {index query : ℕ}
    {st st' : (ℕ → K × K) × List ℕ} {e : BatchMultiOpening K MP × Claim K Com × List (K × K)}
    (hn : ∀ m ∈ e.2.1.matrices, 1 ≤ m.domain.log_n) (hh : ∀ m ∈ e.2.1.matrices, m.domain.log_n + lb ≤ H)
    (h : reduceBatch (IME := IME) (FME := FME) G lb H αs index query st e = pure st')
    (hk : KeysOK lb H st.2) : KeysOK lb H st'.2 := by
  obtain ⟨bo, c, pows⟩ := e
  dsimp only at hn hh
  unfold reduceBatch at h
  rw [bind_eq_pure'] at h
  obtain ⟨row, -, h⟩ := h
  simp only [throw_bind'', ite_throw_eq_pure] at h
  refine foldlM_invariant (P := fun s => KeysOK lb H s.2) (fun s mr s' hmr hs hks => ?_) h.2 hk
  obtain ⟨hm, -⟩ := mem_zipIdx_zip hmr
  rw [bind_eq_pure'] at hs
  obtain ⟨ap, -, hs⟩ := hs
  exact reduceMatrix_keys (hn _ hm) (hh _ hm) hs hks

/-! ## Lists the reduction returns -/

theorem desc_of_pairwise : ∀ {l : List (ℕ × K)}, l.Pairwise (fun a b => b.1 < a.1) → Desc l
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: l, h => by
    have hy := desc_of_pairwise (List.pairwise_cons.mp h).2
    have hxy := (List.pairwise_cons.mp h).1 y List.mem_cons_self
    unfold Desc at hy ⊢
    simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, hxy, decide_true, Bool.true_and]
    simpa using hy

/-- A sorted list of distinct keys is strictly increasing. -/
theorem pairwise_lt_mergeSort {keys : List ℕ} (hk : keys.Nodup) :
    (keys.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· < ·) := by
  have hle := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) keys
  have hne : (keys.mergeSort (fun a b => decide (a ≤ b))).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr hk
  exact (hle.and hne).imp fun ⟨h1, h2⟩ => by simp only [decide_eq_true_eq] at h1; omega

theorem option_mapM_isSome {α β : Type _} {f : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
      (option_mapM_isSome l fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [List.mapM_cons, hb, hbs]

theorem option_mapM_forall₂ {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → List.Forall₂ (fun a b => f a = some b) l r
  | [], r, h => by simp only [List.mapM_nil] at h; cases h; exact .nil
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    rcases hx : f x with _ | b
    · simp [hx] at h
    · rcases hl : l.mapM f with _ | bs
      · simp [hx, hl] at h
      · simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        exact .cons hx (option_mapM_forall₂ hl)

/-- The first-layer leaf of a height the reduction saw: a pair with a nonzero twiddle. -/
theorem firstLayerLeaf_some (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H k : ℕ} (index : ℕ)
    (hk : lb + 1 ≤ k) (hkH : k ≤ H) (hG : H + 1 ≤ G.adicity) (ro sib lam : K) :
    ∃ y vals, firstLayerLeaf G lb H index (((k, ro), sib), lam) = some (k, y, vals, (2, 2 ^ (k - 1))) ∧
      y ≠ 0 ∧ vals.length = 2 := by
  have hpt := standard_nth_point hV (h := k) (by omega) (by omega)
    (cfft_permute_index (index / 2 ^ (H - k)) k)
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  set P := twinPoint (genPt G (k + 1)) (genPt G (k - 1)) (cfft_permute_index (index / 2 ^ (H - k)) k)
  have hy : P.y ≠ 0 := twinPoint_standard_y_ne_zero hV h2 (by omega) (by omega) _
  unfold firstLayerLeaf
  simp only [show k ≠ 0 by omega, show ¬ k < lb by omega, show ¬ H < k by omega, ↓reduceIte,
    standard_eq hV _ (by omega : k + 1 ≤ G.adicity), hpt, v_n_ofC, show 1 ≤ k - lb by omega,
    Option.bind_eq_bind, Option.bind_some]
  split_ifs <;> exact ⟨_, _, rfl, by simpa [ofC] using hy, rfl⟩

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → ∀ b ∈ r, ∃ a ∈ l, R a b
  | _, _, .nil, b, hb => by simp at hb
  | a :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_imp_mem {α β : Type _} {R S : α → β → Prop} {l : List α} (hRS : ∀ a b, a ∈ l → R a b → S a b) :
    ∀ {l' : List α} {r : List β}, l' ⊆ l → List.Forall₂ R l' r → List.Forall₂ S l' r
  | _, _, _, .nil => .nil
  | _ :: _, _ :: _, hsub, .cons hab h =>
    .cons (hRS _ _ (hsub List.mem_cons_self) hab) (forall₂_imp_mem hRS (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) h)

theorem fold_row_isSome {t β : K} {vals : List K} (h : vals.length = 2) :
    (fold_row_with_inv_twiddle t β vals).isSome := by
  match vals, h with
  | [_, _], _ => rfl

/-- The first-layer leaves of the heights a query saw: one per height, each a pair with a nonzero twiddle. -/
theorem perHeight_facts (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (index : ℕ)
    (hG : H + 1 ≤ G.adicity) {keys : List ℕ} (hk : KeysOK lb H keys) (f : ℕ → K) (fls lams : List K)
    {per : List (ℕ × K × List K × (ℕ × ℕ))}
    (h : ((((keys.mergeSort (fun a b => decide (a ≤ b))).map fun k => (k, f k)).zip fls).zip lams).mapM
      (firstLayerLeaf G lb H index) = some per) :
    List.Forall₂ (fun (k : ℕ) (r : ℕ × K × List K × (ℕ × ℕ)) => r.1 = k ∧ r.2.1 ≠ 0 ∧ r.2.2.1.length = 2)
      (((((keys.mergeSort (fun a b => decide (a ≤ b))).map fun k => (k, f k)).zip fls).zip lams).map
        (·.1.1.1)) per := by
  have h2' := option_mapM_forall₂ h
  rw [List.forall₂_map_left_iff]
  refine forall₂_imp_mem (fun e r he hr => ?_) (List.Subset.refl _) h2'
  have hk' : e.1.1.1 ∈ keys := by
    have h1 := (List.of_mem_zip (List.of_mem_zip he).1).1
    obtain ⟨k, hk, hke⟩ := List.mem_map.mp h1
    rw [← hke]; exact (List.mergeSort_perm _ _).mem_iff.mp hk
  obtain ⟨⟨⟨k, ro⟩, sib⟩, lam⟩ := e
  obtain ⟨y, vals, hleaf, hy, hv⟩ := firstLayerLeaf_some hV h2 index (hk.2 k hk').1 (hk.2 k hk').2 hG ro sib lam
  rw [hleaf, Option.some.injEq] at hr
  subst hr
  exact ⟨rfl, hy, hv⟩

theorem reduceQuery_total (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs : MmcsOps K) {FME : Type}
    {lb H : ℕ} (bb : K) (αs : List K) (mpows : List (List (K × K)))
    (rounds : List (Claim K immcs.Commitment)) (input_openings : List (BatchMultiOpening K immcs.MultiProof))
    (fls : List (List K)) (lams : List K) (index query : ℕ) (hG : H + 1 ≤ G.adicity)
    (hb : ∀ e ∈ input_openings.zip (rounds.zip mpows), BatchOK lb H query e) (hq : query < fls.length) :
    Total (reduceQuery (FME := FME) G immcs lb H bb αs mpows rounds input_openings fls lams index query) := by
  unfold reduceQuery
  refine total_ite (fun _ => by total_leaf) fun _ => ?_
  refine total_bind (total_foldlM _ _ fun st e he => reduceBatch_total hV αs index query st e (hb e he) hG)
    fun res hres => ?_
  obtain ⟨acc, keys⟩ := res
  have hk : KeysOK lb H keys :=
    foldlM_invariant (P := fun s => KeysOK lb H s.2)
      (fun s e s' he hs hks => reduceBatch_keys (hb e he).log_n (hb e he).height hs hks) hres
      ⟨List.nodup_nil, by simp⟩
  dsimp only
  simp only [List.getElem?_eq_getElem hq, lift_some_bind']
  refine total_ite (fun _ => by total_leaf) fun hl1 => total_ite (fun _ => by total_leaf) fun hl2 => ?_
  obtain ⟨per, hper⟩ := Option.isSome_iff_exists.mp (option_mapM_isSome (f := firstLayerLeaf G lb H index)
    ((((keys.mergeSort (fun a b => decide (a ≤ b))).map fun k => (k, (acc k).2)).zip fls[query]).zip lams)
    fun e he => by
      have hk' : e.1.1.1 ∈ keys := by
        have h1 := (List.of_mem_zip (List.of_mem_zip he).1).1
        obtain ⟨k, hk, hke⟩ := List.mem_map.mp h1
        rw [← hke]; exact (List.mergeSort_perm _ _).mem_iff.mp hk
      obtain ⟨⟨⟨k, ro⟩, sib⟩, lam⟩ := e
      obtain ⟨y, vals, hleaf, -⟩ := firstLayerLeaf_some hV h2 index (hk.2 k hk').1 (hk.2 k hk').2 hG ro sib lam
      simp [hleaf])
  have hfacts := perHeight_facts hV h2 index hG hk _ _ _ hper
  have hr : ∀ r ∈ per, r.2.1 ≠ 0 ∧ r.2.2.1.length = 2 := fun r hr' => by
    obtain ⟨_, -, -, h⟩ := forall₂_mem_right hfacts r hr'; exact h
  rw [hper, lift_some_bind', batchInv_eq (fun y hy => by
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hy
    exact (hr r hr').1), lift_some_bind']
  obtain ⟨fi, hfi⟩ := Option.isSome_iff_exists.mp (option_mapM_isSome
    (f := fun e : (ℕ × K × List K × (ℕ × ℕ)) × K =>
      Option.map (fun v => (e.1.1 - 1, v)) (fold_row_with_inv_twiddle e.2 bb e.1.2.2.1))
    (per.zip ((per.map fun e => e.2.1).map (·⁻¹))) fun e he => by
    have hv := (hr e.1 (List.of_mem_zip he).1).2
    simp only [Option.isSome_map]
    exact fold_row_isSome hv)
  rw [hfi, lift_some_bind']
  exact total_pure _

theorem lift_eq_pure {ε α : Type _} {o : Option α} {a : α} :
    (ExceptT.lift o : ExceptT ε Option α) = pure a ↔ o = some a := by
  rcases o with _ | b
  · constructor
    · intro h; cases h
    · intro h; cases h
  · constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl

theorem map_zip_zip_fst {α β γ : Type _} :
    ∀ {A : List α} {B : List β} {C : List γ}, A.length ≤ B.length → A.length ≤ C.length →
      ((A.zip B).zip C).map (fun x => x.1.1) = A
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | a :: A, b :: B, c :: C, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact map_zip_zip_fst (by simpa using h1) (by simpa using h2)

theorem map_eq_of_forall₂ {α β γ : Type _} {g : α → γ} {h : β → γ} :
    ∀ {l : List α} {r : List β}, List.Forall₂ (fun a b => g a = h b) l r → l.map g = r.map h
  | _, _, .nil => rfl
  | _, _, .cons hab h' => by simp [hab, map_eq_of_forall₂ h']

/-- A query's inputs to circle FRI come with strictly decreasing heights. -/
theorem reduceQuery_desc (immcs : MmcsOps K) {FME : Type} {lb H : ℕ} {bb : K} {αs : List K}
    {mpows : List (List (K × K))} {rounds : List (Claim K immcs.Commitment)}
    {input_openings : List (BatchMultiOpening K immcs.MultiProof)} {fls : List (List K)} {lams : List K}
    {index query : ℕ} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (hG : H + 1 ≤ G.adicity)
    (hb : ∀ e ∈ input_openings.zip (rounds.zip mpows), BatchOK lb H query e)
    {out : List (ℕ × K) × List (ℕ × ℕ) × List (List K)}
    (h : reduceQuery (FME := FME) G immcs lb H bb αs mpows rounds input_openings fls lams index query = pure out) :
    Desc out.1 := by
  unfold reduceQuery at h
  simp only [throw_bind'', ite_throw_eq_pure] at h
  obtain ⟨-, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨⟨acc, keys⟩, hres, h⟩ := h
  have hk : KeysOK lb H keys :=
    foldlM_invariant (P := fun s => KeysOK lb H s.2)
      (fun s e s' he hs hks => reduceBatch_keys (hb e he).log_n (hb e he).height hs hks) hres
      ⟨List.nodup_nil, by simp⟩
  dsimp only at h
  rw [bind_eq_pure'] at h
  obtain ⟨fl, -, h⟩ := h
  simp only [ite_throw_eq_pure] at h
  obtain ⟨hl1, hl2, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨per, hper, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨invs, hinvs, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨fi, hfi, h⟩ := h
  cases pure_inj' h
  rw [lift_eq_pure] at hper hinvs hfi
  set sorted := keys.mergeSort (fun a b => decide (a ≤ b))
  have hfacts := perHeight_facts hV h2 index hG hk (fun k => (acc k).2) fl lams hper
  have hL1 : ((((sorted.map fun k => (k, (acc k).2)).zip fl).zip lams).map (·.1.1.1)) = sorted := by
    simp only [ne_eq, not_not] at hl1 hl2
    rw [show (fun x : ((ℕ × K) × K) × K => x.1.1.1) = (fun y : ℕ × K => y.1) ∘ (fun x => x.1.1) from rfl,
      ← List.map_map, map_zip_zip_fst hl1.le hl2.le]
    simp [Function.comp_def]
  have hperfst : per.map (·.1) = sorted := by
    have := map_eq_of_forall₂ (g := id) (h := (·.1)) (hfacts.imp fun _ _ h => h.1.symm)
    rw [← this, List.map_id]; exact hL1
  have hinvl : invs.length = per.length := by
    unfold batchInv at hinvs
    split_ifs at hinvs
    cases hinvs; simp
  have hfifst : fi.map (·.1) = sorted.map (· - 1) := by
    have h1 := map_eq_of_forall₂ (g := fun e : (ℕ × K × List K × (ℕ × ℕ)) × K => e.1.1 - 1) (h := Prod.fst)
      ((option_mapM_forall₂ hfi).imp fun e b hb => by
        obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp hb; rfl)
    have h3 : (per.zip invs).map Prod.fst = per := List.map_fst_zip (by omega)
    rw [← h1, ← hperfst, show (fun e : (ℕ × K × List K × (ℕ × ℕ)) × K => e.1.1 - 1) =
      (fun r : ℕ × K × List K × (ℕ × ℕ) => r.1 - 1) ∘ Prod.fst from rfl, ← List.map_map, h3, List.map_map]
    rfl
  have hsorted : (sorted.map (· - 1)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    refine (pairwise_lt_mergeSort hk.1).imp_of_mem fun {a b} ha _ hab => ?_
    have := (hk.2 a ((List.mergeSort_perm _ _).mem_iff.mp ha)).1
    omega
  apply desc_of_pairwise
  rw [List.pairwise_reverse]
  rw [← hfifst, List.pairwise_map] at hsorted
  exact hsorted

theorem mem_zip_map_self {α β : Type _} {g : α → β} :
    ∀ {l : List α} {x : α × β}, x ∈ l.zip (l.map g) → x.1 ∈ l ∧ x.2 = g x.1
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := mem_zip_map_self h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Every batch of a query the input checks reach satisfies the reduction's needs. -/
theorem batchOK_of {Com MP : Type} {lb H query : ℕ} {rounds : List (Claim K Com)}
    {input_openings : List (BatchMultiOpening K MP)} (g : MatrixOpening K (CircleDomain K) → K × K)
    (hc : ClaimsOK lb H rounds) (hq : ∀ bo ∈ input_openings, query < bo.opened_values.length) :
    ∀ e ∈ input_openings.zip (rounds.zip (rounds.map fun c => c.matrices.map g)), BatchOK lb H query e := by
  intro e he
  obtain ⟨he1, he2⟩ := List.of_mem_zip he
  obtain ⟨hc1, hc2⟩ := mem_zip_map_self he2
  exact ⟨hq _ he1, by rw [hc2]; simp, hc.log_n _ hc1, hc.height _ hc1, hc.points _ hc1⟩

theorem open_inputs_total (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs fmmcs : MmcsOps K) {lb H : ℕ}
    (rounds : List (Claim K immcs.Commitment)) (flc : fmmcs.Commitment) (lams : List K) (bb : K)
    (αs : List K) (g : MatrixOpening K (CircleDomain K) → K × K) (indices : List ℕ)
    (ip : CircleInputProof K immcs.MultiProof fmmcs.MultiProof) (hc : ClaimsOK lb H rounds)
    (hG : H + 1 ≤ G.adicity) :
    Total (open_inputs G immcs fmmcs lb H rounds flc lams bb αs (rounds.map fun c => c.matrices.map g)
      indices ip) := by
  obtain ⟨input_openings, fls, flp⟩ := ip
  unfold open_inputs
  dsimp only
  refine total_ite (fun _ => by total_leaf) fun hfl => total_ite (fun _ => by total_leaf) fun hov => ?_
  refine total_ite (fun _ => by total_leaf) fun _ => ?_
  refine total_bind (total_forM _ fun bc hbc => checkBatch_total immcs indices bc
    (hc.height _ (List.of_mem_zip hbc).2)) fun _ _ => ?_
  have hrow : ∀ bo ∈ input_openings, bo.opened_values.length = indices.length := by
    simpa using hov
  refine total_bind (total_mapM _ fun e he => ?_) fun _ _ => by split <;> total_leaf
  obtain ⟨-, hlt⟩ := mem_zipIdx_mem he
  exact reduceQuery_total hV h2 immcs bb αs _ rounds input_openings fls lams e.1 e.2 hG
    (batchOK_of g hc fun bo hbo => (hrow bo hbo).symm ▸ hlt) (by simp only [ne_eq, not_not] at hfl; omega)

theorem open_inputs_desc (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs fmmcs : MmcsOps K) {lb H : ℕ}
    {rounds : List (Claim K immcs.Commitment)} {flc : fmmcs.Commitment} {lams : List K} {bb : K}
    {αs : List K} {g : MatrixOpening K (CircleDomain K) → K × K} {indices : List ℕ}
    {ip : CircleInputProof K immcs.MultiProof fmmcs.MultiProof} (hc : ClaimsOK lb H rounds)
    (hG : H + 1 ≤ G.adicity) {out : List (List (ℕ × K))}
    (h : open_inputs G immcs fmmcs lb H rounds flc lams bb αs (rounds.map fun c => c.matrices.map g)
      indices ip = pure out) : ∀ ro ∈ out, Desc ro := by
  obtain ⟨input_openings, fls, flp⟩ := ip
  unfold open_inputs at h
  dsimp only at h
  simp only [throw_bind'', ite_throw_eq_pure] at h
  obtain ⟨-, hov, -, h⟩ := h
  have hrow : ∀ bo ∈ input_openings, bo.opened_values.length = indices.length := by
    simpa using hov
  rw [bind_eq_pure'] at h
  obtain ⟨_, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨pq, hpq, h⟩ := h
  split at h
  · simp at h
  · cases pure_inj' h
    intro ro hro
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hro
    obtain ⟨e, he, hre⟩ := mapM_eq_pure_mem hpq r hr
    obtain ⟨-, hlt⟩ := mem_zipIdx_mem he
    exact reduceQuery_desc immcs hV h2 hG (batchOK_of g hc fun bo hbo => (hrow bo hbo).symm ▸ hlt) hre

/-! ## The replayed transcript -/

theorem option_mapM_eq_none {α β : Type _} {f : α → Option β} :
    ∀ {l : List α}, (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨x, hx, _⟩ => by simp at hx
  | y :: l, ⟨x, hx, hfx⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hfx]
    · rcases hy : f y with _ | b
      · simp
      · simp [option_mapM_eq_none ⟨x, hx, hfx⟩]

/-- Every opening point of the claims. -/
def claimPoints {Com : Type} (rounds : List (Claim K Com)) : List (PointOpening K) :=
  rounds.flatMap fun c => c.matrices.flatMap fun m => m.points

theorem mem_claimPoints {Com : Type} {rounds : List (Claim K Com)} {p : PointOpening K} :
    p ∈ claimPoints rounds ↔ ∃ c ∈ rounds, ∃ m ∈ c.matrices, p ∈ m.points := by
  simp [claimPoints]

theorem txResult_total {ME IE α : Type} (r : Except Unit α) : Total (txResult (ME := ME) (IE := IE) r) := by
  rcases r with ⟨⟩ | a <;> total_leaf

theorem replay_total {ME IE Com C S IMP FMP : Type} (tx : CircleVerifierTx K Com S)
    (rounds : List (Claim K C)) (proof : CirclePcsProof K Com IMP FMP) (s : S)
    (hpts : ∀ p ∈ claimPoints rounds, 1 + p.point * p.point ≠ 0) :
    Total (replay_transcript (ME := ME) (IE := IE) tx rounds proof s) := by
  unfold replay_transcript
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (option_mapM_isSome
    (f := fun p : PointOpening K => (Point.from_projective_line p.point).map fun z => (z, p.values))
    (claimPoints rounds) fun p hp => by simp [from_projective_line_eq, hpts p hp])
  rw [show rounds.flatMap (fun c => c.matrices.flatMap fun m => m.points) = claimPoints rounds from rfl,
    lift, hcl, lift_some_bind']
  refine total_bind (txResult_total _) fun _ _ => ?_
  refine total_bind (total_foldlM _ _ fun _ _ _ => total_bind (txResult_total _) fun _ _ => total_pure _)
    fun _ _ => ?_
  exact total_bind (txResult_total _) fun _ _ => total_pure _

theorem replay_panics {ME IE Com C S IMP FMP : Type} (tx : CircleVerifierTx K Com S)
    (rounds : List (Claim K C)) (proof : CirclePcsProof K Com IMP FMP) (s : S)
    (hbad : ∃ p ∈ claimPoints rounds, 1 + p.point * p.point = 0) :
    ¬ Total (replay_transcript (ME := ME) (IE := IE) tx rounds proof s) := by
  unfold replay_transcript
  rw [show rounds.flatMap (fun c => c.matrices.flatMap fun m => m.points) = claimPoints rounds from rfl,
    lift, option_mapM_eq_none (by
      obtain ⟨p, hp, h⟩ := hbad
      exact ⟨p, hp, by simp [from_projective_line_eq, h]⟩), lift_none_bind']
  exact not_total_lift_none

/-- The indices the replay returns are the query phase's. -/
theorem replay_indices {ME IE Com C S IMP FMP : Type} {tx : CircleVerifierTx K Com S}
    {rounds : List (Claim K C)} {proof : CirclePcsProof K Com IMP FMP} {s : S} {r : Replayed K}
    (h : replay_transcript (ME := ME) (IE := IE) tx rounds proof s = pure r) :
    ∃ s' f w s'', tx.query_phase s' f w = .ok (r.indices, s'') := by
  unfold replay_transcript at h
  rw [bind_eq_pure'] at h
  obtain ⟨_, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨r1, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨r3, -, h⟩ := h
  rw [bind_eq_pure'] at h
  obtain ⟨r4, hq, h⟩ := h
  cases pure_inj' h
  refine ⟨r3.2, proof.fri_proof.final_poly, proof.fri_proof.pow_witness, r4.2, ?_⟩
  revert hq
  generalize tx.query_phase r3.2 proof.fri_proof.final_poly proof.fri_proof.pow_witness = e
  rcases e with ⟨⟩ | a
  · intro hq; cases hq
  · intro hq; cases pure_inj' hq; rfl

/-! ## The verifier -/

/-- The query phase draws at most one index per configured query, as the transcript's description fixes. -/
def TxQueries {Com S : Type} (tx : CircleVerifierTx K Com S) (params : FriParameters) : Prop :=
  ∀ s f w r, tx.query_phase s f w = .ok r → r.1.length ≤ params.num_queries

/-- The committed heights of the claims, blowup included. -/
def claimHeights {Com : Type} (lb : ℕ) (rounds : List (Claim K Com)) : List ℕ :=
  rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + lb

/-- The verifier never panics when:

- every claimed domain has at least 2 rows
- every opening point t has 1 + t^2 nonzero. -/
theorem verify_total (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {S : Type} (immcs fmmcs : MmcsOps K)
    (tx : CircleVerifierTx K fmmcs.Commitment S) (params : FriParameters)
    (rounds : List (Claim K immcs.Commitment))
    (proof : CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) (s : S)
    (htx : TxQueries tx params) (hlog : ∀ c ∈ rounds, ∀ m ∈ c.matrices, 1 ≤ m.domain.log_n)
    (hpts : ∀ p ∈ claimPoints rounds, 1 + p.point * p.point ≠ 0) :
    Total (verify G immcs fmmcs tx params rounds proof s) := by
  unfold verify
  rw [show (rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + params.log_blowup) =
    claimHeights params.log_blowup rounds from rfl]
  dsimp only
  rcases hmax : (claimHeights params.log_blowup rounds).max? with _ | H
  · simp only [throw_bind'']; exact total_throw _
  simp only [pure_bind]
  have hH := (List.max?_eq_some_iff.mp hmax).2
  refine total_ite (fun _ => by total_leaf) fun hlb => total_ite (fun _ => by total_leaf) fun had => ?_
  refine total_bind (validate_proof_shape_total _ _ _) fun la hla => ?_
  obtain ⟨rfl, hshape⟩ := validate_proof_shape_spec hla
  refine total_ite (fun _ => by total_leaf) fun _ => ?_
  refine total_bind (replay_total tx rounds proof s hpts) fun r hr => ?_
  obtain ⟨s', f, w, s'', hq⟩ := replay_indices hr
  have hc : ClaimsOK params.log_blowup H rounds :=
    ⟨hlog, fun c hc m hm => hH _ (by simp only [claimHeights, List.mem_flatMap, List.mem_map]; exact ⟨c, hc, m, hm, rfl⟩),
      fun c hc m hm p hp => hpts p (mem_claimPoints.mpr ⟨c, hc, m, hm, hp⟩)⟩
  have hG : H + 1 ≤ G.adicity := by omega
  exact verify_queries_total hV h2 fmmcs params proof.fri_proof r.betas r.indices _ hshape.blowup
    (by omega) hshape.queries hshape.siblings (htx _ _ _ _ hq)
    (open_inputs_total hV h2 immcs fmmcs rounds _ _ _ _ _ _ _ hc hG)
    (fun out hout => open_inputs_desc hV h2 immcs fmmcs hc hG hout)

theorem not_total_bind {ε α β : Type _} {m : ExceptT ε Option α} {k : α → ExceptT ε Option β}
    (h : ¬ Total m) : ¬ Total (m >>= k) := fun h' => h (total_bind_iff.mp h').1

/-- The checks before the transcript all pass:

- some matrix is claimed, and the tallest committed height H lies above the blowup and below the adicity
- the proof's shape check passes
- a zero batching difficulty comes with a zero witness. -/
def PreChecks (G : Gen (K × K)) (immcs fmmcs : MmcsOps K) (params : FriParameters)
    (rounds : List (Claim K immcs.Commitment))
    (proof : CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) : Prop :=
  ∃ H, (claimHeights params.log_blowup rounds).max? = some H ∧ params.log_blowup + 1 ≤ H ∧ H < G.adicity ∧
    (∃ la, validate_proof_shape (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error) params
      proof.fri_proof (H - (params.log_blowup + 1)) = pure la) ∧
    ¬ (params.batch_proof_of_work_bits = 0 ∧ proof.batch_pow_witness ≠ 0)

/-- On claimed domains of at least 2 rows, the verifier panics exactly when:

- the checks before the transcript pass
- some opening point t has t^2 = -1. -/
theorem verify_panics_iff (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {S : Type} (immcs fmmcs : MmcsOps K)
    (tx : CircleVerifierTx K fmmcs.Commitment S) (params : FriParameters)
    (rounds : List (Claim K immcs.Commitment))
    (proof : CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) (s : S)
    (htx : TxQueries tx params) (hlog : ∀ c ∈ rounds, ∀ m ∈ c.matrices, 1 ≤ m.domain.log_n) :
    ¬ Total (verify G immcs fmmcs tx params rounds proof s) ↔
      PreChecks G immcs fmmcs params rounds proof ∧
        ∃ p ∈ claimPoints rounds, 1 + p.point * p.point = 0 := by
  constructor
  · intro hnt
    refine ⟨?_, ?_⟩
    · by_contra hpre
      apply hnt
      unfold verify
      rw [show (rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + params.log_blowup) =
        claimHeights params.log_blowup rounds from rfl]
      dsimp only
      rcases hmax : (claimHeights params.log_blowup rounds).max? with _ | H
      · simp only [throw_bind'']; exact total_throw _
      simp only [pure_bind]
      refine total_ite (fun _ => by total_leaf) fun hlb => total_ite (fun _ => by total_leaf) fun had => ?_
      refine total_bind (validate_proof_shape_total _ _ _) fun la hla => ?_
      refine total_ite (fun _ => by total_leaf) fun hbp => ?_
      exact absurd ⟨H, hmax, by omega, by omega, ⟨la, hla⟩, hbp⟩ hpre
    · by_contra hb
      push Not at hb
      exact hnt (verify_total hV h2 immcs fmmcs tx params rounds proof s htx hlog hb)
  · rintro ⟨⟨H, hmax, hlb, had, ⟨la, hla⟩, hbp⟩, hbad⟩
    unfold verify
    rw [show (rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + params.log_blowup) =
      claimHeights params.log_blowup rounds from rfl]
    dsimp only
    rw [hmax]
    simp only [pure_bind, show ¬ H < params.log_blowup + 1 by omega, show ¬ G.adicity ≤ H - 1 + 1 by omega,
      ↓reduceIte, hla, pure_bind, hbp]
    exact not_total_bind (replay_panics tx rounds proof s hbad)

/-- The lambda correction of a one-row claimed domain panics: its committed height is the blowup, and v_0 is read. -/
theorem firstLayerLeaf_one_row (hV : CircleGenValid G) {lb H : ℕ} (index : ℕ) (hlb : 1 ≤ lb) (hH : lb ≤ H)
    (hG : H + 1 ≤ G.adicity) (ro sib lam : K) :
    firstLayerLeaf G lb H index (((lb, ro), sib), lam) = none := by
  have hpt := standard_nth_point hV (h := lb) hlb (by omega) (cfft_permute_index (index / 2 ^ (H - lb)) lb)
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  unfold firstLayerLeaf
  simp [show lb ≠ 0 by omega, show ¬ H < lb by omega, standard_eq hV _ (by omega : lb + 1 ≤ G.adicity), hpt,
    v_n_ofC]

end Plonky3Lean.Proofs.Circle
