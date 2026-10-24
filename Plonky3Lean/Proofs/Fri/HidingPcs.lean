module

public import P3Fri.HidingPcs
public import Plonky3Lean.Proofs.Fri.Complete
public import Plonky3Lean.Proofs.Fri.Hiding

@[expose] public section

/-!
# The hiding PCS: opening and verification

The prover opens the randomized batch, then moves the last r values of every private point into the proof.

The verifier checks the counts and the hiding budget, then appends the hidden values back.

On honest openings the merge rebuilds the randomized batch exactly.

So the hiding verifier runs the plain verifier on the randomized batch, and nothing else.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.hiding_pcs.mirror p3_commit.pcs.univariate.mirror p3_fri.verifier.mirror p3_fri.mirror
open p3_fri.config.mirror p3_fri.transcript.mirror p3_dft.mirror p3_fri.two_adic_pcs.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-! ## One point -/

/-- The prover's split panics exactly when a point has fewer than k opened values. -/
theorem splitHidden_eq_none (k : ℕ) (vals : List K) : splitHidden k vals = none ↔ vals.length < k := by
  unfold splitHidden; split_ifs with h <;> simp [h]

/-- The verifier's merge of one point undoes the prover's split. -/
theorem mergeHiddenPoint_split {ME IE : Type} {k : ℕ} (z : K) (vals : List K) (hk : k ≤ vals.length) :
    mergeHiddenPoint (ME := ME) (IE := IE) k (⟨z, vals.take (vals.length - k)⟩, vals.drop (vals.length - k)) =
      pure ⟨z, vals⟩ := by
  simp [mergeHiddenPoint, show vals.length - (vals.length - k) = k by omega]

/-- The verifier's merge of one point rejects exactly a hidden part of the wrong count. -/
theorem mergeHiddenPoint_eq {ME IE : Type} (k : ℕ) (p : PointOpening K) (rand : List K) :
    mergeHiddenPoint (ME := ME) (IE := IE) k (p, rand) =
      if rand.length = k then pure ⟨p.point, p.values ++ rand⟩ else throw .HidingRandomOpeningValueCountMismatch := by
  unfold mergeHiddenPoint; split_ifs <;> simp_all

/-! ## The merge never panics -/

theorem total_throw_bind {ME IE α β : Type} (e : FriError ME IE) (k : α → Res ME IE β) :
    Total (throw e >>= k) := total_throw e

theorem mergeHiddenPoint_total {ME IE : Type} (k : ℕ) (x : PointOpening K × List K) :
    Total (mergeHiddenPoint (ME := ME) (IE := IE) k x) := by
  unfold mergeHiddenPoint; split_ifs
  · exact total_throw _
  · exact total_pure _

theorem mergeHiddenMatrix_total {ME IE : Type} (G : Gen K) (q D e : ℕ)
    (x : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List (List K)) :
    Total (mergeHiddenMatrix (ME := ME) (IE := IE) G q D e x) := by
  unfold mergeHiddenMatrix
  dsimp only
  split
  · split_ifs
    all_goals first
      | exact total_throw_bind _ _
      | exact total_bind (total_mapM (mergeHiddenPoint_total e) _) fun _ _ => total_pure _
  · exact total_throw_bind _ _

/-- The verifier's merge returns or rejects, and never panics. -/
theorem mergeHidden_total {ME IE : Type} (G : Gen K) {C : Type} (q D r : ℕ) (pre : Option ℕ)
    (claims : List (Claim G C)) (rand : List (List (List (List K)))) :
    Total (mergeHidden (ME := ME) (IE := IE) G q D r pre claims rand) := by
  have hround : ∀ x : (Claim G C × List (List (List K))) × ℕ,
      Total (mergeHiddenRound (ME := ME) (IE := IE) G q D r pre x) := by
    intro x
    unfold mergeHiddenRound
    dsimp only
    split_ifs
    all_goals first
      | exact total_throw_bind _ _
      | exact total_bind (total_mapM (mergeHiddenMatrix_total G q D _) _) fun _ _ => total_pure _
  unfold mergeHidden
  dsimp only
  split
  · split_ifs
    all_goals first | exact total_throw_bind _ _ | exact total_mapM hround _
  · split_ifs
    all_goals first | exact total_throw_bind _ _ | exact total_mapM hround _

/-- The hiding verifier never panics at safe difficulties:

- the three difficulties are safe for the field order p
- 2^h < p for the adicity h, with h < 64. -/
theorem verify_hiding_total (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) (g : K) {C S : Type}
    (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S) (params : FriParameters) (D r : ℕ)
    (pre : Option ℕ) (claims : List (Claim G C)) (rand : List (List (List (List K))))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment)
    (hb : PowSafe sp.order params.batch_proof_of_work_bits)
    (hc : PowSafe sp.order params.commit_proof_of_work_bits) (hq : PowSafe sp.order params.query_proof_of_work_bits)
    (hG : G.adicity < 64 ∧ 2 ^ G.adicity < sp.order) :
    Total (verify_hiding G g fmmcs immcs sp params D r pre claims rand proof s commit_of) :=
  total_bind (mergeHidden_total G _ D r pre claims rand) fun merged _ =>
    verify_total G hV h2 g fmmcs immcs sp params merged proof s commit_of hb hc hq hG

/-! ## The hiding verifier is the plain verifier on the merged batch -/

/-- Once the merge returns a batch, the hiding verifier is the plain verifier on that batch. -/
theorem verify_hiding_of_merge (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
    (sp : Sponge K fmmcs.Commitment S) (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (claims : List (Claim G C)) (rand : List (List (List (List K))))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) {merged : List (Claim G C)}
    (h : mergeHidden (ME := fmmcs.Error) (IE := immcs.Error) G params.num_queries D r pre claims rand =
      pure merged) :
    verify_hiding G g fmmcs immcs sp params D r pre claims rand proof s commit_of =
      verify G g fmmcs immcs sp params merged proof s commit_of := by
  rw [verify_hiding, h, pure_bind]

/-- The number of hidden values of every point of round idx: none for the trusted preprocessed round, r otherwise. -/
def hiddenCount (r : ℕ) (pre : Option ℕ) (idx : ℕ) : ℕ := if pre = some idx then 0 else r

/-- The prover's split of a batch: the public openings, and the hidden values of every point. -/
def hideClaims {G : Gen K} {C : Type} (r : ℕ) (pre : Option ℕ) (full : List (Claim G C)) :
    List (Claim G C) × List (List (List (List K))) :=
  (full.zipIdx.map fun e => ⟨e.1.commitment, e.1.matrices.map fun m => ⟨m.domain, m.points.map fun p =>
      ⟨p.point, p.values.take (p.values.length - hiddenCount r pre e.2)⟩⟩⟩,
    full.zipIdx.map fun e => e.1.matrices.map fun m => m.points.map fun p =>
      p.values.drop (p.values.length - hiddenCount r pre e.2))

theorem mapM_map_eq_pure {ε α β γ : Type _} {f : β → ExceptT ε Option γ} {F : α → β} {g : α → γ} :
    ∀ (l : List α), (∀ x ∈ l, f (F x) = pure (g x)) → (l.map F).mapM f = pure (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.mapM_cons, h x List.mem_cons_self, pure_bind,
      mapM_map_eq_pure l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem zipIdx_zip_map {α β γ : Type _} (f : α × ℕ → β) (g : α × ℕ → γ) :
    ∀ (l : List α) (n : ℕ), (List.zip ((l.zipIdx n).map f) ((l.zipIdx n).map g)).zipIdx n =
      (l.zipIdx n).map fun e => ((f e, g e), e.2)
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.zipIdx_cons, List.map_cons, List.zip_cons_cons]
    exact congrArg _ (zipIdx_zip_map f g l (n + 1))

/-- On an honest split, the merge rebuilds the batch.

This needs four facts:

- the preprocessing index, if any, names a round
- there are at least D random codewords
- every matrix's claimed domain meets the hiding budget
- every point holds at least its hidden count of values. -/
theorem mergeHidden_hideClaims {ME IE : Type} (G : Gen K) {C : Type} (q D r : ℕ) (pre : Option ℕ)
    (full : List (Claim G C)) (hpre : ∀ i, pre = some i → i < full.length) (hD : D ≤ r)
    (hbud : ∀ c ∈ full, ∀ m ∈ c.matrices, ∃ req, hiding_budget q D m.points.length = some req ∧
      req ≤ m.domain.size / 2)
    (hlen : ∀ e ∈ full.zipIdx, ∀ m ∈ e.1.matrices, ∀ p ∈ m.points, hiddenCount r pre e.2 ≤ p.values.length) :
    mergeHidden (ME := ME) (IE := IE) G q D r pre (hideClaims r pre full).1 (hideClaims r pre full).2 =
      pure full := by
  -- The rounds merge one by one back into the batch.
  have hrounds : ((hideClaims r pre full).1.zip (hideClaims r pre full).2).zipIdx.mapM
      (mergeHiddenRound (ME := ME) (IE := IE) G q D r pre) = pure full := by
    unfold hideClaims
    rw [zipIdx_zip_map, mapM_map_eq_pure (g := Prod.fst) _ ?_, List.zipIdx_map_fst]
    rintro ⟨c, idx⟩ he
    have hmem : c ∈ full := by
      rw [(List.mem_zipIdx' he).2]
      exact List.getElem_mem _
    simp only [mergeHiddenRound, List.length_map, ne_eq, not_true_eq_false, ↓reduceIte, List.zip_map']
    rw [mapM_map_eq_pure (g := id) _ fun m hm => ?_]
    · simp
    obtain ⟨req, hreq, hle⟩ := hbud c hmem m hm
    simp only [mergeHiddenMatrix, List.length_map, hreq, show ¬ m.domain.size / 2 < req by omega, ↓reduceIte,
      ne_eq, not_true_eq_false, List.zip_map']
    rw [mapM_map_eq_pure (g := id) _ fun p hp => ?_]
    · simp
    exact mergeHiddenPoint_split p.point p.values (hlen (c, idx) he m hm p hp)
  have hlen12 : ∀ p', (hideClaims r p' full).2.length = (hideClaims r p' full).1.length := fun _ => by
    simp [hideClaims]
  have hlen1 : ∀ p', (hideClaims r p' full).1.length = full.length := fun _ => by simp [hideClaims]
  unfold mergeHidden
  dsimp only
  rcases hp : pre with _ | i
  · simp only [show ¬ r < D by omega, ↓reduceIte]
    split_ifs with h2
    · exact absurd (hlen12 _) h2
    · rw [← hp]; exact hrounds
  · have := hpre i hp
    simp only [show ¬ r < D by omega, ↓reduceIte]
    split_ifs with h1 h2 h2
    · have := hlen1 (some i); omega
    · have := hlen1 (some i); omega
    · exact absurd (hlen12 _) h2
    · rw [← hp]; exact hrounds

/-- On an honest split, the hiding verifier is exactly the plain verifier on the randomized batch. -/
theorem verify_hiding_hideClaims (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
    (sp : Sponge K fmmcs.Commitment S) (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (full : List (Claim G C)) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) (hpre : ∀ i, pre = some i → i < full.length) (hD : D ≤ r)
    (hbud : ∀ c ∈ full, ∀ m ∈ c.matrices, ∃ req, hiding_budget params.num_queries D m.points.length = some req ∧
      req ≤ m.domain.size / 2)
    (hlen : ∀ e ∈ full.zipIdx, ∀ m ∈ e.1.matrices, ∀ p ∈ m.points, hiddenCount r pre e.2 ≤ p.values.length) :
    verify_hiding G g fmmcs immcs sp params D r pre (hideClaims r pre full).1 (hideClaims r pre full).2 proof s
      commit_of = verify G g fmmcs immcs sp params full proof s commit_of :=
  verify_hiding_of_merge G g fmmcs immcs sp params D r pre _ _ proof s commit_of
    (mergeHidden_hideClaims G _ D r pre full hpre hD hbud hlen)

/-- Completeness of the hiding verifier.

When the plain verifier accepts the randomized batch, the hiding verifier accepts its honest split. -/
theorem verify_hiding_complete (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
    (sp : Sponge K fmmcs.Commitment S) (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (full : List (Claim G C)) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) (hpre : ∀ i, pre = some i → i < full.length) (hD : D ≤ r)
    (hbud : ∀ c ∈ full, ∀ m ∈ c.matrices, ∃ req, hiding_budget params.num_queries D m.points.length = some req ∧
      req ≤ m.domain.size / 2)
    (hlen : ∀ e ∈ full.zipIdx, ∀ m ∈ e.1.matrices, ∀ p ∈ m.points, hiddenCount r pre e.2 ≤ p.values.length)
    (hfull : verify G g fmmcs immcs sp params full proof s commit_of = pure ()) :
    verify_hiding G g fmmcs immcs sp params D r pre (hideClaims r pre full).1 (hideClaims r pre full).2 proof s
      commit_of = pure () := by
  rw [verify_hiding_hideClaims G g fmmcs immcs sp params D r pre full proof s commit_of hpre hD hbud hlen, hfull]

/-! ## Edge cases -/

/-- Zero random codewords are rejected by the verifier, once a preprocessing index names a round. -/
theorem mergeHidden_zero_codewords {ME IE : Type} (G : Gen K) {C : Type} (q D : ℕ) (hD : 0 < D) (pre : Option ℕ)
    (claims : List (Claim G C)) (rand : List (List (List (List K))))
    (hpre : ∀ i, pre = some i → i < claims.length) :
    mergeHidden (ME := ME) (IE := IE) G q D 0 pre claims rand = throw .InsufficientHidingRandomCodewords := by
  unfold mergeHidden
  dsimp only
  rcases hp : pre with _ | i
  · simp [hD]
  · have := hpre i hp
    simp [show ¬ claims.length ≤ i by omega, hD]

/-- Zero random codewords are rejected by the prover's budget check too. -/
theorem check_hiding_budget_zero_codewords (q mask D n : ℕ) (hD : 0 < D) :
    check_hiding_budget 0 q mask D n = .error (.InsufficientRandomCodewords D 0) := by
  simp [check_hiding_budget, hD]

/-- The required mask is at least 2 D, so at least 2. -/
theorem hiding_budget_ge {q D n req : ℕ} (h : hiding_budget q D n = some req) : 2 * D ≤ req := by
  unfold hiding_budget at h
  dsimp only at h
  split_ifs at h
  obtain rfl := (Option.some.inj h).symm
  have : D ≤ D * max n 1 := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- A matrix whose claimed domain is too small for the budget is rejected.

A domain of 1 or 2 points has a mask of at most one value, below the minimum budget of 2 D. -/
theorem mergeHiddenMatrix_small {ME IE : Type} (G : Gen K) (q D e : ℕ) (hD : 0 < D)
    (m : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen)) (rm : List (List K))
    (hm : m.domain.log_size ≤ 1) :
    mergeHiddenMatrix (ME := ME) (IE := IE) G q D e (m, rm) = throw .HidingBudgetExceeded := by
  have hmask : m.domain.size / 2 ≤ 1 := by
    simp only [p3_field.coset.mirror.TwoAdicMultiplicativeCoset.size]
    interval_cases h : m.domain.log_size <;> simp
  unfold mergeHiddenMatrix
  dsimp only
  rcases hb : hiding_budget q D m.points.length with _ | req
  · rfl
  · have := hiding_budget_ge hb
    simp only [show m.domain.size / 2 < req by omega, ↓reduceIte]
    rfl

/-- Blinding a one-row trace is refused at commit: one mask value is below the budget. -/
theorem check_hiding_budget_one_row (r q D : ℕ) (hD : 0 < D) (hr : D ≤ r) {req : ℕ}
    (hb : hiding_budget q D 1 = some req) :
    check_hiding_budget r q 1 D 1 = .error (.HidingBudgetExceeded 1 q 1 D) := by
  have := hiding_budget_ge hb
  simp only [check_hiding_budget, show ¬ r < D by omega, ↓reduceIte, hb, show 1 < req by omega]

/-! ## The opening -/

theorem option_mapM_eq_some {α β : Type _} {f : α → Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, option_mapM_eq_some l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem option_mapM_eq_none {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {x : α}, x ∈ l → f x = none → l.mapM f = none
  | y :: l, x, hx, hf => by
    rw [List.mapM_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hf]; rfl
    · rcases f y with _ | b
      · rfl
      · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        rw [option_mapM_eq_none hx hf]; rfl

/-- The opening returns the split of the inner opening when:

- every round passes its checks
- no private round was already opened
- the inner opening returns
- every point holds at least its hidden count of values.

Every private round is then marked opened. -/
theorem open_hiding_ok {P : Type} (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (rounds : List (HidingRound K)) (values : List (List (List (List K)))) (proof : P)
    (hchk : checkHidingRounds params D r pre rounds = some (.ok ()))
    (hopen : rounds.any (fun rd => !rd.preprocessed && rd.opened) = false)
    (hlen : ∀ e ∈ values.zipIdx, ∀ vm ∈ e.1, ∀ vp ∈ vm, hiddenCount r pre e.2 ≤ vp.length) :
    open_hiding params D r pre rounds (some (.ok (values, proof))) =
      some (.ok ((values.zipIdx.map fun e => e.1.map (·.map fun vp => vp.take (vp.length - hiddenCount r pre e.2)),
        values.zipIdx.map fun e => e.1.map (·.map fun vp => vp.drop (vp.length - hiddenCount r pre e.2)),
        proof), rounds.map fun rd => rd.opened || !rd.preprocessed)) := by
  have hsplit : values.zipIdx.mapM (fun e => e.1.mapM fun vm => vm.mapM fun vp =>
      splitHidden (if pre = some e.2 then 0 else r) vp) =
      some (values.zipIdx.map fun e => e.1.map (·.map fun vp =>
        (vp.take (vp.length - hiddenCount r pre e.2), vp.drop (vp.length - hiddenCount r pre e.2)))) := by
    refine option_mapM_eq_some _ fun e he => option_mapM_eq_some _ fun vm hvm =>
      option_mapM_eq_some _ fun vp hvp => ?_
    have := hlen e he vm hvm vp hvp
    simp only [hiddenCount] at this ⊢
    simp [splitHidden, show ¬ vp.length < (if pre = some e.2 then 0 else r) by omega]
  unfold open_hiding
  simp only [hchk, Option.bind_eq_bind, Option.bind_some, hopen, Bool.false_eq_true, ↓reduceIte, hsplit,
    List.map_map, Function.comp_def]

/-- The opening panics when a private round was already opened, once every round passes its checks. -/
theorem open_hiding_reopened {P : Type} (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (rounds : List (HidingRound K)) (inner : Option (Except FriProverError (List (List (List (List K))) × P)))
    (hchk : checkHidingRounds params D r pre rounds = some (.ok ()))
    (hopen : rounds.any (fun rd => !rd.preprocessed && rd.opened) = true) :
    open_hiding params D r pre rounds inner = none := by
  unfold open_hiding
  simp only [hchk, Option.bind_eq_bind, Option.bind_some, hopen, ↓reduceIte]

/-- The opening panics when a point holds fewer values than its hidden count, once everything before passes. -/
theorem open_hiding_short {P : Type} (params : FriParameters) (D r : ℕ) (pre : Option ℕ)
    (rounds : List (HidingRound K)) (values : List (List (List (List K)))) (proof : P)
    (hchk : checkHidingRounds params D r pre rounds = some (.ok ()))
    (hopen : rounds.any (fun rd => !rd.preprocessed && rd.opened) = false)
    {e : List (List (List K)) × ℕ} (he : e ∈ values.zipIdx) {vm : List (List K)} (hvm : vm ∈ e.1)
    {vp : List K} (hvp : vp ∈ vm) (hshort : vp.length < hiddenCount r pre e.2) :
    open_hiding params D r pre rounds (some (.ok (values, proof))) = none := by
  have hsplit : values.zipIdx.mapM (fun e => e.1.mapM fun vm => vm.mapM fun vp =>
      splitHidden (if pre = some e.2 then 0 else r) vp) = none := by
    refine option_mapM_eq_none he ?_
    refine option_mapM_eq_none hvm ?_
    refine option_mapM_eq_none hvp ?_
    simp only [hiddenCount] at hshort
    simp [splitHidden, hshort]
  unfold open_hiding
  simp only [hchk, Option.bind_eq_bind, Option.bind_some, hopen, Bool.false_eq_true, ↓reduceIte, hsplit,
    Option.bind_none]

end Plonky3Lean.Proofs.Fri
