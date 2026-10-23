/-
Transcriptions of the FRI verifier: the fold chain of one query, the input openings and their reduction, and verify_fri.

What a transcription abstracts, beyond Fold.lean and Types.lean:

* the folding strategy is the two-adic one, which samples no extra index bits;
* the field's generator is a parameter g, and a claimed domain is a coset over the generator table G;
* an ordered map keyed by height is a function of the height, read at the keys present, tallest first;
* the denominators are inverted one at a time, in the order the batch inversion consumes them;
* a usize is a natural number, and a shift by at least 64 bits fails;
* an assertion panics, and a debug assertion is checked, as in a debug build;
* a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Fri.Config
public import P3Fri.Fold
public import P3Fri.Types
public import P3Commit.Domain

@[expose] public section

namespace p3_fri.verifier.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror p3_fri.mirror p3_fri.config.mirror
open p3_fri.two_adic_pcs.mirror p3_field.coset.mirror

variable {K : Type} [Field K] [DecidableEq K]

/-- The verifier's rejections, without their payloads. -/
inductive FriError (ME IE : Type) where
  | CommitPhaseOpeningsCountMismatch
  | CommitRoundCountMismatch
  | CommitPhaseQueryCountMismatch
  | InputOpeningsQueryCountMismatch
  | CommitPowWitnessCountMismatch
  | FinalPolyLengthMismatch
  | ZeroQueries
  | NoCommittedMatrices
  | ZeroFoldingArity
  | ZeroBlowup
  | MissingInitialReducedOpening
  | InitialReducedOpeningHeightMismatch
  | GlobalMaxHeightTooLarge
  | SiblingValuesLengthMismatch
  | FinalFoldHeightMismatch
  | FoldScheduleArityOutOfRange
  | FoldScheduleTooLong
  | UnconsumedReducedOpenings
  | InputProofBatchCountMismatch
  | BatchOpenedValuesCountMismatch
  | MatrixWithoutOpeningPoints
  | PointEvaluationCountMismatch
  | CommitPhaseMmcsError (e : ME)
  | InputError (e : IE)
  | FinalPolyMismatch
  | InvalidPowWitness
  | NonCanonicalPowWitness
  | OpeningPointMatchesQueryPoint

/-- The transcript's rejections, as the verifier reports them. -/
def FriError.ofTranscript {ME IE : Type} : TranscriptFailure → FriError ME IE
  | .PowWitness | .MissingPowWitness => .InvalidPowWitness
  | .FinalPolyLen _ _ => .FinalPolyLengthMismatch
  | .CommitRoundCount _ _ => .CommitRoundCountMismatch
  | .CommitPowWitnessCount _ _ => .CommitPowWitnessCountMismatch

/-- The outcome of a verifier step: a panic is none, a rejection an error. -/
abbrev Res (ME IE : Type) := ExceptT (FriError ME IE) Option

/-- A panic. -/
def crash {ME IE α : Type} : Res ME IE α := ExceptT.lift none

/-- A value that may panic, read into a verifier step. -/
def lift {ME IE α : Type} (o : Option α) : Res ME IE α := ExceptT.lift o

/-- The claims about one input commitment, over cosets of the table G. -/
abbrev Claim (G : Gen K) (C : Type) := CommitmentOpening K C (TwoAdicMultiplicativeCoset K G.adicity G.gen)

/-- At zero difficulty a witness must be zero. -/
def check_canonical_pow_witnesses {C MP IMP : Type} (params : FriParameters) (proof : FriProof K C MP IMP) : Bool :=
  !(params.batch_proof_of_work_bits = 0 && proof.batch_pow_witness ≠ 0) &&
  !(params.commit_proof_of_work_bits = 0 && proof.commit_pow_witnesses.any (· ≠ 0)) &&
  !(params.query_proof_of_work_bits = 0 && proof.query_pow_witness ≠ 0)

/-- Rebuild a row of 2^log_arity values: the folded value at index_in_group, the siblings elsewhere in order. -/
def rebuildRow (arity index_in_group : ℕ) (folded : K) (siblings : List K) : List K :=
  (List.range arity).map fun j =>
    if j = index_in_group then folded
    else siblings.getD (if j < index_in_group then j else j - 1) 0

/-- The state of the fold chain: the index, the folded value, the height, the openings left, and each round's group index and row. -/
abbrev ChainState (K : Type) := ℕ × K × ℕ × List (ℕ × K) × List (ℕ × List K)

/-- One round of the fold chain: rebuild the row, shift the index, fold, record the group and row, and roll in an opening at the folded height. -/
def foldStep (G : Gen K) (query : ℕ) (st : ChainState K) (round : K × ℕ × List (List K)) :
    Option (ChainState K) := do
  let (index, folded_eval, log_current_height, ro, recorded) := st
  let (beta, log_arity, sibling_values) := round
  let arity := 2 ^ log_arity
  let siblings ← sibling_values[query]?
  let evals := rebuildRow arity (index % arity) folded_eval siblings
  let log_folded_height := log_current_height - log_arity
  let index' := index / arity
  let folded ← fold_row G index' log_folded_height log_arity beta evals
  let recorded' := recorded ++ [(index', evals)]
  match ro with
  | (lh, v) :: ro' =>
    if lh = log_folded_height then
      some (index', folded + beta ^ 2 ^ log_arity * v, log_folded_height, ro', recorded')
    else some (index', folded, log_folded_height, ro, recorded')
  | [] => some (index', folded, log_folded_height, [], recorded')

/-- A round whose opening misses the query or has the wrong sibling count. -/
def badRound (query : ℕ) (e : List (List K) × ℕ) : Bool :=
  match e.1[query]? with
  | none => true
  | some s => s.length ≠ 2 ^ e.2 - 1

/-- Check the schedule and the opened shapes, start from the opening at the tallest height, fold every round, and check the final height and that every opening was rolled in.

It returns the folded value, the final index, and each round's group index and rebuilt row. -/
def fold_query {ME IE : Type} (G : Gen K) (query start_index : ℕ) (betas : List K) (log_arities : List ℕ)
    (sibling_values : List (List (List K))) (reduced_openings : List (ℕ × K))
    (log_global_max_height log_final_height : ℕ) : Res ME IE (K × ℕ × List (ℕ × List K)) := do
  if log_arities.any (fun la => la = 0 ∨ 64 ≤ la) then throw .FoldScheduleArityOutOfRange
  match (sibling_values.zip log_arities).find? (badRound query) with
  | some (sv, _) =>
    if sv[query]?.isNone then throw .CommitPhaseQueryCountMismatch
    else throw .SiblingValuesLengthMismatch
  | none => pure ()
  if log_global_max_height - log_final_height < log_arities.sum then throw .FoldScheduleTooLong
  let (lh, v, ro) ← match reduced_openings with
    | [] => throw .MissingInitialReducedOpening
    | (lh, v) :: ro => pure (lh, v, ro)
  if lh ≠ log_global_max_height then throw .InitialReducedOpeningHeightMismatch
  let (index, folded, log_h, ro', recorded) ← lift <|
    (List.zip betas (List.zip log_arities sibling_values)).foldlM (foldStep G query)
      (start_index, v, log_global_max_height, ro, [])
  if log_h ≠ log_final_height then throw .FinalFoldHeightMismatch
  if ro' ≠ [] then throw .UnconsumedReducedOpenings
  pure (folded, index, recorded)

/-- The points of the claims, flattened in batch, matrix, point order, each with its matrix's log height. -/
def openingPoints {G : Gen K} {C : Type} (log_blowup : ℕ) (claims : List (Claim G C)) :
    List (ℕ × PointOpening K) :=
  claims.flatMap fun c => c.matrices.flatMap fun m =>
    m.points.map fun p => (m.domain.log_size + log_blowup, p)

/-- The ladder start of each opening point: the number of claimed values at its height before it. -/
def ladderOffsets (pts : List (ℕ × PointOpening K)) : List ℕ :=
  (pts.foldl (fun (st : (ℕ → ℕ) × List ℕ) e =>
    (Function.update st.1 e.1 (st.1 e.1 + e.2.values.length), st.2 ++ [st.1 e.1])) (fun _ => 0, [])).2

/-- The query point of a matrix of log height h at a global index: g G_h^rev_h(index >> (H - h)). -/
def queryPoint (G : Gen K) (g : K) (log_global_max_height log_height index : ℕ) : Option K := do
  let w ← G.get log_height
  some (g * w ^ bitRev log_height (index / 2 ^ (log_global_max_height - log_height)))

/-- The contribution of one point: the sum over the columns of alpha^(off + i) (y_i - p_i(x)), over z - x. -/
def pointTerm (alpha x : K) (off : ℕ) (p : PointOpening K) (row : List K) : K :=
  (((List.range p.values.length).map fun i => alpha ^ (off + i) * p.values.getD i 0).sum -
    ((List.range row.length).map fun i => alpha ^ (off + i) * row.getD i 0).sum) * (p.point - x)⁻¹

/-- The running state of one query's reduction: the value at each height, the heights seen in order, and the ladder starts left. -/
abbrev RedState (K : Type) := (ℕ → K) × List ℕ × List ℕ

/-- One matrix of one query: every point of the matrix adds its term at the matrix's height. -/
def reduceMatrix {ME IE : Type} (G : Gen K) (g : K) (log_blowup log_global_max_height : ℕ) (alpha : K)
    (index : ℕ) (st : RedState K) (mr : MatrixOpening K (TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K) :
    Res ME IE (RedState K) := do
  let (acc, keys, offs) := st
  let (m, row) := mr
  let h := m.domain.log_size + log_blowup
  let x ← lift (queryPoint G g log_global_max_height h index)
  let keys' := if h ∈ keys then keys else keys ++ [h]
  let (acc', offs') ← m.points.foldlM (fun (st2 : (ℕ → K) × List ℕ) p => do
      let (acc2, offs2) := st2
      if row.length ≠ p.values.length then throw .PointEvaluationCountMismatch
      if p.point - x = 0 then throw .OpeningPointMatchesQueryPoint
      pure (Function.update acc2 h (acc2 h + pointTerm alpha x (offs2.headD 0) p row), offs2.drop 1))
    (acc, offs)
  pure (acc', keys', offs')

/-- One query's reduced openings, tallest height first.

A nonzero value at the blowup height is rejected. -/
def reduceQuery {ME IE : Type} (G : Gen K) (g : K) {C : Type} (log_blowup log_global_max_height : ℕ)
    (alpha : K) (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) :
    Res ME IE (List (ℕ × K)) := do
  let offs := ladderOffsets (openingPoints log_blowup claims)
  let mats := (claims.zip rows).flatMap fun cr => cr.1.matrices.zip cr.2
  let (acc, keys, _) ← mats.foldlM (reduceMatrix G g log_blowup log_global_max_height alpha index)
    (fun _ => 0, [], offs)
  if log_blowup ∈ keys ∧ acc log_blowup ≠ 0 then throw .FinalPolyMismatch
  pure ((keys.mergeSort (fun a b => decide (b ≤ a))).map fun h => (h, acc h))

/-- The shape checks and the shared opening check of one input batch. -/
def checkBatch {ME : Type} (G : Gen K) {C : Type} (mmcs : MmcsOps K) (log_blowup log_global_max_height : ℕ)
    (indices : List ℕ) (commit_of : C → mmcs.Commitment)
    (bc : BatchMultiOpening K mmcs.MultiProof × Claim G C) : Res ME mmcs.Error Unit := do
  let (bo, c) := bc
  if bo.opened_values.length ≠ indices.length then throw .InputOpeningsQueryCountMismatch
  if bo.opened_values.any (·.length ≠ c.matrices.length) then throw .BatchOpenedValuesCountMismatch
  if c.matrices.any (·.points = []) then throw .MatrixWithoutOpeningPoints
  let heights := c.matrices.map fun m => 2 ^ m.domain.log_size * 2 ^ log_blowup
  let dims := c.matrices.map fun m => ((m.points.headD ⟨0, []⟩).values.length,
    2 ^ m.domain.log_size * 2 ^ log_blowup)
  let reduced := match heights.max? with
    | some h => indices.map (· / 2 ^ (log_global_max_height - Nat.log 2 h))
    | none => indices.map fun _ => 0
  match mmcs.verify_multi_batch (commit_of c.commitment) dims reduced bo.opened_values bo.opening_proof with
  | .error e => throw (.InputError e)
  | .ok () => pure ()

/-- The denominators of every query, batch, matrix and point, before any is inverted: a zero rejects. -/
def checkDenominators {ME IE : Type} (G : Gen K) (g : K) {C : Type} (log_blowup log_global_max_height : ℕ)
    (indices : List ℕ) (claims : List (Claim G C)) : Res ME IE Unit :=
  indices.forM fun index => claims.forM fun c => c.matrices.forM fun m => do
    let x ← lift (queryPoint G g log_global_max_height (m.domain.log_size + log_blowup) index)
    m.points.forM fun p => if p.point - x = 0 then throw .OpeningPointMatchesQueryPoint else pure ()

/-- The batch count, every batch's checks, the denominators, then every query's reduced openings. -/
def open_inputs {ME : Type} (G : Gen K) (g : K) {C : Type} (mmcs : MmcsOps K) (log_blowup log_global_max_height : ℕ)
    (indices : List ℕ) (input_openings : List (BatchMultiOpening K mmcs.MultiProof)) (alpha : K)
    (claims : List (Claim G C)) (commit_of : C → mmcs.Commitment) :
    Res ME mmcs.Error (List (List (ℕ × K))) := do
  if input_openings.length ≠ claims.length then throw .InputProofBatchCountMismatch
  (input_openings.zip claims).forM (checkBatch G mmcs log_blowup log_global_max_height indices commit_of)
  checkDenominators G g log_blowup log_global_max_height indices claims
  indices.zipIdx.mapM fun e =>
    reduceQuery G g log_blowup log_global_max_height alpha claims
      (input_openings.map fun bo => bo.opened_values.getD e.2 []) e.1

/-- The input log heights the claims imply, tallest first, without repeats. -/
def inputLogHeights {G : Gen K} {C : Type} (log_blowup : ℕ) (claims : List (Claim G C)) : List ℕ :=
  ((claims.flatMap fun c => c.matrices.map fun m => m.domain.log_size + log_blowup).mergeSort
    (fun a b => decide (b ≤ a))).dedup

/-- The evaluation of a coefficient list at x, constant term first. -/
def horner (coeffs : List K) (x : K) : K := coeffs.foldr (fun c acc => acc * x + c) 0

/-- One query: its fold chain, then the final polynomial at x = G_H^rev_H(final index). -/
def checkQuery {ME IE : Type} (G : Gen K) (betas : List K) (log_arities : List ℕ)
    (sibling_values : List (List (List K))) (final_poly : List K) (log_global_max_height log_final_height : ℕ)
    (e : (ℕ × List (ℕ × K)) × ℕ) : Res ME IE (List (ℕ × List K)) := do
  let (folded, domain_index, recorded) ← fold_query G e.2 e.1.1 betas log_arities sibling_values e.1.2
    log_global_max_height log_final_height
  let gH ← lift (G.get log_global_max_height)
  if horner final_poly (gH ^ bitRev log_global_max_height domain_index) ≠ folded then
    throw .FinalPolyMismatch
  pure recorded

/-- The shared check of one round over every query's group index and row, descending one round's arity. -/
def checkRound {IE : Type} (fmmcs : MmcsOps K) (recorded : List (List (ℕ × List K))) (log_current_height : ℕ)
    (e : (fmmcs.Commitment × CommitPhaseMultiStep K fmmcs.MultiProof × ℕ) × ℕ) :
    Res fmmcs.Error IE ℕ := do
  let ((commit, opening, log_arity), round) := e
  let log_folded_height := log_current_height - log_arity
  let groups := recorded.map fun rs => (rs.getD round (0, [])).1
  let rows := recorded.map fun rs => [(rs.getD round (0, [])).2]
  match fmmcs.verify_multi_batch commit [(2 ^ log_arity, 2 ^ log_folded_height)] groups rows
      opening.opening_proof with
  | .error err => throw (.CommitPhaseMmcsError err)
  | .ok () => pure log_folded_height

/-- The input checks, run with the commit-phase scheme's error type. -/
def open_inputs' (G : Gen K) (g : K) {C : Type} (fmmcs immcs : MmcsOps K) (log_blowup log_global_max_height : ℕ)
    (indices : List ℕ) (input_openings : List (BatchMultiOpening K immcs.MultiProof)) (alpha : K)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) :
    Res fmmcs.Error immcs.Error (List (List (ℕ × K))) :=
  open_inputs G g immcs log_blowup log_global_max_height indices input_openings alpha claims commit_of

/-- The full verifier.

It rejects vacuous instances, derives the shape, checks the proof's lengths, and replays the transcript.
Then it checks the input openings, each query's fold chain and final value, and every round's openings. -/
def verify_fri (G : Gen K) (g : K) {C S : Type} (fmmcs : MmcsOps K) (immcs : MmcsOps K)
    (tx : VerifierTx K fmmcs.Commitment S) (params : FriParameters)
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) :
    Res fmmcs.Error immcs.Error Unit := do
  if params.num_queries = 0 then throw .ZeroQueries
  if params.log_blowup = 0 then throw .ZeroBlowup
  if params.max_log_arity = 0 then throw .ZeroFoldingArity
  if claims.all (·.matrices = []) then throw .NoCommittedMatrices
  let heights := inputLogHeights params.log_blowup claims
  let log_global_max_height := heights.headD 0
  if G.adicity < log_global_max_height then throw .GlobalMaxHeightTooLarge
  let log_arities ← lift (fold_schedule heights (params.log_blowup + params.log_final_poly_len)
    params.max_log_arity)
  if proof.commit_phase_openings.length ≠ log_arities.length then throw .CommitPhaseOpeningsCountMismatch
  match (proof.commit_phase_openings.zip log_arities).find? (fun e =>
      e.1.sibling_values.length ≠ params.num_queries ∨
        e.1.sibling_values.any (·.length ≠ 2 ^ e.2 - 1)) with
  | some e =>
    if e.1.sibling_values.length ≠ params.num_queries then throw .CommitPhaseQueryCountMismatch
    else throw .SiblingValuesLengthMismatch
  | none => pure ()
  if ¬ check_canonical_pow_witnesses params proof then throw .NonCanonicalPowWitness
  if proof.final_poly.length ≠ params.final_poly_len then throw .FinalPolyLengthMismatch
  let (betas, s1) ← match tx.commit_rounds s proof.commit_phase_commits proof.commit_pow_witnesses with
    | .error f => throw (.ofTranscript f)
    | .ok r => pure r
  let (indices, _) ← match tx.query_phase s1 proof.final_poly (some proof.query_pow_witness) with
    | .error f => throw (.ofTranscript f)
    | .ok r => pure r
  let log_final_height := params.log_blowup + params.log_final_poly_len
  let reduced_openings ← open_inputs' G g fmmcs immcs params.log_blowup log_global_max_height indices
    proof.input_openings alpha claims commit_of
  let sibling_values := proof.commit_phase_openings.map (·.sibling_values)
  let recorded ← ((indices.zip reduced_openings).zipIdx).mapM
    (checkQuery G betas log_arities sibling_values proof.final_poly log_global_max_height log_final_height)
  let _ ← ((proof.commit_phase_commits.zip (proof.commit_phase_openings.zip log_arities)).zipIdx).foldlM
    (checkRound fmmcs recorded) log_global_max_height
  pure ()

end p3_fri.verifier.mirror
