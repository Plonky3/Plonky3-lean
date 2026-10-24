/-
Transcriptions of the circle PCS verifier: the replayed transcript, the input openings, the DEEP quotients, the first-layer fold, and the circle FRI checks.

What a transcription abstracts, beyond the models of the points, the domains, the DEEP quotient and the circle FRI verifier:

- the base field and its extension are one mathlib field K, base values read through their embedding
- the input and the first-layer commitment schemes' methods are fields of records, as in p3-fri's model
- the transcript is a record of its four phases, with explicit state, each returning its challenge or a rejected witness
- the transcript's description is left out: the run follows it, since both come from the same claims
- the circle two-adicity is the adicity of the generator table
- an ordered map keyed by height is a function of the height and its list of keys, read in increasing order
- a matrix's height 2^log_n shifted by the blowup is 2^log_n 2^log_blowup
- a usize is a natural number, and a subtraction below zero panics
- an index out of bounds panics
- an assertion panics, and a debug assertion is checked, as in a debug build
- a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Circle.DeepQuotient
public import P3Circle.Verifier
public import P3Commit.Types

@[expose] public section

namespace p3_circle.pcs.mirror

open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_commit.pcs.univariate.mirror
open p3_commit.domain.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_circle.ordering.mirror
open p3_circle.folding.mirror p3_circle.deep_quotient.mirror p3_circle.verifier.mirror

/-- The input checks' rejections, without their payloads. -/
inductive InputError (IME FME : Type) where
  | InputMmcsError (e : IME)
  | FirstLayerMmcsError (e : FME)
  | InputShapeError
  | OpeningPointMatchesQueryPoint
  | MatrixWithoutOpeningPoints
  | DomainTooSmall

/-- The input part of a circle PCS proof:

- one shared multi-opening per input commitment
- each query's first-layer siblings, one per committed height
- one shared proof of the first-layer rows. -/
structure CircleInputProof (K IMP FMP : Type _) where
  input_openings : List (BatchMultiOpening K IMP)
  first_layer_siblings : List (List K)
  first_layer_proof : FMP

/-- A circle PCS proof. -/
structure CirclePcsProof (K FCom IMP FMP : Type _) where
  batch_pow_witness : K
  first_layer_commitment : FCom
  lambdas : List K
  fri_proof : CircleFriProof K FCom FMP (CircleInputProof K IMP FMP)

/-- The verifier's circle PCS transcript, as its four phases:

- the claims and the batching grind, which return the batching challenge
- the first-layer commitment, which returns the bivariate challenge
- a commit round and its grind, which return the folding challenge
- the final constant and the query grind, which return the query indices.

A phase fails exactly when its grinding witness misses the difficulty. -/
structure CircleVerifierTx (K Com S : Type _) where
  batch_phase : S → List (Point K × List K) → K → Except Unit (K × S)
  first_layer : S → Com → K × S
  commit_round : S → Com → K → Except Unit (K × S)
  query_phase : S → K → K → Except Unit (List ℕ × S)

/-- The claims about the matrices behind one input commitment. -/
abbrev Claim (K Com : Type _) := CommitmentOpening K Com (CircleDomain K)

/-- The input checks' result: a panic is none, a rejection an error. -/
abbrev IRes (IME FME : Type) := ExceptT (InputError IME FME) Option

variable {K : Type _} [Field K] [DecidableEq K]

/-- The challenges the replay returns: alpha, the bivariate beta, every round's beta, and the indices. -/
structure Replayed (K : Type _) where
  alpha : K
  bivariate_beta : K
  betas : List K
  indices : List ℕ

/-- A transcript phase's result: a rejected witness is reported as an invalid grind. -/
def txResult {ME IE α : Type} : Except Unit α → Res ME IE α
  | .error () => throw .InvalidPowWitness
  | .ok r => pure r

/-- Replay the transcript.

Each opening point is mapped to the circle, which panics at t^2 = -1. -/
def replay_transcript {ME IE Com C S IMP FMP : Type} (tx : CircleVerifierTx K Com S)
    (rounds : List (Claim K C)) (proof : CirclePcsProof K Com IMP FMP) (s : S) : Res ME IE (Replayed K) := do
  let claims ← lift ((rounds.flatMap fun c => c.matrices.flatMap fun m => m.points).mapM fun p =>
    (Point.from_projective_line p.point).map fun z => (z, p.values))
  let r1 ← txResult (tx.batch_phase s claims proof.batch_pow_witness)
  let r2 := tx.first_layer r1.2 proof.first_layer_commitment
  let r3 ← (proof.fri_proof.commit_phase_commits.zip proof.fri_proof.commit_pow_witnesses).foldlM
    (fun (acc : List K × S) cw => do
      let r ← txResult (tx.commit_round acc.2 cw.1 cw.2)
      pure (acc.1 ++ [r.1], r.2)) ([], r2.2)
  let r4 ← txResult (tx.query_phase r3.2 proof.fri_proof.final_poly proof.fri_proof.pow_witness)
  pure ⟨r1.1, r2.1, r3.1, r4.1⟩

/-- The shape checks and the shared opening check of one input batch. -/
def checkBatch (immcs : MmcsOps K) {FME : Type} (log_blowup log_global_max_height : ℕ) (indices : List ℕ)
    (bc : BatchMultiOpening K immcs.MultiProof × Claim K immcs.Commitment) : IRes immcs.Error FME Unit := do
  let (bo, c) := bc
  let heights : List ℕ := c.matrices.map fun m => 2 ^ m.domain.log_n * 2 ^ log_blowup
  if bo.opened_values.any (·.length ≠ c.matrices.length) then throw .InputShapeError
  let dims ← c.matrices.mapM fun m => match m.points with
    | [] => throw .MatrixWithoutOpeningPoints
    | p :: _ => pure (p.values.length, 2 ^ m.domain.log_n * 2 ^ log_blowup)
  let reduced ← match heights.max? with
    | none => pure (indices.map fun _ => 0)
    | some h => do
      let lh ← ExceptT.lift (log2Strict h)
      if log_global_max_height < lh then ExceptT.lift none
      pure (indices.map (· / 2 ^ (log_global_max_height - lh)))
  match immcs.verify_multi_batch c.commitment dims reduced bo.opened_values bo.opening_proof with
  | .error e => throw (.InputMmcsError e)
  | .ok () => pure ()

/-- The DEEP quotients of one matrix at one query, added to the running value at its height.

The map holds, at each height, the running power of alpha and the running value. -/
def reduceMatrix {IME FME : Type} (G : Gen (K × K)) (log_blowup log_global_max_height : ℕ)
    (alpha_powers : List K) (index : ℕ) (st : (ℕ → K × K) × List ℕ)
    (m : MatrixOpening K (CircleDomain K) × List K × (K × K)) : IRes IME FME ((ℕ → K × K) × List ℕ) := do
  let (acc, keys) := st
  let (mat, ps_at_x, alpha_pow_width, alpha_pow_width_2) := m
  let log_height := mat.domain.log_n + log_blowup
  if log_global_max_height < log_height then ExceptT.lift none
  let bits_reduced := log_global_max_height - log_height
  let orig_idx := cfft_permute_index (index / 2 ^ bits_reduced) log_height
  let committed_domain ← ExceptT.lift (CircleDomain.standard G log_height)
  let x ← ExceptT.lift (CircleDomain.nth_point G committed_domain orig_idx)
  let keys := if log_height ∈ keys then keys else keys ++ [log_height]
  let entry ← mat.points.foldlM (fun (e : K × K) p => do
      if p.values.length ≠ ps_at_x.length then throw .InputShapeError
      let zeta ← ExceptT.lift (Point.from_projective_line p.point)
      let r ← match deep_quotient_reduce_row alpha_pow_width alpha_powers x zeta ps_at_x p.values with
        | none => throw .OpeningPointMatchesQueryPoint
        | some r => pure r
      pure (e.1 * alpha_pow_width_2, e.2 + e.1 * r)) (acc log_height)
  pure (Function.update acc log_height entry, keys)

/-- The first-layer leaf of one height at one query.

It corrects the reduced value by lambda v_n, places it beside the sibling, and returns the y-twiddle and the leaf's shape. -/
def firstLayerLeaf (G : Gen (K × K)) (log_blowup log_global_max_height index : ℕ)
    (e : ((ℕ × K) × K) × K) : Option (ℕ × K × List K × (ℕ × ℕ)) := do
  let (((log_height, ro), fl_sib), lambda) := e
  if log_height = 0 then none
  if log_height < log_blowup then none
  let orig_size := log_height - log_blowup
  if log_global_max_height < log_height then none
  let bits_reduced := log_global_max_height - log_height
  let b := (index / 2 ^ bits_reduced) % 2
  let orig_idx := cfft_permute_index (index / 2 ^ bits_reduced) log_height
  let lde_domain ← CircleDomain.standard G log_height
  let p ← CircleDomain.nth_point G lde_domain orig_idx
  let vn ← Point.v_n p orig_size
  let lambda_corrected := ro - lambda * vn
  let fl_values := if b = 0 then [lambda_corrected, fl_sib] else [fl_sib, lambda_corrected]
  let y_twiddle := if b = 0 then p.y else -p.y
  some (log_height, y_twiddle, fl_values, (2, 2 ^ (log_height - 1)))

/-- The DEEP quotients of every matrix of one batch at one query. -/
def reduceBatch {IME FME : Type} (G : Gen (K × K)) {Com MP : Type} (log_blowup log_global_max_height : ℕ)
    (alpha_powers : List K) (index query : ℕ) (st : (ℕ → K × K) × List ℕ)
    (e : BatchMultiOpening K MP × Claim K Com × List (K × K)) : IRes IME FME ((ℕ → K × K) × List ℕ) := do
  let (bo, c, pows) := e
  let row ← ExceptT.lift bo.opened_values[query]?
  if row.length ≠ c.matrices.length then throw .InputShapeError
  (c.matrices.zip row).zipIdx.foldlM (fun st mr => do
      let ap ← ExceptT.lift pows[mr.2]?
      reduceMatrix G log_blowup log_global_max_height alpha_powers index st (mr.1.1, mr.1.2, ap)) st

/-- One query's reduced openings, folded once along y.

It returns the inputs to circle FRI, tallest first, then the first-layer leaves and their shapes. -/
def reduceQuery (G : Gen (K × K)) (immcs : MmcsOps K) {FME : Type} (log_blowup log_global_max_height : ℕ)
    (bivariate_beta : K) (alpha_powers : List K) (matrix_alpha_pows : List (List (K × K)))
    (rounds : List (Claim K immcs.Commitment)) (input_openings : List (BatchMultiOpening K immcs.MultiProof))
    (first_layer_siblings : List (List K)) (lambdas : List K) (index query : ℕ) :
    IRes immcs.Error FME (List (ℕ × K) × List (ℕ × ℕ) × List (List K)) := do
  if input_openings.length ≠ rounds.length then throw .InputShapeError
  let (acc, keys) ← (input_openings.zip (rounds.zip matrix_alpha_pows)).foldlM
    (reduceBatch G log_blowup log_global_max_height alpha_powers index query) (fun _ => (1, 0), [])
  let reduced := (keys.mergeSort (fun a b => decide (a ≤ b))).map fun h => (h, (acc h).2)
  let fls ← ExceptT.lift first_layer_siblings[query]?
  if reduced.length ≠ fls.length then throw .InputShapeError
  if reduced.length ≠ lambdas.length then throw .InputShapeError
  let per_height ← ExceptT.lift (((reduced.zip fls).zip lambdas).mapM
    (firstLayerLeaf G log_blowup log_global_max_height index))
  let y_twiddles_inv ← ExceptT.lift (batchInv (per_height.map fun e => e.2.1))
  let fri_input ← ExceptT.lift ((per_height.zip y_twiddles_inv).mapM fun e =>
    (fold_row_with_inv_twiddle e.2 bivariate_beta e.1.2.2.1).map fun v => (e.1.1 - 1, v))
  pure (fri_input.reverse, per_height.map (·.2.2.2), per_height.map (·.2.2.1))

/-- The input checks the circle FRI verifier calls.

They check every batch's shape and opening, reduce every query, then check the first-layer rows. -/
def open_inputs (G : Gen (K × K)) (immcs fmmcs : MmcsOps K) (log_blowup log_global_max_height : ℕ)
    (rounds : List (Claim K immcs.Commitment)) (first_layer_commitment : fmmcs.Commitment) (lambdas : List K)
    (bivariate_beta : K) (alpha_powers : List K) (matrix_alpha_pows : List (List (K × K))) (indices : List ℕ)
    (input_proof : CircleInputProof K immcs.MultiProof fmmcs.MultiProof) :
    IRes immcs.Error fmmcs.Error (List (List (ℕ × K))) := do
  let ⟨input_openings, first_layer_siblings, first_layer_proof⟩ := input_proof
  if first_layer_siblings.length ≠ indices.length then throw .InputShapeError
  if input_openings.any (·.opened_values.length ≠ indices.length) then throw .InputShapeError
  if input_openings.length ≠ rounds.length then throw .InputShapeError
  (input_openings.zip rounds).forM (checkBatch immcs log_blowup log_global_max_height indices)
  let per_query ← indices.zipIdx.mapM fun e =>
    reduceQuery G immcs log_blowup log_global_max_height bivariate_beta alpha_powers matrix_alpha_pows rounds
      input_openings first_layer_siblings lambdas e.1 e.2
  let fl_dims := (per_query.head?.map (·.2.1)).getD []
  match fmmcs.verify_multi_batch first_layer_commitment fl_dims (indices.map (· / 2))
      (per_query.map (·.2.2)) first_layer_proof with
  | .error e => throw (.FirstLayerMmcsError e)
  | .ok () => pure (per_query.map (·.1))

/-- The width a matrix claims: the evaluation count of its first opening point, and 0 with none. -/
def claimedWidth (m : MatrixOpening K (CircleDomain K)) : ℕ := (m.points.headD ⟨0, []⟩).values.length

/-- The full verifier.

It derives the tallest height, checks the proof's lengths, replays the transcript, and checks the queries. -/
def verify (G : Gen (K × K)) {S : Type} (immcs fmmcs : MmcsOps K) (tx : CircleVerifierTx K fmmcs.Commitment S)
    (params : FriParameters) (rounds : List (Claim K immcs.Commitment))
    (proof : CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) (s : S) :
    Res fmmcs.Error (InputError immcs.Error fmmcs.Error) Unit := do
  let heights : List ℕ := rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + params.log_blowup
  let log_global_max_height ← match heights.max? with
    | none => throw .NoCommittedMatrices
    | some h => pure h
  if log_global_max_height < params.log_blowup + 1 then throw (.InputError .DomainTooSmall)
  let num_commit_rounds := log_global_max_height - (params.log_blowup + 1)
  let index_bits := log_global_max_height - 1 + 1
  if G.adicity ≤ index_bits then throw .GlobalMaxHeightTooLarge
  let log_arities ← validate_proof_shape params proof.fri_proof num_commit_rounds
  if params.batch_proof_of_work_bits = 0 ∧ proof.batch_pow_witness ≠ 0 then throw .NonCanonicalPowWitness
  let r ← replay_transcript tx rounds proof s
  let matrix_alpha_pows := rounds.map fun c => c.matrices.map fun m =>
    (r.alpha ^ claimedWidth m, (r.alpha ^ claimedWidth m) ^ 2)
  let max_width := ((rounds.flatMap fun c => c.matrices.flatMap fun m => m.points.map (·.values.length)).max?).getD 0
  let alpha_powers := (List.range max_width).map (r.alpha ^ ·)
  verify_queries G fmmcs params proof.fri_proof r.betas r.indices log_arities
    (open_inputs G immcs fmmcs params.log_blowup log_global_max_height rounds proof.first_layer_commitment
      proof.lambdas r.bivariate_beta alpha_powers matrix_alpha_pows)

end p3_circle.pcs.mirror
