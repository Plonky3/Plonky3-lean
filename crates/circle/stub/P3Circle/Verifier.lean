/-
Transcriptions of the circle FRI verifier: the proof shape check, the fold chain of one query, and the query checks.

What a transcription abstracts, beyond the model of the folds and p3-fri's proof types:

- the base field and its extension are one mathlib field K, base values read through their embedding
- a commitment scheme's methods are fields of a record, as in p3-fri's model
- the input openings are checked by a function the caller passes, as in the Rust closure
- the folding strategy's extra query index bit is a division by 2
- a usize is a natural number, and a subtraction below zero panics
- an index out of bounds panics
- an assertion panics, and a debug assertion is checked, as in a debug build
- a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Circle.Folding
public import P3Fri.Types
public import P3Fri.Config

@[expose] public section

namespace p3_circle.verifier.mirror

open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_circle.folding.mirror

/-- The verifier's rejections, without their payloads. -/
inductive FriError (ME IE : Type) where
  | ZeroQueries
  | ZeroBlowup
  | UnsupportedFoldingCap
  | CommitRoundCountMismatch
  | CommitPowWitnessCountMismatch
  | NonCanonicalPowWitness
  | CommitPhaseOpeningsCountMismatch
  | CommitPhaseQueryCountMismatch
  | SiblingValuesLengthMismatch
  | NoCommittedMatrices
  | GlobalMaxHeightTooLarge
  | InvalidPowWitness
  | FinalPolyMismatch
  | FinalFoldHeightMismatch
  | UnconsumedReducedOpenings
  | CommitPhaseMmcsError (e : ME)
  | InputError (e : IE)

/-- The outcome of a verifier step: a panic is none, a rejection an error. -/
abbrev Res (ME IE : Type) := ExceptT (FriError ME IE) Option

/-- A panic. -/
def crash {ME IE α : Type} : Res ME IE α := ExceptT.lift none

/-- A value that may panic, read into a verifier step. -/
def lift {ME IE α : Type} (o : Option α) : Res ME IE α := ExceptT.lift o

/-- A circle FRI proof.

Its final polynomial is one constant. -/
structure CircleFriProof (K Com MP IP : Type _) where
  commit_phase_commits : List Com
  commit_pow_witnesses : List K
  input_openings : IP
  commit_phase_openings : List (CommitPhaseMultiStep K MP)
  final_poly : K
  pow_witness : K

variable {K : Type _} [Field K] [DecidableEq K]

/-- Check every length the proof declares.

It returns the schedule: one bit per round. -/
def validate_proof_shape {ME IE Com MP IP : Type} (params : FriParameters)
    (proof : CircleFriProof K Com MP IP) (num_commit_rounds : ℕ) : Res ME IE (List ℕ) := do
  if params.num_queries = 0 then throw .ZeroQueries
  if params.log_blowup = 0 then throw .ZeroBlowup
  if params.max_log_arity ≠ 1 then throw .UnsupportedFoldingCap
  if proof.commit_phase_commits.length ≠ num_commit_rounds then throw .CommitRoundCountMismatch
  if proof.commit_pow_witnesses.length ≠ num_commit_rounds then throw .CommitPowWitnessCountMismatch
  if params.commit_proof_of_work_bits = 0 ∧ proof.commit_pow_witnesses.any (· ≠ 0) then
    throw .NonCanonicalPowWitness
  if params.query_proof_of_work_bits = 0 ∧ proof.pow_witness ≠ 0 then throw .NonCanonicalPowWitness
  if proof.commit_phase_openings.length ≠ num_commit_rounds then throw .CommitPhaseOpeningsCountMismatch
  let log_arities := List.replicate num_commit_rounds 1
  (proof.commit_phase_openings.zip log_arities).forM fun e => do
    if e.1.sibling_values.length ≠ params.num_queries then throw .CommitPhaseQueryCountMismatch
    if e.1.sibling_values.any (·.length ≠ 2 ^ e.2 - 1) then throw .SiblingValuesLengthMismatch
  pure log_arities

/-- Rebuild a row of arity values.

The running value sits at the index in the group, and the siblings fill the rest in order. -/
def rebuildRow (arity index_in_group : ℕ) (folded : K) (siblings : List K) : Option (List K) :=
  (List.range arity).mapM fun j =>
    if j = index_in_group then some folded
    else siblings[if j < index_in_group then j else j - 1]?

/-- The state of the fold chain:

- the index
- the running value
- the height
- the openings not yet rolled in
- each round's group index and row. -/
abbrev ChainState (K : Type _) := ℕ × K × ℕ × List (ℕ × K) × List (ℕ × List K)

/-- One round of the fold chain.

It rolls in an opening at the current height, rebuilds the row, and folds it with the round's twiddle. -/
def foldStep (query : ℕ) (x_twiddle_inv : List K) (st : ChainState K)
    (r : (K × ℕ × List (List K)) × ℕ) : Option (ChainState K) := do
  let (index, folded_eval, log_current_height, ro, recorded) := st
  let ((beta, log_arity, sibling_values), round) := r
  let arity := 2 ^ log_arity
  let (folded_eval, ro) := match ro with
    | (lh, v) :: ro' => if lh = log_current_height then (folded_eval + v, ro') else (folded_eval, ro)
    | [] => (folded_eval, [])
  let siblings ← sibling_values[query]?
  let evals ← rebuildRow arity (index % arity) folded_eval siblings
  if log_current_height < log_arity then none
  let log_folded_height := log_current_height - log_arity
  let index := index / arity
  if log_arity ≠ 1 then none
  let t ← x_twiddle_inv[round]?
  let folded ← fold_row_with_inv_twiddle t beta evals
  some (index, folded, log_folded_height, ro, recorded ++ [(index, evals)])

/-- The fold chain of one query.

It folds every round from the tallest height, then checks the final height and that every opening was rolled in.

It returns the folded value, and each round's group index and rebuilt row. -/
def fold_query {ME IE : Type} (log_blowup query index : ℕ) (betas : List K) (log_arities : List ℕ)
    (sibling_values : List (List (List K))) (reduced_openings : List (ℕ × K)) (log_max_height : ℕ)
    (x_twiddle_inv : List K) : Res ME IE (K × List (ℕ × List K)) := do
  let (_, folded, log_h, ro, recorded) ← lift <|
    ((betas.zip (log_arities.zip sibling_values)).zipIdx).foldlM (foldStep query x_twiddle_inv)
      (index, 0, log_max_height, reduced_openings, [])
  if log_h ≠ log_blowup then throw .FinalFoldHeightMismatch
  if ro ≠ [] then throw .UnconsumedReducedOpenings
  pure (folded, recorded)

/-- An input check's errors, carried into the verifier's. -/
def mapInputError {ME IE α : Type} (m : ExceptT IE Option α) : Res ME IE α :=
  ExceptT.mk ((ExceptT.run m).map (Except.mapError FriError.InputError))

/-- The shared check of one round over every query's group index and row. -/
def checkRound {IE : Type} (fmmcs : MmcsOps K) (recorded : List (List (ℕ × List K)))
    (log_current_height : ℕ) (e : (fmmcs.Commitment × CommitPhaseMultiStep K fmmcs.MultiProof × ℕ) × ℕ) :
    Res fmmcs.Error IE ℕ := do
  let ((commit, opening, log_arity), round) := e
  let log_folded_height := log_current_height - log_arity
  let groups := recorded.map fun rs => (rs.getD round (0, [])).1
  let rows := recorded.map fun rs => [(rs.getD round (0, [])).2]
  match fmmcs.verify_multi_batch commit [(2 ^ log_arity, 2 ^ log_folded_height)] groups rows
      opening.opening_proof with
  | .error err => throw (.CommitPhaseMmcsError err)
  | .ok () => pure log_folded_height

/-- One query: its input openings sorted by height, its twiddle chain, its fold chain, and the final value. -/
def checkQuery {ME IE : Type} (G : Gen (K × K)) (log_blowup : ℕ) (betas : List K) (log_arities : List ℕ)
    (sibling_values : List (List (List K))) (final_poly : K) (log_max_height : ℕ)
    (e : (ℕ × List (ℕ × K)) × ℕ) : Res ME IE (List (ℕ × List K)) := do
  let ((index, ro), query) := e
  if !((ro.zip ro.tail).all fun p => p.2.1 < p.1.1) then crash
  let top_level_index := index / 2
  let x_twiddle_inv ← lift (query_x_twiddles_inv G top_level_index log_max_height log_arities.length)
  let (folded, recorded) ← fold_query log_blowup query top_level_index betas log_arities sibling_values ro
    log_max_height x_twiddle_inv
  if folded ≠ final_poly then throw .FinalPolyMismatch
  pure recorded

/-- Check every query's fold chain, then every round's openings.

The input openings are checked first, by the function the caller passes. -/
def verify_queries {IE IP : Type} (G : Gen (K × K)) (fmmcs : MmcsOps K) (params : FriParameters)
    (proof : CircleFriProof K fmmcs.Commitment fmmcs.MultiProof IP) (betas : List K) (indices : List ℕ)
    (log_arities : List ℕ) (open_inputs : List ℕ → IP → ExceptT IE Option (List (List (ℕ × K)))) :
    Res fmmcs.Error IE Unit := do
  let log_max_height := log_arities.sum + params.log_blowup
  let reduced_openings ← mapInputError (open_inputs indices proof.input_openings)
  let sibling_values := proof.commit_phase_openings.map (·.sibling_values)
  let recorded ← ((indices.zip reduced_openings).zipIdx).mapM
    (checkQuery G params.log_blowup betas log_arities sibling_values proof.final_poly log_max_height)
  let _ ← ((proof.commit_phase_commits.zip (proof.commit_phase_openings.zip log_arities)).zipIdx).foldlM
    (checkRound fmmcs recorded) log_max_height
  pure ()

end p3_circle.verifier.mirror
