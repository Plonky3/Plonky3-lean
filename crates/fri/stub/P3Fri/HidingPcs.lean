/-
Transcriptions of the hiding FRI PCS's opening and verification.

What a transcription abstracts, beyond Hiding.lean and PcsVerify.lean:

* the challenge extension degree is a parameter D
* the inner PCS's opening is its result: the opened values with a proof, an error, or a panic
* a round's prover data is its configuration, its two flags and its matrices' heights
* the rounds hold distinct prover data, so each has its own opened flag, returned updated
* a usize subtraction that underflows panics, and so does the drain that follows it
* a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Fri.PcsVerify
public import P3Fri.Hiding

@[expose] public section

namespace p3_fri.hiding_pcs.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror p3_fri.mirror p3_fri.config.mirror
open p3_fri.verifier.mirror p3_fri.transcript.mirror p3_fri.two_adic_pcs.mirror

variable {K : Type} [Field K] [DecidableEq K]

/-! ## Verification -/

/-- One point of the verifier's merge: the hidden values must number the expected count. -/
def mergeHiddenPoint {ME IE : Type} (expected : ℕ) (e : PointOpening K × List K) :
    Res ME IE (PointOpening K) :=
  if e.2.length ≠ expected then throw .HidingRandomOpeningValueCountMismatch
  else pure ⟨e.1.point, e.1.values ++ e.2⟩

/-- One matrix of the verifier's merge.

It checks the hiding budget against half the claimed domain, then the point count, then every point. -/
def mergeHiddenMatrix {ME IE : Type} (G : Gen K) (num_queries D expected : ℕ)
    (e : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List (List K)) :
    Res ME IE (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen)) := do
  let (m, rm) := e
  let mask_height := m.domain.size / 2
  match hiding_budget num_queries D m.points.length with
  | some required => if mask_height < required then throw .HidingBudgetExceeded
  | none => throw .HidingBudgetExceeded
  if rm.length ≠ m.points.length then throw .HidingRandomOpeningPointCountMismatch
  let points ← (m.points.zip rm).mapM (mergeHiddenPoint expected)
  pure ⟨m.domain, points⟩

/-- One round of the verifier's merge.

A trusted preprocessed round expects no hidden values, every other round r of them. -/
def mergeHiddenRound {ME IE : Type} (G : Gen K) {C : Type} (num_queries D r : ℕ) (preprocessed : Option ℕ)
    (e : (Claim G C × List (List (List K))) × ℕ) : Res ME IE (Claim G C) := do
  let ((c, rr), idx) := e
  if rr.length ≠ c.matrices.length then throw .HidingRandomOpeningMatrixCountMismatch
  let expected := if preprocessed = some idx then 0 else r
  let matrices ← (c.matrices.zip rr).mapM (mergeHiddenMatrix G num_queries D expected)
  pure ⟨c.commitment, matrices⟩

/-- The verifier's merge of the public openings with the hidden ones, after its parameter checks. -/
def mergeHidden {ME IE : Type} (G : Gen K) {C : Type} (num_queries D r : ℕ) (preprocessed : Option ℕ)
    (claims : List (Claim G C)) (rand : List (List (List (List K)))) : Res ME IE (List (Claim G C)) := do
  match preprocessed with
  | some index => if claims.length ≤ index then throw .HidingPreprocessedCommitmentOutOfBounds
  | none => pure ()
  if r < D then throw .InsufficientHidingRandomCodewords
  if rand.length ≠ claims.length then throw .HidingRandomOpeningRoundCountMismatch
  (claims.zip rand).zipIdx.mapM (mergeHiddenRound G num_queries D r preprocessed)

/-- The hiding verifier: the merge, then the inner verifier on the merged openings. -/
def verify_hiding (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S)
    (params : FriParameters) (D r : ℕ) (preprocessed : Option ℕ) (claims : List (Claim G C))
    (rand : List (List (List (List K))))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) : Res fmmcs.Error immcs.Error Unit := do
  let merged ← mergeHidden G params.num_queries D r preprocessed claims rand
  verify G g fmmcs immcs sp params merged proof s commit_of

/-! ## Opening -/

/-- The prover's split of one point's values: the last k are hidden.

The usize subtraction panics when fewer than k values are opened. -/
def splitHidden (k : ℕ) (values : List K) : Option (List K × List K) :=
  if values.length < k then none
  else some (values.take (values.length - k), values.drop (values.length - k))

/-- One round of a hiding opening, as the prover holds it. -/
structure HidingRound (K : Type) where
  num_random_codewords : ℕ
  log_blowup : ℕ
  preprocessed : Bool
  opened : Bool
  heights : List ℕ
  points : List (List K)

/-- The checks of one round before anything is opened.

They panic on a configuration mismatch, a wrong preprocessing flag, or a matrix count mismatch.

They reject an input too short to fold, or a mask below the hiding budget. -/
def checkHidingRound (params : FriParameters) (D r : ℕ) (preprocessed : Option ℕ) (e : HidingRound K × ℕ) :
    Option (Except HidingFriProverError Unit) :=
  let (rd, idx) := e
  if rd.num_random_codewords ≠ r ∨ rd.log_blowup ≠ params.log_blowup then none
  else if rd.preprocessed ≠ decide (preprocessed = some idx) then none
  else if rd.heights.length ≠ rd.points.length then none
  else (rd.heights.zip rd.points).foldlM (fun (acc : Except HidingFriProverError Unit) hp =>
      match acc with
      | .error err => some (.error err)
      | .ok () => do
        let lh ← log2Strict hp.1
        match params.validate_input_height lh with
        | .error err => some (.error (.Fri err))
        | .ok () => some (check_hiding_budget r params.num_queries
            (lde_mask_height params.log_blowup hp.1) D hp.2.length))
    (.ok ())

/-- The checks of every round, in order, stopping at the first rejection. -/
def checkHidingRounds (params : FriParameters) (D r : ℕ) (preprocessed : Option ℕ) (rounds : List (HidingRound K)) :
    Option (Except HidingFriProverError Unit) :=
  rounds.zipIdx.foldlM (fun (acc : Except HidingFriProverError Unit) e =>
    match acc with
    | .error err => some (.error err)
    | .ok () => checkHidingRound params D r preprocessed e) (.ok ())

/-- The hiding opening.

It checks every round, then consumes the opened flag of every private round, panicking if it was set.

It runs the inner opening, then moves the last r values of every private point into the proof. -/
def open_hiding {P : Type} (params : FriParameters) (D r : ℕ) (preprocessed : Option ℕ)
    (rounds : List (HidingRound K))
    (inner_open : Option (Except FriProverError (List (List (List (List K))) × P))) :
    Option (Except HidingFriProverError
      ((List (List (List (List K))) × (List (List (List (List K))) × P)) × List Bool)) := do
  match ← checkHidingRounds params D r preprocessed rounds with
  | .error err => some (.error err)
  | .ok () =>
    if rounds.any (fun rd => !rd.preprocessed && rd.opened) then none
    else
      let flags := rounds.map fun rd => rd.opened || !rd.preprocessed
      match ← inner_open with
      | .error err => some (.error (.Fri err))
      | .ok (values, proof) => do
        let split ← values.zipIdx.mapM fun e =>
          e.1.mapM fun vm => vm.mapM fun vp => splitHidden (if preprocessed = some e.2 then 0 else r) vp
        some (.ok ((split.map (·.map (·.map (·.1))), split.map (·.map (·.map (·.2))), proof), flags))

end p3_fri.hiding_pcs.mirror
