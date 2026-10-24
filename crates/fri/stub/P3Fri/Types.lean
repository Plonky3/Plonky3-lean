/-
The proof types of p3-fri, the commitment scheme it opens with, and its transcript, as records.

What a transcription abstracts:

* a matrix is its height, width and entries, as in p3-commit's model
* a scheme's or a transcript's required methods are fields of a record, with explicit state
* the Fiat-Shamir transcript is its typed steps
* a commit round returns the folding challenge, and the query phase the indices
* a proof-of-work witness is a field element, base values read through their embedding
* a panic is none.
-/
module

public import P3Commit.Types

@[expose] public section

namespace p3_fri.mirror

open p3_commit.pcs.univariate.mirror

/-- The methods of a mixed matrix commitment scheme that FRI calls.

They are commit, the committed matrices, and the shared multi-openings. -/
structure MmcsOps (T : Type _) where
  Commitment : Type
  ProverData : Type
  MultiProof : Type
  Error : Type
  commit : List (Mat T) → Commitment × ProverData
  get_matrices : ProverData → List (Mat T)
  open_multi_batch : List ℕ → ProverData → List (List (List T)) × MultiProof
  verify_multi_batch : Commitment → List (ℕ × ℕ) → List ℕ → List (List (List T)) → MultiProof →
    Except Error Unit

/-- All queries' openings of one commit-phase codeword.

They hold the siblings of each query, and one shared proof. -/
structure CommitPhaseMultiStep (K MP : Type _) where
  sibling_values : List (List K)
  opening_proof : MP

/-- All queries' openings of one input batch.

Entry [q][m] of the values is the row of matrix m at query q.
One proof is shared by all of them. -/
structure BatchMultiOpening (K MP : Type _) where
  opened_values : List (List (List K))
  opening_proof : MP

/-- A FRI proof. -/
structure FriProof (K Com MP IMP : Type _) where
  batch_pow_witness : K
  commit_phase_commits : List Com
  commit_pow_witnesses : List K
  input_openings : List (BatchMultiOpening K IMP)
  commit_phase_openings : List (CommitPhaseMultiStep K MP)
  final_poly : List K
  query_pow_witness : K

/-- The reasons a described transcript rejects a run. -/
inductive TranscriptFailure where
  | PowWitness
  | MissingPowWitness
  | FinalPolyLen (expected got : ℕ)
  | CommitRoundCount (expected got : ℕ)
  | CommitPowWitnessCount (expected got : ℕ)
  deriving DecidableEq

/-- The prover's FRI transcript.

A commit round binds a commitment, grinds if the difficulty is positive, and draws the challenge.

The query phase binds the final polynomial, grinds, and draws the indices. -/
structure ProverTx (K Com S : Type _) where
  commit_round : S → Com → K × Option K × S
  query_phase : S → List K → List ℕ × Option K × S

/-- The verifier's FRI transcript.

It replays the same steps, failing on a count or a witness the description rejects. -/
structure VerifierTx (K Com S : Type _) where
  commit_rounds : S → List Com → List K → Except TranscriptFailure (List K × S)
  query_phase : S → List K → Option K → Except TranscriptFailure (List ℕ × S)

end p3_fri.mirror
