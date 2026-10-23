/-
Transcriptions of the described transcripts of FRI and of the PCS around it.

What a transcription abstracts:

* a transcript step is its kind, its label and its length, as the interaction pattern lists them;
* the domain separator's encoding of the steps and instance values is left out;
* a usize is a natural number;
* a panic is none.

Loops and branches are kept.
-/
module

public import P3Fri.Config

@[expose] public section

namespace p3_fri.transcript.mirror

open p3_fri.config.mirror

/-- One described step: a commitment, a grinding step of some bits, a challenge, a message of some length, or the bracket of a sub-protocol. -/
inductive Step where
  | commitment
  | commitPow (bits : ℕ)
  | foldChallenge
  | finalPoly (len : ℕ)
  | queryPow (bits : ℕ)
  | queryIndices (bits count : ℕ)
  | claimedEvaluations (len : ℕ)
  | batchPow (bits : ℕ)
  | alpha
  | ldtBegin
  | ldtEnd
  deriving DecidableEq

/-- The shape of one FRI run. -/
structure FriShape where
  log_arities : List ℕ
  final_poly_len : ℕ
  commit_pow_bits : ℕ
  query_pow_bits : ℕ
  num_queries : ℕ
  index_bits : ℕ
  log_blowup : ℕ
  max_log_arity : ℕ

namespace FriShape

/-- The shape at a given schedule. -/
def with_schedule (params : FriParameters) (log_arities : List ℕ) (index_bits : ℕ) : FriShape :=
  ⟨log_arities, params.final_poly_len, params.commit_proof_of_work_bits, params.query_proof_of_work_bits,
    params.num_queries, index_bits, params.log_blowup, params.max_log_arity⟩

/-- The shape at the schedule the parameters and the input heights derive. -/
def new (params : FriParameters) (input_log_heights : List ℕ) (index_bits : ℕ) : Option FriShape := do
  let log_arities ← fold_schedule input_log_heights (params.log_blowup + params.log_final_poly_len)
    params.max_log_arity
  some (with_schedule params log_arities index_bits)

/-- The steps in order.

Each round: a commitment, a grinding step if its difficulty is positive, and a challenge.
Then: the final polynomial, the query grinding step if positive, and the indices. -/
def pattern (s : FriShape) : List Step :=
  (s.log_arities.flatMap fun _ =>
    [Step.commitment] ++ (if 0 < s.commit_pow_bits then [Step.commitPow s.commit_pow_bits] else []) ++
      [Step.foldChallenge]) ++
  [Step.finalPoly s.final_poly_len] ++
  (if 0 < s.query_pow_bits then [Step.queryPow s.query_pow_bits] else []) ++
  [Step.queryIndices s.index_bits s.num_queries]

end FriShape

/-- The shape of one PCS opening: the claimed evaluation count of every point, and the batching difficulty. -/
structure PcsShape where
  claimed_evaluation_counts : List (List (List ℕ))
  batch_pow_bits : ℕ

/-- One message per opening point, the batching grinding step if positive, the challenge, and the bracket of the low-degree test. -/
def PcsShape.pattern (s : PcsShape) : List Step :=
  (s.claimed_evaluation_counts.flatten.flatten.map Step.claimedEvaluations) ++
  (if 0 < s.batch_pow_bits then [Step.batchPow s.batch_pow_bits] else []) ++
  [Step.alpha, Step.ldtBegin, Step.ldtEnd]

end p3_fri.transcript.mirror
