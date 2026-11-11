/-
Transcriptions of the STARK's transcript: its pattern, and the verifier's two phases.

These do not extract.
They are generic over the challenger, the commitment and the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the sponge state is the list of messages absorbed so far, starting from the domain separator
* a challenge is an arbitrary function of that list, as a random oracle
* the grind check is an arbitrary predicate of that list, the bit count and the witness
* the pattern player's bookkeeping is the pattern itself
* a commitment absorbs as one message, and a field element as one message.

The order of absorptions, samples and checks is kept.
-/
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace p3_uni_stark.transcript.mirror

/-- The numbers the transcript is described by.

They come from the configuration and the AIR, never from a proof. -/
structure StarkShape where
  log_ext_degree : ℕ
  log_degree : ℕ
  main_width : ℕ
  preprocessed_width : ℕ
  num_public_values : ℕ
  num_periodic_columns : ℕ
  num_quotient_chunks : ℕ
  opens_main_next_row : Bool
  opens_preprocessed_next_row : Bool
  has_randomization : Bool
  ood_pow_bits : ℕ

/-- The steps of the transcript. -/
inductive Step where
  | trace_commitment
  | preprocessed_commitment
  | public_values (n : ℕ)
  | alpha
  | quotient_commitment
  | random_commitment
  | ood_pow (bits : ℕ)
  | zeta
  | begin_opening_argument
  | end_opening_argument
  deriving DecidableEq

/-- The pattern, in order:

- the commitments and public values, then alpha
- the quotient, randomization and grind, then zeta
- the opening argument. -/
def StarkShape.pattern (s : StarkShape) : List Step :=
  [.trace_commitment] ++
  (if s.preprocessed_width > 0 then [.preprocessed_commitment] else []) ++
  [.public_values s.num_public_values, .alpha, .quotient_commitment] ++
  (if s.has_randomization then [.random_commitment] else []) ++
  (if s.ood_pow_bits > 0 then [.ood_pow s.ood_pow_bits] else []) ++
  [.zeta, .begin_opening_argument, .end_opening_argument]

/-- A message the sponge absorbs.

It is a commitment, a field element, or the marker of a challenge drawn. -/
inductive Msg (C F : Type) where
  | com (c : C)
  | scalar (x : F)
  | challenge (s : Step)

/-- Why a transcript phase is rejected. -/
inductive StarkTranscriptFailure where
  | MissingPreprocessedCommitment
  | UnexpectedPreprocessedCommitment
  | MissingRandomCommitment
  | UnexpectedRandomCommitment
  | OodPowWitness
  deriving DecidableEq

variable {C F E : Type}

/-- An optional commitment.

It is absorbed when described and present, and an error when only one of the two holds. -/
def optional_commitment (described : Bool) (commitment : Option C) (missing unexpected : StarkTranscriptFailure)
    (st : List (Msg C F)) : Except StarkTranscriptFailure (List (Msg C F)) :=
  match described, commitment with
  | true, some c => .ok (st ++ [.com c])
  | false, none => .ok st
  | true, none => .error missing
  | false, some _ => .error unexpected

/-- The verifier's first phase.

It absorbs the trace commitment, the preprocessed commitment when described, and the public values.
It then draws alpha. -/
def constraint_phase (shape : StarkShape) (H : List (Msg C F) → E) (st : List (Msg C F))
    (trace : C) (preprocessed : Option C) (public_values : List F) :
    Except StarkTranscriptFailure (List (Msg C F) × E) := do
  let st ← optional_commitment (shape.preprocessed_width > 0) preprocessed
    .MissingPreprocessedCommitment .UnexpectedPreprocessedCommitment (st ++ [.com trace])
  let st := st ++ public_values.map .scalar
  pure (st ++ [.challenge .alpha], H st)

/-- The verifier's second phase.

It absorbs the quotient commitment, and the randomization commitment when described.
It checks the grind when it has bits, then draws zeta. -/
def ood_phase (shape : StarkShape) (H : List (Msg C F) → E)
    (powOk : List (Msg C F) → ℕ → F → Bool) (st : List (Msg C F)) (quotient : C)
    (random : Option C) (witness : F) : Except StarkTranscriptFailure (List (Msg C F) × E) := do
  let st ← optional_commitment shape.has_randomization random
    .MissingRandomCommitment .UnexpectedRandomCommitment (st ++ [.com quotient])
  let st ← if shape.ood_pow_bits > 0 then
      if powOk st shape.ood_pow_bits witness then pure (st ++ [.scalar witness])
      else throw .OodPowWitness
    else pure st
  pure (st ++ [.challenge .zeta], H st)

end p3_uni_stark.transcript.mirror
