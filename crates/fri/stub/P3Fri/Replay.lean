/-
Transcriptions of the verifier transcripts of FRI and of the PCS around it, over the duplex challenger.

What a transcription abstracts:

* the challenger is a record of its absorb and sample operations over a prime field of order p
* a sampled base element is its canonical value, a natural number below p
* the domain separator, its instance values and the bracket markers absorb nothing
* the interaction pattern's bookkeeping is left out, since every driver call matches its description
* a usize is a natural number
* an assertion panics, and a panic is none.

Loops, branches and early returns are kept.
-/
module

public import P3Fri.Types
public import P3Fri.Transcript
public import P3Commit.Types

@[expose] public section

namespace p3_fri.transcript.mirror

open p3_fri.mirror p3_fri.config.mirror p3_commit.pcs.univariate.mirror

/-- The challenger operations the transcripts call.

The order is the field order p.

Sampling a base element returns its canonical value. -/
structure Sponge (K Com S : Type _) where
  order : ℕ
  observe_commitment : S → Com → S
  observe_values : S → List K → S
  observe_witness : S → K → S
  sample : S → K × S
  sample_canonical : S → ℕ × S

variable {K Com S : Type _}

/-- The low bits of a sampled element.

It asserts that bits < 64 and 2^bits < p. -/
def sample_bits (sp : Sponge K Com S) (s : S) (bits : ℕ) : Option (ℕ × S) :=
  if 64 ≤ bits ∨ sp.order ≤ 2 ^ bits then none
  else some ((sp.sample_canonical s).1 % 2 ^ bits, (sp.sample_canonical s).2)

/-- The grinding check.

Zero difficulty accepts.

Otherwise it absorbs the witness, samples the bits, and accepts when they are zero. -/
def check_witness (sp : Sponge K Com S) (s : S) (bits : ℕ) (w : K) : Option (Bool × S) :=
  if bits = 0 then some (true, s)
  else (sample_bits sp (sp.observe_witness s w) bits).map fun r => (decide (r.1 = 0), r.2)

/-- One commit round: absorb the commitment, grind at positive difficulty, draw the challenge. -/
def commit_round (sp : Sponge K Com S) (shape : FriShape) (s : S) (cw : Com × K) :
    ExceptT TranscriptFailure Option (K × S) := do
  let s1 := sp.observe_commitment s cw.1
  let s2 ← if 0 < shape.commit_pow_bits then do
      let (ok, s') ← ExceptT.lift (check_witness sp s1 shape.commit_pow_bits cw.2)
      if ok then pure s' else throw .PowWitness
    else pure s1
  pure (sp.sample s2)

/-- Every commit round, after the counts of commitments and witnesses are checked. -/
def commit_rounds (sp : Sponge K Com S) (shape : FriShape) (s : S) (coms : List Com) (ws : List K) :
    ExceptT TranscriptFailure Option (List K × S) := do
  if coms.length ≠ shape.log_arities.length then
    throw (.CommitRoundCount shape.log_arities.length coms.length)
  if ws.length ≠ shape.log_arities.length then
    throw (.CommitPowWitnessCount shape.log_arities.length ws.length)
  (coms.zip ws).foldlM (fun acc cw => do
    let (b, s') ← commit_round sp shape acc.2 cw
    pure (acc.1 ++ [b], s')) ([], s)

/-- The query phase.

It absorbs the final polynomial, grinds at positive difficulty, and draws one index per query. -/
def query_phase (sp : Sponge K Com S) (shape : FriShape) (s : S) (final_poly : List K) (w : Option K) :
    ExceptT TranscriptFailure Option (List ℕ × S) := do
  if shape.final_poly_len ≠ final_poly.length then
    throw (.FinalPolyLen shape.final_poly_len final_poly.length)
  let s1 := sp.observe_values s final_poly
  let s2 ← if 0 < shape.query_pow_bits then
      match w with
      | none => throw .MissingPowWitness
      | some w => do
        let (ok, s') ← ExceptT.lift (check_witness sp s1 shape.query_pow_bits w)
        if ok then pure s' else throw .PowWitness
    else pure s1
  (List.range shape.num_queries).foldlM (fun acc _ => do
    let (i, s') ← ExceptT.lift (sample_bits sp acc.2 shape.index_bits)
    pure (acc.1 ++ [i], s')) ([], s2)

/-- The FRI verifier transcript of a shape. -/
def verifierTx (sp : Sponge K Com S) (shape : FriShape) : VerifierTx K Com S :=
  ⟨commit_rounds sp shape, query_phase sp shape⟩

/-- The PCS shape of the claims: each point's claimed evaluation count, and the batching difficulty. -/
def PcsShape.from_claims {C D : Type _} (params : FriParameters) (claims : List (CommitmentOpening K C D)) :
    PcsShape :=
  ⟨claims.map fun c => c.matrices.map fun m => m.points.map (·.values.length), params.batch_proof_of_work_bits⟩

/-- Replay every claimed evaluation, in commitment, matrix and point order.

A point whose count differs from the described one rejects.

A point past the description reaches a step of another kind, and the pattern player panics. -/
def claimed_openings {C D : Type _} (sp : Sponge K Com S) (shape : PcsShape) (s : S)
    (claims : List (CommitmentOpening K C D)) : ExceptT PcsTranscriptFailure Option S := do
  let described := shape.claimed_evaluation_counts.flatten.flatten
  let pts := claims.flatMap fun c => c.matrices.flatMap fun m => m.points
  pts.zipIdx.foldlM (fun st e => do
    match described[e.2]? with
    | none => ExceptT.lift none
    | some n =>
      if n ≠ e.1.values.length then throw (.ClaimedEvaluationCount e.2 n e.1.values.length)
      pure (sp.observe_values st e.1.values)) s

/-- The batching phase: grind at positive difficulty, then draw alpha. -/
def batch_phase (sp : Sponge K Com S) (shape : PcsShape) (s : S) (w : Option K) :
    ExceptT PcsTranscriptFailure Option (K × S) := do
  let s1 ← if 0 < shape.batch_pow_bits then
      match w with
      | none => throw .MissingPowWitness
      | some w => do
        let (ok, s') ← ExceptT.lift (check_witness sp s shape.batch_pow_bits w)
        if ok then pure s' else throw .PowWitness
    else pure s
  pure (sp.sample s1)

end p3_fri.transcript.mirror
