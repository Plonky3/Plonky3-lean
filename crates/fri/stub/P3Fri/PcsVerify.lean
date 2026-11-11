/-
Transcription of the two-adic FRI PCS verifier.

What a transcription abstracts, beyond Verifier.lean and Replay.lean:

* the challenger is one duplex sponge, which the PCS transcript lends to the FRI run
* a panic is none, and a returned error is an error.

Branches and early returns are kept.
-/
module

public import P3Fri.Verifier
public import P3Fri.Replay

@[expose] public section

namespace p3_fri.two_adic_pcs.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror p3_fri.mirror p3_fri.config.mirror
open p3_fri.verifier.mirror p3_fri.transcript.mirror

variable {K : Type} [Field K] [DecidableEq K]

/-- The PCS verifier.

It pins the witnesses of zero difficulty, then replays the claims and the batching grind.

It draws alpha, and runs the FRI verifier on the same sponge. -/
def verify (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S)
    (params : FriParameters) (claims : List (Claim G C))
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) : Res fmmcs.Error immcs.Error Unit := do
  if ¬ check_canonical_pow_witnesses params proof then throw .NonCanonicalPowWitness
  let shape := PcsShape.from_claims params claims
  let s1 ← match ← lift (claimed_openings sp shape s claims).run with
    | .error f => throw (.ofPcsTranscript f)
    | .ok s1 => pure s1
  let (alpha, s2) ← match ← lift (batch_phase sp shape s1 (some proof.batch_pow_witness)).run with
    | .error f => throw (.ofPcsTranscript f)
    | .ok r => pure r
  verify_fri G g fmmcs immcs (verifierTx sp) params proof s2 claims commit_of alpha

end p3_fri.two_adic_pcs.mirror
