/-
Transcriptions of the quadratic sumcheck verifier: strategy.rs (the round identity), transcript.rs and data.rs.
-/
module

public import P3Sumcheck.Lagrange

@[expose] public section

namespace p3_sumcheck.mirror

open p3_sumcheck.lagrange.mirror

variable {F EF : Type _} [Field EF]

/-- How the two values a round sends are read. -/
inductive Basis where
  /-- The pair is h(0) and h(inf), and h(1) comes from the claim. -/
  | Evaluation
  /-- The pair is s(1) and s(inf), and s(0) comes from the claim. -/
  | Projective

/-- Basis::reduce_claim: the round polynomial at r, rebuilt from the pair and the running claim. -/
def Basis.reduce_claim : Basis → EF → EF → EF → EF → EF
  | .Evaluation, c_a, c_inf, r, claimed_sum => extrapolate_01inf c_a (claimed_sum - c_a) c_inf r
  | .Projective, c_a, c_inf, r, claimed_sum => extrapolate_01inf (claimed_sum - c_inf) c_a c_inf r

/-- The instance label of the basis. -/
def Basis.label : Basis → ℕ
  | .Evaluation => 0
  | .Projective => 1

/-- The errors of the quadratic sumcheck verifier. -/
inductive SumcheckError where
  | RoundCountMismatch (expected actual : ℕ)
  | MissingSumcheckData (expected_rounds : ℕ)
  | InvalidPowWitness (round difficulty : ℕ)
  | MissingPowWitness (round difficulty : ℕ)
  | PowWitnessCountMismatch (expected actual : ℕ)
  deriving DecidableEq

/-- SumcheckShape::domain_separator: the protocol name, the round count, the difficulty and the basis label. -/
def SumcheckShape.seed (num_rounds pow_bits : ℕ) (basis : Basis) : Step F EF :=
  .seed "p3-sumcheck-quadratic" [num_rounds, pow_bits, basis.label]

/-- VerifierTranscript::round: absorb the pair, check the witness, and draw the challenge. -/
def VerifierTranscript.round (S : Sponge F EF) (pow_bits round : ℕ) (h : List (Step F EF))
    (c_a c_inf : EF) (witness : Option F) : Except SumcheckError (EF × List (Step F EF)) := do
  let h := h ++ [.message [c_a, c_inf]]
  let h ← if 0 < pow_bits then
      match witness with
      | none => throw (.MissingPowWitness round pow_bits)
      | some w =>
        if S.grind h pow_bits w then pure (h ++ [.pow pow_bits w])
        else throw (.InvalidPowWitness round pow_bits)
    else pure h
  pure (S.sample h, h ++ [.challenge])

/-- One iteration of the round loop of verify_rounds. -/
def verifyRound (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F) (pow_bits : ℕ)
    (basis : Basis) (acc : List EF × EF × List (Step F EF)) (round : ℕ) :
    Except SumcheckError (List EF × EF × List (Step F EF)) := do
  let (rs, claimed_sum, h) := acc
  let (c_a, c_inf) := evals.getD round (0, 0)
  let witness := if 0 < pow_bits then wits[round]? else none
  let (r, h) ← VerifierTranscript.round S pow_bits round h c_a c_inf witness
  pure (rs ++ [r], basis.reduce_claim c_a c_inf r claimed_sum, h)

/-- SumcheckData::verify_rounds: the challenges, the reduced claim, and the sponge history.

Both counts are checked against the configuration first.

A batch of no rounds absorbs nothing. -/
def verify_rounds (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F) (h : List (Step F EF))
    (claimed_sum : EF) (expected_rounds pow_bits : ℕ) (basis : Basis) :
    Except SumcheckError (List EF × EF × List (Step F EF)) :=
  if evals.length ≠ expected_rounds then throw (.RoundCountMismatch expected_rounds evals.length)
  else
    let expected_witnesses := if 0 < pow_bits then expected_rounds else 0
    if wits.length ≠ expected_witnesses then
      throw (.PowWitnessCountMismatch expected_witnesses wits.length)
    else
      let h := if 0 < expected_rounds then h ++ [SumcheckShape.seed expected_rounds pow_bits basis] else h
      (List.range expected_rounds).foldlM (verifyRound S evals wits pow_bits basis) ([], claimed_sum, h)

/-- verify_final_sumcheck_rounds: no rounds return the empty point, and missing data with rounds is an error. -/
def verify_final_sumcheck_rounds (S : Sponge F EF) (data : Option (List (EF × EF) × List F))
    (h : List (Step F EF)) (claimed_sum : EF) (rounds pow_bits : ℕ) (basis : Basis) :
    Except SumcheckError (List EF × EF × List (Step F EF)) :=
  if rounds = 0 then pure ([], claimed_sum, h)
  else match data with
    | none => throw (.MissingSumcheckData rounds)
    | some (evals, wits) => verify_rounds S evals wits h claimed_sum rounds pow_bits basis

end p3_sumcheck.mirror
