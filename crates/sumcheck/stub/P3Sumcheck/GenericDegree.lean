/-
Transcriptions of the generic-degree sumcheck verifier: generic_degree/util.rs, transcript.rs and proof.rs.

The interpolation node i is a parameter, the field's interpolation_node(i).
-/
module

public import P3Sumcheck.Model
public import P3Matrix.Assumptions.Mirror
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace p3_sumcheck.generic_degree.mirror

open p3_sumcheck.mirror p3_matrix.interpolation.mirror

variable {F EF : Type _} [Field EF] [DecidableEq EF]

/-- RoundPolyInterpolator::new: the barycentric weights of the nodes 0, ..., d, which panics on equal nodes. -/
def RoundPolyInterpolator.new (node : ℕ → EF) (degree : ℕ) : Option (Fin (degree + 1) → EF) :=
  barycentric_weights fun i : Fin (degree + 1) => node i

/-- RoundPolyInterpolator::eval: h(r) from h(0), h(2), ..., h(d) and the sum h(0) + h(1).

The width is a debug assertion, and an empty slice panics on its first entry.

A challenge on a node returns that node's value. -/
def RoundPolyInterpolator.eval (node : ℕ → EF) (degree : ℕ) (weights : Fin (degree + 1) → EF)
    (evals : List EF) (sum_constraint r : EF) : Option EF :=
  if evals.length + 1 ≠ degree + 1 then none
  else match evals with
    | [] => none
    | e0 :: rest =>
      let full : List EF := e0 :: (sum_constraint - e0) :: rest
      match (List.finRange (degree + 1)).find? (fun i : Fin (degree + 1) => decide (r - node i.val = 0)) with
      | some i => some (full.getD i.val 0)
      | none =>
        (interpolate_arbitrary_with_precomputation (fun i (_ : Fin 1) => full.getD i 0) weights
          fun i => (r - node i)⁻¹).map (· 0)

/-- The errors of the generic-degree verifier. -/
inductive GenericDegreeError where
  | RoundCountMismatch (expected actual : ℕ)
  | PolyEvalCountMismatch (round expected actual : ℕ)
  | PowWitnessCountMismatch (expected actual : ℕ)
  | MissingPowWitness (round : ℕ)
  | InvalidPowWitness (round : ℕ)
  | InvalidDegree (degree : ℕ)
  deriving DecidableEq

/-- GenericDegreeShape::domain_separator. -/
def GenericDegreeShape.seed (num_rounds degree pow_bits : ℕ) : Step F EF :=
  .seed "p3-sumcheck-generic-degree" [num_rounds, degree, pow_bits]

/-- VerifierTranscript::round: absorb the d values, whose count the step fixes, check the witness, draw the challenge. -/
def VerifierTranscript.round (S : Sponge F EF) (degree pow_bits round : ℕ) (h : List (Step F EF))
    (evals : List EF) (witness : Option F) : Except GenericDegreeError (EF × List (Step F EF)) := do
  if evals.length ≠ degree then throw (.PolyEvalCountMismatch round degree evals.length)
  let h := h ++ [.message evals]
  let h ← if 0 < pow_bits then
      match witness with
      | none => throw (.MissingPowWitness round)
      | some w =>
        if S.grind h pow_bits w then pure (h ++ [.pow pow_bits w]) else throw (.InvalidPowWitness round)
    else pure h
  pure (S.sample h, h ++ [.challenge])

/-- One iteration of the round loop of verify; none is a panic of the interpolator. -/
def verifyRound (S : Sponge F EF) (node : ℕ → EF) (degree pow_bits : ℕ)
    (weights : Fin (degree + 1) → EF) (polys : List (List EF)) (wits : List F)
    (acc : Except GenericDegreeError (List EF × EF × List (Step F EF))) (round : ℕ) :
    Option (Except GenericDegreeError (List EF × EF × List (Step F EF))) :=
  match acc with
  | .error e => some (.error e)
  | .ok (rs, running_sum, h) =>
    let evals := polys.getD round []
    let witness := if 0 < pow_bits then wits[round]? else none
    match VerifierTranscript.round S degree pow_bits round h evals witness with
    | .error e => some (.error e)
    | .ok (r, h) =>
      (RoundPolyInterpolator.eval node degree weights evals running_sum r).map fun s =>
        .ok (rs ++ [r], s, h)

/-- GenericDegreeProof::verify: the challenges, the reduced claim, and the sponge history.

The claimed sum is absorbed after the seed, before any round. -/
def verify (S : Sponge F EF) (node : ℕ → EF) (claimed_sum : EF) (polys : List (List EF))
    (wits : List F) (h : List (Step F EF)) (num_rounds degree pow_bits : ℕ) :
    Option (Except GenericDegreeError (List EF × EF × List (Step F EF))) :=
  if degree = 0 then some (.error (.InvalidDegree degree))
  else if polys.length ≠ num_rounds then some (.error (.RoundCountMismatch num_rounds polys.length))
  else
    let expected := if 0 < pow_bits then num_rounds else 0
    if wits.length ≠ expected then some (.error (.PowWitnessCountMismatch expected wits.length))
    else
      let h := h ++ [GenericDegreeShape.seed num_rounds degree pow_bits, .message [claimed_sum]]
      (RoundPolyInterpolator.new node degree).bind fun weights =>
        (List.range num_rounds).foldlM (verifyRound S node degree pow_bits weights polys wits)
          (.ok ([], claimed_sum, h))

end p3_sumcheck.generic_degree.mirror
