/-
Transcriptions of the fractional-GKR verifier of p3-multi-stark.

These do not extract.
They are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a field is a mathlib field
- the interpolation nodes are a parameter, read through the field trait
- the Fiat-Shamir transcript is a record of its challenge steps over an abstract state
- each step binds the messages it is given
- a vector is a list, a fixed-width array a function on Fin, and a panic is none.

Loops, branches and the order of checks are kept.
-/
module

public import P3Sumcheck
public import P3MultilinearUtil

@[expose] public section

namespace p3_multi_stark.fractional_gkr.mirror

open p3_sumcheck.generic_degree.mirror p3_multilinear_util.point.mirror

/-- SplitFraction: the two child fractions a layer opens. -/
structure SplitFraction (T : Type _) where
  n0 : T
  d0 : T
  n1 : T
  d1 : T

/-- SplitFraction::gate: the sum of the two fractions, batched by lambda.

It is d1 n0 + d0 n1 + lambda d0 d1. -/
def SplitFraction.gate {A : Type _} [CommRing A] (s : SplitFraction A) (lambda : A) : A :=
  s.d1 * s.n0 + s.d0 * s.n1 + lambda * s.d0 * s.d1

/-- FractionGkrError: why the verifier rejects. -/
inductive FractionGkrError where
  | InvalidVariableCount
  | InvalidLayerCount (expected actual : ℕ)
  | InvalidRoundCount (layer expected actual : ℕ)
  | ZeroRootDenominator
  | LayerConsistency (layer : ℕ)
  deriving DecidableEq, Repr

/-- The evaluations a cubic round polynomial carries: at the nodes 0, 2 and 3. -/
def ROUND_POLY_LEN : ℕ := 3

/-- FractionGkrLayerProof: the round polynomials and the two children of one layer. -/
structure FractionGkrLayerProof (EF : Type _) where
  round_polys : List (Fin 3 → EF)
  claims : SplitFraction EF

/-- FractionGkrProof: the root denominator and the layers, root first. -/
structure FractionGkrProof (EF : Type _) where
  root_denominator : EF
  layers : List (FractionGkrLayerProof EF)

/-- FractionGkrOutput: the point, and the claimed numerator and denominator there. -/
structure FractionGkrOutput (EF : Type _) where
  point : List EF
  numerator : EF
  denominator : EF

/-- FractionGkrVerifierTranscript: its state after the root denominator, and its three challenge steps.

Each step binds its messages. -/
structure VerifierTranscript (EF S : Type _) where
  init : ℕ → EF → S
  begin_layer : S → EF × S
  round : S → List EF → EF × S
  end_layer : S → SplitFraction EF → EF × S

/-- The verifier's loop state:

- the point
- the claimed numerator and denominator there
- the first inconsistent layer
- the transcript. -/
structure VerifyState (EF S : Type _) where
  point : List EF
  numerator : EF
  denominator : EF
  inconsistent : Option ℕ
  transcript : S

/-- The first layer whose round count is not its position, with that count. -/
def firstBadRound {EF : Type _} (layers : List (FractionGkrLayerProof EF)) : Option (ℕ × ℕ) :=
  (layers.zipIdx.find? fun p => p.1.round_polys.length != p.2).map fun p =>
    (p.2, p.1.round_polys.length)

section Verify

variable {EF S : Type _} [Field EF] [DecidableEq EF] (node : ℕ → EF) (T : VerifierTranscript EF S)

/-- The round loop of one layer: each round draws its challenge, then interpolates the claim there. -/
def roundStep (weights : Fin 4 → EF) (acc : EF × List EF × S) (round_poly : Fin 3 → EF) :
    Option (EF × List EF × S) := do
  let (r, t) := T.round acc.2.2 (List.ofFn round_poly)
  let running_sum ← RoundPolyInterpolator.eval node 3 weights (List.ofFn round_poly) acc.1 r
  pure (running_sum, acc.2.1 ++ [r], t)

/-- One layer of verify_fractional_gkr, in order:

- lambda batches the claimed numerator and denominator
- the rounds reduce the batched claim to one point
- the claim is compared with eq times the gate of the children
- the branch challenge interpolates the children into the next claim.

A failed comparison is recorded, and the replay goes on. -/
def verify_layer (weights : Fin 4 → EF) (st : VerifyState EF S) (layer_index : ℕ)
    (layer : FractionGkrLayerProof EF) : Option (VerifyState EF S) := do
  let (lambda, t) := T.begin_layer st.transcript
  let (running_sum, round_point, t) ← layer.round_polys.foldlM (roundStep node T weights)
    (st.numerator + lambda * st.denominator, [], t)
  let eq ← Point.eval_eq (F := EF) (EF := EF) st.point round_point
  let expected := eq * layer.claims.gate lambda
  let inconsistent := if running_sum ≠ expected then st.inconsistent.or (some layer_index)
    else st.inconsistent
  let (branch, t) := T.end_layer t layer.claims
  pure ⟨branch :: round_point, layer.claims.n0 + branch * (layer.claims.n1 - layer.claims.n0),
    layer.claims.d0 + branch * (layer.claims.d1 - layer.claims.d0), inconsistent, t⟩

/-- verify_fractional_gkr, in order:

- the variable count, the layer count and each layer's round count
- the root denominator
- a panic on equal interpolation nodes
- the layers, from the claim of a zero root numerator
- the first inconsistent layer, if any. -/
def verify_fractional_gkr (proof : FractionGkrProof EF) (num_variables : ℕ) :
    Option (Except FractionGkrError (FractionGkrOutput EF)) := do
  if num_variables < 1 then return .error .InvalidVariableCount
  if proof.layers.length ≠ num_variables then
    return .error (.InvalidLayerCount num_variables proof.layers.length)
  match firstBadRound proof.layers with
  | some (layer, actual) => return .error (.InvalidRoundCount layer layer actual)
  | none => pure ()
  if proof.root_denominator = 0 then return .error .ZeroRootDenominator
  let t := T.init num_variables proof.root_denominator
  let weights ← RoundPolyInterpolator.new node 3
  let st ← proof.layers.zipIdx.foldlM (fun st p => verify_layer node T weights st p.2 p.1)
    ⟨[], 0, proof.root_denominator, none, t⟩
  match st.inconsistent with
  | some layer => pure (.error (.LayerConsistency layer))
  | none => pure (.ok ⟨st.point, st.numerator, st.denominator⟩)

end Verify

end p3_multi_stark.fractional_gkr.mirror
