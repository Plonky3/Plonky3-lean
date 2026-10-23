/-
Transcriptions of the batched product-tree reduction: its arithmetic, its shape, and its verifier.

These do not extract: they are generic over the field traits, and the crate's dependencies do not compile in the extraction variant (docs/extractor-issues.md 180).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* a field is a mathlib field, and a `usize` is a natural number with its 64-bit bound kept where Rust checks it;
* the field's bit count and its interpolation nodes are parameters, read through the field trait;
* the Fiat-Shamir transcript is a record of its four challenge steps over an abstract state, each binding the messages it is given;
* a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Sumcheck
public import P3MultilinearUtil
public import Mathlib.Data.List.Range

@[expose] public section

namespace p3_bus.product.mirror

open p3_sumcheck.generic_degree.mirror p3_multilinear_util.point.mirror

/-! ## Arithmetic -/

section Math

variable {F : Type _} [Field F]

/-- combine: one claim per tree, weighted by consecutive powers of the challenge. -/
def combine (values : List F) (challenge : F) : F :=
  ((values.zip ((List.range values.length).map (challenge ^ ·))).map fun p => p.1 * p.2).sum

/-- interpolate_pair: the line through two values at a point. -/
def interpolate_pair (values : F × F) (point : F) : F := values.1 + point * (values.2 - values.1)

/-- interpolate_quad: a four-entry table at two low-order coordinates. -/
def interpolate_quad (values : F × F × F × F) (point : F × F) : F :=
  let low_zero := interpolate_pair (values.1, values.2.1) point.1
  let low_one := interpolate_pair (values.2.2.1, values.2.2.2) point.1
  interpolate_pair (low_zero, low_one) point.2

/-- has_distinct_round_nodes: a field of at least three bits whose nodes 0 to 5 are pairwise distinct. -/
def has_distinct_round_nodes [DecidableEq F] (bits : ℕ) (node : ℕ → F) : Bool :=
  if bits < 3 then false
  else (List.range 6).all fun i => (List.range 6).all fun j => j ≤ i || node i != node j

end Math

/-! ## Shape -/

/-- How roots are carried. -/
inductive ProductGkrRootShape where
  | Distinct
  | FirstTwoShared
  deriving DecidableEq, Repr

/-- The errors of the shape constructor. -/
inductive ProductGkrShapeError where
  | NoTrees (num_trees minimum : ℕ)
  | SharedRootNeedsTwoTrees (num_trees minimum : ℕ)
  | TreeCountOverflow (num_trees maximum : ℕ)
  | HeightOverflow (log_height maximum : ℕ)
  deriving DecidableEq, Repr

/-- The errors of the reduction. -/
inductive ProductGkrError where
  | ChallengeFieldTooSmall
  | TreeCountMismatch (expected actual : ℕ)
  | InputTooLong (tree capacity actual : ℕ)
  | SharedRootMismatch
  | RootCountMismatch (expected actual : ℕ)
  | LayerCountMismatch (expected actual : ℕ)
  | MalformedLayer (layer : ℕ)
  | LayerConsistency (layer : ℕ)
  deriving DecidableEq, Repr

/-- `usize::MAX`. -/
def USIZE_MAX : ℕ := 2 ^ 64 - 1

/-- The dimensions of one batched reduction. -/
structure ProductGkrShape where
  log_height : ℕ
  num_trees : ℕ
  root_shape : ProductGkrRootShape
  deriving DecidableEq, Repr

/-- ProductGkrShape::new: the height must fit a word, the batch must be nonempty and fit, and a shared root needs two trees. -/
def ProductGkrShape.new (log_height num_trees : ℕ) (root_shape : ProductGkrRootShape) :
    Except ProductGkrShapeError ProductGkrShape :=
  if log_height ≥ 64 then .error (.HeightOverflow log_height 63)
  else if num_trees = 0 then .error (.NoTrees num_trees 1)
  else if num_trees > USIZE_MAX / 4 then .error (.TreeCountOverflow num_trees (USIZE_MAX / 4))
  else if root_shape = .FirstTwoShared ∧ num_trees < 2 then
    .error (.SharedRootNeedsTwoTrees num_trees 2)
  else .ok ⟨log_height, num_trees, root_shape⟩

/-- root_message_len: one root per tree, less one when the first two share. -/
def ProductGkrShape.root_message_len (s : ProductGkrShape) : ℕ :=
  match s.root_shape with
  | .Distinct => s.num_trees
  | .FirstTwoShared => s.num_trees - 1

/-- The loop of layers: an odd tree starts with one binary level, and every later layer contracts two. -/
def layersLoop (log_height : ℕ) : (point_len remaining : ℕ) → List (ℕ × ℕ)
  | _, 0 => []
  | point_len, remaining + 1 =>
    let arity := if remaining + 1 = log_height ∧ (remaining + 1) % 2 = 1 then 2 else 4
    let branch_count := Nat.log2 arity
    (arity, point_len) :: layersLoop log_height (point_len + branch_count)
      (remaining + 1 - branch_count)
termination_by _ r => r
decreasing_by exact Nat.sub_lt (Nat.succ_pos _) (by split <;> decide)

/-- layers: the arity and round count of each layer, root first. -/
def ProductGkrShape.layers (s : ProductGkrShape) : List (ℕ × ℕ) := layersLoop s.log_height 0 s.log_height

/-- identity_padding_evaluation: the sum of eq(point, i) over the addresses at or above the prefix, by the binary threshold.

A point of the wrong dimension, or a prefix longer than the table, panics. -/
def ProductGkrShape.identity_padding_evaluation {F : Type _} [Field F] (s : ProductGkrShape)
    (prefix_len : ℕ) (point : List F) : Option F :=
  if point.length ≠ s.log_height then none
  else
    let capacity := 2 ^ s.log_height
    if prefix_len > capacity then none
    else if prefix_len = capacity then some 0
    else
      let (below, _) := (point.zipIdx).foldl (fun (acc : F × F) (cb : F × ℕ) =>
        let (coordinate, bit_index) := cb
        let shift := point.length - 1 - bit_index
        if (prefix_len >>> shift) % 2 = 1 then
          (acc.1 + acc.2 * (1 - coordinate), acc.2 * coordinate)
        else (acc.1, acc.2 * (1 - coordinate))) (0, 1)
      some (1 - below)

/-- encode: the roots as carried, refusing unequal shared roots. -/
def ProductGkrRootShape.encode {F : Type _} [DecidableEq F] (shape : ProductGkrRootShape)
    (roots : List F) : Option (Except ProductGkrError (List F)) :=
  match shape with
  | .Distinct => some (.ok roots)
  | .FirstTwoShared => do
    let r0 ← roots[0]?
    let r1 ← roots[1]?
    if r0 ≠ r1 then return .error .SharedRootMismatch
    pure (.ok (r0 :: roots.drop 2))

/-- decode: the roots as expanded, the first message standing for the first two roots. -/
def ProductGkrRootShape.decode {F : Type _} (shape : ProductGkrRootShape) (encoded : List F) :
    Option (List F) :=
  match shape with
  | .Distinct => some encoded
  | .FirstTwoShared => do
    let e0 ← encoded[0]?
    pure (e0 :: e0 :: encoded.drop 1)

/-! ## The proof and its verifier -/

/-- One layer's messages. -/
inductive ProductGkrLayerProof (F : Type _) where
  | Binary (children : List (F × F))
  | RadixFour (round_polys : List (Fin 5 → F)) (children : List (F × F × F × F))

/-- `ROUND_POLY_LEN`: the evaluations a degree-five round polynomial carries. -/
def ROUND_POLY_LEN : ℕ := 5

/-- The roots and the layers, root first. -/
structure ProductGkrProof (F : Type _) where
  roots : List F
  layers : List (ProductGkrLayerProof F)

/-- The roots, the shared point, and the leaf evaluations. -/
structure ProductGkrOutput (F : Type _) where
  roots : List F
  point : List F
  values : List F

/-- validate_shape: the root count, the layer count, and each layer's kind and lengths. -/
def ProductGkrProof.validate_shape {F : Type _} (p : ProductGkrProof F) (shape : ProductGkrShape) :
    Except ProductGkrError Unit := do
  if p.roots.length ≠ shape.root_message_len then
    throw (.RootCountMismatch shape.root_message_len p.roots.length)
  let layers := shape.layers
  if p.layers.length ≠ layers.length then
    throw (.LayerCountMismatch layers.length p.layers.length)
  (List.range layers.length).forM fun layer_index => do
    let valid := match layers[layer_index]?, p.layers[layer_index]? with
      | some (2, _), some (.Binary children) => children.length == shape.num_trees
      | some (4, rounds), some (.RadixFour round_polys children) =>
        round_polys.length == rounds && children.length == shape.num_trees
      | _, _ => false
    if !valid then throw (.MalformedLayer layer_index)

/-- The verifier's transcript: its state after the roots, and its four challenge steps, each binding its messages. -/
structure VerifierTranscript (F S : Type _) where
  init : List F → S
  begin_layer : S → F × S
  round : S → List F → F × S
  end_binary_layer : S → List (F × F) → F × S
  end_radix_four_layer : S → List (F × F × F × F) → (F × F) × S

/-- The verifier's loop state: the claims, the point, the first inconsistent layer, and the transcript. -/
structure VerifyState (F S : Type _) where
  values : List F
  point : List F
  inconsistent : Option ℕ
  transcript : S

section Verify

variable {F S : Type _} [Field F] [DecidableEq F] (node : ℕ → F) (T : VerifierTranscript F S)

/-- One layer of the verifier. -/
def verify_layer (weights : Fin 6 → F) (st : VerifyState F S) (layer_index : ℕ)
    (layer : ProductGkrLayerProof F) : Option (VerifyState F S) := do
  let (batching, t) := T.begin_layer st.transcript
  let running_sum := combine st.values batching
  match layer with
  | .Binary children =>
    let (b0, t) := T.end_binary_layer t children
    let expected := combine (children.map fun c => c.1 * c.2) batching
    let inconsistent := if running_sum ≠ expected then st.inconsistent.or (some layer_index)
      else st.inconsistent
    pure ⟨children.map (interpolate_pair · b0), [b0], inconsistent, t⟩
  | .RadixFour round_polys children =>
    let (running_sum, round_point, t) ← round_polys.foldlM (fun (acc : F × List F × S) round_poly => do
      let (challenge, t) := T.round acc.2.2 (List.ofFn round_poly)
      let running_sum ← RoundPolyInterpolator.eval node 5 weights (List.ofFn round_poly) acc.1
        challenge
      pure (running_sum, acc.2.1 ++ [challenge], t)) (running_sum, [], t)
    let eq ← Point.eval_eq (F := F) (EF := F) st.point round_point
    let expected := eq * combine (children.map fun c => c.1 * c.2.1 * c.2.2.1 * c.2.2.2) batching
    let inconsistent := if running_sum ≠ expected then st.inconsistent.or (some layer_index)
      else st.inconsistent
    let (branches, t) := T.end_radix_four_layer t children
    pure ⟨children.map (interpolate_quad · branches), [branches.1, branches.2] ++ round_point,
      inconsistent, t⟩

/-- ProductGkrProof::verify: the field check, the shape check, the layers, then the first inconsistent layer, if any.

The point is reversed to the most-significant-first convention. -/
def ProductGkrProof.verify (bits : ℕ) (p : ProductGkrProof F) (shape : ProductGkrShape) :
    Option (Except ProductGkrError (ProductGkrOutput F)) := do
  if !has_distinct_round_nodes bits node then return .error .ChallengeFieldTooSmall
  match p.validate_shape shape with
  | .error e => return .error e
  | .ok () => pure ()
  let roots ← shape.root_shape.decode p.roots
  let weights ← RoundPolyInterpolator.new node 5
  let st ← ((shape.layers.zip p.layers).zipIdx).foldlM (fun st (lp : ((ℕ × ℕ) × ProductGkrLayerProof F) × ℕ) =>
    verify_layer node T weights st lp.2 lp.1.2) ⟨roots, [], none, T.init p.roots⟩
  match st.inconsistent with
  | some layer => pure (.error (.LayerConsistency layer))
  | none => pure (.ok ⟨roots, st.point.reverse, st.values⟩)

end Verify

end p3_bus.product.mirror
