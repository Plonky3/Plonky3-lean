/-
Transcriptions of the evaluation of planned declarations: the leaf factor of one declaration at one point.

These do not extract: they are generic over the field traits.

Code over `ExtensionField` also does not extract (docs/extractor-issues.md 180).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- the evaluation point and the challenges share one extension field EF, into which base values embed
- the flattening of a declaration is a post-order walk of its tree
- the Rust worklist records each distinct node once, in another order
- evaluation only needs every operand to precede its user, so the order does not matter
- the fingerprint weights are the equality table of p3-multilinear-util, at its packing width and task split
- a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Bus.Plan
public import P3MultilinearUtil

@[expose] public section

namespace p3_bus.evaluation.mirror

open p3_bus.mirror p3_bus.plan.mirror p3_air.symbolic.mirror p3_multilinear_util.point.mirror

variable {F EF : Type} [Field F] [Field EF] [Algebra F EF]

/-- The values resolving every supported leaf at one point. -/
structure BusEvaluation (F EF : Type) where
  main : List EF
  preprocessed : List EF
  «public» : List F
  periodic : List EF
  is_first_row : EF
  is_last_row : EF
  is_transition : EF

/-- One node of a flattened declaration, operands by position. -/
inductive BusNode (F : Type) where
  | Main (column : ℕ)
  | Preprocessed (column : ℕ)
  | Public (index : ℕ)
  | Periodic (column : ℕ)
  | IsFirstRow
  | IsLastRow
  | IsTransition
  | Constant (value : F)
  | Add (x y : ℕ)
  | Sub (x y : ℕ)
  | Neg (x : ℕ)
  | Mul (x y : ℕ)

/-- The evaluation errors. -/
inductive BusEvaluationError where
  | MainOffset (column offset : ℕ)
  | PreprocessedOffset (column offset : ℕ)
  | PeriodicColumn (column : ℕ)
  | MainColumn (column : ℕ)
  | PreprocessedColumn (column : ℕ)
  | PublicValue (index : ℕ)
  | UnknownBus (bus num_buses : ℕ)
  | PayloadWidth (bus expected actual : ℕ)
  | FingerprintWidth (expected actual : ℕ)
  deriving DecidableEq

/-- Compile a leaf: a current-row access, a selector or a constant.

Any other row is an error. -/
def compile_leaf : BaseLeaf F → Except BusEvaluationError (BusNode F)
  | .Variable v => match v.entry with
    | .Main 0 => .ok (.Main v.index)
    | .Main offset => .error (.MainOffset v.index offset)
    | .Preprocessed 0 => .ok (.Preprocessed v.index)
    | .Preprocessed offset => .error (.PreprocessedOffset v.index offset)
    | .Public => .ok (.Public v.index)
    | .Periodic => .ok (.Periodic v.index)
  | .IsFirstRow => .ok .IsFirstRow
  | .IsLastRow => .ok .IsLastRow
  | .IsTransition => .ok .IsTransition
  | .Constant c => .ok (.Constant c)

/-- Append the expression's nodes, operands first, and return its position. -/
def compile_expression : List (BusNode F) → SymbolicExpression F →
    Except BusEvaluationError (List (BusNode F) × ℕ)
  | nodes, .Leaf leaf => do pure (nodes ++ [← compile_leaf leaf], nodes.length)
  | nodes, .Add x y _ => do
    let (nodes, ix) ← compile_expression nodes x
    let (nodes, iy) ← compile_expression nodes y
    pure (nodes ++ [.Add ix iy], nodes.length)
  | nodes, .Sub x y _ => do
    let (nodes, ix) ← compile_expression nodes x
    let (nodes, iy) ← compile_expression nodes y
    pure (nodes ++ [.Sub ix iy], nodes.length)
  | nodes, .Mul x y _ => do
    let (nodes, ix) ← compile_expression nodes x
    let (nodes, iy) ← compile_expression nodes y
    pure (nodes ++ [.Mul ix iy], nodes.length)
  | nodes, .Neg x _ => do
    let (nodes, ix) ← compile_expression nodes x
    pure (nodes ++ [.Neg ix], nodes.length)

/-- The equality table of the fingerprint point, with coordinate 0 on the top bit. -/
def fingerprint_weights (W task_len : ℕ) (fingerprint : List EF) : Option (List EF) :=
  Point.equality_weights_msb W task_len fingerprint

/-- One declaration's factor, settled against the weights. -/
structure BusFactorPlan (F EF : Type) where
  nodes : List (BusNode F)
  payload : List ℕ
  activation : Option ℕ
  payload_weights : List EF
  shifted_offset : EF

/-- One node's value, from the values of the nodes before it. -/
def nodeValue (values : BusEvaluation F EF) (scratch : List EF) :
    BusNode F → Except BusEvaluationError EF
  | .Main column => match values.main[column]? with
    | some v => .ok v
    | none => .error (.MainColumn column)
  | .Preprocessed column => match values.preprocessed[column]? with
    | some v => .ok v
    | none => .error (.PreprocessedColumn column)
  | .Public index => match values.«public»[index]? with
    | some v => .ok (algebraMap F EF v)
    | none => .error (.PublicValue index)
  | .Periodic column => match values.periodic[column]? with
    | some v => .ok v
    | none => .error (.PeriodicColumn column)
  | .IsFirstRow => .ok values.is_first_row
  | .IsLastRow => .ok values.is_last_row
  | .IsTransition => .ok values.is_transition
  | .Constant c => .ok (algebraMap F EF c)
  | .Add x y => .ok (scratch.getD x 0 + scratch.getD y 0)
  | .Sub x y => .ok (scratch.getD x 0 - scratch.getD y 0)
  | .Neg x => .ok (-scratch.getD x 0)
  | .Mul x y => .ok (scratch.getD x 0 * scratch.getD y 0)

/-- Evaluate one declaration's factor, in order:

- one forward pass over the nodes
- the payload inner product
- the shift
- the activation's interpolation with the identity.

An operand index is always earlier than its user, so reading it never panics.

The transcription reads zero past the end. -/
def BusFactorPlan.evaluate (f : BusFactorPlan F EF) (values : BusEvaluation F EF) :
    Except BusEvaluationError EF := do
  let scratch ← f.nodes.foldlM (fun scratch node => do
    pure (scratch ++ [← nodeValue values scratch node])) []
  let fingerprint := ((f.payload.zip f.payload_weights).map fun (node, weight) =>
    weight * scratch.getD node 0).foldl (· + ·) 0
  let factor := f.shifted_offset - fingerprint
  pure (match f.activation with
    | none => factor
    | some node => 1 + (factor - 1) * scratch.getD node 0)

/-- Compile one declaration's factor:

- check the bus, the payload width and the weight count
- fold the identity bits into the shift
- flatten the declaration. -/
def BusPlan.compile_factor (plan : BusPlan) (bus : ℕ) (interaction : SymbolicBusInteraction F)
    (weights : List EF) (offset : EF) : Except BusEvaluationError (BusFactorPlan F EF) := do
  let some domain := plan.domains[bus]?
    | throw (.UnknownBus bus plan.domains.length)
  if interaction.fields.length ≠ domain.payload_width then
    throw (.PayloadWidth bus domain.payload_width interaction.fields.length)
  if weights.length ≠ plan.fingerprint_width then
    throw (.FingerprintWidth plan.fingerprint_width weights.length)
  let domain_constant := ((weights.zipIdx).filter fun (_, slot) =>
    plan.tuple_slot bus slot = some (.DomainBit true)).foldl
    (fun (acc : EF) (p : EF × ℕ) => acc + p.1) 0
  let (nodes, payload) ← interaction.fields.foldlM (fun (acc : List (BusNode F) × List ℕ) e => do
    let (nodes, i) ← compile_expression acc.1 e
    pure (nodes, acc.2 ++ [i])) ([], [])
  let (nodes, activation) ← match interaction.activation with
    | .Always => pure (nodes, none)
    | .Boundary .First => pure (nodes ++ [.IsFirstRow], some nodes.length)
    | .Boundary .Last => pure (nodes ++ [.IsLastRow], some nodes.length)
    | .Boolean selector => do
      let (nodes, i) ← compile_expression nodes selector
      pure (nodes, some i)
  pure ⟨nodes, payload, activation, weights.take domain.payload_width, offset - domain_constant⟩

end p3_bus.evaluation.mirror
