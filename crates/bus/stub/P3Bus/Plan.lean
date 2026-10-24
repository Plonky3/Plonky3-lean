/-
Transcriptions of the bus plan: the named domains, the tuple layout, the block layout, and the planner.

These do not extract: the planner is generic over the field traits.

Code over `ExtensionField` also does not extract (docs/extractor-issues.md 180).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a machine word is a natural number
- an addition, a shift or a power of two past 64 bits is the error Rust returns
- a sorted map keyed by name is a list sorted by name
- a symbolic expression is its tree
- the planner's pointer-keyed visited set is omitted, since a tree has no shared node
- revisiting a node would change no answer anyway
- a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Bus.Builder
public import P3Bus.Product

@[expose] public section

namespace p3_bus.plan.mirror

open p3_bus.mirror p3_bus.product.mirror p3_air.symbolic.mirror

/-! ## Machine-word helpers -/

/-- ceil(log_2 n): the bit length of n - 1. -/
def log2_ceil_usize (n : ℕ) : ℕ := (n - 1).size

/-- The least power of two at or above n, none past 2^63. -/
def checked_next_power_of_two (n : ℕ) : Option ℕ :=
  if n ≤ 2 ^ 63 then some (2 ^ Nat.clog 2 n) else none

/-- Addition of machine words, none at 2^64 or more. -/
def checked_add (a b : ℕ) : Option ℕ := if a + b < 2 ^ 64 then some (a + b) else none

/-! ## Domains and slots -/

/-- One named bus and its identity. -/
structure BusDomain where
  «name» : String
  payload_width : ℕ
  identity : ℕ
  deriving DecidableEq

/-- One little-endian bit of the identity, zero past 64. -/
def BusDomain.identity_bit (d : BusDomain) (bit : ℕ) : Bool :=
  bit < 64 && (d.identity >>> bit) % 2 == 1

/-- The meaning of one slot of a padded tuple. -/
inductive BusTupleSlot where
  | Payload (index : ℕ)
  | DomainBit (bit : Bool)
  | Zero
  deriving DecidableEq

/-- The AIR and declaration owning a block. -/
structure BusBlockOwner where
  air : ℕ
  declaration : ℕ
  deriving DecidableEq

/-- One aligned block of a side's product tree. -/
structure BusBlock where
  bus : ℕ
  direction : BusDirection
  owner : BusBlockOwner
  log_height : ℕ
  offset : ℕ
  deriving DecidableEq

/-- The dimensions the security accounting reads. -/
structure BusSecurityGeometry where
  tuple_variables : ℕ
  non_padding_leaf_counts : ℕ × ℕ
  logical_leaf_count : ℕ
  log_logical_leaf_count : ℕ
  tree_count : ℕ
  layer_count : ℕ
  deriving DecidableEq

/-- A plan:

- the domains
- the tuple dimensions
- the blocks of each side
- the geometry
- the product shape. -/
structure BusPlan where
  domains : List BusDomain
  payload_slots : ℕ
  domain_slots : ℕ
  logical_tuple_width : ℕ
  fingerprint_width : ℕ
  pushes : List BusBlock
  pulls : List BusBlock
  geometry : BusSecurityGeometry
  product_shape : ProductGkrShape

/-- The meaning of a tuple slot, in slot order:

- a payload position
- zero up to the widest payload
- the identity bits
- zero. -/
def BusPlan.tuple_slot (plan : BusPlan) (bus slot : ℕ) : Option BusTupleSlot := do
  let domain ← plan.domains[bus]?
  if slot ≥ plan.fingerprint_width then none
  if slot < domain.payload_width then return .Payload slot
  if slot < plan.payload_slots then return .Zero
  if slot < plan.logical_tuple_width then
    return .DomainBit (domain.identity_bit (slot - plan.payload_slots))
  return .Zero

/-- The blocks of one side. -/
def BusPlan.blocks (plan : BusPlan) : BusDirection → List BusBlock
  | .Push => plan.pushes
  | .Pull => plan.pulls

/-! ## The planner -/

/-- An access the opening-based evaluator cannot answer. -/
inductive UnsupportedBusAccess where
  | MainOffset (offset : ℕ)
  | PreprocessedOffset (offset : ℕ)
  deriving DecidableEq

/-- Where a rejected expression sits. -/
inductive BusExpressionLocation where
  | Field (index : ℕ)
  | Activation
  deriving DecidableEq

/-- The planner's errors. -/
inductive BusPlanError where
  | DeclarationCountOverflow
  | HeightOverflow (air : ℕ)
  | EmptyTuple (air declaration : ℕ)
  | InvalidBusName (air declaration : ℕ) (source : BusNameError)
  | PayloadWidthMismatch («name» : String) (expected actual : ℕ)
  | DomainCountOverflow
  | TupleWidthOverflow
  | LeafCountOverflow (direction : BusDirection)
  | UnsupportedExpression (air declaration : ℕ) (location : BusExpressionLocation)
      (access : UnsupportedBusAccess)
  | ProductShape (error : ProductGkrShapeError)

/-- One symbolic declaration. -/
structure SymbolicBusInteraction (F : Type _) where
  bus_name : String
  direction : BusDirection
  fields : List (SymbolicExpression F)
  activation : BusActivation (SymbolicExpression F)

/-- One AIR's declarations and its height. -/
structure BusPlanInput (F : Type _) where
  log_height : ℕ
  interactions : List (SymbolicBusInteraction F)

/-- The access of one leaf, if the evaluator cannot answer it. -/
def leafAccess {F : Type _} : BaseLeaf F → Option UnsupportedBusAccess
  | .Variable v => match v.entry with
    | .Main 0 | .Preprocessed 0 | .Public | .Periodic => none
    | .Main offset => some (.MainOffset offset)
    | .Preprocessed offset => some (.PreprocessedOffset offset)
  | _ => none

/-- The worklist walk of expression validation: pop a node, report a rejected leaf, push the operands. -/
def validateWalk {F : Type _} : List (SymbolicExpression F) → Option UnsupportedBusAccess
  | [] => none
  | .Leaf leaf :: pending => (leafAccess leaf).or (validateWalk pending)
  | .Add x y _ :: pending | .Sub x y _ :: pending | .Mul x y _ :: pending =>
    validateWalk (y :: x :: pending)
  | .Neg x _ :: pending => validateWalk (x :: pending)
termination_by pending => (pending.map sizeOf).sum
decreasing_by all_goals (simp_wf; try omega)

/-- The first rejected access in the walk. -/
def validate_expression {F : Type _} (air declaration : ℕ) (location : BusExpressionLocation)
    (expression : SymbolicExpression F) : Except BusPlanError Unit :=
  match validateWalk [expression] with
  | some access => .error (.UnsupportedExpression air declaration location access)
  | none => .ok ()

/-- Validate one declaration: each field in order, then a caller selector. -/
def validate_interaction {F : Type _} (air declaration : ℕ) (interaction : SymbolicBusInteraction F) :
    Except BusPlanError Unit := do
  (interaction.fields.zipIdx).forM fun (expression, field) =>
    validate_expression air declaration (.Field field) expression
  match interaction.activation with
  | .Boolean expression => validate_expression air declaration .Activation expression
  | _ => pure ()

/-- One declaration waiting for its block. -/
structure PendingBlock where
  bus : ℕ
  direction : BusDirection
  owner : BusBlockOwner
  log_height : ℕ

/-- The block order: pushes first, then by decreasing height, then bus, AIR and declaration. -/
def pendingLe (a b : PendingBlock) : Bool :=
  let ka := (a.direction.index, a.log_height, a.bus, a.owner.air, a.owner.declaration)
  let kb := (b.direction.index, b.log_height, b.bus, b.owner.air, b.owner.declaration)
  ka.1 < kb.1 || (ka.1 = kb.1 && (ka.2.1 > kb.2.1 || (ka.2.1 = kb.2.1 &&
    (ka.2.2.1 < kb.2.2.1 || (ka.2.2.1 = kb.2.2.1 && (ka.2.2.2.1 < kb.2.2.2.1 ||
      (ka.2.2.2.1 = kb.2.2.2.1 && ka.2.2.2.2 ≤ kb.2.2.2.2)))))))

/-- The planner's first loop.

It checks each AIR's height and each declaration, and records each bus's width. -/
def collectWidths {F : Type _} (inputs : List (BusPlanInput F)) :
    Except BusPlanError (List (String × ℕ)) :=
  (inputs.zipIdx).foldlM (fun widths (input, air) => do
    if input.log_height ≥ 64 then throw (.HeightOverflow air)
    (input.interactions.zipIdx).foldlM (fun widths (interaction, declaration) => do
      if interaction.fields.isEmpty then throw (.EmptyTuple air declaration)
      match BusName.try_new interaction.bus_name with
      | .error source => throw (.InvalidBusName air declaration source)
      | .ok _ => pure ()
      validate_interaction air declaration interaction
      match widths.lookup interaction.bus_name with
      | some expected =>
        if expected ≠ interaction.fields.length then
          throw (.PayloadWidthMismatch interaction.bus_name expected interaction.fields.length)
        pure widths
      | none => pure (widths ++ [(interaction.bus_name, interaction.fields.length)])) widths) []

/-- One step of the block layout loop: the block starts where its side's leaves end so far. -/
def layoutStep (acc : List BusBlock × List BusBlock × ℕ × ℕ) (block : PendingBlock) :
    Except BusPlanError (List BusBlock × List BusBlock × ℕ × ℕ) := do
  let len := 2 ^ block.log_height
  let offset := if block.direction.index = 0 then acc.2.2.1 else acc.2.2.2
  let some next := checked_add offset len | throw (.LeafCountOverflow block.direction)
  let b : BusBlock := ⟨block.bus, block.direction, block.owner, block.log_height, offset⟩
  match block.direction with
  | .Push => pure (acc.1 ++ [b], acc.2.1, next, acc.2.2.2)
  | .Pull => pure (acc.1, acc.2.1 ++ [b], acc.2.2.1, next)

/-- The block layout loop. -/
def layoutBlocks (pending : List PendingBlock) :
    Except BusPlanError (List BusBlock × List BusBlock × ℕ × ℕ) :=
  pending.foldlM layoutStep ([], [], 0, 0)

/-- Build the plan, in order:

- the widths
- the domains, in name order
- the tuple dimensions
- the sorted blocks and their offsets
- the product shape. -/
def BusPlan.build {F : Type _} (inputs : List (BusPlanInput F)) :
    Except BusPlanError (Option BusPlan) := do
  let some declaration_count := inputs.foldlM (fun count input =>
      checked_add count input.interactions.length) 0
    | throw .DeclarationCountOverflow
  if declaration_count = 0 then return none
  let widths ← collectWidths inputs
  let sorted := widths.mergeSort fun a b => decide (a.1 ≤ b.1)
  let domain_count := sorted.length
  let some identity_limit := checked_add domain_count 1 | throw .DomainCountOverflow
  let domain_slots := log2_ceil_usize identity_limit
  let payload_slots := (sorted.map (·.2)).foldl max 0
  let some logical_tuple_width := checked_add payload_slots domain_slots
    | throw .TupleWidthOverflow
  let some fingerprint_width := checked_next_power_of_two logical_tuple_width
    | throw .TupleWidthOverflow
  let tuple_variables := Nat.log2 fingerprint_width
  let domains := (sorted.zipIdx).map fun ((nm, payload_width), bus) =>
    (⟨nm, payload_width, bus + 1⟩ : BusDomain)
  let busIndex (nm : String) : ℕ := (domains.findIdx? (·.«name» = nm)).getD 0
  let pending := (inputs.zipIdx).flatMap fun (input, air) =>
    (input.interactions.zipIdx).map fun (interaction, declaration) =>
      (⟨busIndex interaction.bus_name, interaction.direction, ⟨air, declaration⟩, input.log_height⟩ :
        PendingBlock)
  let pending := pending.mergeSort pendingLe
  let (pushes, pulls, push_count, pull_count) ← layoutBlocks pending
  let (largest_direction, used) := if push_count ≥ pull_count then (BusDirection.Push, push_count)
    else (BusDirection.Pull, pull_count)
  let used := max used 1
  let some logical_leaf_count := checked_next_power_of_two used
    | throw (.LeafCountOverflow largest_direction)
  let log_logical_leaf_count := Nat.log2 logical_leaf_count
  let product_shape ← match ProductGkrShape.new log_logical_leaf_count 2 .FirstTwoShared with
    | .ok shape => pure shape
    | .error e => throw (.ProductShape e)
  let geometry : BusSecurityGeometry := ⟨tuple_variables, (push_count, pull_count),
    logical_leaf_count, log_logical_leaf_count, product_shape.num_trees,
    product_shape.layers.length⟩
  return some ⟨domains, payload_slots, domain_slots, logical_tuple_width, fingerprint_width,
    pushes, pulls, geometry, product_shape⟩

end p3_bus.plan.mirror
