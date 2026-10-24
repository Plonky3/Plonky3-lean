/-
Transcriptions of the bus family's closing value in p3-multi-stark.

These do not extract.
They are generic over the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a share is the numbers the plan gives it: its side, its row and prefix variables, its block index
- the factor of a share is a function of its row point, through the openings, with a single error value
- a vector is a list, and a panic is none.

Loops, branches and the order of checks are kept.
-/
module

public import P3MultilinearUtil

@[expose] public section

namespace p3_multi_stark.bus.mirror

open p3_multilinear_util.point.mirror

/-- BusTerminalShare, read through the numbers the closing value uses. -/
structure TerminalShare where
  pull : Bool
  row_variables : ℕ
  prefix_variables : ℕ
  prefix_index : ℕ

/-- BusBindingError, the cases the closing value raises. -/
inductive BusBindingError where
  | CompositionPointDimension (expected actual : ℕ)
  | ProductPointDimension (expected actual : ℕ)
  | Evaluation
  deriving DecidableEq, Repr

variable {EF : Type _} [Field EF]

/-- One share's term of BusContext::terminal_composition.

The leading coordinates of the point not read by the table weigh it by their product.

The product-tree point selects its block, then weighs its rows against the table's rows. -/
def shareTerm (product_log_height : ℕ) (factor : TerminalShare → List EF → Except Unit EF)
    (product_point : List EF) (direction_challenge : EF) (point : List EF) (s : TerminalShare) :
    Except BusBindingError EF := do
  let direction_weight := if s.pull then direction_challenge else 1
  let row_point := point.drop (point.length - s.row_variables)
  let unused := point.take (point.length - s.row_variables)
  let fixed_all_one_selector := unused.prod
  let block_weight ← match Point.equality_at_vertex (product_point.take s.prefix_variables)
      s.prefix_index, decide (s.prefix_variables ≤ product_point.length) with
    | some w, true => pure w
    | _, _ => throw (.ProductPointDimension product_log_height product_point.length)
  let row_suffix := product_point.drop s.prefix_variables
  if row_suffix.length ≠ row_point.length then
    throw (.ProductPointDimension (s.prefix_variables + s.row_variables) product_point.length)
  let row_weight ← match Point.eval_eq (F := EF) (EF := EF) row_suffix row_point with
    | some w => pure w
    | none => throw (.ProductPointDimension product_log_height product_point.length)
  let f ← match factor s row_point with
    | .ok f => pure f
    | .error () => throw .Evaluation
  pure (direction_weight * block_weight * fixed_all_one_selector * row_weight * (f - 1))

/-- BusContext::terminal_composition, in order:

- the point must reach the tallest bus table
- the product-tree point must have the plan's dimension
- the push shares, then the pull shares, each adding its term. -/
def terminal_composition (shares : List TerminalShare) (max_num_variables product_log_height : ℕ)
    (factor : TerminalShare → List EF → Except Unit EF) (product_point : List EF)
    (direction_challenge : EF) (point : List EF) : Except BusBindingError EF := do
  if point.length < max_num_variables then
    throw (.CompositionPointDimension max_num_variables point.length)
  if product_point.length ≠ product_log_height then
    throw (.ProductPointDimension product_log_height product_point.length)
  (shares.filter (!·.pull) ++ shares.filter (·.pull)).foldlM (fun acc s => do
    let t ← shareTerm product_log_height factor product_point direction_challenge point s
    pure (acc + t)) 0

end p3_multi_stark.bus.mirror
