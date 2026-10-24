/-
Transcriptions of the bus's security accounting.

They cover the dimensions the plan derives, and the numerators p3-security charges for them.

These do not extract: the plan is built by the generic planner, and the error bits are floating-point numbers.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- an error term is its numerator over the challenge-field order
- p3-security takes logarithms of it in floating point, which is not transcribed
- a term with a zero numerator is omitted, as p3-security omits it.

Loops, branches and the order of operations are kept.
-/
module

public import P3Bus.Plan

@[expose] public section

namespace p3_bus.security.mirror

open p3_bus.plan.mirror p3_bus.product.mirror

/-- The dimensions the security model reads off the plan's product schedule and geometry. -/
structure BusSecurityDims where
  log_height : ℕ
  tree_count : ℕ
  sumcheck_rounds : ℕ
  layer_count : ℕ
  collapse_challenges : ℕ
  tuple_variables : ℕ
  non_padding_leaf_counts : ℕ × ℕ

/-- The security model of a plan.

It reads the schedule's rounds, layers and collapse coordinates.

Then it reads the tuple variables and leaf counts. -/
def BusPlan.security_dims (plan : BusPlan) : BusSecurityDims :=
  let shape := plan.product_shape
  let layers := shape.layers
  { log_height := shape.log_height
    tree_count := shape.num_trees
    sumcheck_rounds := (layers.map (·.2)).sum
    layer_count := layers.length
    collapse_challenges := (layers.map fun l => Nat.log2 l.1).sum
    tuple_variables := plan.geometry.tuple_variables
    non_padding_leaf_counts := plan.geometry.non_padding_leaf_counts }

/-- The numerators of the fingerprint, sumcheck, batching and collapse terms.

The last three appear only when nonzero. -/
def components (d : BusSecurityDims) : List ℕ :=
  let factors := max d.non_padding_leaf_counts.1 d.non_padding_leaf_counts.2
  [max d.tuple_variables 1 * factors] ++
    ([5 * d.sumcheck_rounds, d.layer_count * (d.tree_count - 1), d.collapse_challenges].filter
      (· ≠ 0))

end p3_bus.security.mirror
