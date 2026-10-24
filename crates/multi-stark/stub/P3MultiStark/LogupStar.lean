/-
Transcriptions of the indexed-lookup (logup*) reduction of p3-multi-stark.

These do not extract.
They are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a field is a mathlib field, and its interpolation nodes are a parameter
- a machine word is a natural number below 2^64
- a statement is the list of each table's readers, each the list of its claimed values
- a vector is a list.

Loops and the order of operations are kept.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

namespace p3_multi_stark.logup_star.mirror

section Position

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- position::embed: the sum of the nodes 2^k over the set bits k of a 64-bit entry. -/
def embed (node : ℕ → F) (entry : ℕ) : F :=
  (((List.range 64).filter fun bit => entry.testBit bit).map fun bit => node (2 ^ bit)).sum

/-- position::fits: a table of 2^m entries embeds injectively when m is below the field's bits. -/
def fits (bits num_variables : ℕ) : Bool := decide (num_variables < bits)

/-- position::eval: the sum over the coordinates s of y_s embed(2^(m - 1 - s)). -/
def eval (node : ℕ → F) (point : List EF) : EF :=
  ((point.zipIdx).map fun p => p.1 * algebraMap F EF (embed node (2 ^ (point.length - 1 - p.2)))).sum

end Position

section Product

variable {EF : Type _} [Field EF]

/-- product::claimed_sum.

Readers of one table are weighted by powers of the first challenge.

Every column claim is weighted by powers of the second, tables in statement order.

A table's width is its first reader's claim count. -/
def claimed_sum (tables : List (List (List EF))) (reader_batching column_batching : EF) : EF :=
  (((tables.flatMap fun readers => (List.range (readers.headD []).length).map fun column =>
      ((readers.zipIdx).map fun q => reader_batching ^ q.2 * q.1.getD column 0).sum).zipIdx).map
    fun q => column_batching ^ q.2 * q.1).sum

end Product

end p3_multi_stark.logup_star.mirror
