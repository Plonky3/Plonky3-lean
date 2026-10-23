/-
The objects the transcriptions of p3-stir are written in.

* The base field F and the extension EF are mathlib fields, and EF is an F-algebra.
* A product of an extension element by a base element maps the base element into EF first.
* A vector or a slice is a list, and a panic is none.
* An inversion panics on zero.
* batch_multiplicative_inverse inverts every entry, and panics when one is zero.
* halve is division by 2.
* The two-adic generators are a table, read through Gen.get, which panics above the adicity.
* A parallel loop whose items write disjoint outputs runs its items in order.
* A chunk size of the cost model is a parameter, for every positive value.
* A usize subtraction that would wrap panics, as in a debug build.

Loops, branches and the order of operations are kept.
-/
module

public import P3Dft.Model
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.List.Iterate

@[expose] public section

namespace p3_stir.mirror

variable {K : Type _}

/-- Field::inverse, which panics on zero. -/
def inverse [Field K] [DecidableEq K] (x : K) : Option K :=
  if x = 0 then none else some x⁻¹

/-- batch_multiplicative_inverse: every inverse, which panics when an entry is zero. -/
def batchInv [Field K] [DecidableEq K] (l : List K) : Option (List K) :=
  if 0 ∈ l then none else some (l.map (·⁻¹))

/-- chunks(c): consecutive pieces of c entries, the last one possibly shorter.

It panics for c = 0. -/
def chunks (c : ℕ) (l : List K) : Option (List (List K)) :=
  if c = 0 then none
  else some ((List.range ((l.length + c - 1) / c)).map fun j => (l.drop (j * c)).take c)

/-- A geometric sweep over n entries in chunks of c: chunk i seeds start r^(i c), then each entry multiplies by r. -/
def chunkSweep [Monoid K] (c n : ℕ) (start r : K) : List K :=
  (List.range ((n + c - 1) / c)).flatMap fun i =>
    List.iterate (· * r) (start * r ^ (i * c)) (min c (n - i * c))

/-- The usize subtraction a - b, which panics when b > a. -/
def subChecked (a b : ℕ) : Option ℕ := if b ≤ a then some (a - b) else none

end p3_stir.mirror
