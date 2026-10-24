/-
Transcriptions of the security accounting p3-multi-stark charges for its own AIR reduction.

These do not extract: the statement is read off generic AIRs, and the error bits are floating-point numbers.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* an error term is its numerator over a field order, before p3-security takes logarithms in floating point;
* the denominator is the challenge field's order, or one less for a draw rejecting zero;
* a term with a zero numerator is omitted, as p3-security omits it;
* only the four AIR terms are kept, for a statement with no skip round: the lookup terms have their own transcriptions.

Loops, branches and the order of terms are kept.
-/
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace p3_multi_stark.security.mirror

/-- Which denominator a term is charged over. -/
inductive Denominator where
  /-- The challenge field's order. -/
  | Field
  /-- One less than the order: the draw rejects zero. -/
  | NonZero
  deriving DecidableEq

/-- One charged term: its label, its numerator, its denominator. -/
structure Term where
  label : String
  numerator : ℕ
  denominator : Denominator
  deriving DecidableEq

/-- MultilinearAirParams, the fields the AIR terms read. -/
structure AirParams where
  num_instances : ℕ
  max_num_constraints : ℕ
  num_variables : ℕ
  constraint_degree : ℕ

/-- p3_security::multilinear::reduction_terms, its AIR terms with no skip round: alpha over the constraints, beta over the instances, the zerocheck point over the variables, and the sumcheck rounds at one degree above the constraints. -/
def air_terms (p : AirParams) : List Term :=
  [⟨"constraint-batching", p.max_num_constraints - 1, .Field⟩,
   ⟨"air-batching", p.num_instances - 1, .Field⟩,
   ⟨"zerocheck", p.num_variables, .NonZero⟩,
   ⟨"constraint-sumcheck", p.num_variables * (p.constraint_degree + 1), .Field⟩].filter
    (·.numerator ≠ 0)

/-- assess_statement: the variable count, the largest trace arity or the lookup reduction's. -/
def num_variables (heights : List ℕ) (lookup_variables : Option ℕ) : ℕ :=
  max (heights.foldl max 0) (lookup_variables.getD 0)

/-- assess_statement: the degree charged, the largest AIR degree, raised to one below the bus composition degree. -/
def charged_degree (air_degrees : List ℕ) (bus_degree : Option ℕ) : ℕ :=
  let d := air_degrees.foldl max 0
  match bus_degree with
  | none => d
  | some b => max d (b - 1)

end p3_multi_stark.security.mirror
