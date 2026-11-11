/-
Transcriptions of the periodic-column support.

They include the trait default that tabulates periodic columns on the quotient domain.

What a transcription abstracts, beyond the model of the coset's polynomial space:

- a machine word is a natural number below 2^64
- an operation that leaves the word panics
- the trailing-zero count of zero is 64, the word size
- a row-major matrix is its flat list of values and its width
- the error values are kept, with the offending index
- a debug assertion is checked, as in a debug build.

Loops, branches, early returns and the order of checks are kept.
-/
module

public import P3Commit.Domain
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace p3_commit.periodic.mirror

open p3_dft.mirror p3_field.coset.mirror p3_commit.domain.mirror

/-- The word size: values are below 2^64. -/
abbrev WORD : ℕ := 2 ^ 64

/-- The power-of-two test on a word. -/
def isPowerOfTwo (n : ℕ) : Bool := decide (n ≠ 0 ∧ 2 ^ Nat.log 2 n = n)

/-- The trailing-zero count of a word: the 2-adic valuation, and 64 for zero. -/
def trailingZeros (n : ℕ) : ℕ := if n = 0 then 64 else padicValNat 2 n

/-- Why a column cannot be laid over the trace. -/
inductive PeriodicColumnShapeError where
  | LengthNotPowerOfTwo (index length : ℕ)
  | LengthNotDividingHeight (index length height : ℕ)
  deriving DecidableEq

/-- Columns screened against a height. -/
structure PeriodicColumns (K : Type _) where
  columns : List (List K)
  height : ℕ

variable {K : Type _}

/-- Screen one column: its length must be a power of two dividing the height. -/
def screenStep (height : ℕ) (acc : Except PeriodicColumnShapeError Unit) (c : List K × ℕ) :
    Except PeriodicColumnShapeError Unit := do
  acc
  let length := c.1.length
  if ¬ isPowerOfTwo length then throw (.LengthNotPowerOfTwo c.2 length)
  if height % length ≠ 0 then throw (.LengthNotDividingHeight c.2 length height)
  pure ()

/-- The screening constructor: the first offending column, in order, is reported. -/
def PeriodicColumns.new (columns : List (List K)) (height : ℕ) :
    Except PeriodicColumnShapeError (PeriodicColumns K) := do
  columns.zipIdx.foldl (screenStep height) (pure ())
  pure ⟨columns, height⟩

/-- The longest period, absent when there are no columns. -/
def PeriodicColumns.max_period (p : PeriodicColumns K) : Option ℕ :=
  (p.columns.map List.length).max?

/-- The compact table: values in row-major order, the width, and the cached height. -/
structure PeriodicLdeTable (K : Type _) where
  values : List K
  width : ℕ
  height : ℕ

/-- The constructor.

The height is the length over the width, zero for width zero.

It must be zero or a power of two. -/
def PeriodicLdeTable.new (values : List K) (width : ℕ) : Option (PeriodicLdeTable K) :=
  let height := if width = 0 then 0 else values.length / width
  if height = 0 ∨ isPowerOfTwo height then some ⟨values, width, height⟩ else none

/-- The empty table. -/
def PeriodicLdeTable.empty : PeriodicLdeTable K := ⟨[], 0, 0⟩

def PeriodicLdeTable.is_empty (t : PeriodicLdeTable K) : Bool := t.values.isEmpty

/-- The period of the packed row groups.

It is the height shifted right by the smaller trailing-zero count.

A zero pack width fails the debug check, and a shift by 64 or more panics. -/
def PeriodicLdeTable.packed_group_period (t : PeriodicLdeTable K) (pack_width : ℕ) : Option ℕ :=
  if pack_width = 0 then none
  else
    let log_gcd := min (trailingZeros t.height) (trailingZeros pack_width)
    if log_gcd < 64 then some (t.height / 2 ^ log_gcd) else none

/-- The value of a column at an LDE index.

The row is the index masked by height - 1.

An empty table fails the debug check, and an index past the values panics. -/
def PeriodicLdeTable.get (t : PeriodicLdeTable K) (lde_idx col_idx : ℕ) : Option K :=
  if t.height = 0 then none
  else
    let row_idx := Nat.land lde_idx (t.height - 1)
    t.values[row_idx * t.width + col_idx]?

/-- The evaluator for no periodic columns: it asserts there are none. -/
def unitEvalOnLde (periodic_table : List (List K)) : Option (PeriodicLdeTable K) :=
  if periodic_table.isEmpty then some PeriodicLdeTable.empty else none

def unitEvalAtPoint (periodic_table : List (List K)) : Option (List K) :=
  if periodic_table.isEmpty then some [] else none

variable [Field K] [DecidableEq K] (G : Gen K)

/-- The quotient-domain points the table is built on.

They are the first point, then the next point taken repeatedly. -/
def quotientPoints (quotient : Coset G) : ℕ → K → Option (List K)
  | 0, _ => some []
  | n + 1, pt => do
    let next ← Coset.next_point G quotient pt
    let rest ← quotientPoints quotient n next
    pure (pt :: rest)

/-- The trait default.

It tabulates every periodic column, padded to the longest period.

The table covers the first p b quotient points, for p the longest period and b the blowup. -/
def build_periodic_lde_table (cols : List (List K)) (trace quotient : Coset G) :
    Option (PeriodicLdeTable K) :=
  let trace_size := Coset.size G trace
  let quotient_size := Coset.size G quotient
  if quotient_size < trace_size then none
  else if quotient_size % trace_size ≠ 0 then none
  else
    let blowup := quotient_size / trace_size
    match PeriodicColumns.new cols trace_size with
    | .error _ => none
    | .ok periodic_cols =>
      match periodic_cols.max_period with
      | none => some PeriodicLdeTable.empty
      | some max_period =>
        let extended_height := max_period * blowup
        if WORD ≤ extended_height then none
        else if quotient_size < extended_height then none
        else
          let num_cols := periodic_cols.columns.length
          if WORD ≤ extended_height * num_cols then none
          else do
            let quotient_pts ← quotientPoints G quotient extended_height
              (Coset.first_point G quotient)
            let padded_cols := periodic_cols.columns.map fun col =>
              (List.range max_period).map fun i => col.getD (i % col.length) 0
            let row_major ← (quotient_pts.take extended_height).mapM fun point =>
              padded_cols.mapM fun padded => Coset.evaluate_periodic_column_at G trace padded point
            PeriodicLdeTable.new row_major.flatten num_cols

end p3_commit.periodic.mirror
