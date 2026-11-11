/-
Transcriptions of the polynomial space of a two-adic multiplicative coset.

What a transcription abstracts, beyond the models of p3-field's coset, p3-dft and p3-matrix:

- the base field and its extension are one mathlib field K, base values read through their embedding
- the field's generator is a parameter g
- a matrix of height h is its rows, a function from row indices, as in p3-dft's model
- an inverse or a division by zero panics, and so does a batch inversion with a zero entry
- an iterator is the list it yields
- an ordered map is a list sorted by key
- a debug assertion is checked, and a subtraction that leaves the word panics, as in a debug build.

Loops, branches and the order of operations are kept.
-/
module

public import P3Dft.Model
public import P3Field.Coset
public import P3Matrix
public import Mathlib.Data.Nat.Size

@[expose] public section

namespace p3_commit.domain.mirror

open p3_dft.mirror p3_field.coset.mirror p3_matrix.interpolation.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- The coset type over the generator table G. -/
abbrev Coset (G : Gen K) := TwoAdicMultiplicativeCoset K G.adicity G.gen

/-- The four selectors:

- the first row
- the last row
- all but the last row
- the inverse vanishing polynomial. -/
structure LagrangeSelectors (T : Type _) where
  is_first_row : T
  is_last_row : T
  is_transition : T
  inv_vanishing : T

/-- The inverse, which panics at zero. -/
def inv (a : K) : Option K := if a = 0 then none else some a⁻¹

/-- The quotient, which panics when the divisor is zero. -/
def div (a b : K) : Option K := if b = 0 then none else some (a / b)

/-- Batch inversion: every entry inverted, and a panic if any entry is zero. -/
def batchInv (l : List K) : Option (List K) :=
  if ∀ x ∈ l, x ≠ 0 then some (l.map (·⁻¹)) else none

/-- Zip a list with the endless repetition of another.

Entry m is a_(m mod |a|) * b_m. -/
def zipCycle (a b : List K) : List K :=
  b.zipIdx.map fun p => a.getD (p.2 % a.length) 0 * p.1

/-- The ceiling base-2 logarithm, as the bit length of n - 1.

It is zero for n = 0 and n = 1. -/
def log2Ceil (n : ℕ) : ℕ := Nat.size (n - 1)

variable (G : Gen K)

namespace Coset

/-- The number of points. -/
def size (c : Coset G) : ℕ := TwoAdicMultiplicativeCoset.size c

/-- The first point: the shift. -/
def first_point (c : Coset G) : K := c.shift

/-- The next point: multiplication by the subgroup generator, always defined. -/
def next_point (c : Coset G) (x : K) : Option K := some (x * c.subgroup_generator)

/-- A coset disjoint from this one.

Its shift is this shift times the field generator.

Its subgroup is the smallest one of size at least min_size. -/
def try_create_disjoint_domain (c : Coset G) (g : K) (min_size : ℕ) : Option (Coset G) :=
  TwoAdicMultiplicativeCoset.new (c.shift * g) (log2Ceil min_size)

/-- The panicking variant of the disjoint domain. -/
def create_disjoint_domain (c : Coset G) (g : K) (min_size : ℕ) : Option (Coset G) :=
  Coset.try_create_disjoint_domain G c g min_size

/-- The num_chunks cosets shift h^i K, with K the subgroup num_chunks times smaller.

The chunk count must be a power of two no larger than the size. -/
def split_domains (c : Coset G) (num_chunks : ℕ) : Option (List (Coset G)) := do
  let log_chunks ← log2Strict num_chunks
  if log_chunks ≤ c.log_size then
    (List.range num_chunks).mapM fun i =>
      TwoAdicMultiplicativeCoset.new (c.shift * c.subgroup_generator ^ i)
        (c.log_size - log_chunks)
  else none

/-- Distribute the rows over num_chunks matrices.

Row r goes to chunk r mod num_chunks, at row r / num_chunks.

The two debug assertions are checked, and the copy is the row-by-row loop. -/
def split_evals {V : Type _} [Zero V] (c : Coset G) (num_chunks height : ℕ) (rows : ℕ → V) :
    Option (List (ℕ → V)) :=
  if height ≠ Coset.size G c then none
  else match log2Strict num_chunks with
    | none => none
    | some l =>
      if l ≤ c.log_size then
        let rows_per_chunk := height / num_chunks
        let values := (List.range rows_per_chunk).foldl (fun acc i =>
          (List.range num_chunks).foldl (fun acc chunk =>
            fun ch r => if ch = chunk ∧ r = i then rows (i * num_chunks + chunk) else acc ch r)
            acc) (fun _ _ => 0)
        some ((List.range num_chunks).map values)
      else none

/-- The vanishing polynomial at a point: (x / shift)^(2^log_size) - 1. -/
def vanishing_poly_at_point (c : Coset G) (point : K) : K :=
  (point * c.shift_inverse) ^ 2 ^ c.log_size - 1

/-- The selectors at a point, with u = x / shift, z = u^n - 1 and h the subgroup generator.

They are z / (u - 1), z / (u - h^(-1)), u - h^(-1) and 1 / z. -/
def selectors_at_point (c : Coset G) (point : K) : Option (LagrangeSelectors K) := do
  let unshifted_point := point * c.shift_inverse
  let z_h := unshifted_point ^ 2 ^ c.log_size - 1
  let is_first_row ← div z_h (unshifted_point - 1)
  let h_inv ← inv c.subgroup_generator
  let is_last_row ← div z_h (unshifted_point - h_inv)
  let h_inv' ← inv c.subgroup_generator
  let inv_vanishing ← inv z_h
  pure ⟨is_first_row, is_last_row, unshifted_point - h_inv', inv_vanishing⟩

/-- The selectors of a subgroup at every point of a coset at least as large.

It requires:

- the subgroup's shift is one
- the coset's shift is not one
- the coset is at least as large. -/
def selectors_on_coset (c coset : Coset G) : Option (LagrangeSelectors (List K)) :=
  if c.shift ≠ 1 then none
  else if coset.shift = 1 then none
  else if coset.log_size < c.log_size then none
  else do
    let rate_bits := coset.log_size - c.log_size
    let s_pow_n := coset.shift ^ 2 ^ c.log_size
    let ω ← G.get rate_bits
    let evals := (powersList ω (2 ^ rate_bits)).map fun x => s_pow_n * x - 1
    let xs := coset.iter
    let single_point_selector := fun (i : ℕ) => do
      let coset_i := c.subgroup_generator ^ i
      let invs ← batchInv (xs.map fun x => x - coset_i)
      pure (zipCycle evals invs)
    let subgroup_last ← inv c.subgroup_generator
    let is_first_row ← single_point_selector 0
    let is_last_row ← single_point_selector (Coset.size G c - 1)
    let inv_evals ← batchInv evals
    pure ⟨is_first_row, is_last_row, xs.map (· - subgroup_last),
      (List.range (Coset.size G coset)).map fun m => inv_evals.getD (m % inv_evals.length) 0⟩

/-- Interpolate evaluations over the coset of their length, with this coset's shift, at a point.

The length must be a power of two that the table covers. -/
def evaluate_polynomial_at (c : Coset G) (evals : List K) (point : K) : Option K := do
  let k ← log2Strict evals.length
  let ω ← G.get k
  let v ← interpolate_coset (w := 1) k ω c.shift point fun i _ => evals.getD i.val 0
  pure (v 0)

/-- The trait's default for one periodic column: expand to the full size, then interpolate. -/
def default_evaluate_periodic_column_at (c : Coset G) (col : List K) (point : K) : Option K :=
  if col.length = 0 then none
  else Coset.evaluate_polynomial_at G c
    ((List.range (Coset.size G c)).map fun i => col.getD (i % col.length) 0) point

/-- One periodic column of length p.

Interpolate over the coset of order p with the shift raised to n / p, at x^(n / p). -/
def evaluate_periodic_column_at (c : Coset G) (col : List K) (point : K) : Option K := do
  let log_period ← log2Strict col.length
  if log_period ≤ c.log_size then
    let folds := c.log_size - log_period
    let sub_coset ← (TwoAdicMultiplicativeCoset.new (c.shift ^ 2 ^ folds) log_period : Option (Coset G))
    Coset.evaluate_polynomial_at G sub_coset col (point ^ 2 ^ folds)
  else none

/-- The trait's default for several columns: one at a time, after the debug check of the height. -/
def default_evaluate_periodic_columns_at (c : Coset G) (cols : List (List K)) (height : ℕ)
    (point : K) : Option (List K) :=
  if height ≠ Coset.size G c then none
  else cols.mapM fun col => Coset.evaluate_periodic_column_at G c col point

/-- Insert a value under a key of a map kept sorted by key, appending to the key's list. -/
def mapInsert (k v : ℕ) : List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | [] => [(k, [v])]
  | (k', vs) :: rest =>
    if k = k' then (k', vs ++ [v]) :: rest
    else if k < k' then (k, [v]) :: (k', vs) :: rest
    else (k', vs) :: mapInsert k v rest

/-- The column indices grouped by length, in increasing length. -/
def colsByPeriod (cols : List (List K)) : List (ℕ × List ℕ) :=
  cols.zipIdx.foldl (fun m p => mapInsert p.1.length p.2 m) []

/-- One period class: interleave its columns into one matrix and interpolate them together. -/
def periodStep (c : Coset G) (cols : List (List K)) (point : K) (acc : Option (ℕ → K))
    (entry : ℕ × List ℕ) : Option (ℕ → K) := do
  let result ← acc
  let (period, indices) := entry
  let log_period ← log2Strict period
  if log_period ≤ c.log_size then
    let folds := c.log_size - log_period
    let sub_shift := c.shift ^ 2 ^ folds
    let sub_point := point ^ 2 ^ folds
    let k := indices.length
    let values := indices.zipIdx.foldl (fun (values : ℕ → K) q =>
      ((cols.getD q.1 []).zipIdx.foldl (fun (values : ℕ → K) rv =>
        fun j => if j = rv.2 * k + q.2 then rv.1 else values j) values)) (fun _ => 0)
    let ω ← G.get log_period
    let evals ← interpolate_coset (w := k) log_period ω sub_shift sub_point
      fun r col => values (r.val * k + col.val)
    pure (indices.zipIdx.foldl (fun (result : ℕ → K) q =>
      fun j => if h : j = q.1 ∧ q.2 < k then evals ⟨q.2, h.2⟩ else result j) result)
  else none

/-- Several periodic columns: columns sharing a period share one interpolation. -/
def evaluate_periodic_columns_at (c : Coset G) (cols : List (List K)) (height : ℕ)
    (point : K) : Option (List K) :=
  if height ≠ Coset.size G c then none
  else do
    let result ← (colsByPeriod cols).foldl (periodStep G c cols point) (some fun _ => 0)
    pure ((List.range cols.length).map result)

end Coset

end p3_commit.domain.mirror
