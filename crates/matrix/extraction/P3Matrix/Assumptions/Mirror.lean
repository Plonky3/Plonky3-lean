/-
Transcriptions of the interpolation routines, the in-place bit reversal and the flattened extension view.

These do not extract: they are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the field is a mathlib field K, standing for the extension field;
* base-field values are read in K through their embedding;
* the column-wise dot product is its meaning, M^T v;
* batch inversion is the elementwise inverse;
* the two-adic generator of order 2^k is a parameter omega;
* a panic is none.

Loops, branches, early returns and the order of checks are kept.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace p3_matrix.interpolation.mirror

open Finset

variable {K : Type _} [Field K] [DecidableEq K]

/-- The column-wise dot product M^T v, one sum per column. -/
def columnwise {N w : ℕ} (M : Fin N → Fin w → K) (v : Fin N → K) : Fin w → K :=
  fun c => ∑ i, v i * M i c

/-- Adjusted weights: asserts z != 0, then subtracts 1 / z from each inverse difference. -/
def compute_adjusted_weights {N : ℕ} (z : K) (d : Fin N → K) : Option (Fin N → K) :=
  if z = 0 then none else some fun i => d i - z⁻¹

/-- The precomputed coset path on 2^k rows.

It scales the dot product with the weights by z (z^N - g^N) / (N g^N).

Inverting N g^N panics when it is zero. -/
def interpolate_coset_with_precomputation {w : ℕ} (k : ℕ) (M : Fin (2 ^ k) → Fin w → K)
    (g z : K) (adj : Fin (2 ^ k) → K) : Option (Fin w → K) :=
  let gN := g ^ 2 ^ k
  let denom := gN * (2 ^ k : K)
  if denom = 0 then none
  else some fun c => columnwise M adj c * (z * (z ^ 2 ^ k - gN) * denom⁻¹)

/-- Coset interpolation on 2^k rows, with omega for the generator of order 2^k.

* A zero shift panics, as the coset constructor rejects it.
* The first coset point g omega^i equal to z returns row i.
* The point z = 0 returns the column sums times 2^(-k).
* Any other point goes through the adjusted weights of 1 / (z - g omega^i). -/
def interpolate_coset {w : ℕ} (k : ℕ) (ω g z : K) (M : Fin (2 ^ k) → Fin w → K) :
    Option (Fin w → K) :=
  if g = 0 then none
  else
    match (List.finRange (2 ^ k)).find? (fun i => decide (z - g * ω ^ i.val = 0)) with
    | some i => some (M i)
    | none =>
      if z = 0 then some fun c => columnwise M (fun _ => 1) c * ((2 : K) ^ k)⁻¹
      else
        (compute_adjusted_weights z fun i => (z - g * ω ^ i.val)⁻¹).bind
          (interpolate_coset_with_precomputation k M g z)

/-- Subgroup interpolation: coset interpolation with shift 1. -/
def interpolate_subgroup {w : ℕ} (k : ℕ) (ω z : K) (M : Fin (2 ^ k) → Fin w → K) :
    Option (Fin w → K) :=
  interpolate_coset k ω 1 z M

/-- One step (i, j), j < i, of the weight loop.

A zero difference x_i - x_j returns nothing.

Otherwise the denominator of i is multiplied by the difference, and that of j by its negation. -/
def barycentric_step {n : ℕ} (x : Fin n → K) (acc : Option (Fin n → K)) (p : Fin n × Fin n) :
    Option (Fin n → K) :=
  acc.bind fun d =>
    let diff := x p.1 - x p.2
    if diff = 0 then none
    else some fun t => if t = p.1 then d t * diff else if t = p.2 then d t * -diff else d t

/-- The pairs (i, j) with j < i, in loop order: i ascending, then j ascending. -/
def lowerPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => j.val < i.val).map fun j => (i, j)

/-- Barycentric weights: an empty list for no points, otherwise the double loop, then each inverse. -/
def barycentric_weights {n : ℕ} (x : Fin n → K) : Option (Fin n → K) :=
  if n = 0 then some fun _ => 0
  else ((lowerPairs n).foldl (barycentric_step x) (some fun _ => 1)).map fun d i => (d i)⁻¹

/-- The precomputed arbitrary-domain path.

No rows give zero columns.

Otherwise it divides M^T s by the sum of s, where s_i is the inverse difference times the weight.

Inverting a zero sum panics. -/
def interpolate_arbitrary_with_precomputation {n w : ℕ} (M : Fin n → Fin w → K)
    (wt d : Fin n → K) : Option (Fin w → K) :=
  if n = 0 then some fun _ => 0
  else
    let s : Fin n → K := fun i => d i * wt i
    let den := ∑ i, s i
    if den = 0 then none else some fun c => columnwise M s c * den⁻¹

/-- Interpolation at an arbitrary point.

The weights come first, so equal points return nothing.

Then the first x_i equal to z returns row i, and otherwise the precomputed path runs with 1 / (z - x_i). -/
def interpolate_arbitrary_point {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (z : K) :
    Option (Fin w → K) :=
  (barycentric_weights x).bind fun wt =>
    match (List.finRange n).find? (fun i => decide (z = x i)) with
    | some i => some (M i)
    | none => interpolate_arbitrary_with_precomputation M wt fun i => (z - x i)⁻¹

/-- The state of Newton's loop: the coefficient rows, and the coefficients of the basis polynomial. -/
structure RecoverState (w : ℕ) (K : Type _) where
  result : ℕ → Fin w → K
  basis : ℕ → K

/-- Iteration k of Newton's loop over n points.

* b = prod_{i<k} (x_k - x_i), whose inverse returns nothing at zero.
* s_j evaluates the current rows at x_k by Horner's rule, from row k - 1 down to row 0.
* c_j = (y_{k,j} - s_j) / b.
* Row i gains c_j times basis coefficient i, for i <= k.
* The basis is multiplied by X - x_k, top coefficient first when it fits. -/
def recover_step {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (k : Fin n)
    (st : RecoverState w K) : Option (RecoverState w K) :=
  let xk := x k
  let b := ((List.finRange n).filter (fun i => i.val < k.val)).foldl (fun acc i => acc * (xk - x i)) 1
  if b = 0 then none
  else
    let scratch : Fin w → K := fun j =>
      (List.range k.val).reverse.foldl (fun s i => s * xk + st.result i j) 0
    let coef : Fin w → K := fun j => (M k j - scratch j) * b⁻¹
    let result : ℕ → Fin w → K := fun i j =>
      if i ≤ k.val then st.result i j + coef j * st.basis i else st.result i j
    let basis : ℕ → K := fun i =>
      if i = k.val + 1 then (if k.val + 1 < n then st.basis k.val else st.basis i)
      else if 1 ≤ i ∧ i ≤ k.val then st.basis (i - 1) - xk * st.basis i
      else if i = 0 then -xk * st.basis 0
      else st.basis i
    some { result, basis }

/-- Newton's recovery of the coefficients: the loop from zero rows and the basis 1.

Row i of the result holds the degree-i coefficients. -/
def recover_coefficients {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) :
    Option (Fin n → Fin w → K) :=
  ((List.finRange n).foldl (fun st k => st.bind (recover_step M x k))
    (some { result := fun _ _ => 0, basis := fun i => if i = 0 then 1 else 0 })).map
    fun st i j => st.result i.val j

/-- Interpolation from pairs: an empty list for no points, otherwise the one column of Newton's recovery. -/
def interpolate_lagrange {n : ℕ} (pts : Fin n → K × K) : Option (Fin n → K) :=
  if n = 0 then some fun _ => 0
  else (recover_coefficients (w := 1) (fun i _ => (pts i).2) (fun i => (pts i).1)).map
    fun r i => r i 0

end p3_matrix.interpolation.mirror

namespace p3_matrix.util.mirror

variable {R : Type _}

/-- Exchanges two rows. -/
def swap {h : ℕ} (rows : Fin h → R) (i j : Fin h) : Fin h → R :=
  fun r => if r = i then rows j else if r = j then rows i else rows r

/-- In-place bit reversal on h rows, with rev for the k-bit reversal.

Each row i is swapped with row rev(i) when i < rev(i).

The parallel branch runs the same swaps in chunks.

The width-one branch calls a different slice routine and is not transcribed. -/
def reverse_matrix_index_bits {h : ℕ} (rev : Fin h → Fin h) (rows : Fin h → R) : Fin h → R :=
  (List.finRange h).foldl (fun acc i => if i < rev i then swap acc i (rev i) else acc) rows

end p3_matrix.util.mirror

namespace p3_matrix.extension.mirror

variable {F EF : Type _}

/-- The flat iterator, taking len items from the remaining extension elements.

The index counts the coordinates of the current element already read.

Reading moves to the next element once the index reaches the dimension D. -/
def flat_iter_take [Inhabited F] (D : ℕ) (coords : EF → List F) : List EF → ℕ → ℕ → List F
  | _, _, 0 => []
  | inner, idx, len + 1 =>
    let inner' := if idx = D then inner.tail else inner
    let idx' := if idx = D then 0 else idx
    match inner' with
    | [] => []
    | a :: _ => (coords a)[idx']! :: flat_iter_take D coords inner' (idx' + 1) len

/-- A run of a flat row: skip start / D elements, start at coordinate start mod D, take end - start items. -/
def flat_row_subseq [Inhabited F] (D : ℕ) (coords : EF → List F) (row : List EF) (start stop : ℕ) : List F :=
  flat_iter_take D coords (row.drop (start / D)) (start % D) (stop - start)

end p3_matrix.extension.mirror
