/-
Transcriptions of the circle FRI folds: the first-layer y-fold, the x-folds, and the per-query twiddle chain.

What a transcription abstracts, beyond the models of the points, the domains and the circle FFT:

* a matrix of width 2 is its list of rows, each a pair;
* halve(x) is x / 2;
* reverse_bits_len(x, k) is the k-bit reversal of x, which it is for k > 0 or x = 0, and the folds call it on x < 2^k only;
* a parallel loop whose items write disjoint outputs runs its items in order;
* an inverse of zero panics, and so does a batch inversion with a zero entry;
* an assertion panics, and a debug assertion and a subtraction below zero are checked, as in a debug build;
* a panic is none.

Loops and the order of operations are kept.
-/
module

public import P3Circle.Cfft

@[expose] public section

namespace p3_circle.folding.mirror

open p3_dft.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_circle.cfft.mirror
open p3_commit.domain.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- Fold each row (lo, hi) with its inverted twiddle t: ((lo + hi) + beta (lo - hi) t) / 2.

It debug-asserts one twiddle per row. -/
def fold (rows : List (K × K)) (beta : K) (twiddles : List K) : Option (List K) :=
  if rows.length ≠ twiddles.length then none
  else some ((rows.zip twiddles).map fun r => (r.1.1 + r.1.2 + beta * ((r.1.1 - r.1.2) * r.2)) / 2)

variable (G : Gen (K × K))

/-- The first-layer fold, with the inverted y-twiddles of the standard domain twice the height. -/
def fold_y (beta : K) (rows : List (K × K)) : Option (List K) := do
  let log_n ← (log2Strict rows.length).map (· + 1)
  let d ← CircleDomain.standard G log_n
  let ys ← y_twiddles G d
  let invs ← batchInv ys
  fold rows beta invs

/-- The x-fold of a matrix of width 2, with the inverted x-twiddles of the standard domain twice its size.

It asserts arity 2. -/
def fold_x (beta : K) (log_arity : ℕ) (rows : List (K × K)) : Option (List K) := do
  if log_arity ≠ 1 then none
  else
    let log_n ← log2Strict (2 * rows.length)
    let d ← CircleDomain.standard G (log_n + 1)
    let xs ← x_twiddles G d 0
    let invs ← batchInv xs
    fold rows beta invs

/-- Fold two values with an inverted twiddle; it asserts exactly two values. -/
def fold_row_with_inv_twiddle (inv_twiddle beta : K) (evals : List K) : Option K :=
  match evals with
  | [e0, e1] => some ((e0 + e1 + beta * ((e0 - e1) * inv_twiddle)) / 2)
  | _ => none

/-- One query's x-fold of a row, with the twiddle of index rev(index) of the standard domain of size 2^(h + 2).

It asserts arity 2 and two values. -/
def fold_x_row (index log_folded_height log_arity : ℕ) (beta : K) (evals : List K) : Option K := do
  if log_arity ≠ 1 then none
  else if evals.length ≠ 2 then none
  else
    let d ← CircleDomain.standard G (log_folded_height + log_arity + 1)
    let tw ← nth_x_twiddle G d (bitRev log_folded_height index)
    let t ← p3_commit.domain.mirror.inv tw
    let e0 := evals.getD 0 0
    let e1 := evals.getD 1 0
    some ((e0 + e1 + beta * ((e0 - e1) * t)) / 2)

/-- The loop of the per-query chain: square the x-coordinate, and negate it when the next index bit is set. -/
def twiddleChainLoop (top_level_index : ℕ) (acc : List K × K) (r : ℕ) : List K × K :=
  let x := Point.vnStep acc.2
  let x := if (top_level_index / 2 ^ (r + 1)) % 2 = 1 then -x else x
  (acc.1 ++ [x], x)

/-- The inverted x-twiddles of every round of one query, from one seed and the squaring map. -/
def query_x_twiddles_inv (top_level_index log_max_height num_rounds : ℕ) : Option (List K) :=
  if num_rounds = 0 then some []
  else if log_max_height < 1 then none
  else do
    let seed_log_folded_height := log_max_height - 1
    let seed_idx := bitRev seed_log_folded_height (top_level_index / 2)
    let d ← CircleDomain.standard G (log_max_height + 1)
    let x ← nth_x_twiddle G d seed_idx
    let r := (List.range (num_rounds - 1)).foldl (twiddleChainLoop top_level_index) ([x], x)
    batchInv r.1

end p3_circle.folding.mirror
