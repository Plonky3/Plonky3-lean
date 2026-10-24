/-
Transcriptions of the prefix round kernel of strategy.rs, for tables over one field.

The delayed-reduction dot product is its meaning, the sum of the products.

A parallel fold adds its partial results, which field addition makes independent of the split.
-/
module

public import P3Sumcheck.Model
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace p3_sumcheck.strategy.mirror

variable {A : Type _} [Field A]

/-- The tile width K of the delayed-reduction loop. -/
def K : ℕ := 8

/-- The dot product of two slices of K entries. -/
def mixed_dot_product (a b : List A) : A := ∑ i ∈ Finset.range K, a.getD i 0 * b.getD i 0

/-- round_reduce: the component-wise sum of two accumulator pairs. -/
def round_reduce (a b : A × A) : A × A := (a.1 + b.1, a.2 + b.2)

/-- round_step: one pair of the streaming tail. -/
def round_step (acc : A × A) (e0 e1 w0 w1 : A) : A × A :=
  (acc.1 + w0 * e0, acc.2 + (w1 - w0) * (e1 - e0))

/-- chunk_round_step: one tile of K pairs, the constant term and the product of the differences. -/
def chunk_round_step (e_lo e_hi w_lo w_hi : List A) : A × A :=
  let diffs_e := List.zipWith (· - ·) e_hi e_lo
  let diffs_w := List.zipWith (· - ·) w_hi w_lo
  (mixed_dot_product w_lo e_lo, mixed_dot_product diffs_w diffs_e)

/-- sumcheck_coefficients_prefix: [h(0), h(inf)] of the product, with the round variable on the top index bit.

Unequal or odd lengths panic. -/
def sumcheck_coefficients_prefix (evals weights : List A) : Option (A × A) :=
  if evals.length ≠ weights.length ∨ evals.length % 2 ≠ 0 then none
  else
    let half := evals.length / 2
    let (e_lo, e_hi) := (evals.take half, evals.drop half)
    let (w_lo, w_hi) := (weights.take half, weights.drop half)
    let body := half / K * K
    let tile := fun (l : List A) (j : ℕ) => (l.drop (j * K)).take K
    let main := (List.range (half / K)).foldl (fun acc j =>
      round_reduce acc (chunk_round_step (tile e_lo j) (tile e_hi j) (tile w_lo j) (tile w_hi j))) (0, 0)
    let tail := (List.range (half - body)).foldl (fun acc t =>
      round_step acc (e_lo.getD (body + t) 0) (e_hi.getD (body + t) 0) (w_lo.getD (body + t) 0)
        (w_hi.getD (body + t) 0)) (0, 0)
    some (round_reduce main tail)

end p3_sumcheck.strategy.mirror
