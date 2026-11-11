/-
Transcriptions of the DEEP quotient on the circle and of the lambda extraction.

What a transcription abstracts, beyond the models of the points, the domains, the order and the circle FFT:

- the base field and its extension are one mathlib field K, base values read through their embedding
- a matrix is its list of rows
- a dot product zips its two iterators, so it stops at the shorter one
- a parallel loop whose items write disjoint outputs runs its items in order
- the fallible inverse returns none at zero
- the plain inverse of zero panics, and so does a batch inversion with a zero entry
- raising x to a machine-word power k is x^k
- a panic is none
- a returned option that may also panic is an option inside an option.

Loops and the order of operations are kept.
-/
module

public import P3Circle.Cfft
public import P3Circle.Ordering

@[expose] public section

namespace p3_circle.deep_quotient.mirror

open p3_dft.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_circle.ordering.mirror
open p3_commit.domain.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- The sum of the products of two lists, as far as the shorter one goes. -/
def dot_product (l r : List K) : K := ((l.zip r).map fun p => p.1 * p.2).sum

/-- The numerator and the denominator of the vanishing part.

For v_p(zeta) = re + i im, they are re - alpha^W im and 2 re. -/
def deep_quotient_vanishing_part (x zeta : Point K) (alpha_pow_width : K) : K × K :=
  let (re_v_zeta, im_v_zeta) := Point.v_p x zeta
  (re_v_zeta - alpha_pow_width * im_v_zeta, re_v_zeta + re_v_zeta)

/-- The DEEP quotient of one row: the vanishing part times sum_j alpha^j (p_j(x) - p_j(zeta)).

It is none when the denominator vanishes. -/
def deep_quotient_reduce_row (alpha_pow_width : K) (alpha_powers : List K) (x zeta : Point K)
    (ps_at_x ps_at_zeta : List K) : Option K := do
  let (vp_num, vp_denom) := deep_quotient_vanishing_part x zeta alpha_pow_width
  let vp_denom_inv ← tryInverse vp_denom
  let constraint_part := dot_product alpha_powers ((ps_at_x.zip ps_at_zeta).map fun p => -p.2 + p.1)
  some (vp_num * vp_denom_inv * constraint_part)

/-- im / (2 re) of v_p(zeta) at every point, with one batch inversion. -/
def compute_vanishing_parts (points : List (Point K)) (zeta : Point K) : Option (List K) := do
  let reim := points.map fun x => Point.v_p x zeta
  let denoms := reim.map fun p => p.1 + p.1
  let denom_inv ← batchInv denoms
  some ((reim.zip denom_inv).map fun p => p.1.2 * p.2)

/-- Add the DEEP quotient of one matrix and point to the running reduced openings:

```text
ro_i += (offset / 2 - offset alpha^W im_i / (2 re_i)) (r_i - c)
``` -/
def accumulate_deep_quotient (ro : List K) (alpha_offset alpha_pow_width : K) (reduced_rows vp : List K)
    (reduced_ps_at_zeta : K) : List K :=
  let alpha_offset_over_two := alpha_offset / 2
  let alpha_offset_alpha_pow_width := alpha_offset * alpha_pow_width
  ((ro.zip reduced_rows).zip vp).map fun p =>
    p.1.1 + (alpha_offset_over_two - alpha_offset_alpha_pow_width * p.2) * (p.1.2 - reduced_ps_at_zeta)

/-- Each row reduced with the powers of alpha: r_i = sum_j alpha^j m_ij. -/
def rowwise_alpha_reduce (rows : List (List K)) (alpha : K) : List K :=
  rows.map fun row => dot_product ((List.range row.length).map fun j => alpha ^ j) row

variable (G : Gen (K × K))

/-- Remove from an LDE in circle FFT order its component along the vanishing polynomial of the pre-blowup domain.

It uses lambda = <lde, v_d> / 2^(log_lde - 1).

Here v_d is read through the circle FFT order and the zigzag of the 2 2^log_blowup cosets.

The subtractions log_lde - log_blowup and log_lde - 1 panic below zero. -/
def extract_lambda (lde : List K) (log_blowup : ℕ) : Option (K × List K) := do
  let log_lde_size ← log2Strict lde.length
  if log_lde_size < log_blowup then none else
  let d ← CircleDomain.standard G log_lde_size
  let pts ← CircleDomain.points G d
  let v_d_init ← (pts.take (2 ^ log_blowup)).mapM fun p => Point.v_n p (log_lde_size - log_blowup)
  let b := 2 ^ log_blowup
  let v_d_at := fun (i : ℕ) =>
    let m := cfft_permute_index i log_lde_size % (2 * b)
    v_d_init.getD (if m < b then m else 2 * b - 1 - m) 0
  if log_lde_size < 1 then none else
  let v_d_2 := (2 : K) ^ (log_lde_size - 1)
  let inv_v_d_2 ← p3_commit.domain.mirror.inv v_d_2
  let lambda := ((List.range lde.length).map fun i => lde.getD i 0 * v_d_at i).sum * inv_v_d_2
  some (lambda, (List.range lde.length).map fun i => lde.getD i 0 - lambda * v_d_at i)

end p3_circle.deep_quotient.mirror
