/-
Transcriptions of p3-sumcheck's lagrange.rs: interpolation through 0, 1 and infinity.
-/
module

public import P3Sumcheck.Model

@[expose] public section

namespace p3_sumcheck.lagrange.mirror

variable {EF : Type _} [Field EF]

/-- lagrange_weights_01inf: the weights 1 - r, r and r (r - 1). -/
def lagrange_weights_01inf (r : EF) : EF × EF × EF :=
  let r_minus_one := r - 1
  (1 - r, r, r * r_minus_one)

/-- lagrange_weights_01inf_multi: the tensor product of the weights, r_0 varying fastest. -/
def lagrange_weights_01inf_multi (rs : List EF) : List EF :=
  rs.foldl (fun current r =>
    let (l0, l1, linf) := lagrange_weights_01inf r
    [l0, l1, linf].flatMap fun li => current.map (· * li)) [1]

/-- extrapolate_01inf: the quadratic with values e0, e1 at 0, 1 and leading coefficient e_inf, at r. -/
def extrapolate_01inf (e0 e1 e_inf r : EF) : EF :=
  let (w0, w1, w_inf) := lagrange_weights_01inf r
  e0 * w0 + e1 * w1 + e_inf * w_inf

end p3_sumcheck.lagrange.mirror
