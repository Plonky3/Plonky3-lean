/-
Transcriptions of the points of the circle x^2 + y^2 = 1 and their maps.

What a transcription abstracts:

* the base field and its extension are one mathlib field K, base values read through their embedding;
* the field's circle generators are a table G of coordinate pairs, and asking past its adicity panics;
* square(x) is x x, double(x) is x + x, and mul_2exp_u64(x, k) is x 2^k;
* an inverse of zero panics, and so does a batch inversion with a zero entry;
* a debug assertion is checked, as in a debug build, except the circle check of the point constructor;
* a panic is none.

The point constructor debug-asserts x^2 + y^2 = 1.

That assertion is not modelled: every point the crate builds lies on the circle, which the proofs show for each map.

Loops and the order of operations are kept.
-/
module

public import P3Dft.Model
public import P3Commit.Domain

@[expose] public section

namespace p3_circle.point.mirror

open p3_dft.mirror

/-- A point of the plane, which the crate keeps on the circle. -/
structure Point (K : Type _) where
  x : K
  y : K
deriving DecidableEq

variable {K : Type _} [Field K] [DecidableEq K]

/-- The inverse, which panics at zero. -/
abbrev inv (a : K) : Option K := p3_commit.domain.mirror.inv a

/-- The inverse, or none at zero, without a panic. -/
def tryInverse (a : K) : Option K := if a = 0 then none else some a⁻¹

namespace Point

/-- The constructor; its debug assertion of x^2 + y^2 = 1 is not modelled. -/
def new (x y : K) : Point K := ⟨x, y⟩

/-- The neutral element (1, 0). -/
def ZERO : Point K := ⟨1, 0⟩

/-- The inverse stereographic projection t -> ((1 - t^2) / (1 + t^2), 2 t / (1 + t^2)), which panics at t^2 = -1. -/
def from_projective_line (t : K) : Option (Point K) := do
  let t2 := t * t
  let inv_denom ← inv (1 + t2)
  some (new ((1 - t2) * inv_denom) ((t + t) * inv_denom))

/-- The stereographic projection y / (x + 1), or none at x = -1. -/
def to_projective_line (p : Point K) : Option K :=
  (tryInverse (p.x + 1)).map fun i => i * p.y

/-- The squaring map (2 x^2 - 1, 2 x y). -/
def double (p : Point K) : Point K :=
  new (p.x * p.x + p.x * p.x - 1) ((p.x + p.x) * p.y)

/-- The squaring map applied n times. -/
def repeated_double (p : Point K) : ℕ → Point K
  | 0 => p
  | n + 1 => repeated_double (double p) n

/-- The x-coordinate step of the squaring map. -/
def vnStep (x : K) : K := x * x + x * x - 1

/-- The vanishing polynomial of the standard coset of size 2^log_n: the x-coordinate after log_n - 1 squarings.

It debug-asserts log_n >= 1. -/
def v_n (p : Point K) (log_n : ℕ) : Option K :=
  if log_n ≥ 1 then some (vnStep^[log_n - 1] p.x) else none

/-- The loop of the product of successive v_n: square, then multiply into the output. -/
def vnProdLoop : ℕ → K → K → K
  | 0, _, out => out
  | n + 1, x, out => vnProdLoop n (vnStep x) (out * vnStep x)

/-- The product of v_1, ..., v_(log_n - 1) at the point, one for log_n <= 1. -/
def v_n_prod (p : Point K) (log_n : ℕ) : K :=
  if log_n ≤ 1 then 1 else vnProdLoop (log_n - 2) p.x p.x

/-- The conjugate (x, -y), the group inverse. -/
def neg (p : Point K) : Point K := ⟨p.x, -p.y⟩

/-- The group law (x_0 x_1 - y_0 y_1, x_0 y_1 + y_0 x_1). -/
def add (p q : Point K) : Point K :=
  new (p.x * q.x - p.y * q.y) (p.x * q.y + p.y * q.x)

/-- The difference p - q = p + J(q). -/
def sub (p q : Point K) : Point K :=
  new (p.x * q.x + p.y * q.y) (p.y * q.x - p.x * q.y)

/-- The selector that vanishes at self: the projection of at - self, which panics at its pole. -/
def v_tilde_p (self at_ : Point K) : Option K :=
  to_projective_line (sub at_ self)

/-- The numerator and the denominator of the reciprocal of v_tilde_p: (at - self).x + 1 and (at - self).y. -/
def recip_v_tilde_p_num_den (self at_ : Point K) : K × K :=
  let diff := sub at_ self
  (diff.x + 1, diff.y)

/-- The value of the selector v_n / v_tilde_p at p itself: -2^(2 log_n - 1) v_n_prod(p) p.y.

It debug-asserts log_n >= 1. -/
def s_p_at_p (self : Point K) (log_n : ℕ) : Option K :=
  if log_n ≥ 1 then some (-(v_n_prod self log_n * 2 ^ (2 * log_n - 1)) * self.y) else none

/-- The single-point vanishing function at at, as a + b i: (1 - d.x, -d.y) for d = self - at. -/
def v_p (self at_ : Point K) : K × K :=
  let diff := add (neg at_) self
  (1 - diff.x, -diff.y)

/-- The double-and-add loop of the scalar multiplication. -/
def mulLoop (res self : Point K) (rhs : ℕ) : Point K :=
  if rhs = 0 then res
  else
    let res := if rhs % 2 = 1 then add res self else res
    mulLoop res (double self) (rhs / 2)
termination_by rhs
decreasing_by omega

/-- The scalar multiple n p, by double-and-add from the neutral element. -/
def mul (self : Point K) (rhs : ℕ) : Point K := mulLoop ZERO self rhs

/-- The generator of the circle subgroup of order 2^log_n, which panics past the table. -/
def generator (G : Gen (K × K)) (log_n : ℕ) : Option (Point K) :=
  (G.get log_n).map fun g => new g.1 g.2

end Point

end p3_circle.point.mirror
