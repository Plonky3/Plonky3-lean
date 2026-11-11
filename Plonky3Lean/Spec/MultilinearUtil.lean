module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Multilinear extensions

The definitions follow Thaler, "Proofs, Arguments, and Zero-Knowledge", Section 3.5.

A table f of 2^n values is a function on the Boolean cube {0,1}^n.

Its multilinear extension is the unique polynomial that agrees with f on the cube.

It has degree at most 1 in each variable:

```text
    f~(r) = sum_{b in {0,1}^n} eq(b, r) f(b)
    eq(x, r) = prod_i (x_i r_i + (1 - x_i)(1 - r_i))
```

A point is a list of coordinates r_0, ..., r_{n-1}.

Entry b of a table is the vertex whose coordinate 0 is the most significant bit of b:

```text
    n = 3, b = 6 = 0b110:   vertex (1, 1, 0)
```

This is the reverse of CompPoly's convention, where coordinate 0 is the least significant bit.
-/

namespace Plonky3Lean.Spec.MultilinearUtil

open MvPolynomial Finset

variable {K : Type _} [CommRing K]

/-- The vertex b of the n-cube as a point: coordinate i is bit n - 1 - i of b. -/
def vertex (n b : ℕ) : List K :=
  (List.range n).map fun i => if b.testBit (n - 1 - i) then 1 else 0

/-- The equality polynomial eq(x, r) = prod_i (x_i r_i + (1 - x_i)(1 - r_i)). -/
def eq (x r : List K) : K :=
  (List.zipWith (fun a c => a * c + (1 - a) * (1 - c)) x r).prod

/-- The equality table: entry b is eq(b, r), for b < 2^n. -/
def eqTable (r : List K) : List K :=
  (List.range (2 ^ r.length)).map fun b => eq (vertex r.length b) r

/-- The multilinear extension of the table f, evaluated at r. -/
def mle (f r : List K) : K :=
  ∑ b ∈ range (2 ^ r.length), eq (vertex r.length b) r * f.getD b 0

/-- The multilinear extension of the table f in n variables, as a polynomial. -/
noncomputable def mlePoly (f : List K) (n : ℕ) : MvPolynomial (Fin n) K :=
  ∑ b ∈ range (2 ^ n), C (f.getD b 0) *
    ∏ i : Fin n, if b.testBit (n - 1 - i) then X i else 1 - X i

/-- A polynomial of degree at most 1 in each variable. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

/-- The polynomial whose monomial coefficients are the table c.

Entry b is the coefficient of the product of the X_i whose bit n - 1 - i is set in b. -/
noncomputable def coeffPoly (c : List K) (n : ℕ) : MvPolynomial (Fin n) K :=
  ∑ b ∈ range (2 ^ n), C (c.getD b 0) * ∏ i : Fin n, if b.testBit (n - 1 - i) then X i else 1

/-- The successor on the n-cube that repeats the last vertex.

It maps x to x + 1 below 2^n - 1, and fixes 2^n - 1. -/
def succRepeat (n x : ℕ) : ℕ := if x + 1 < 2 ^ n then x + 1 else x

/-- The successor table: entry y sums eq(x, r) over the x whose successor is y. -/
def nextTable (r : List K) : List K :=
  (List.range (2 ^ r.length)).map fun y =>
    ∑ x ∈ range (2 ^ r.length), if succRepeat r.length x = y then eq (vertex r.length x) r else 0

/-- The table of the powers of v: entry b is v^b. -/
def powTable (v : K) (n : ℕ) : List K := (List.range (2 ^ n)).map (v ^ ·)

end Plonky3Lean.Spec.MultilinearUtil
