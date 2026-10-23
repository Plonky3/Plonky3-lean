module

public import Mathlib.LinearAlgebra.Lagrange
public import P3Dft.Model

@[expose] public section

/-!
# FRI: the folding operator

The folding operator of Ben-Sasson, Bentov, Horesh and Riabzev, "Fast Reed-Solomon IOP of proximity", ICALP 2018.

A polynomial p splits into a pieces by the residue of its exponents modulo a:

```text
    p(X) = sum_{j < a} X^j p_j(X^a),     coefficient m of p_j = coefficient m a + j of p
```

The fold at the challenge beta recombines the pieces:

```text
    fold(p, a, beta) = sum_{j < a} beta^j p_j
```

For a = 2 this is the even part plus beta times the odd part.

ArkLib names the pieces splitNth and the fold polyFold, with the same coefficients.

A word on the a points of a coset folds to the value at beta of the polynomial of degree below a through it.

The points of a coset s H of order a = 2^k come in bit-reversed order, as the code stores them: point j is s omega^(rev_k(j)).
-/

namespace Plonky3Lean.Spec.Fri

open Polynomial Finset

variable {K : Type _} [Field K]

/-- The j-th of the a pieces of p: coefficient m is coefficient m a + j of p. -/
noncomputable def split (p : K[X]) (a j : ℕ) : K[X] :=
  ∑ i ∈ p.support with i % a = j, C (p.coeff i) * X ^ (i / a)

/-- The fold of p by a at beta: the sum of beta^j times the j-th piece. -/
noncomputable def polyFold (p : K[X]) (a : ℕ) (β : K) : K[X] :=
  ∑ j ∈ range a, C (β ^ j) * split p a j

/-- The points of the coset s H of order 2^k in bit-reversed order: point j is s omega^(rev_k(j)). -/
def revCoset (s ω : K) (k : ℕ) (j : Fin (2 ^ k)) : K := s * ω ^ p3_dft.mirror.bitRev k j.val

/-- The fold of a word on the coset: the value at beta of the polynomial of degree below 2^k through it. -/
noncomputable def foldValue (s ω : K) (k : ℕ) (y : Fin (2 ^ k) → K) (β : K) : K :=
  (Lagrange.interpolate univ (revCoset s ω k) y).eval β

/-! ## The reduced opening

The opening argument batches every claim f_i(z) = y_i into one function, with powers of a challenge alpha.

Haböck's summary of FRI (eprint 2022/1216) and the ethSTARK documentation (eprint 2021/582) use the quotient (f(X) - y) / (X - z).

The code writes the same quotient as (y - f(x)) / (z - x).

At one height, claim k carries values y_(k,i) of columns with values c_(k,i) at the query point x, and starts at ladder position off_k:

```text
    R(x) = sum_k sum_i alpha^(off_k + i) (y_(k,i) - c_(k,i)) / (z_k - x)

    off_0 = 0,   off_(k+1) = off_k + (number of values of claim k)
```
-/

/-- The reduced opening at x of claims (z, values, column values at x), from ladder position off. -/
def reducedOpening (α x : K) : ℕ → List (K × List K × List K) → K
  | _, [] => 0
  | off, (z, ys, cs) :: L =>
    (∑ i ∈ range ys.length, α ^ (off + i) * (ys.getD i 0 - cs.getD i 0)) / (z - x) +
      reducedOpening α x (off + ys.length) L

end Plonky3Lean.Spec.Fri
