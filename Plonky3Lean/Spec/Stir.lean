module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-!
# STIR's operators

The definitions follow Arnon, Chiesa, Fenzi and Yogev, "STIR: Reed-Solomon Proximity Testing with Fewer Queries", eprint 2024/390, Sections 4 and 5.

They are stated over one field K.

Where ArkLib's STIR formalization has the same object, the definition here is the same: ansPoly, vanishingPoly and quotient follow ArkLib.ProofSystem.Stir.Quotienting, and degCor, ri and combine follow ArkLib.ProofSystem.Stir.Combine.

A coefficient list reads as a polynomial, constant term first:

```text
    [c_0, c_1, c_2]   reads as   c_0 + c_1 X + c_2 X^2
```

A smooth coset of size 2^n is s <omega> for omega of order 2^n:

```text
    L = { s, s omega, ..., s omega^(2^n - 1) },   entry i of a codeword is the value at s omega^i
```
-/

namespace Plonky3Lean.Spec.Stir

open Polynomial Finset

variable {K : Type _} [Field K]

/-- The polynomial with coefficient list l, constant term first. -/
noncomputable def coeffPoly (l : List K) : K[X] :=
  ∑ i ∈ range l.length, C (l.getD i 0) * X ^ i

/-- The smooth coset s <omega> of size 2^n. -/
def cosetSet [DecidableEq K] (s ω : K) (n : ℕ) : Finset K :=
  (range (2 ^ n)).image fun i => s * ω ^ i

/-! ## Quotients (Section 4.2) -/

/-- Definition 4.2: the interpolant of degree below |S| of the answers on S. -/
noncomputable def ansPoly [DecidableEq K] (S : Finset K) (ans : K → K) : K[X] :=
  Lagrange.interpolate S id ans

/-- Definition 4.2: the monic polynomial vanishing exactly on S. -/
noncomputable def vanishingPoly (S : Finset K) : K[X] :=
  ∏ s ∈ S, (X - C s)

/-- Definition 4.2: Quotient(f, S, Ans, Fill). -/
noncomputable def quotient [DecidableEq K] (f : K → K) (S : Finset K) (ans fill : K → K) (x : K) : K :=
  if x ∈ S then fill x else (f x - (ansPoly S ans).eval x) / (vanishingPoly S).eval x

/-- Definition 4.3: PolyQuotient(f, S), the quotient of f - Ans by the vanishing polynomial. -/
noncomputable def polyQuotient [DecidableEq K] (f : K[X]) (S : Finset K) : K[X] :=
  (f - ansPoly S fun x => f.eval x) /ₘ vanishingPoly S

/-! ## Folding (Section 4.4) -/

/-- Fact 4.6 for q = X^k: the l-th part f_l, with f(X) = sum_{l < k} X^l f_l(X^k). -/
noncomputable def splitPart (f : K[X]) (k l : ℕ) : K[X] :=
  ∑ i ∈ range (f.natDegree + 1), C (f.coeff (i * k + l)) * X ^ i

/-- Definition 4.7: PolyFold(f, k, r) = sum_{l < k} r^l f_l. -/
noncomputable def polyFold (f : K[X]) (k : ℕ) (r : K) : K[X] :=
  ∑ l ∈ range k, C (r ^ l) * splitPart f k l

/-- Definition 4.8: Fold(f, k, alpha)(y) is p_y(alpha), where p_y interpolates f on the points of L whose k-th power is y. -/
noncomputable def fold [DecidableEq K] (L : Finset K) (f : K → K) (k : ℕ) (α y : K) : K :=
  (Lagrange.interpolate (L.filter fun x => x ^ k = y) id f).eval α

/-! ## Degree correction (Section 4.5) -/

/-- Definition 4.12: DegCor(d*, r, f, d)(x) = f(x) sum_{l <= d* - d} (x r)^l. -/
def degCor (dstar d : ℕ) (r : K) (f : K → K) (x : K) : K :=
  f x * ∑ l ∈ range (dstar - d + 1), (x * r) ^ l

/-- Definition 4.12 on polynomials: f(X) sum_{l <= d* - d} (r X)^l. -/
noncomputable def polyDegCor (dstar d : ℕ) (r : K) (f : K[X]) : K[X] :=
  f * ∑ l ∈ range (dstar - d + 1), (C r * X) ^ l

/-- Definition 4.11: r_i = r^(i + sum_{j < i} (d* - d_j)), counting from 0. -/
def ri (dstar : ℕ) (degs : List ℕ) (r : K) (i : ℕ) : K :=
  r ^ (i + ∑ j ∈ range i, (dstar - degs.getD j 0))

/-- Definition 4.11: Combine(d*, r, (f_i, d_i)_i)(x) = sum_i r_i f_i(x) sum_{l <= d* - d_i} (x r)^l. -/
def combine (dstar : ℕ) (r : K) (fs : List (K → K)) (degs : List ℕ) (x : K) : K :=
  ∑ i ∈ range fs.length,
    ri dstar degs r i * (fs.getD i 0) x * ∑ l ∈ range (dstar - degs.getD i 0 + 1), (x * r) ^ l

/-! ## One round (Construction 5.2) -/

/-- The honest next polynomial of a round: fold f by k at r_fold, quotient by G, and degree-correct to d_next at r_comb. -/
noncomputable def nextPoly [DecidableEq K] (f : K[X]) (k : ℕ) (rFold rComb : K) (G : Finset K)
    (dNext : ℕ) : K[X] :=
  polyDegCor dNext (dNext - G.card) rComb (polyQuotient (polyFold f k rFold) G)

end Plonky3Lean.Spec.Stir
