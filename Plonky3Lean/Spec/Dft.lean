module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# The discrete Fourier transform

The definitions follow Cormen, Leiserson, Rivest and Stein, Introduction to Algorithms, chapter 30.

A vector x_0, ..., x_(n-1) is read as the coefficients of the polynomial P(X) = sum_j x_j X^j.

Its DFT at the root omega lists the values of P at the powers of omega, in natural order:

```text
    y_i = P(omega^i) = sum_{j < n} omega^(i j) x_j,     0 <= i < n
```

The entries may lie in any vector space V over the field K.

A matrix of width w is the case V = K^w, and the transform then acts on each column.

Entries at index n and above are not part of the vector, and nothing reads them.
-/

namespace Plonky3Lean.Spec.Dft

open Finset

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The values of sum_j x_j X^j at the points 1, omega, ..., omega^(n - 1). -/
def dft (ω : K) (n : ℕ) (x : ℕ → V) : ℕ → V :=
  fun i => ∑ j ∈ range n, (ω ^ (i * j)) • x j

/-- The values of sum_j x_j X^j at the points s, s omega, ..., s omega^(n - 1). -/
def cosetDft (s ω : K) (n : ℕ) (x : ℕ → V) : ℕ → V :=
  fun i => ∑ j ∈ range n, ((s * ω ^ i) ^ j) • x j

/-- The inverse transform: 1/n times the transform at the root omega^(-1). -/
def idft (ω : K) (n : ℕ) (x : ℕ → V) : ℕ → V :=
  fun i => (n : K)⁻¹ • ∑ j ∈ range n, (ω⁻¹ ^ (i * j)) • x j

/-- The inverse of the coset transform: the inverse transform, then entry i divided by s^i. -/
def cosetIdft (s ω : K) (n : ℕ) (x : ℕ → V) : ℕ → V :=
  fun i => (s⁻¹ ^ i) • idft ω n x i

/-- The k-bit reversal of the entries: entry i is entry rev_k(i). -/
def bitRevVec (rev : ℕ → ℕ) (x : ℕ → V) : ℕ → V := fun i => x (rev i)

/-- The polynomial sum_j x_j X^j of degree below n, for scalar entries. -/
noncomputable def poly (n : ℕ) (x : ℕ → K) : Polynomial K :=
  ∑ j ∈ range n, Polynomial.C (x j) * Polynomial.X ^ j

/-- The polynomial of degree below n that takes the value x_i at omega^i, for i < n. -/
noncomputable def interpolant (ω : K) (n : ℕ) (x : ℕ → K) : Polynomial K :=
  Lagrange.interpolate (univ : Finset (Fin n)) (fun i => ω ^ i.val) (fun i => x i.val)

end Plonky3Lean.Spec.Dft
