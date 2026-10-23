module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Algebra.Module.BigOperators

@[expose] public section

/-!
# The additive NTT over a binary field

The definitions follow Lin, Chung and Han, "Novel Polynomial Basis and Its Application to
Reed-Solomon Erasure Codes", FOCS 2014.

The binary-field presentation is that of Diamond and Posen (eprint 2023/1784 and 2024/504).

A basis is a sequence beta_0, beta_1, ... of field elements.

Point m of the subspace S_l = span(beta_0, ..., beta_(l-1)) sums the beta_r over the set bits r of m:

```text
    point(m) = sum_r (bit r of m) beta_r          point(5) = beta_0 + beta_2
```

The subspace polynomial W_i vanishes exactly on S_i, and its normalisation is one at beta_i:

```text
    W_i(x) = prod_(s in S_i) (x - s)              W^_i(x) = W_i(x) / W_i(beta_i)
```

The novel basis takes a product of normalised subspace polynomials, one per set bit of k:

```text
    X_k(x) = prod_(j < l) W^_j(x)^(bit j of k)
```

The additive NTT of coefficients d_0, ..., d_(2^l - 1) over the coset shift + S_l lists the values
of sum_k d_k X_k at the points shift + point(i), in natural order.

Coefficients may lie in any vector space V over the field: a matrix of width w is V = F^w.

Rows at index 2^l and above are not part of the vector, and nothing reads them.
-/

namespace Plonky3Lean.Spec.BinaryDft

open Finset

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-- Point m of the span of the basis: the sum of beta_r over the set bits r of m. -/
def point (β : ℕ → F) (m : ℕ) : F := ∑ r ∈ range m, if m.testBit r then β r else 0

/-- The subspace polynomial W_i: the product of x - s over the 2^i points s of S_i. -/
def vanishing (β : ℕ → F) (i : ℕ) (x : F) : F := ∏ m ∈ range (2 ^ i), (x - point β m)

/-- The normalised subspace polynomial W_i(x) / W_i(beta_i). -/
def normalized (β : ℕ → F) (i : ℕ) (x : F) : F := vanishing β i x / vanishing β i (β i)

/-- The novel basis polynomial X_k of the first l normalised subspace polynomials. -/
def novel (β : ℕ → F) (l k : ℕ) (x : F) : F :=
  ∏ j ∈ range l, if k.testBit j then normalized β j x else 1

/-- The value at x of sum_(k < 2^l) d_k X_k. -/
def novelEval (β : ℕ → F) (l : ℕ) (d : ℕ → V) (x : F) : V :=
  ∑ k ∈ range (2 ^ l), novel β l k x • d k

/-- The additive NTT over shift + S_l: entry i is sum_k d_k X_k at shift + point(i). -/
def ntt (β : ℕ → F) (l : ℕ) (shift : F) (d : ℕ → V) : ℕ → V :=
  fun i => novelEval β l d (shift + point β i)

/-- The first n basis vectors are independent: no beta_i is a point of the span of the earlier ones. -/
def Independent (β : ℕ → F) (n : ℕ) : Prop := ∀ i < n, ∀ m < 2 ^ i, point β m ≠ β i

/-- A Cantor basis of length n: beta_0 = 1 and beta_i^2 + beta_i = beta_(i-1) for 0 < i < n. -/
def IsCantor (β : ℕ → F) (n : ℕ) : Prop :=
  β 0 = 1 ∧ ∀ i, i + 1 < n → β (i + 1) ^ 2 + β (i + 1) = β i

/-! ## The butterfly network -/

/-- The forward butterfly (u, v) -> (u + t v, u + t v + v). -/
def butterfly (t : F) (u v : V) : V × V := (u + t • v, u + t • v + v)

/-- The inverse butterfly (u, v) -> (u + t (u + v), u + v). -/
def ibutterfly (t : F) (u v : V) : V × V := (u + t • (u + v), u + v)

/-- Stage j of the forward network.

Row i pairs with the row 2^j away inside its block of 2^(j+1) rows, and block b uses twiddle tau(b). -/
def stage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if i % 2 ^ (j + 1) < 2 ^ j then (butterfly (τ (i / 2 ^ (j + 1))) (x i) (x (i + 2 ^ j))).1
  else (butterfly (τ (i / 2 ^ (j + 1))) (x (i - 2 ^ j)) (x i)).2

/-- Stage j of the inverse network, pairing rows as the forward stage does. -/
def istage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if i % 2 ^ (j + 1) < 2 ^ j then (ibutterfly (τ (i / 2 ^ (j + 1))) (x i) (x (i + 2 ^ j))).1
  else (ibutterfly (τ (i / 2 ^ (j + 1))) (x (i - 2 ^ j)) (x i)).2

/-- The forward network of l stages: stage l - 1 first, down to stage 0, stage j with twiddles tau_j. -/
def network (τ : ℕ → ℕ → F) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => network τ l (stage (τ l) l x)

/-- The inverse network of l stages: stage 0 first, up to stage l - 1. -/
def inetwork (τ : ℕ → ℕ → F) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => istage (τ l) l (inetwork τ l x)

/-- The Lin-Chung-Han twiddle of stage j, block b over shift + S: W^_j at the first point of the block. -/
def twiddle (β : ℕ → F) (shift : F) (j b : ℕ) : F :=
  normalized β j (shift + point β (b * 2 ^ (j + 1)))

/-- The iterated map x -> x^2 + x, which is W_j for a Cantor basis. -/
def sqAddIter (j : ℕ) (x : F) : F := (fun y => y ^ 2 + y)^[j] x

end Plonky3Lean.Spec.BinaryDft
