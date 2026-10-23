module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The LogUp lookup argument

The definitions follow Haböck, "Multivariate lookups based on logarithmic derivatives" (eprint 2022/1530).

A message is a key with a multiplicity in a field F.

A list of messages balances when every key has net multiplicity zero.

LogUp replaces that check by one identity of rational functions:

```text
    sum_k m_k / (X - v_k) = 0   in F(X)
```

Lemma 5 of the paper reads a lookup this way.

The queries f_1, ..., f_N lie in the table t_1, ..., t_M when, for some multiplicities m_i,

```text
    sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i)
```

This needs a characteristic p > N, since p equal queries cancel.

## Tuples and buses

A tuple (e_0, ..., e_{k-1}) is compressed by a challenge beta into its fingerprint:

```text
    fingerprint(e) = sum_i e_i beta^(k - 1 - i)
```

Plonky3 separates the buses with one more power of beta, above every payload power:

```text
    denominator(bus, e) = alpha + (bus + 1) beta^W - fingerprint(e),    W >= every width
```

## The running sum

Eprint 2023/1284 encodes the sum in an AIR with a running-sum column.

On every row r, a fraction column holds the row's sum of m / d.

An accumulator starts at 0 and adds the fractions of each row.

The last row binds a committed terminal, the sum over the whole trace:

```text
    acc_0 = 0,    acc_(r+1) = acc_r + sum_c f_(r,c),    terminal = acc_(n-1) + sum_c f_(n-1,c)
```
-/

namespace Plonky3Lean.Spec.Lookup

open Polynomial

/-- ArkLib's lookup relation: every value lies in the table. -/
def LookupRelation {α : Type _} (values table : List α) : Prop := ∀ v ∈ values, v ∈ table

/-- The net multiplicity of a key: the sum of the multiplicities of its messages. -/
def netMult {κ R : Type _} [DecidableEq κ] [AddCommMonoid R] (msgs : List (κ × R)) (k : κ) : R :=
  ((msgs.filter (·.1 = k)).map (·.2)).sum

/-- Messages balance when every key has net multiplicity zero. -/
def Balanced {κ R : Type _} [DecidableEq κ] [AddCommMonoid R] (msgs : List (κ × R)) : Prop :=
  ∀ k, netMult msgs k = 0

variable {F : Type _} [Field F]

/-- The logarithmic-derivative sum: sum_k m_k / (X - v_k) in F(X). -/
noncomputable def logDerivSum (msgs : List (F × F)) : RatFunc F :=
  (msgs.map fun p => algebraMap F[X] (RatFunc F) (C p.2) /
    algebraMap F[X] (RatFunc F) (X - C p.1)).sum

/-- The fingerprint of a tuple: sum_i e_i beta^(k - 1 - i), the last entry at beta^0. -/
def fingerprint {R : Type _} [CommSemiring R] (β : R) (e : List R) : R :=
  ∑ j ∈ Finset.range e.length, e.reverse.getD j 0 * β ^ j

/-- The fingerprint as a polynomial in beta. -/
noncomputable def fingerprintPoly {R : Type _} [CommSemiring R] (e : List R) : R[X] :=
  ∑ j ∈ Finset.range e.length, C (e.reverse.getD j 0) * X ^ j

/-- The domain-separated denominator: alpha + (bus + 1) beta^W - fingerprint(e). -/
def busDenom {R : Type _} [CommRing R] (α β : R) (W bus : ℕ) (e : List R) : R :=
  α + ((bus : R) + 1) * β ^ W - fingerprint β e

/-- The sum of m / d over messages on buses, each keyed by its bus and payload. -/
def busSum {K : Type _} [Field K] (α β : K) (W : ℕ) (msgs : List ((ℕ × List K) × K)) : K :=
  (msgs.map fun p => p.2 / busDenom α β W p.1.1 p.1.2).sum

/-! ## The running sum of one AIR -/

/-- The LogUp columns of one AIR over a trace of n rows.

On row r, lookup column c holds the fraction f r c, and the accumulator holds acc r.

The terminal is the committed sum. -/
structure RunningSum (K : Type _) where
  acc : ℕ → K
  frac : ℕ → ℕ → K
  terminal : K

variable {K : Type _} [Field K]

/-- The sum of the fractions of row r, over the columns c < width. -/
def RunningSum.rowSum (t : RunningSum K) (width r : ℕ) : K :=
  ∑ c ∈ Finset.range width, t.frac r c

/-- The constraints of the running sum on n rows: start at 0, add each row, and end at the terminal. -/
structure RunningSum.Constrained (t : RunningSum K) (n width : ℕ) : Prop where
  first : t.acc 0 = 0
  transition : ∀ r, r + 1 < n → t.acc (r + 1) = t.acc r + t.rowSum width r
  last : t.terminal = t.acc (n - 1) + t.rowSum width (n - 1)

section Row

variable {R : Type _} [CommRing R]

/-- Denominator i of a row's (d, m) pairs. -/
def den (terms : List (R × R)) (i : ℕ) : R := (terms.getD i (1, 0)).1

/-- Multiplicity i of a row's (d, m) pairs. -/
def mul (terms : List (R × R)) (i : ℕ) : R := (terms.getD i (1, 0)).2

/-- The numerator of a row: V = sum_i m_i prod_(j != i) d_j. -/
def numerator (terms : List (R × R)) : R :=
  ∑ i ∈ Finset.range terms.length,
    mul terms i * ∏ j ∈ (Finset.range terms.length).erase i, den terms j

/-- The denominator of a row: U = prod_i d_i. -/
def denominator (terms : List (R × R)) : R := ∏ i ∈ Finset.range terms.length, den terms i

/-- A fraction column pinned on a row: U f = V. -/
def Pinned (terms : List (R × R)) (f : R) : Prop := denominator terms * f = numerator terms

end Row

/-- The sum of m / d over a row's (d, m) pairs. -/
def fracSum (terms : List (K × K)) : K :=
  ∑ i ∈ Finset.range terms.length, mul terms i / den terms i

end Plonky3Lean.Spec.Lookup
