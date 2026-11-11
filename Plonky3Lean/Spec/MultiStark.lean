module

public import Plonky3Lean.Spec.MultilinearUtil

@[expose] public section

/-!
# The multilinear AIR zerocheck

The reduction follows two sources:

- the CCS paper of Setty, Thaler and Wahby (eprint 2023/552), Section 5
- Spartan (eprint 2019/550), Section 4.

A trace of 2^n rows is a table on the Boolean cube {0,1}^n.

Row b is the vertex whose coordinate 0 is the most significant bit of b.

An AIR asserts that some constraint values vanish on every row.

The constraint values of row b read the row itself, its successor, and three selectors:

```text
    first(b)       = 1 if b = 0,        else 0
    last(b)        = 1 if b = 2^n - 1,  else 0
    transition(b)  = 1 if b < 2^n - 1,  else 0
    succ(b)        = b + 1 below 2^n - 1, and 2^n - 1 itself
```

The successor repeats the last row: it does not wrap around to row 0.

The constraints of one AIR are batched by the powers of alpha.

The AIRs are batched by the powers of beta.

A table of fewer rows than the batch's cube reads the low bits of the row index:

```text
    g(b) = sum_i beta^i sum_j alpha^(k_i - 1 - j) C_ij(b mod 2^(n_i))
```

The batch is satisfied exactly when g vanishes on the cube, for every alpha and beta.

The zerocheck tests that through one sum at a random point tau:

```text
    sum_{b in {0,1}^m} eq(b, tau) g(b) = 0
```

The left side is the multilinear extension of g at tau, a polynomial of degree at most m.
-/

namespace Plonky3Lean.Spec.MultiStark

open Plonky3Lean.Spec.MultilinearUtil Finset

variable {K : Type _} [CommRing K]

/-! ## Rows and selectors -/

/-- The extension at r of the table f on the cube of r's dimension.

It is the sum of eq(b, r) f(b). -/
def rowExt (f : ℕ → K) (r : List K) : K :=
  ∑ b ∈ range (2 ^ r.length), eq (vertex r.length b) r * f b

/-- The first-row selector. -/
def firstRow (b : ℕ) : K := if b = 0 then 1 else 0

/-- The last-row selector of a table of 2^n rows. -/
def lastRow (n b : ℕ) : K := if b + 1 = 2 ^ n then 1 else 0

/-- The transition selector of a table of 2^n rows: one on every row but the last. -/
def transitionRow (n b : ℕ) : K := if b + 1 < 2 ^ n then 1 else 0

/-! ## A batch of AIR instances -/

/-- One AIR instance: the arity of its trace, and the table of each constraint it asserts. -/
structure Instance (K : Type _) where
  log_height : ℕ
  constraints : List (ℕ → K)

/-- The instance is satisfied: every constraint vanishes on every row of its trace. -/
def Instance.Satisfied (A : Instance K) : Prop :=
  ∀ C ∈ A.constraints, ∀ b < 2 ^ A.log_height, C b = 0

/-- The batch is satisfied: every instance is. -/
def Satisfied (batch : List (Instance K)) : Prop := ∀ A ∈ batch, A.Satisfied

/-- The constraints of one instance at row b, batched by alpha in Horner order.

The result is C_0 alpha^(k-1) + ... + C_(k-1). -/
def Instance.batched (A : Instance K) (α : K) (b : ℕ) : K :=
  A.constraints.foldl (fun acc C => acc * α + C b) 0

/-- The batched constraint of the batch at row b of the batch's cube.

Instance i is weighted by beta^i and reads the low bits of b. -/
def batchedRow (batch : List (Instance K)) (α β : K) (b : ℕ) : K :=
  ∑ i : Fin batch.length, β ^ (i : ℕ) * batch[i].batched α (b % 2 ^ batch[i].log_height)

/-- The zerocheck sum at tau. -/
def zerocheckSum (batch : List (Instance K)) (α β : K) (τ : List K) : K :=
  rowExt (batchedRow batch α β) τ

/-! ## The fraction tree

The fractional sum-check follows Papini and Haböck (eprint 2023/1284), Section 3.

A fraction is a pair (numerator, denominator).

Two fractions add without a division:

```text
    n0 / d0 + n1 / d1 = (n0 d1 + n1 d0) / (d0 d1)
```

A table of 2^n fractions folds its two halves into a table of 2^(n - 1):

```text
    level k (x) = level (k + 1) (x)  +  level (k + 1) (2^k + x),     x < 2^k
```

The root, at level 0, carries the sum of every fraction as one numerator over one denominator.
-/

/-- The sum of two fractions, kept as a numerator and a denominator. -/
def addFrac (a b : K × K) : K × K := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Level k of the tree over a table t of 2^n fractions.

It is t at k = n, and each level adds the two halves of the level below. -/
def fracLevel (t : ℕ → K × K) (n k : ℕ) : ℕ → K × K :=
  if n ≤ k then t else fun x => addFrac (fracLevel t n (k + 1) x) (fracLevel t n (k + 1) (2 ^ k + x))
termination_by n - k

/-- The batched value of a fraction: numerator + lambda denominator. -/
def batchFrac (lambda : K) (a : K × K) : K := a.1 + lambda * a.2

end Plonky3Lean.Spec.MultiStark
