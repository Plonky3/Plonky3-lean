module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-!
# Algebraic intermediate representations

An AIR constrains a trace: a table of field elements with n rows.

Each constraint is a polynomial in:

- the cells of two consecutive rows
- the public values
- the periodic columns.

A trace satisfies the AIR when every constraint vanishes on every row it applies to.

This follows the AIR of the ethSTARK documentation (eprint 2021/582).

Ben-Sasson, Bentov, Horesh and Riabzev introduce it in eprint 2018/046.

Plonky3 writes every constraint as one polynomial that applies on every row.

Three selector variables restrict it:

```text
    row i of n:     is_first_row = [i = 0]
                    is_last_row  = [i = n - 1]
                    is_transition = [i != n - 1]
                    next row     = row (i + 1) mod n
```

The next row of the last row is row 0.

A constraint with no selector therefore also relates the last row to the first.

A constraint domain is the set of rows a constraint applies to.

The selector form and the domain form describe the same traces.

## Degrees

A trace of n rows is interpolated over a subgroup H of order n.

A column then has degree at most n - 1, and so does each boundary selector.

The transition selector X - g^(-1) has degree 1.

A periodic column of period p is f(X^(n/p)) with deg f < p, of degree at most n - n/p.

A public value is a constant.

Substituting these polynomials into a constraint gives the constraint polynomial C(X).

On a satisfying trace C vanishes on H, so C = Q Z_H with deg Q = deg C - n.

The prover commits to Q in c chunks of n coefficients, so it needs deg C < (c + 1) n.
-/

namespace Plonky3Lean.Spec.Air

/-- A variable of a constraint.

It is a cell of the current or next row, a public value, a periodic value, or a selector. -/
inductive Var where
  | main (offset : Fin 2) (col : ℕ)
  | prep (offset : Fin 2) (col : ℕ)
  | pub (i : ℕ)
  | periodic (i : ℕ)
  | isFirstRow
  | isLastRow
  | isTransition
  deriving DecidableEq

/-- A trace with its public data.

It holds n rows of main and preprocessed cells, public values, and periodic columns. -/
structure Instance (F : Type _) where
  height : ℕ
  main : ℕ → ℕ → F
  prep : ℕ → ℕ → F
  pub : ℕ → F
  periodic : ℕ → ℕ → F

variable {F : Type _} [Field F]

/-- The values of the variables on row i: the next row wraps to row 0. -/
def rowEnv (T : Instance F) (i : ℕ) : Var → F
  | .main 0 c => T.main i c
  | .main 1 c => T.main ((i + 1) % T.height) c
  | .prep 0 c => T.prep i c
  | .prep 1 c => T.prep ((i + 1) % T.height) c
  | .pub j => T.pub j
  | .periodic j => T.periodic j i
  | .isFirstRow => if i = 0 then 1 else 0
  | .isLastRow => if i = T.height - 1 then 1 else 0
  | .isTransition => if i = T.height - 1 then 0 else 1

/-- A trace satisfies polynomial constraints when each one vanishes on each row. -/
def Satisfies (C : List (MvPolynomial Var F)) (T : Instance F) : Prop :=
  ∀ i < T.height, ∀ c ∈ C, MvPolynomial.eval (rowEnv T i) c = 0

/-- The rows a constraint applies to. -/
inductive Domain where
  | everyRow
  | firstRow
  | lastRow
  | transition

/-- Row i of n lies in the domain: every row, row 0, row n - 1, or a row with a successor. -/
def Domain.Contains (n i : ℕ) : Domain → Prop
  | .everyRow => True
  | .firstRow => i = 0
  | .lastRow => i + 1 = n
  | .transition => i + 1 < n

instance (n i : ℕ) (d : Domain) : Decidable (d.Contains n i) := by
  cases d <;> unfold Domain.Contains <;> infer_instance

/-- The selector that restricts a constraint to its domain. -/
noncomputable def Domain.selector : Domain → MvPolynomial Var F
  | .everyRow => 1
  | .firstRow => .X .isFirstRow
  | .lastRow => .X .isLastRow
  | .transition => .X .isTransition

/-- A constraint with a domain. -/
structure Constraint (F : Type _) [CommSemiring F] where
  domain : Domain
  poly : MvPolynomial Var F

/-- A trace satisfies constraints with domains when each one vanishes on each row of its domain. -/
def SatisfiesOn (C : List (Constraint F)) (T : Instance F) : Prop :=
  ∀ c ∈ C, ∀ i < T.height, c.domain.Contains T.height i →
    MvPolynomial.eval (rowEnv T i) c.poly = 0

/-- Degree bounds for an assignment of univariate polynomials to the variables.

The trace has n rows.

* A cell and a boundary selector have degree at most n - 1.
* The transition selector has degree at most 1.
* Periodic column j has degree at most n - n / p_j, for a period p_j dividing n.
* A public value is a constant. -/
structure DegreeBounds (σ : Var → Polynomial F) (n : ℕ) (periods : List ℕ) : Prop where
  main : ∀ o c, (σ (.main o c)).natDegree ≤ n - 1
  prep : ∀ o c, (σ (.prep o c)).natDegree ≤ n - 1
  pub : ∀ j, (σ (.pub j)).natDegree = 0
  periodic : ∀ j p, periods[j]? = some p → 0 < p → p ∣ n → (σ (.periodic j)).natDegree ≤ n - n / p
  periodic_default : ∀ j, (σ (.periodic j)).natDegree ≤ n - 1
  isFirstRow : (σ .isFirstRow).natDegree ≤ n - 1
  isLastRow : (σ .isLastRow).natDegree ≤ n - 1
  isTransition : (σ .isTransition).natDegree ≤ 1

/-- The constraint polynomial of a constraint, for an assignment of univariate polynomials. -/
noncomputable def constraintPoly (σ : Var → Polynomial F) (c : MvPolynomial Var F) : Polynomial F :=
  MvPolynomial.aeval σ c

/-- A quotient in c chunks of n coefficients holds a constraint polynomial when deg C < (c + 1) n. -/
def FitsChunks (n c : ℕ) (C : Polynomial F) : Prop := C.natDegree < (c + 1) * n

end Plonky3Lean.Spec.Air
