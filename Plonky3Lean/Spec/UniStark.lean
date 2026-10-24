module

public import Plonky3Lean.Spec.Air
public import Plonky3Lean.Spec.Commit

@[expose] public section

/-!
# The STARK IOP

This follows two sources:

- the ethSTARK documentation (eprint 2021/582), Section 3
- Haböck's summary of FRI (eprint 2022/1216).

The prover interpolates the trace over a coset s H of order n = 2^k, with generator omega.

It combines the constraint polynomials with powers of a random alpha:

```text
    C_alpha(X) = sum_i alpha^(m - 1 - i) C_i(X)        for m constraints, in emission order
```

On a satisfying trace C_alpha vanishes on s H.

So the quotient Q = C_alpha / Z is a polynomial.

The prover splits Q into chunks.

The verifier checks C_alpha(zeta) / Z(zeta) = Q(zeta) at a random zeta.

## Selectors

Plonky3 does not substitute 0/1 selectors.

Its selectors are the unnormalized Lagrange selectors of p3-commit:

```text
    is_first_row   = n L_0(X)              value n on row 0, 0 elsewhere
    is_last_row    = n omega L_(n-1)(X)    value n omega on row n - 1, 0 elsewhere
    is_transition  = (X - s omega^(n-1)) / s
                                           value omega^i - omega^(n-1) on row i
```

So the STARK checks the constraints with these row values.

It does not use the 0/1 values of the AIR's reference semantics.

Both agree on constraints that are a product of selectors times a selector-free polynomial.
-/

open Polynomial Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit

namespace Plonky3Lean.Spec.UniStark

variable {K : Type _} [Field K]

/-- The random linear combination of values v_0, ..., v_(m-1).

It is sum_i alpha^(m - 1 - i) v_i. -/
def combine (α : K) (vs : List K) : K :=
  ∑ i ∈ Finset.range vs.length, α ^ (vs.length - 1 - i) * vs.getD i 0

/-! ## The STARK's row semantics -/

/-- A selector variable. -/
def IsSelector : Var → Prop
  | .isFirstRow | .isLastRow | .isTransition => True
  | _ => False

/-- The values of the variables on row i as the STARK evaluates them.

The subgroup has generator omega.

The cells, public values and periodic values are those of the reference semantics.

The selectors take the values of the unnormalized Lagrange selectors. -/
def starkRowEnv (T : Instance K) (ω : K) (i : ℕ) : Var → K
  | .isFirstRow => if i = 0 then (T.height : K) else 0
  | .isLastRow => if i = T.height - 1 then T.height * ω else 0
  | .isTransition => ω ^ i - ω ^ (T.height - 1)
  | v => rowEnv T i v

/-- The relation the STARK proves.

Each constraint vanishes on each row, with the STARK's selector values. -/
def SatisfiesStark (C : List (MvPolynomial Var K)) (T : Instance K) (ω : K) : Prop :=
  ∀ i < T.height, ∀ c ∈ C, MvPolynomial.eval (starkRowEnv T ω i) c = 0

/-- A constraint in selector form.

It is a product of selector variables times a polynomial with no selector variable. -/
def SelectorSeparated (c : MvPolynomial Var K) : Prop :=
  ∃ (ss : List Var) (p : MvPolynomial Var K), (∀ s ∈ ss, IsSelector s) ∧
    (∀ v ∈ p.vars, ¬ IsSelector v) ∧ c = (ss.map MvPolynomial.X).prod * p

/-! ## The univariate polynomials -/

/-- The univariate polynomials substituted for the variables.

- The selectors are the unnormalized Lagrange selectors of s H.
- The trace columns are read on the current or next row. -/
noncomputable def starkAssign (s ω : K) (k : ℕ) (main prep : ℕ → K[X]) (pub : ℕ → K)
    (periodic : ℕ → K[X]) : Var → K[X]
  | .main 0 c => main c
  | .main 1 c => (main c).comp (C ω * X)
  | .prep 0 c => prep c
  | .prep 1 c => (prep c).comp (C ω * X)
  | .pub j => C (pub j)
  | .periodic j => periodic j
  | .isFirstRow => C (2 ^ k : K) * lagrange s ω k ⟨0, by positivity⟩
  | .isLastRow => C (2 ^ k * ω : K) * lagrange s ω k ⟨2 ^ k - 1, Nat.sub_lt (by positivity) one_pos⟩
  | .isTransition => C s⁻¹ * (X - C (s * ω ^ (2 ^ k - 1)))

/-- The combined constraint polynomial sum_i alpha^(m - 1 - i) C_i(X), for the constraints in order.

The constraints have coefficients in a base field F.

The challenge alpha and the polynomials lie in an extension K. -/
noncomputable def combinedPoly {F : Type _} [CommRing F] [Algebra F K] (α : K) (σ : Var → K[X])
    (C : List (MvPolynomial Var F)) : K[X] :=
  ∑ i ∈ Finset.range C.length, Polynomial.C (α ^ (C.length - 1 - i)) * MvPolynomial.aeval σ (C.getD i 0)

/-- The combination sum_i alpha^(m - 1 - i) P_i(X) of m polynomials, in order.

The lookup constraints have coefficients in K, so they enter here rather than as constraints over F. -/
noncomputable def combinePolys (α : K) (ps : List K[X]) : K[X] :=
  ∑ i ∈ Finset.range ps.length, Polynomial.C (α ^ (ps.length - 1 - i)) * ps.getD i 0

end Plonky3Lean.Spec.UniStark
