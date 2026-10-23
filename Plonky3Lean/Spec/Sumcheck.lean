module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# The sumcheck protocol

The protocol of Lund, Fortnow, Karloff and Nisan (1992), as Thaler states it in "Proofs, Arguments, and Zero-Knowledge", Section 4.1.

The prover claims that a polynomial g in n variables sums to H over the Boolean cube:

```text
    H = sum_{b in {0,1}^n} g(b)
```

Round i, for i = 0, ..., n - 1:

```text
    prover:    a univariate polynomial g_i of degree at most d
    verifier:  checks g_i(0) + g_i(1) = c_i, where c_0 = H
               samples r_i, and sets c_{i+1} = g_i(r_i)
```

At the end the verifier checks g(r_0, ..., r_{n-1}) = c_n.

A prover is a strategy: its message in round i is a function of the challenges.

It is causal when round i reads only the challenges r_0, ..., r_{i-1}.

An interactive verifier draws the challenges uniformly at random, and the soundness error counts the challenge vectors that accept.
-/

namespace Plonky3Lean.Spec.Sumcheck

open MvPolynomial

variable {F : Type _} [CommRing F] [DecidableEq F]

/-- The Boolean cube {0,1}^n, as points of F^n. -/
def cube (n : ℕ) : Finset (Fin n → F) := Fintype.piFinset fun _ => {0, 1}

/-- The sum of g over the Boolean cube. -/
noncomputable def cubeSum {n : ℕ} (g : MvPolynomial (Fin n) F) : F :=
  ∑ b ∈ cube n, eval b g

/-- g has degree at most d in each variable. -/
def IndividualDegreeLE {n : ℕ} (g : MvPolynomial (Fin n) F) (d : ℕ) : Prop :=
  ∀ i, g.degreeOf i ≤ d

/-- g with its first variable set to a. -/
noncomputable def fixFirst {n : ℕ} (a : F) (g : MvPolynomial (Fin (n + 1)) F) :
    MvPolynomial (Fin n) F :=
  Polynomial.eval (C a) (finSuccEquiv F n g)

/-- The honest first message: the first variable is kept, the others are summed over the cube.

```text
    s(X) = sum_{b in {0,1}^n} g(X, b)
```
-/
noncomputable def honestMessage {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) : Polynomial F :=
  ∑ b ∈ cube n, (finSuccEquiv F n g).map (eval b)

/-- The honest prover: round 0 sends the honest first message, and later rounds recurse on g with its first variable set to r_0. -/
noncomputable def honestProver : {n : ℕ} → MvPolynomial (Fin n) F → Fin n → (Fin n → F) → Polynomial F
  | 0, _ => fun i => i.elim0
  | _ + 1, g => fun i r =>
    Fin.cases (honestMessage g) (fun j => honestProver (fixFirst (r 0) g) j (Fin.tail r)) i

/-- A prover strategy is causal when its message in round i reads only the challenges before i. -/
def Causal {α : Type _} {n : ℕ} (P : Fin n → (Fin n → F) → α) : Prop :=
  ∀ i r r', (∀ j : Fin n, j < i → r j = r' j) → P i r = P i r'

/-- The verifier accepts the claim c against the prover P on the challenges r.

Every round checks the degree bound and the sum g_i(0) + g_i(1) = c_i.

The last check is g(r) = c_n.
-/
def Accepts (d : ℕ) : {n : ℕ} → MvPolynomial (Fin n) F → F → (Fin n → (Fin n → F) → Polynomial F) →
    (Fin n → F) → Prop
  | 0, g, c, _, r => eval r g = c
  | _ + 1, g, c, P, r =>
    (P 0 r).natDegree ≤ d ∧ (P 0 r).eval 0 + (P 0 r).eval 1 = c ∧
      Accepts d (fixFirst (r 0) g) ((P 0 r).eval (r 0))
        (fun i r' => P i.succ (Fin.cons (r 0) r')) (Fin.tail r)

end Plonky3Lean.Spec.Sumcheck
