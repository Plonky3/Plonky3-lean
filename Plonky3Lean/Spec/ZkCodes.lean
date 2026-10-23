module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# Zero-knowledge codes

The definitions follow Chiesa, Fenzi and Weissenberg, eprint 2026/391, Section 3.2.1.

A code has positions 0, ..., m - 1, and a word assigns a symbol to each.

An encoding maps a message of l field elements and a randomness of r field elements to a word.

It is t-query zero knowledge with error zeta when a simulator, given only a set S of at most t positions, samples a restriction to S whose distance from the real one is at most zeta:

```text
    Delta( Enc(msg, rho)[S]  with rho uniform ,  Sim(S) )  <=  zeta
```

A distribution on a finite set is the probability of each outcome, a rational number.

The paper also asks the simulator to run in polynomial time, which is not stated here.

The Reed-Solomon encoding of Proposition 3.19 puts the message in the low coefficients and the randomness in the next t:

```text
    p_{f,rho}(X) = f_0 + f_1 X + ... + f_{l-1} X^{l-1} + rho_0 X^l + ... + rho_{t-1} X^{l+t-1}
```

Its codeword lists the values of that polynomial at the points L_0, ..., L_{m-1}.
-/

namespace Plonky3Lean.Spec.ZkCodes

open Polynomial

/-- The distribution of g(a) for a uniform a in the finite set alpha. -/
def pushUniform {α β : Type _} [Fintype α] [DecidableEq β] (g : α → β) (y : β) : ℚ :=
  ((Finset.univ.filter fun a => g a = y).card : ℚ) / Fintype.card α

/-- The uniform distribution on a finite set. -/
def uniform (β : Type _) [Fintype β] (_ : β) : ℚ := 1 / Fintype.card β

/-- The statistical distance between two distributions on a finite set: half the sum of the gaps. -/
def statDist {β : Type _} [Fintype β] (p q : β → ℚ) : ℚ :=
  (∑ b, |p b - q b|) / 2

variable {K : Type _} [Field K] [Fintype K] [DecidableEq K]

/-- The word c read at the positions of S. -/
def restrict {m : ℕ} {A : Type _} (c : Fin m → A) (S : Finset (Fin m)) : S → A := fun i => c i

/-- The distribution of Enc(msg, rho)[S] for a uniform rho. -/
def realView {l r m : ℕ} {A : Type _} [DecidableEq A]
    (enc : (Fin l → K) → (Fin r → K) → Fin m → A) (msg : Fin l → K) (S : Finset (Fin m)) :
    (S → A) → ℚ :=
  pushUniform fun ρ => restrict (enc msg ρ) S

/-- Definition 3.16: a t-query zero-knowledge encoding with error zeta, witnessed by the simulator sim. -/
def IsZkEncoding {l r m : ℕ} {A : Type _} [Fintype A] [DecidableEq A]
    (enc : (Fin l → K) → (Fin r → K) → Fin m → A) (t : ℕ) (ζ : ℚ)
    (sim : (S : Finset (Fin m)) → (S → A) → ℚ) : Prop :=
  ∀ (msg : Fin l → K) (S : Finset (Fin m)), S.card ≤ t → statDist (realView enc msg S) (sim S) ≤ ζ

/-- Definition 3.17, for symbols in K: Enc(f, rho) = G^# f + G^$ rho. -/
def IsGeneratingMatrix {l r m : ℕ} (enc : (Fin l → K) → (Fin r → K) → Fin m → K)
    (Gm : Matrix (Fin m) (Fin l) K) (Gr : Matrix (Fin m) (Fin r) K) : Prop :=
  ∀ f ρ, enc f ρ = Gm.mulVec f + Gr.mulVec ρ

/-- Definition 3.18: the words that agree with a polynomial of degree below l at every point. -/
def rsCode {m : ℕ} (L : Fin m → K) (l : ℕ) : Set (Fin m → K) :=
  {c | ∃ p : K[X], p.degree < l ∧ ∀ i, p.eval (L i) = c i}

/-- The polynomial of Proposition 3.19: the message in degrees below l, the randomness in the next t. -/
noncomputable def rsZkPoly {l t : ℕ} (f : Fin l → K) (ρ : Fin t → K) : K[X] :=
  ∑ j, C (f j) * X ^ (j : ℕ) + ∑ j, C (ρ j) * X ^ (l + (j : ℕ))

/-- The Reed-Solomon zero-knowledge encoding: the polynomial's values at the points L_i. -/
noncomputable def rsZkEnc {l t m : ℕ} (L : Fin m → K) (f : Fin l → K) (ρ : Fin t → K) :
    Fin m → K :=
  fun i => (rsZkPoly f ρ).eval (L i)

/-- The message part of the generating matrix: row i is 1, L_i, ..., L_i^(l-1). -/
def rsMsgMatrix {l m : ℕ} (L : Fin m → K) : Matrix (Fin m) (Fin l) K :=
  fun i j => L i ^ (j : ℕ)

/-- The randomness part of the generating matrix: row i is L_i^l, ..., L_i^(l+t-1). -/
def rsRandMatrix {l t m : ℕ} (L : Fin m → K) : Matrix (Fin m) (Fin t) K :=
  fun i j => L i ^ (l + (j : ℕ))

/-- The simulator: a uniform symbol at every queried position, independently. -/
def uniformSim {m : ℕ} (S : Finset (Fin m)) : (S → K) → ℚ :=
  uniform (S → K)

end Plonky3Lean.Spec.ZkCodes
