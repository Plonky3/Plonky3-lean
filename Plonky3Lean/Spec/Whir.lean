module

public import Plonky3Lean.Spec.MultilinearUtil

@[expose] public section

/-!
# WHIR

The protocol of Arnon, Chiesa, Fenzi and Yogev, eprint 2024/1586, Construction 5.1.

Their paper is "WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification".

The polynomial is a table P of 2^n entries, read two ways:

- the sumcheck runs on its multilinear extension P~, as in Thaler, Section 3.5
- the code encodes the univariate polynomial with coefficients P.

```text
    P~(x)  = sum_b eq(b, x) P[b]
    P^(y)  = sum_b P[b] y^b
```

The codeword of P at fold width k is interleaved.

Block j holds the entries j 2^(n-k), ..., (j + 1) 2^(n-k) - 1.

Row i holds every block's polynomial at omega^i:

```text
    row_i = (block_0^(omega^i), ..., block_(2^k - 1)^(omega^i))
```

Folding P at k challenges r sets the first k variables of P~ to r.

The paper's weight update, step 2(e) of Construction 5.1, then reads:

```text
    w'(x) = w(r, x) + sum_j gamma^(j+1) eq(pow(z_j), x) + sum_j gamma^(s+j+1) sel(q_j, x)
    sigma' = sigma_r + sum_j gamma^(j+1) y_j + sum_j gamma^(s+j+1) v_j
```

An out-of-domain sample z_j asks for y_j = P~(pow(z_j)).

A shift query q_j asks for v_j = P^(q_j).

Its weight is the selector of the powers of q_j.
-/

namespace Plonky3Lean.Spec.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil

variable {K : Type _} [CommRing K]

/-- The univariate polynomial with coefficients c, at y. -/
def uni (c : List K) (y : K) : K := ∑ b ∈ range c.length, c.getD b 0 * y ^ b

/-- The point pow(z, n).

Coordinate i is z^(2^(n - 1 - i)), so coordinate 0 carries the top bit. -/
def pow (z : K) (n : ℕ) : List K := (List.range n).map fun i => z ^ 2 ^ (n - 1 - i)

/-- The selector of the powers of q: the multilinear polynomial equal to q^b at the vertex b. -/
def sel (q : K) (x : List K) : K :=
  (List.zipWith (fun xi e => xi * q ^ 2 ^ e + (1 - xi)) x
    ((List.range x.length).map fun i => x.length - 1 - i)).prod

/-- The fold of a table of 2^n entries at the challenges r: the table of P~(r, .). -/
def foldTable (P : List K) (n : ℕ) (r : List K) : List K :=
  (List.range (2 ^ (n - r.length))).map fun c =>
    ∑ j ∈ range (2 ^ r.length), eq (vertex r.length j) r * P.getD (j * 2 ^ (n - r.length) + c) 0

/-- Block j of the interleaved code at fold width k. -/
def block (P : List K) (n k j : ℕ) : List K := (P.drop (j * 2 ^ (n - k))).take (2 ^ (n - k))

/-- Row i of the interleaved codeword: every block's polynomial at omega^i. -/
def row (P : List K) (n k : ℕ) (ω : K) (i : ℕ) : List K :=
  (List.range (2 ^ k)).map fun j => uni (block P n k j) (ω ^ i)

/-- The sum over the cube of a table against a weight. -/
def cubeDot (P : List K) (n : ℕ) (w : List K → K) : K :=
  ∑ b ∈ range (2 ^ n), P.getD b 0 * w (vertex n b)

/-- The weight after one iteration, step 2(e) of Construction 5.1. -/
def nextWeight (w : List K → K) (r : List K) (γ : K) (ood queries : List K) (n : ℕ) (x : List K) : K :=
  w (r ++ x) + ∑ j ∈ range ood.length, γ ^ (j + 1) * eq (pow (ood.getD j 0) n) x +
    ∑ j ∈ range queries.length, γ ^ (ood.length + j + 1) * sel (queries.getD j 0) x

/-- The claim after one iteration, check 2(c) of Construction 5.1. -/
def nextClaim (σ γ : K) (oodAnswers queryAnswers : List K) : K :=
  σ + ∑ j ∈ range oodAnswers.length, γ ^ (j + 1) * oodAnswers.getD j 0 +
    ∑ j ∈ range queryAnswers.length, γ ^ (oodAnswers.length + j + 1) * queryAnswers.getD j 0

end Plonky3Lean.Spec.Whir
