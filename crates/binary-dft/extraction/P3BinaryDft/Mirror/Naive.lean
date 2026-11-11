/-
Transcriptions of the reference additive NTT of p3-binary-dft.

The matrix is its height and its rows, in a vector space V over the field.
-/
module

public import P3BinaryDft.Mirror.Domain
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace p3_binary_dft.naive.mirror

open p3_binary_dft.mirror p3_binary_dft.domain.mirror p3_dft.mirror

variable {F : Type _} [Field F] [DecidableEq F] {V : Type _} [AddCommGroup V] [Module F V]

/-- The product of y + s over the 2^j points s of the subspace, in index order. -/
def vanishing (L : Level F) (j : ℕ) (y : F) : Option F :=
  ((List.range (2 ^ j)).mapM fun m => (domain_point L m).map (y + ·)).map List.prod

/-- The subspace polynomial from its product definition, normalised to one at basis vector j.

The normaliser is inverted with try_inverse, which is none at zero, and the expect panics on none. -/
def normalised_subspace_poly (L : Level F) (j : ℕ) (x : F) : Option F := do
  let a ← vanishing L j x
  let v ← L.cantorBasis j
  let c ← vanishing L j v
  let inv ← if c = 0 then none else some c⁻¹
  pure (a * inv)

/-- The novel basis at x, built by doubling the filled prefix: stage j writes entries 2^j to 2^(j+1) - 1. -/
def basisAt (L : Level F) (log_n : ℕ) (x : F) : Option (ℕ → F) :=
  (List.range log_n).foldlM (fun basis j => do
      let w ← normalised_subspace_poly L j x
      pure fun i => if 2 ^ j ≤ i ∧ i < 2 ^ j + 2 ^ j then basis (i - 2 ^ j) * w else basis i)
    (fun i => if i = 0 then 1 else 0)

/-- The forward reference transform: row i is sum_k X_k(shift + point(i)) d_k, point by point. -/
def NaiveAdditiveNtt.shifted_ntt_batch (L : Level F) (height : ℕ) (mat : ℕ → V) (shift : F) :
    Option (ℕ → V) := do
  let log_n ← log2Strict height
  let rows : List V ← (List.range height).mapM fun row => do
    let p ← domain_point L row
    let basis ← basisAt L log_n (shift + p)
    pure (∑ i ∈ Finset.range height, basis i • mat i)
  pure fun r => rows.getD r 0

/-- The butterflies of one block of the inverse stage, offsets in order. -/
def blockLoop (b m : ℕ) (op : V → V → V × V) (x : ℕ → V) : ℕ → V :=
  pairLoop ((List.range m).map fun s => (b, s)) m (fun _ _ => op) x

/-- The inverse reference transform: the inverse butterflies, each twiddle from the product definition. -/
def NaiveAdditiveNtt.shifted_intt_batch (L : Level F) (height : ℕ) (mat : ℕ → V) (shift : F) :
    Option (ℕ → V) := do
  let log_n ← log2Strict height
  (List.range log_n).foldlM (fun mat j => do
      let half := 2 ^ j
      (List.range ((height + 2 * half - 1) / (2 * half))).foldlM (fun mat block => do
          let p ← domain_point L (block * 2 ^ (j + 1))
          let t ← normalised_subspace_poly L j (shift + p)
          pure (blockLoop block half (fun u v => (u + t • (u + v), u + v)) mat)) mat) mat

end p3_binary_dft.naive.mirror
