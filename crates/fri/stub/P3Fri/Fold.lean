/-
Transcriptions of the two-adic folding.

They cover the row fold, the matrix fold on its three paths, and Lagrange interpolation.

What a transcription abstracts, beyond the models of p3-dft and p3-commit:

* the base field and its extension are one mathlib field K, base values read through their embedding
* the field's two-adic generators are a table G, and asking past its adicity panics
* reverse_bits_len(x, k) is the k-bit reversal of x, exact for k > 0 or x = 0, and only called on x < 2^k
* halve(x) is x / 2
* a matrix of width w is its row-major entries
* a packed value has W lanes, a function on Fin W, and packed arithmetic acts lane by lane
* a parallel loop whose items write disjoint outputs runs its items in order
* the scratch buffer a worker thread reuses across packed blocks is an arbitrary list of the right length
* an inverse of zero panics, and so does a batch inversion with a zero entry
* an assertion panics, and a debug assertion is checked, as in a debug build
* a panic is none.

Loops, branches and early returns are kept.
-/
module

public import P3Dft.Model
public import P3Commit.Domain

@[expose] public section

namespace p3_fri.two_adic_pcs.mirror

open p3_dft.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- The inverse, which panics at zero. -/
abbrev inv (a : K) : Option K := p3_commit.domain.mirror.inv a

/-- Batch inversion, which panics on a zero entry. -/
abbrev batchInv (l : List K) : Option (List K) := p3_commit.domain.mirror.batchInv l

/-- The barycentric formula over points xs, on a coset of 2^log_n roots of unity.

A point equal to z returns its value.
The weight of x_i is x_i / (n x_0^n). -/
def lagrange_interpolate_at (xs ys : List K) (z : K) : Option K :=
  if xs.length ≠ ys.length then none
  else
    let n := xs.length
    if n = 0 then some 0
    else match (List.range n).find? (fun i => z - xs.getD i 0 = 0) with
      | some i => some (ys.getD i 0)
      | none => do
        let log_n ← log2Strict n
        let coset_power := xs.getD 0 0 ^ 2 ^ log_n
        let weight_scale ← inv ((n : K) * coset_power)
        let diffs := xs.map (z - ·)
        let diff_invs ← batchInv diffs
        let l_z := diffs.prod
        let result := ((xs.zip ys).zip diff_invs).foldl
          (fun acc e => acc + e.1.2 * (e.1.1 * weight_scale) * e.2) 0
        some (result * l_z)

/-- The two-point fold: (lo + hi) / 2 + (lo - hi) beta c. -/
def foldPair (lo hi beta c : K) : K := (lo + hi) / 2 + (lo - hi) * beta * c

/-- The fold of one opened row at the challenge beta.

The row holds the values at s w^rev(j), with s = g^rev(index).

Here g has order 2^(log_height + log_arity) and w has order 2^log_arity.

Arity 2 uses the closed form.
Other arities interpolate. -/
def fold_row (G : Gen K) (index log_height log_arity : ℕ) (beta : K) (evals : List K) : Option K := do
  let arity := 2 ^ log_arity
  let g ← G.get (log_height + log_arity)
  let subgroup_start := g ^ bitRev log_height index
  if log_arity = 1 then
    match evals with
    | [lo, hi] => do
      let halve_inv_power ← inv (subgroup_start + subgroup_start)
      some ((lo + hi) / 2 + (lo - hi) * beta * halve_inv_power)
    | _ => none
  else if evals.length ≠ arity then none
  else do
    let w ← G.get log_arity
    let xs := revIndex arity (shiftedPowersList w subgroup_start arity)
    lagrange_interpolate_at xs evals beta

/-- One arity-2 pass: entry i folds entries 2i and 2i + 1 with the factor tbl_i. -/
def foldPairs (beta : K) (tbl d : List K) (n : ℕ) : List K :=
  (List.range n).map fun i => foldPair (d.getD (2 * i) 0) (d.getD (2 * i + 1) 0) beta (tbl.getD i 0)

/-- The later passes of the scalar path: each squares the challenge and reuses a prefix of the table. -/
def foldRounds (tbl : List K) : ℕ → K → List K → List K
  | 0, _, d => d
  | r + 1, beta, d => foldRounds tbl r (beta ^ 2) (foldPairs beta tbl d (d.length / 2))

/-- The scalar paths of fold_matrix, on a matrix of width 2^log_arity given by its entries v.

Arity 2 folds each row with the bit-reversed table of g^(-i) / 2.
Arity 2^k folds the pairs of every row.
It then folds the result k - 1 more times, with beta^2, beta^4, and so on. -/
def fold_matrix_scalar (G : Gen K) (beta : K) (log_arity : ℕ) (v : List K) : Option (List K) := do
  let width := 2 ^ log_arity
  let height := v.length / width
  if log_arity = 1 then do
    let lh ← log2Strict height
    let g ← G.get (lh + 1)
    let g_inv ← inv g
    let halve_inv_powers := revIndex height (shiftedPowersList g_inv (1 / 2) height)
    some (foldPairs beta halve_inv_powers v height)
  else if width % 2 ≠ 0 then none
  else do
    let pairs_per_row := width / 2
    let initial_height := height * pairs_per_row
    let lih ← log2Strict initial_height
    let g ← G.get (lih + 1)
    let g_inv ← inv g
    let halve_inv_powers := revIndex initial_height (shiftedPowersList g_inv (1 / 2) initial_height)
    let data := foldPairs beta halve_inv_powers v initial_height
    some (foldRounds halve_inv_powers (log_arity - 1) (beta ^ 2) data)

/-- Whether n is a power of two, which zero is not. -/
def isPow2 (n : ℕ) : Bool := decide (2 ^ Nat.log 2 n = n)

/-- The packed kernel runs under three conditions:

- the packing width W is a power of two above 1
- W is no taller than the matrix
- the field has at most 32 bits. -/
def use_packed_fold (packing_width height field_bits : ℕ) : Bool :=
  decide (1 < packing_width) && isPow2 packing_width && decide (packing_width ≤ height) &&
    decide (field_bits ≤ 32)

/-- One packed lane-wise fold. -/
def foldPacked {W : ℕ} (lo hi : Fin W → K) (scalar : K) (row_factor : Fin W → K) : Fin W → K :=
  fun l => (lo l + hi l) / 2 + (lo l - hi l) * scalar * row_factor l

/-- A later round in place: pair k becomes the fold of pairs 2k and 2k + 1, for k in order. -/
def packedRound {W : ℕ} (scalars : List K) (row_factor : Fin W → K) (pairs : List (Fin W → K)) :
    List (Fin W → K) :=
  scalars.zipIdx.foldl (fun ps e =>
    ps.set e.2 (foldPacked (ps.getD (2 * e.2) 0) (ps.getD (2 * e.2 + 1) 0) e.1 row_factor)) pairs

/-- The rounds after the first, each squaring the row factor before it runs. -/
def packedRounds {W : ℕ} : List (List K) → (Fin W → K) → List (Fin W → K) → List (Fin W → K)
  | [], _, pairs => pairs
  | s :: rest, row_factor, pairs =>
    packedRounds rest (row_factor ^ 2) (packedRound s (row_factor ^ 2) pairs)

/-- fold_matrix_packed, on a matrix of width 2^log_arity given by its entries v, W rows at a time.

Round s halves pair k of row t by g^(-2^s rev(t)) w^(-2^s rev(k)) / 2.

The row part is packed.
The pair part is merged with beta^(2^s).

Each block starts from the buffer init, which its first round overwrites. -/
def fold_matrix_packed (G : Gen K) (W : ℕ) (init : List (Fin W → K)) (beta : K) (log_arity : ℕ)
    (v : List K) : Option (List K) := do
  let mw := 2 ^ log_arity
  let height := v.length / mw
  let pairs_per_row := 2 ^ (log_arity - 1)
  if ¬ (isPow2 W = true ∧ W ≤ height ∧ height % W = 0) then none
  else if mw ≠ 2 * pairs_per_row then none
  else do
    let lh ← log2Strict height
    let g ← G.get (lh + log_arity)
    let g_inv ← inv g
    let num_blocks := height / W
    let block_factors := revIndex num_blocks (powersList g_inv num_blocks)
    let lane_root := g_inv ^ num_blocks
    let log_width ← log2Strict W
    let lane_factors : Fin W → K := fun l => lane_root ^ bitRev log_width l.val
    let w ← G.get log_arity
    let w_inv ← inv w
    let pair_factors := revIndex pairs_per_row (powersList w_inv pairs_per_row)
    let round_scalars : List (List K) := (List.range log_arity).map fun r =>
      (pair_factors.take (pairs_per_row / 2 ^ r)).map fun wf => beta ^ 2 ^ r / 2 * wf
    let block (b : ℕ) : List K :=
      let column (c : ℕ) : Fin W → K := fun l => v.getD ((b * W + l.val) * mw + c) 0
      let row_factor : Fin W → K := fun l => lane_factors l * block_factors.getD b 0
      let first := (round_scalars.headD []).zipIdx.foldl (fun ps e =>
        ps.set e.2 (foldPacked (column (2 * e.2)) (column (2 * e.2 + 1)) e.1 row_factor)) init
      let pairs := packedRounds (round_scalars.drop 1) row_factor first
      List.ofFn (pairs.getD 0 0)
    some ((List.range num_blocks).flatMap block)

/-- The packed kernel where it applies, the scalar paths elsewhere. -/
def fold_matrix (G : Gen K) (W field_bits : ℕ) (init : List (Fin W → K)) (beta : K)
    (log_arity : ℕ) (v : List K) : Option (List K) :=
  if use_packed_fold W (v.length / 2 ^ log_arity) field_bits then
    fold_matrix_packed G W init beta log_arity v
  else fold_matrix_scalar G beta log_arity v

end p3_fri.two_adic_pcs.mirror
