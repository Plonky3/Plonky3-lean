/-
Transcriptions of the hiding FRI PCS.

They cover the randomized commitment, the quotient masks and the budget.

The opening and the verifier are in HidingPcs.lean.

What a transcription abstracts:

* the random generator is the list of values it yields, consumed in order
* a matrix of width w is its row-major entries
* a usize is a natural number, and a checked operation fails when it leaves 64 bits
* the inner PCS and the DFT backend are left out: the masks are stated on coefficients
* a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Commit.Types
public import P3Fri.Config
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Field.Basic

@[expose] public section

namespace p3_fri.hiding_pcs.mirror

open p3_commit.pcs.univariate.mirror

variable {K : Type} [Field K]

/-- Append k random values to each of the h rows of width w. -/
def withRandomCols (v : List K) (w k : ℕ) (rnd : List K) : List K :=
  (List.range (v.length / w)).flatMap fun i =>
    (v.drop (i * w)).take w ++ (rnd.drop (i * k)).take k

/-- The randomized commitment of a matrix.

It appends w + 2r random columns, then reads the result at width w + r. -/
def randomize (v : List K) (w r : ℕ) (rnd : List K) : List K × ℕ :=
  (withRandomCols v w (w + 2 * r) rnd, w + r)

/-- The hiding budget 2 (D max(points, 1) + num_queries), or nothing on overflow. -/
def hiding_budget (num_queries extension_degree num_points : ℕ) : Option ℕ :=
  let a := extension_degree * max num_points 1
  if 2 ^ 64 ≤ a then none else
  let b := a + num_queries
  if 2 ^ 64 ≤ b then none else
  if 2 ^ 64 ≤ 2 * b then none else some (2 * b)

/-- The reasons a hiding prover refuses. -/
inductive HidingFriProverError where
  | Fri (e : p3_fri.config.mirror.FriProverError)
  | InsufficientRandomCodewords (required got : ℕ)
  | BudgetOverflow
  | HidingBudgetExceeded (mask_height num_queries num_opening_points extension_degree : ℕ)
  deriving DecidableEq

/-- Enough random codewords, and a mask at least the budget. -/
def check_hiding_budget (num_random_codewords num_queries mask_height extension_degree num_points : ℕ) :
    Except HidingFriProverError Unit :=
  if num_random_codewords < extension_degree then
    .error (.InsufficientRandomCodewords extension_degree num_random_codewords)
  else match hiding_budget num_queries extension_degree num_points with
    | none => .error .BudgetOverflow
    | some required =>
      if mask_height < required then
        .error (.HidingBudgetExceeded mask_height num_queries num_points extension_degree)
      else .ok ()

/-- The LDE height without the blowup, halved.

A shift past the word gives zero. -/
def lde_mask_height (log_blowup height : ℕ) : ℕ :=
  (if log_blowup < 64 then height / 2 ^ log_blowup else 0) / 2

/-- The quotient mask of one chunk, on its coefficients, column by column:

- coefficient i loses g^i r_i
- coefficient h + i gains p g^i r_i. -/
def maskCoeffs (g p : K) (h w : ℕ) (rv coeffs : List K) : List K :=
  ((List.range h).flatMap fun i => (List.range w).map fun j => (i, j)).foldl (fun c e =>
    let m := g ^ e.1 * rv.getD (e.1 * w + e.2) 0
    let c := c.set (e.1 * w + e.2) (c.getD (e.1 * w + e.2) 0 - m)
    c.set ((h + e.1) * w + e.2) (c.getD ((h + e.1) * w + e.2) 0 + p * m)) coeffs

/-- The last chunk's mask.

It is minus the sum of the other chunks' masks, each scaled by c_j / c_last. -/
def lastMask (mul_coeffs : List K) (hw : ℕ) (rv : List K) (last : ℕ) : List K :=
  (List.range mul_coeffs.length).foldl (fun acc j =>
    (List.range hw).foldl (fun acc k =>
      acc.set (last * hw + k) (acc.getD (last * hw + k) 0 - acc.getD (j * hw + k) 0 * mul_coeffs.getD j 0))
      acc) rv

/-- The draws before the last chunk is balanced: d - 1 random blocks of hw values, then a zero block. -/
def maskDraws (d hw : ℕ) (rnd : List K) : List K := rnd.take ((d - 1) * hw) ++ List.replicate hw 0

/-- The quotient masks' values, block by block.

There is one constant c_i per evaluation the caller passes, and the caller's chunk count n.

- It asserts more than one chunk.
- It reads c_(n-1), which panics past the constants, and inverts it, which panics at zero.
- It balances chunk n - 1 against the chunks before it. -/
def quotientMaskValues [DecidableEq K] (cis : List K) (num_chunks hw : ℕ) (rnd : List K) : Option (List K) := do
  if num_chunks ≤ 1 then none
  let last := num_chunks - 1
  let clast ← cis[last]?
  if clast = 0 then none
  let mul_coeffs := (List.range last).map fun i => cis.getD i 0 * clast⁻¹
  pure (lastMask mul_coeffs hw (maskDraws cis.length hw rnd) last)

end p3_fri.hiding_pcs.mirror
