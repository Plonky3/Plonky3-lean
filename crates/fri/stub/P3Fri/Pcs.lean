/-
Transcriptions of the two-adic FRI PCS's opening reduction.

They cover the inverse denominators and the reduced openings the prover folds.

What a transcription abstracts, beyond Fold.lean:

* the field's generator is a parameter g
* the opened values are inputs, computed by p3-matrix's coset interpolation
* the packed row dot product with the offset powers of alpha is the plain dot product
* the per-height arrays have 33 slots, and a height past 32 panics, as the array index does
* a map keyed by point is a function of the point
* a parallel loop whose items write disjoint outputs runs its items in order
* a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Fri.Fold
public import P3Commit.Types

@[expose] public section

namespace p3_fri.two_adic_pcs.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror

variable {K : Type} [Field K] [DecidableEq K]

/-- The bit-reversed coset g H of order 2^H: entry r is g G_H^rev_H(r). -/
def bitrevCoset (G : Gen K) (g : K) (log_global_max_height : ℕ) : Option (List K) := do
  let w ← G.get log_global_max_height
  some ((List.range (2 ^ log_global_max_height)).map fun r => g * w ^ bitRev log_global_max_height r)

/-- One matrix to open: its rows, its points, and the values claimed at each point. -/
structure MatToOpen (K : Type) where
  mat : Mat K
  points : List K
  openings : List (List K)

/-- For each point z, the inverses of z - x over the first 2^h coset entries.

Here h is the tallest log height opened at z.
A zero panics. -/
def compute_inverse_denominators (mats : List (MatToOpen K)) (coset : List K) (z : K) : Option (List K) :=
  let hs := (mats.filter fun m => z ∈ m.points).map fun m => Nat.log 2 m.mat.height
  batchInv ((coset.take (2 ^ hs.foldl max 0)).map (z - ·))

/-- The state of the reduction, per log height:

- the count of reduced columns
- the reduced vector, if a matrix of that height was seen. -/
abbrev PcsRedState (K : Type) := (ℕ → ℕ) × (ℕ → Option (List K))

/-- One point of a matrix of log height lh and width w.

It adds (alpha^num y - alpha^(k w) compressed) / (z - x) to every row.
It then advances the ladder by w. -/
def reducePoint (alpha : K) (inv_denoms : K → Option (List K)) (lh w : ℕ) (compressed : List K)
    (st2 : (ℕ → ℕ) × List K) (e : (K × List K) × ℕ) : Option ((ℕ → ℕ) × List K) := do
  let (num2, ro) := st2
  let ((z, ys), k) := e
  let off := alpha ^ num2 lh
  let weighted := off * ((List.range ys.length).map fun i => alpha ^ i * ys.getD i 0).sum
  let inv ← inv_denoms z
  let rescale := if k = 0 then 1 else alpha ^ (k * w)
  let ro' := (List.range ro.length).map fun r =>
    ro.getD r 0 + (weighted - rescale * compressed.getD r 0) * inv.getD r 0
  some (Function.update num2 lh (num2 lh + w), ro')

/-- One matrix of the reduction.

It compresses the rows with the offset powers of alpha.
It then adds each point's quotient at its height. -/
def reduceMat (alpha : K) (inv_denoms : K → Option (List K)) (st : PcsRedState K) (m : MatToOpen K) :
    Option (PcsRedState K) := do
  let (num, red) := st
  let lh ← log2Strict m.mat.height
  if 32 < lh then none
  else
    let ro0 := (red lh).getD ((List.range m.mat.height).map fun _ => 0)
    let first := alpha ^ num lh
    let compressed := (List.range m.mat.height).map fun r =>
      ((List.finRange m.mat.width).map fun c => alpha ^ c.val * first * m.mat.entry r c).sum
    let (num', ro) ← (m.points.zip m.openings).zipIdx.foldlM
      (reducePoint alpha inv_denoms lh m.mat.width compressed) (num, ro0)
    some (num', Function.update red lh (some ro))

/-- The reduced openings of open: one vector per log height present, tallest first. -/
def reduced_openings (G : Gen K) (g : K) (alpha : K) (mats : List (MatToOpen K)) :
    Option (List (ℕ × List K)) := do
  let H ← (mats.map fun m => Nat.log 2 m.mat.height).max?
  let coset ← bitrevCoset G g H
  let (_, red) ← mats.foldlM (reduceMat alpha (compute_inverse_denominators mats coset)) (fun _ => 0, fun _ => none)
  some (((List.range 33).reverse.filterMap fun h => (red h).map fun v => (h, v)))

end p3_fri.two_adic_pcs.mirror
