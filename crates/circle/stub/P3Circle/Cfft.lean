/-
Transcriptions of the circle FFT: the twiddles, the butterfly layers, the transforms and the basis.

What a transcription abstracts, beyond the models of the points, the domains and p3-dft:

* a matrix of height h is its rows, a function from row indices to a vector space V, as in p3-dft's model;
* rows of the buffer that the Rust leaves uninitialised are arbitrary values;
* the fused passes of cfft_layers apply the layers one after another: each pass runs every layer of its run on disjoint groups of rows;
* reverse_slice_index_bits permutes a list of length 2^k by k-bit reversal;
* step_by(2) keeps the entries at even indices;
* div_2exp_u64(1, k) is 1 / 2^k;
* an inverse of zero panics, and so does a batch inversion with a zero entry;
* an assertion panics, and a debug assertion and a subtraction below zero are checked, as in a debug build;
* a panic is none.

Loops and the order of operations are kept.
-/
module

public import P3Circle.Domain
public import P3Dft.Butterflies

@[expose] public section

namespace p3_circle.cfft.mirror

open p3_dft.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_commit.domain.mirror
open p3_dft.butterflies.mirror

/-- A list of length 2^k in k-bit-reversed order: entry i is entry rev_k(i). -/
def revList {α : Type _} (dflt : α) (l : List α) : List α :=
  (List.range l.length).map fun i => l.getD (bitRev (Nat.log 2 l.length) i) dflt

/-- The entries at even indices, as step_by(2) yields them. -/
def stepBy2 {α : Type _} (l : List α) : List α :=
  (l.zipIdx.filter fun e => e.2 % 2 = 0).map Prod.fst

variable {K : Type _} [Field K] [DecidableEq K]

variable (G : Gen (K × K))

/-- The later x-twiddle layers: each keeps the even entries of the previous one and squares them, checking the previous length. -/
def twiddleLoop (log_n : ℕ) (acc : Option (List (List K))) (i : ℕ) : Option (List (List K)) := do
  let tw ← acc
  let prev := tw.getLastD []
  if prev.length ≠ 2 ^ (log_n - 2 - i) then none
  else some (tw ++ [(stepBy2 prev).map Point.vnStep])

/-- The twiddles of every layer: the y-coordinates of the half coset in bit-reversed order, then x-coordinates.

It asserts log_n >= 1. -/
def compute_twiddles (d : CircleDomain K) : Option (List (List K)) := do
  if d.log_n < 1 then none
  else
    let c0 ← CircleDomain.coset0 G d
    let pts := revList Point.ZERO c0
    let tw0 := pts.map Point.y
    if 2 ≤ d.log_n then
      let tw1 := (stepBy2 pts).map Point.x
      (List.range (d.log_n - 2)).foldl (twiddleLoop d.log_n) (some [tw0, tw1])
    else some [tw0]

/-- The y-coordinates of the half coset, in bit-reversed order. -/
def y_twiddles (d : CircleDomain K) : Option (List K) := do
  let c0 ← CircleDomain.coset0 G d
  some (revList 0 (c0.map Point.y))

/-- The x-coordinates of the half coset doubled layer times, in bit-reversed order. -/
def x_twiddles (d : CircleDomain K) (layer : ℕ) : Option (List K) := do
  let g ← CircleDomain.subgroup_generator G d
  let generator := Point.mul g (2 ^ layer)
  let shift := Point.mul d.shift (2 ^ layer)
  if d.log_n < layer + 2 then none
  else some (revList 0 ((chain shift generator (2 ^ (d.log_n - layer - 2))).map Point.x))

/-- The x-coordinate of shift + index g. -/
def nth_x_twiddle (d : CircleDomain K) (index : ℕ) : Option K := do
  let g ← CircleDomain.subgroup_generator G d
  some (Point.add d.shift (Point.mul g index)).x

/-- The basis 1, y, x, x y, v_2, v_2 y, ... at the point: each round appends the products by the current x, then squares x.

It panics for log_n = 0. -/
def circle_basis (p : Point K) (log_n : ℕ) : Option (List K) :=
  if log_n < 1 then none
  else
    let r := (List.range (log_n - 1)).foldl
      (fun (acc : List K × K) _ => (acc.1 ++ acc.1.map (· * acc.2), Point.vnStep acc.2)) ([1, p.y], p.x)
    if r.1.length ≠ 2 ^ log_n then none else some r.1

/-- One layer of a fused pass: a duplication, or one twiddle per block. -/
inductive CfftLayer (B : Type _) where
  | Dup (blocks : ℕ)
  | Butterflies (ts : List B)

/-- The number of blocks of a layer. -/
def CfftLayer.blocks {B : Type _} : CfftLayer B → ℕ
  | .Dup blocks => blocks
  | .Butterflies ts => ts.length

variable {V : Type _} [AddCommGroup V] [Module K V]

/-- One layer on 2^log_h rows: block b of 2m rows pairs rows b 2m + s and b 2m + s + m, m = 2^log_h / (2 blocks).

A duplication copies the lower row onto the upper one; a butterfly applies the block's twiddle. -/
def runLayer (bf : K → V → V → V × V) (log_h : ℕ) (layer : CfftLayer K) (x : ℕ → V) : ℕ → V :=
  let m := 2 ^ log_h / (2 * layer.blocks)
  match layer with
  | .Dup nb => pairLoop (blocks nb m) m (fun _ _ a _ => (a, a)) x
  | .Butterflies ts => pairLoop (blocks ts.length m) m (fun b _ => bf (ts.getD b 0)) x

/-- The layers in order, then the scaling of every row.

It asserts at least one layer when there is a scale. -/
def cfft_layers (bf : K → V → V → V × V) (log_h : ℕ) (layers : List (CfftLayer K))
    (scale : Option K) (x : ℕ → V) : Option (ℕ → V) :=
  if layers.isEmpty ∧ scale.isSome then none
  else
    let y := layers.foldl (fun acc l => runLayer bf log_h l acc) x
    some (match scale with
      | some c => scaleRows c y
      | none => y)

/-- From values in circle FFT order on the domain to coefficients in the circle FFT basis.

Decimation-in-frequency layers with the inverted twiddles, first the y layer, then the x layers, then a scaling by 1 / 2^log_n. -/
def interpolate (d : CircleDomain K) (rows : ℕ → V) : Option (ℕ → V) := do
  let tws ← compute_twiddles G d
  let invs ← tws.mapM batchInv
  let layers := invs.map CfftLayer.Butterflies
  if layers.length ≠ d.log_n then none
  else cfft_layers (fun t => DifButterfly.apply t) d.log_n layers (some (2 ^ d.log_n : K)⁻¹) rows

/-- From 2^log_m coefficients to the values in circle FFT order on a domain at least as large.

The first added bits layers duplicate rows, which is a decimation-in-time layer on zero-padded coefficients. -/
def evaluate (d : CircleDomain K) (height : ℕ) (coeffs : ℕ → V) : Option (ℕ → V) := do
  let log_m ← log2Strict height
  if d.log_n < log_m then none
  else
    let added_bits := d.log_n - log_m
    let tws ← compute_twiddles G d
    let tw_layers := ((tws.map CfftLayer.Butterflies).reverse).drop added_bits
    let layers := (List.range added_bits).map (fun l => CfftLayer.Dup (2 ^ l)) ++ tw_layers
    cfft_layers (fun t => DitButterfly.apply t) d.log_n layers none coeffs

end p3_circle.cfft.mirror
