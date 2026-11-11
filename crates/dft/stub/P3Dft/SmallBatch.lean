/-
Transcriptions of the small-batch radix-2 backend.

What a transcription abstracts, beyond those of the other transforms:

- a layer splits each half block into equal sub-chunks and pairs them in order
- that pairs every element with the element at the same offset
- so the transcription applies the butterfly to whole halves
- the matrix is exactly h rows of w values, without values past the last row
- the shared twiddle cache holds the tables for the largest size requested so far, 2^L >= h
- the rows per parallel chunk are min(2^(ceil(log_2(c / w))), h)
- the element count c of the L1 estimate is a parameter.
-/
module

public import P3Dft.Transforms

@[expose] public section

namespace p3_dft.radix_2_small_batch.mirror

open p3_dft.mirror p3_dft.butterflies.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- Every s-th entry of a list, from the first, as a stepping iterator yields them. -/
def stepBy {α : Type _} (l : List α) (s : ℕ) : List α :=
  ((List.range ((l.length + s - 1) / s)).filterMap fun j => l[j * s]?)

/-- The tables for an FFT of length n = 2^k.

Table i holds every 2^i-th of the first n/2 powers. -/
def roots_of_unity_table (G : Gen K) (n : ℕ) : Option (List (List K)) := do
  let lg_n ← log2Strict n
  if lg_n = 0 then none
  else
    let generator ← G.get lg_n
    let half_n := 2 ^ (lg_n - 1)
    let nth_roots := powersList generator half_n
    pure ((List.range lg_n).map fun i => stepBy nth_roots (2 ^ i))

/-- The cache of the largest size 2^L requested so far.

It holds the tables bit-reversed, and the inverse tables.

An inverse table keeps the one in front and lists the rest reversed and negated. -/
def cache (G : Gen K) (L : ℕ) : Option (List (List K) × List (List K)) :=
  if L = 0 then some ([], [])
  else (roots_of_unity_table G (2 ^ L)).map fun tables =>
    (tables.map fun ts => revIndex ts.length ts,
      tables.map fun ts =>
        let inv := 1 :: (ts.tail.reverse.map fun f => -f)
        revIndex inv.length inv)

/-- The rows per parallel chunk: min(2^(ceil(log_2(c / w))), h), for c the workload. -/
def estimate_num_rows_in_l1 (workload w h : ℕ) : ℕ :=
  min (2 ^ Nat.clog 2 (workload / w)) h

/-- One parallel layer: blocks of h / n rows, for n the table length.

Block ind uses twiddle ind.

Block 0 uses the butterfly without a twiddle. -/
def dft_layer_par (h : ℕ) (twiddles : List K) (fly : K → V → V → V × V) (x : ℕ → V) : ℕ → V :=
  let num_blocks := twiddles.length
  let half := h / (2 * num_blocks)
  pairLoop (blocks num_blocks half) half
    (fun ind _ => if ind = 0 then TwiddleFreeButterfly.apply else fly (twiddles.getD ind 0)) x

/-- The butterfly of entry j of a table, without a twiddle at entry zero. -/
def flyAt (twiddles : List K) (fly : K → V → V → V × V) (j : ℕ) : V → V → V × V :=
  if j = 0 then TwiddleFreeButterfly.apply else fly (twiddles.getD j 0)

/-- The butterflies of sub-blocks lo to lo + n - 1, each with m pairs. -/
def subBlocks (lo n m : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun t => (List.range m).map fun s => (lo + t, s)

/-- Two decimation-in-time layers per outer block: the half of the block, then its two quarters. -/
def dft_layer_par_double_dit (h : ℕ) (small large : List K) (fly : K → V → V → V × V)
    (x : ℕ → V) : ℕ → V :=
  let num_blocks := small.length
  let q := h / (4 * num_blocks)
  (List.range num_blocks).foldl (fun acc ind =>
    let acc := pairLoop (subBlocks ind 1 (2 * q)) (2 * q) (fun b _ => flyAt small fly b) acc
    pairLoop (subBlocks (2 * ind) 2 q) q (fun b _ => flyAt large fly b) acc) x

/-- Three decimation-in-time layers per outer block: the half, the two quarters, the four eighths. -/
def dft_layer_par_triple_dit (h : ℕ) (small med large : List K) (fly : K → V → V → V × V)
    (x : ℕ → V) : ℕ → V :=
  let num_blocks := small.length
  let e := h / (8 * num_blocks)
  (List.range num_blocks).foldl (fun acc ind =>
    let acc := pairLoop (subBlocks ind 1 (4 * e)) (4 * e) (fun b _ => flyAt small fly b) acc
    let acc := pairLoop (subBlocks (2 * ind) 2 (2 * e)) (2 * e) (fun b _ => flyAt med fly b) acc
    pairLoop (subBlocks (4 * ind) 4 e) e (fun b _ => flyAt large fly b) acc) x

/-- Two decimation-in-frequency layers per outer block: the two quarters, then the half. -/
def dft_layer_par_double_dif (h : ℕ) (small large : List K) (fly : K → V → V → V × V)
    (x : ℕ → V) : ℕ → V :=
  let num_blocks := small.length
  let q := h / (4 * num_blocks)
  (List.range num_blocks).foldl (fun acc ind =>
    let acc := pairLoop (subBlocks (2 * ind) 2 q) q (fun b _ => flyAt large fly b) acc
    pairLoop (subBlocks ind 1 (2 * q)) (2 * q) (fun b _ => flyAt small fly b) acc) x

/-- Three decimation-in-frequency layers per outer block: the four eighths, the two quarters, the half. -/
def dft_layer_par_triple_dif (h : ℕ) (small med large : List K) (fly : K → V → V → V × V)
    (x : ℕ → V) : ℕ → V :=
  let num_blocks := small.length
  let e := h / (8 * num_blocks)
  (List.range num_blocks).foldl (fun acc ind =>
    let acc := pairLoop (subBlocks (4 * ind) 4 e) e (fun b _ => flyAt large fly b) acc
    let acc := pairLoop (subBlocks (2 * ind) 2 (2 * e)) (2 * e) (fun b _ => flyAt med fly b) acc
    pairLoop (subBlocks ind 1 (4 * e)) (4 * e) (fun b _ => flyAt small fly b) acc) x

/-- The groups of three consecutive tables, with any one or two left over at the end dropped. -/
def tuples3 {α : Type _} : List α → List (α × α × α)
  | a :: b :: c :: rest => (a, b, c) :: tuples3 rest
  | _ => []

/-- One chunk of rows at chunk index idx: decimation-in-time layers, smallest table last.

Layer l of the chunk reads 2^l consecutive twiddles, from twiddle idx 2^l. -/
def remaining_layers (npr idx : ℕ) (root_table : List (List K)) (x : ℕ → V) : ℕ → V :=
  (List.range root_table.length).foldl (fun acc layer =>
    let twiddles := root_table.getD (root_table.length - 1 - layer) []
    let n := 2 ^ layer
    let half := npr / (2 * n)
    pairLoop ((List.range n).flatMap fun b => (List.range half).map fun s => (idx * n + b, s)) half
      (fun b _ => DitButterfly.apply (twiddles.getD b 0)) acc) x

/-- One chunk of rows at chunk index idx: decimation-in-frequency layers, largest table first.

Layer l of the chunk reads 2^(r - l - 1) consecutive twiddles, for r tables. -/
def initial_layers (npr idx : ℕ) (root_table : List (List K)) (x : ℕ → V) : ℕ → V :=
  let num_rounds := root_table.length
  (List.range num_rounds).foldl (fun acc layer =>
    let twiddles := root_table.getD layer []
    let n := 2 ^ (num_rounds - layer - 1)
    let half := npr / (2 * n)
    pairLoop ((List.range n).flatMap fun b => (List.range half).map fun s => (idx * n + b, s)) half
      (fun b _ => DifButterfly.apply (twiddles.getD b 0)) acc) x

/-- The remaining layers, chunk by chunk. -/
def par_remaining_layers (h npr : ℕ) (root_table : List (List K)) (x : ℕ → V) : ℕ → V :=
  (List.range (h / npr)).foldl (fun acc idx =>
    fun i => if i / npr = idx then remaining_layers npr idx root_table acc i else acc i) x

/-- The initial layers, chunk by chunk.

Each chunk is first divided by the height 2^log_height. -/
def par_initial_layers (h npr : ℕ) (root_table : List (List K)) (log_height : ℕ) (x : ℕ → V) :
    ℕ → V :=
  let inv_height := ((2 : K) ^ log_height)⁻¹
  (List.range (h / npr)).foldl (fun acc idx =>
    let acc := fun i => if i / npr = idx then inv_height • acc i else acc i
    fun i => if i / npr = idx then initial_layers npr idx root_table acc i else acc i) x

/-- The extra one or two layers when the layer count is not a multiple of three. -/
def extra_layers_dit (h : ℕ) (tables : List (List K)) (x : ℕ → V) : Option (ℕ → V) :=
  match tables with
  | [] => some x
  | [t0] => some (dft_layer_par h t0 DitButterfly.apply x)
  | [t0, t1] => some (dft_layer_par_double_dit h t1 t0 DitButterfly.apply x)
  | _ => none

def extra_layers_dif (h : ℕ) (tables : List (List K)) (x : ℕ → V) : Option (ℕ → V) :=
  match tables with
  | [] => some x
  | [t0] => some (dft_layer_par h t0 DifButterfly.apply x)
  | [t0, t1] => some (dft_layer_par_double_dif h t1 t0 DifButterfly.apply x)
  | _ => none

/-- The forward transform with a cache of size 2^L and the L1 element estimate c.

It runs, in order:

- triples of layers, from the one-block layer down
- the extra layers
- the chunked layers
- a bit reversal. -/
def Radix2DFTSmallBatch.dft_batch (G : Gen K) (L c w h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let (g, _) ← cache G L
  let root_table := g.drop (g.length - log_h)
  let num_par_rows := estimate_num_rows_in_l1 c w h
  let log_num_par_rows ← log2Strict num_par_rows
  let x := (tuples3 (root_table.drop log_num_par_rows).reverse).foldl
    (fun acc t => dft_layer_par_triple_dit h t.1 t.2.1 t.2.2 DitButterfly.apply acc) x
  let corr := (log_h - log_num_par_rows) % 3
  let x ← extra_layers_dit h ((root_table.drop log_num_par_rows).take corr) x
  let x := par_remaining_layers h num_par_rows (root_table.take log_num_par_rows) x
  pure (revRows log_h x)

/-- The inverse with a cache of size 2^L.

It runs, in order:

- a bit reversal
- the chunked layers, with the division by the height
- the extra layers
- triples of layers, up to the one-block layer. -/
def Radix2DFTSmallBatch.idft_batch (G : Gen K) (L c w h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let (_, g) ← cache G L
  let root_table := g.drop (g.length - log_h)
  let num_par_rows := estimate_num_rows_in_l1 c w h
  let log_num_par_rows ← log2Strict num_par_rows
  let x := revRows log_h x
  let x := par_initial_layers h num_par_rows (root_table.take log_num_par_rows) log_h x
  let corr := (log_h - log_num_par_rows) % 3
  let x ← extra_layers_dif h ((root_table.drop log_num_par_rows).take corr) x
  pure ((tuples3 (root_table.drop (log_num_par_rows + corr))).foldl
    (fun acc t => dft_layer_par_triple_dif h t.2.2 t.2.1 t.1 DifButterfly.apply acc) x)

end p3_dft.radix_2_small_batch.mirror
