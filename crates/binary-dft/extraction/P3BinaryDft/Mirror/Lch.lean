/-
Transcriptions of the Lin-Chung-Han transform of p3-binary-dft.

A slice of a matrix is its own matrix, its rows renumbered from zero, as the Rust chunks are.

The thread pool is serial, as maybe-rayon without its parallel feature is.

It has one worker, so no stage is staged and a staged group is never reached.

That branch is a panic here.

The staged coset pass of a message larger than one tile is not transcribed.

Its branch is a panic here too.
-/
module

public import P3BinaryDft.Domain
public import P3BinaryDft.Butterfly

@[expose] public section

namespace p3_binary_dft.lch.mirror

open p3_binary_dft.mirror p3_binary_dft.domain.mirror p3_binary_dft.butterfly.mirror p3_dft.mirror

variable {F : Type _} [Field F] [DecidableEq F] {V : Type _} [AddCommGroup V] [Module F V]

/-! ## Slices -/

/-- The rows of a matrix from row o on, renumbered from zero. -/
def slice (x : ℕ → V) (o : ℕ) : ℕ → V := fun r => x (o + r)

/-- Write the first n rows of a slice back at row o. -/
def writeBack (x : ℕ → V) (o n : ℕ) (y : ℕ → V) : ℕ → V :=
  fun r => if o ≤ r ∧ r < o + n then y (r - o) else x r

/-! ## Twiddles -/

/-- The twiddle state: the base of each stage, W_j(shift), and the steps between block twiddles. -/
structure Twiddles (F : Type _) where
  bases : List F
  steps : List F

/-- The twiddle state of a transform of 2^log_n rows over the coset shift + S. -/
def Twiddles.new (L : Level F) (log_n : ℕ) (shift : F) : Option (Twiddles F) := do
  let bases := ((List.range log_n).foldl (fun (acc : List F × F) _ =>
    (acc.1 ++ [acc.2], acc.2 ^ 2 + acc.2)) ([], shift)).1
  let steps ← domain_point_steps L (log_n - 1)
  pure ⟨bases, steps⟩

/-- The twiddle of one block, from its index: the stage base plus domain point 2 b. -/
def Twiddles.at (L : Level F) (tw : Twiddles F) (stage block : ℕ) : Option F := do
  let base ← tw.bases[stage]?
  let p ← domain_point L (block * 2)
  pure (base + p)

/-- What to add to the twiddle of block index - 1 to reach that of block index. -/
def Twiddles.step (tw : Twiddles F) (index : ℕ) : Option F := tw.steps[trailingZeros index]?

/-! ## One stage -/

/-- Field elements one butterfly task covers on each side of a block. -/
def BUTTERFLY_GRAIN : ℕ := 1024

/-- Bytes of one contiguous row tile. -/
def DEEP_TILE_BYTES : ℕ := 128 * 1024

/-- The butterfly of the level on block i of a slice.

The block is split at its half, and the two runs are asserted equal. -/
def blockButterfly (inverse : Bool) (len half i : ℕ) (t : F) (y : ℕ → V) : Option (ℕ → V) :=
  let start := i * (2 * half)
  let blockLen := min (2 * half) (len - start)
  if blockLen < half then none
  else plain_butterfly inverse start (start + half) half (blockLen - half) t y

/-- The blocks of one slice in ascending order, each twiddle stepped from the one before. -/
def walkBlocks (L : Level F) (tw : Twiddles F) (inverse : Bool) (stage first len half : ℕ)
    (y : ℕ → V) : Option (ℕ → V) := do
  let t0 ← tw.at L stage first
  let r ← (List.range ((len + 2 * half - 1) / (2 * half))).foldlM (fun (acc : (ℕ → V) × F) i => do
      let t ← if i = 0 then pure acc.2 else (do pure (acc.2 + (← tw.step (first + i))))
      let y ← blockButterfly inverse len half i t acc.1
      pure (y, t)) (y, t0)
  pure r.1

/-- One stage as a single pass over every row, cut into tasks of whole blocks.

A task covers the grain in elements, so a row of w elements makes 2^j w elements per half block.

The grain is divided by that count, which panics at width zero. -/
def stage_pass (L : Level F) (tw : Twiddles F) (inverse : Bool) (width n j : ℕ) (x : ℕ → V) :
    Option (ℕ → V) :=
  let half := 2 ^ j * width
  if half = 0 then none else
  let per_task := max (BUTTERFLY_GRAIN / half) 1
  let task_rows := per_task * (2 * 2 ^ j)
  (List.range ((n + task_rows - 1) / task_rows)).foldlM (fun x task => do
      let o := task * task_rows
      let len := min task_rows (n - o)
      let y ← walkBlocks L tw inverse j (task * per_task) len (2 ^ j) (slice x o)
      pure (writeBack x o len y)) x

/-! ## Tiles and the schedule -/

/-- Run the k stages of a tile of 2^k rows, which are the global stages from a base stage up.

At its stage j, the tile's blocks continue the global numbering from index * 2^(k - 1 - j). -/
def tile_stages (L : Level F) (tw : Twiddles F) (inverse : Bool) (len log_rows stage_base index : ℕ)
    (y : ℕ → V) : Option (ℕ → V) :=
  (List.range log_rows).foldlM (fun y step =>
      let jj := if inverse then step else log_rows - 1 - step
      walkBlocks L tw inverse (stage_base + jj) (index * 2 ^ (log_rows - 1 - jj)) len
        (2 ^ jj) y) y

/-- Run the bottom k stages inside each contiguous tile of 2^k rows. -/
def deep_tiles (L : Level F) (tw : Twiddles F) (inverse : Bool) (n log_rows : ℕ) (x : ℕ → V) :
    Option (ℕ → V) :=
  (List.range ((n + 2 ^ log_rows - 1) / 2 ^ log_rows)).foldlM (fun x index => do
      let len := min (2 ^ log_rows) (n - index * 2 ^ log_rows)
      let y ← tile_stages L tw inverse len log_rows 0 index (slice x (index * 2 ^ log_rows))
      pure (writeBack x (index * 2 ^ log_rows) len y))
    x

/-- floor(log_2 n), zero at zero. -/
def log2Floor (n : ℕ) : ℕ := Nat.log 2 n

/-- ceil(log_2 n), zero at zero. -/
def log2Ceil (n : ℕ) : ℕ := Nat.clog 2 n

/-- The tile shapes of one matrix, as base-two logarithms. -/
structure Schedule where
  log_tile_rows : ℕ
  log_staged_rows : ℕ
  log_slab_rows : ℕ

/-- The tile shapes a matrix gets from its byte budgets and a worker count. -/
def Schedule.for_workers (bytes width log_n workers : ℕ) : Schedule :=
  let row_bytes := bytes * width
  let capacity := log2Floor (max (DEEP_TILE_BYTES / row_bytes) 1)
  let log_tile_rows := min capacity (log_n - log2Ceil workers)
  let log_slab_rows := min (log2Ceil ((64 + row_bytes - 1) / row_bytes)) log_tile_rows
  let slab_bytes := row_bytes * 2 ^ log_slab_rows
  let log_staged_rows := if 16 ≤ workers then log2Floor (max (64 * 1024 / slab_bytes) 1) else 0
  ⟨log_tile_rows, log_staged_rows, log_slab_rows⟩

/-- The tile shapes on the serial pool, which has one worker. -/
def Schedule.new (bytes width log_n : ℕ) : Schedule := Schedule.for_workers bytes width log_n 1

/-- A schedule clipped to one height: a contiguous tile, and groups of stages above it. -/
structure Cut where
  tile : ℕ
  slab : ℕ
  group : ℕ
  groups : ℕ
  log_n : ℕ

/-- Clip a schedule to a transform of 2^log_n rows. -/
def Cut.new (s : Schedule) (log_n : ℕ) : Cut :=
  let tile := min s.log_tile_rows log_n
  let group := if 2 ≤ s.log_staged_rows then s.log_staged_rows else 1
  ⟨tile, min s.log_slab_rows tile, group, (log_n - tile + group - 1) / group, log_n⟩

/-- The stages low .. high that group g runs, counting up from the tile. -/
def Cut.bounds (c : Cut) (g : ℕ) : ℕ × ℕ :=
  let low := c.tile + g * c.group
  (low, min (low + c.group) c.log_n)

/-- Run the stages low .. high as one pass.

A single stage is a plain pass, and a staged group panics here. -/
def group_pass (L : Level F) (tw : Twiddles F) (inverse : Bool) (width n : ℕ) (b : ℕ × ℕ)
    (x : ℕ → V) : Option (ℕ → V) :=
  if b.2 - b.1 = 1 then stage_pass L tw inverse width n b.1 x else none

/-- The forward groups below the first g from the bottom, top first, then the tile. -/
def forward_below (L : Level F) (tw : Twiddles F) (width n : ℕ) (c : Cut) (groups : ℕ)
    (x : ℕ → V) : Option (ℕ → V) := do
  let x ← (List.range groups).reverse.foldlM
    (fun x g => group_pass L tw false width n (c.bounds g) x) x
  if 0 < c.tile then deep_tiles L tw false n c.tile x else pure x

/-- Run every stage of a transform of 2^log_n rows under one schedule. -/
def run (L : Level F) (tw : Twiddles F) (inverse : Bool) (width log_n : ℕ) (s : Schedule)
    (x : ℕ → V) : Option (ℕ → V) := do
  let c := Cut.new s log_n
  if inverse then
    let x ← if 0 < c.tile then deep_tiles L tw true (2 ^ log_n) c.tile x else pure x
    (List.range c.groups).foldlM (fun x g => group_pass L tw true width (2 ^ log_n) (c.bounds g) x) x
  else forward_below L tw width (2 ^ log_n) c c.groups x

/-! ## The transform -/

/-- Transform a matrix of n rows of width elements in place, over the coset shift + S_l. -/
def transform (L : Level F) (inverse : Bool) (width n : ℕ) (shift : F) (x : ℕ → V) :
    Option (ℕ → V) := do
  if width = 0 then none else
  let log_n ← log2Strict n
  if 2 ^ L.logBits < log_n then none else
  let tw ← Twiddles.new L log_n shift
  if n * width * L.bytes ≤ DEEP_TILE_BYTES then
    (List.range log_n).foldlM (fun x step =>
      stage_pass L tw inverse width n (if inverse then step else log_n - 1 - step) x) x
  else run L tw inverse width log_n (Schedule.new L.bytes width log_n) x

/-- Transform a matrix whose leading 2^m rows hold the message and the rest zeros.

Each further coset starts as a copy of the message, transformed over its own shift.

The message itself is transformed last. -/
def transform_cosets (L : Level F) (width n log_message : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let m := 2 ^ log_message
  if L.bytes * (width * m) ≤ DEEP_TILE_BYTES then
    let x ← (List.range ((n - m + m - 1) / m)).foldlM (fun x c => do
        let shift ← domain_point L ((c + 1) * m)
        let y ← transform L false width m shift (slice x 0)
        pure (writeBack x ((c + 1) * m) m y)) x
    let y ← transform L false width m 0 (slice x 0)
    pure (writeBack x 0 m y)
  else none

/-- The forward transform over a coset. -/
def LchNtt.shifted_ntt_batch (L : Level F) (width n : ℕ) (x : ℕ → V) (shift : F) :
    Option (ℕ → V) := transform L false width n shift x

/-- The inverse transform over a coset. -/
def LchNtt.shifted_intt_batch (L : Level F) (width n : ℕ) (x : ℕ → V) (shift : F) :
    Option (ℕ → V) := transform L true width n shift x

/-- The padded transform.

The height must be a power of two, at least the padding, and within the level. -/
def LchNtt.ntt_batch_padded (L : Level F) (width n : ℕ) (x : ℕ → V) (log_inv_rate : ℕ) :
    Option (ℕ → V) := do
  let log_n ← log2Strict n
  if log_n < log_inv_rate then none else
  if 2 ^ L.logBits < log_n then none else
  transform_cosets L width n (log_n - log_inv_rate) x

end p3_binary_dft.lch.mirror
