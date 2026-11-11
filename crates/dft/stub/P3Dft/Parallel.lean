/-
Transcriptions of the parallel radix-2 DIT backend.

What a transcription abstracts, beyond those of the other transforms:

- the rows of chunk c are the rows c S to c S + S - 1 of the whole matrix
- so a chunk's block b is global block c n + b
- an out-of-place layer writes every destination row
- so it is the in-place layer applied to a copy of the source
- inverting the height in the prime subfield is h^(-1) in K, and none when h is zero in K
- the consumer of finished blocks has no effect on the result
- the result is a bit-reversed view, read through the view: row r is stored row rev(r).
-/
module

public import P3Dft.Transforms

@[expose] public section

namespace p3_dft.radix_2_dit_parallel.mirror

open p3_dft.mirror p3_dft.butterflies.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- Twiddles in natural order, and the same twiddles in bit-reversed order. -/
structure VectorPair (K : Type _) where
  twiddles : List K
  bitrev_twiddles : List K

/-- The forward twiddles: the first half of the powers of the generator, in both orders. -/
def get_or_compute_twiddles (G : Gen K) (log_h : ℕ) : Option (VectorPair K) :=
  (G.get log_h).map fun root =>
    let half_h := 2 ^ log_h / 2
    let twiddles := powersList root half_h
    { twiddles, bitrev_twiddles := revIndex half_h twiddles }

/-- The inverse twiddles: the first half of the powers of the inverse generator, in both orders. -/
def get_or_compute_inverse_twiddles (G : Gen K) (log_h : ℕ) : Option (VectorPair K) :=
  (G.get log_h).map fun root =>
    let half_h := 2 ^ log_h / 2
    let twiddles := powersList root⁻¹ half_h
    { twiddles, bitrev_twiddles := revIndex half_h twiddles }

/-- The coset twiddles.

Table l holds shift^(2^l) (root^(2^l))^i for i < h / 2^(l+1).

Tables with log_h - 1 - l >= ceil(log_h / 2) are bit-reversed. -/
def get_or_compute_coset_twiddles (G : Gen K) (log_h : ℕ) (shift : K) : Option (List (List K)) :=
  (G.get log_h).map fun root =>
    let mid := (log_h + 1) / 2
    let h := 2 ^ log_h
    (List.range log_h).map fun layer =>
      let shift_power := shift ^ 2 ^ layer
      let twiddles := shiftedPowersList (root ^ 2 ^ layer) shift_power (h / 2 ^ (layer + 1))
      let layer_rev := log_h - 1 - layer
      if mid ≤ layer_rev then revIndex (h / 2 ^ (layer + 1)) twiddles else twiddles

/-- The (block, pair) indices of the nb blocks of chunk c.

They are in reverse block order when going backwards. -/
def chunkOrder (c nb m : ℕ) (backwards : Bool) : List (ℕ × ℕ) :=
  let bs := (List.range nb).map (c * nb + ·)
  (if backwards then bs.reverse else bs).flatMap fun b => (List.range m).map fun s => (b, s)

/-- Layer 0 on chunk c of S rows: pairs of rows, with the butterfly without a twiddle. -/
def dit_layer_twiddle_free (c S : ℕ) (backwards : Bool) (x : ℕ → V) : ℕ → V :=
  pairLoop (chunkOrder c (S / 2) 1 backwards) 1 (fun _ _ => TwiddleFreeButterfly.apply) x

/-- A layer on chunk c of S rows whose first pair in each block has twiddle one.

Pair ind of a block uses entry ind of the twiddle iterator. -/
def dit_layer_first_one (c S layer : ℕ) (twiddles : ℕ → K) (backwards : Bool) (x : ℕ → V) :
    ℕ → V :=
  let half_block_size := 2 ^ layer
  pairLoop (chunkOrder c (S / (2 * half_block_size)) half_block_size backwards) half_block_size
    (fun _ ind => if ind = 0 then TwiddleFreeButterfly.apply else DitButterfly.apply (twiddles ind)) x

/-- A layer on chunk c of S rows.

Pair ind of a block uses entry ind of the twiddle iterator. -/
def dit_layer (c S layer : ℕ) (twiddles : ℕ → K) (backwards : Bool) (x : ℕ → V) : ℕ → V :=
  let half_block_size := 2 ^ layer
  pairLoop (chunkOrder c (S / (2 * half_block_size)) half_block_size backwards) half_block_size
    (fun _ ind => DitButterfly.apply (twiddles ind)) x

/-- A layer on chunk c of S rows, in bit-reversed order.

Half blocks have 2^(log_h - 1 - layer) rows.

Block b of the chunk uses the twiddle of index first block + b, through the given butterfly. -/
def dit_layer_rev (c S log_h layer first_block : ℕ) (twiddles_rev : ℕ → K)
    (fly : K → V → V → V × V) (backwards : Bool) (x : ℕ → V) : ℕ → V :=
  let layer_rev := log_h - 1 - layer
  let half_block_size := 2 ^ layer_rev
  let nb := S / (2 * half_block_size)
  pairLoop (chunkOrder c nb half_block_size backwards) half_block_size
    (fun b _ => fly (twiddles_rev (first_block + (b - c * nb)))) x

/-- The first half: layers 0 to mid - 1 in each chunk of 2^mid rows, alternating direction.

Layer 0 has no twiddles, and later layers read every 2^(log_h - 1 - layer)-th twiddle. -/
def first_half (h mid : ℕ) (twiddles : List K) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let S := 2 ^ mid
  pure ((List.range (h / S)).foldl (fun acc c =>
    ((List.range mid).foldl (fun (st : (ℕ → V) × Bool) layer =>
      let acc := st.1
      let backwards := st.2
      let acc := if layer = 0 then dit_layer_twiddle_free c S backwards acc
        else
          let layer_rev := log_h - 1 - layer
          let layer_pow := 2 ^ layer_rev
          dit_layer_first_one c S layer (fun i => twiddles.getD (i * layer_pow) 0) backwards acc
      (acc, !backwards)) (acc, false)).1) x)

/-- The second half, in bit-reversed order.

It runs layers mid to log_h - 1 in each chunk of 2^(log_h - mid) rows.

With a scale, the first layer uses the scaled butterfly.

A chunk with no layers is then scaled directly. -/
def second_half (h mid : ℕ) (twiddles_rev : List K) (scale : Option K) (x : ℕ → V) :
    Option (ℕ → V) := do
  let log_h ← log2Strict h
  let S := 2 ^ (log_h - mid)
  pure ((List.range (h / S)).foldl (fun acc thread =>
    let run := fun (first_fly : K → V → V → V × V) (acc : ℕ → V) =>
      ((List.range (log_h - mid)).foldl (fun (st : (ℕ → V) × Bool) i =>
        let layer := mid + i
        let first_block := thread * 2 ^ (layer - mid)
        let fly := if i = 0 then first_fly else DitButterfly.apply
        (dit_layer_rev thread S log_h layer first_block (fun j => twiddles_rev.getD j 0) fly st.2 st.1,
          !st.2)) (acc, false)).1
    match scale with
    | some s =>
      if mid < log_h then run (fun t => (ScaledDitButterfly.new t s).apply) acc
      else fun i => if i / S = thread then s • acc i else acc i
    | none => run DitButterfly.apply acc) x)

/-- The first half with one twiddle table per layer, for coset shifts.

Layer l reads table log_h - 1 - l. -/
def first_half_general (h mid : ℕ) (twiddles : List (List K)) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let S := 2 ^ mid
  pure ((List.range (h / S)).foldl (fun acc c =>
    ((List.range mid).foldl (fun (st : (ℕ → V) × Bool) layer =>
      let layer_rev := log_h - 1 - layer
      (dit_layer c S layer (fun i => (twiddles.getD layer_rev []).getD i 0) st.2 st.1, !st.2))
      (acc, false)).1) x)

/-- The second half with one twiddle table per layer.

Layer l reads table log_h - 1 - l, starting at the chunk's first block index. -/
def second_half_general (h mid : ℕ) (twiddles_rev : List (List K)) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let S := 2 ^ (log_h - mid)
  pure ((List.range (h / S)).foldl (fun acc thread =>
    ((List.range (log_h - mid)).foldl (fun (st : (ℕ → V) × Bool) i =>
      let layer := mid + i
      let layer_rev := log_h - 1 - layer
      let first_block := thread * 2 ^ (layer - mid)
      (dit_layer_rev thread S log_h layer first_block
        (fun j => (twiddles_rev.getD layer_rev []).getD j 0) DitButterfly.apply st.2 st.1, !st.2))
      (acc, false)).1) x)

/-- The coset transform of bit-reversed rows, in place.

It runs the general first half, a bit reversal, then the general second half. -/
def coset_dft (G : Gen K) (h : ℕ) (shift : K) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let mid := (log_h + 1) / 2
  let twiddles ← get_or_compute_coset_twiddles G log_h shift
  let y ← first_half_general h mid twiddles x
  second_half_general h mid twiddles (revRows log_h y)

/-- The out-of-place first half: layer 0 from the source, then layers 1 to mid - 1 in place. -/
def first_half_general_oop (h mid : ℕ) (twiddles : List (List K)) (src : ℕ → V) :
    Option (ℕ → V) := do
  let log_h ← log2Strict h
  let S := 2 ^ mid
  pure ((List.range (h / S)).foldl (fun acc c =>
    let layer_rev := log_h - 1
    let acc := dit_layer c S 0 (fun i => (twiddles.getD layer_rev []).getD i 0) false acc
    ((List.range' 1 (mid - 1)).foldl (fun (st : (ℕ → V) × Bool) layer =>
      let layer_rev := log_h - 1 - layer
      (dit_layer c S layer (fun i => (twiddles.getD layer_rev []).getD i 0) st.2 st.1, !st.2))
      (acc, true)).1) src)

/-- The out-of-place coset transform with precomputed tables.

It asserts log_h tables, table l holding h / 2^(l+1) entries.

One row is copied.

Otherwise the out-of-place first half, a bit reversal and the second half run. -/
def coset_dft_oop (h : ℕ) (src : ℕ → V) (twiddles : List (List K)) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  if twiddles.length = log_h ∧ ∀ l < log_h, (twiddles.getD l []).length = h / 2 ^ (l + 1) then
    let mid := (log_h + 1) / 2
    if log_h = 0 then pure src
    else
      let dst ← first_half_general_oop h mid twiddles src
      second_half_general h mid twiddles (revRows log_h dst)
  else none

/-- The forward transform: bit reversal, first half, bit reversal, second half.

The result is read through a bit-reversed view. -/
def Radix2DitParallel.dft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let twiddles ← get_or_compute_twiddles G log_h
  let mid := (log_h + 1) / 2
  let y ← first_half h mid twiddles.twiddles (revRows log_h x)
  let y ← second_half h mid twiddles.bitrev_twiddles none (revRows log_h y)
  pure (fun r => y (bitRev log_h r))

/-- The coset transform: bit reversal, then the in-place coset transform.

The result is read through a bit-reversed view. -/
def Radix2DitParallel.coset_dft_batch (G : Gen K) (h : ℕ) (shift : K) (x : ℕ → V) :
    Option (ℕ → V) := do
  let log_h ← log2Strict h
  let y ← coset_dft G h shift (revRows log_h x)
  pure (fun r => y (bitRev log_h r))

/-- The inverse transform.

One row is returned as is.

Otherwise it runs the two halves with the inverse twiddles, the second scaled by 2^(-log_h).

A final bit reversal follows. -/
def Radix2DitParallel.idft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) :=
  if h = 1 then some x
  else do
    let log_h ← log2Strict h
    let mid := (log_h + 1) / 2
    let inverse_twiddles ← get_or_compute_inverse_twiddles G log_h
    let y ← first_half h mid inverse_twiddles.twiddles (revRows log_h x)
    let scale := ((2 : K) ^ log_h)⁻¹
    let y ← second_half h mid inverse_twiddles.bitrev_twiddles (some scale) (revRows log_h y)
    pure (revRows log_h y)

/-- The inverse coset transform: the inverse, then row i times shift^(-i). -/
def Radix2DitParallel.coset_idft_batch (G : Gen K) (w h : ℕ) (shift : K) (x : ℕ → V) :
    Option (ℕ → V) := do
  let c ← Radix2DitParallel.idft_batch G h x
  let s ← inverse shift
  p3_dft.util.mirror.coset_shift_cols w h c s

/-- The extension, in order:

- the inverse without its final bit reversal
- the transform of the coefficients
- one coset transform per coset of the large subgroup in the large group.

The result is read through a bit-reversed view.

Slot k + 1 holds coset rev_a(k + 1), out of place.

Slot 0 holds coset 0, in place. -/
def Radix2DitParallel.lde_with_consumer (G : Gen K) (w h a : ℕ) (shift : K)
    (transform : (ℕ → V) → ℕ → V) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let mid := (log_h + 1) / 2
  let inverse_twiddles ← get_or_compute_inverse_twiddles G log_h
  let y ← first_half h mid inverse_twiddles.twiddles (revRows log_h x)
  let scale := if (h : K) = 0 then none else some (h : K)⁻¹
  let y ← second_half h mid inverse_twiddles.bitrev_twiddles scale (revRows log_h y)
  let y := transform y
  if a < 64 ∧ w * (h * 2 ^ a) < 2 ^ 64 then
    let g_big ← G.get (log_h + a)
    let coset_twiddles ← (List.range (2 ^ a)).mapM fun coset_idx =>
      get_or_compute_coset_twiddles G log_h (g_big ^ coset_idx * shift)
    let rest ← (List.range (2 ^ a - 1)).mapM fun k =>
      coset_dft_oop h y (coset_twiddles.getD (bitRev a (k + 1)) [])
    let first ← coset_dft G h shift y
    let buffer : ℕ → V := fun r =>
      if r < h then first r else (rest.getD (r / h - 1) (fun _ => 0)) (r % h)
    pure (fun r => buffer (bitRev (log_h + a) r))
  else none

end p3_dft.radix_2_dit_parallel.mirror
