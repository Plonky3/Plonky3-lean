/-
Transcriptions of the naive transform, the trait's default methods, the radix-2 DIT backend and the Bowers backend.

What a transcription abstracts, beyond the model of a matrix as its rows:

* the field is a mathlib field K, and a matrix of width w has rows in V = K^w;
* the powers and shifted-powers iterators yield g^i and s g^i;
* dividing one by 2^e in the prime subfield, then embedding it, is (2^e)^(-1);
* inverting zero panics;
* a memoized twiddle table is the table its computation returns, since one key always gets the same computation;
* the parallel iterators of maybe-rayon run serially, in order, as they do without the parallel feature;
* the width w appears only where the Rust's own arithmetic uses it.

Loops, branches and the order of operations are kept.
-/
module

public import P3Dft.Butterflies
public import P3Matrix

@[expose] public section

namespace p3_dft.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- In-place bit reversal of the first 2^k rows, through p3-matrix's transcription. -/
def revRows (k : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if hi : i < 2 ^ k then
    p3_matrix.util.mirror.reverse_matrix_index_bits
      (fun r : Fin (2 ^ k) => ⟨bitRev k r.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩)
      (fun r : Fin (2 ^ k) => x r.val) ⟨i, hi⟩
  else x i

/-- The inverse of a field element, which panics at zero. -/
def inverse (s : K) : Option K := if s = 0 then none else some s⁻¹

end p3_dft.mirror

namespace p3_dft.util.mirror

open p3_dft.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- Divide every row by the height, which must be a power of two. -/
def divide_by_height (h : ℕ) (x : ℕ → V) : Option (ℕ → V) :=
  (log2Strict h).map fun log_h => scaleRows ((2 : K) ^ log_h)⁻¹ x

/-- Multiply row i by shift^i.

A shift of one returns early.

Otherwise the rows are cut into chunks of max(2^15 / w, 1) rows, which divides by the width w.

Each chunk starts from shift^(first row of the chunk) and multiplies the weight by the shift after each row. -/
def coset_shift_cols (w h : ℕ) (x : ℕ → V) (shift : K) : Option (ℕ → V) :=
  if shift = 1 then some x
  else if w = 0 then none
  else
    let chunk_rows := max (2 ^ 15 / w) 1
    let n_chunks := (h + chunk_rows - 1) / chunk_rows
    some ((List.range n_chunks).foldl (fun acc chunk_idx =>
      (List.range (min chunk_rows (h - chunk_idx * chunk_rows))).foldl (fun acc j =>
        let r := chunk_idx * chunk_rows + j
        fun i => if i = r then (shift ^ (chunk_idx * chunk_rows) * shift ^ j) • acc i else acc i)
        acc) x)

end p3_dft.util.mirror

namespace p3_dft.naive.mirror

open p3_dft.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The quadratic transform.

Output row r accumulates point^s times input row s, for point = g^r and every s < h. -/
def NaiveDft.dft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) :=
  (log2Strict h).bind fun log_h => (G.get log_h).map fun g =>
    (List.range h).foldl (fun res res_r =>
      let point := g ^ res_r
      (List.range h).foldl (fun res src_r =>
        fun i => if i = res_r then res i + (point ^ src_r) • x src_r else res i) res)
      (fun _ => 0)

end p3_dft.naive.mirror

namespace p3_dft.traits.mirror

open p3_dft.mirror p3_dft.util.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The default coset transform: multiply row i by shift^i, then run the backend's transform. -/
def coset_dft_batch (dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)) (w h : ℕ) (x : ℕ → V)
    (shift : K) : Option (ℕ → V) :=
  (coset_shift_cols w h x shift).bind (dft_batch h)

/-- The default inverse: transform, divide by the height, then swap row r with row h - r for 0 < r < h / 2. -/
def idft_batch (dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)) (h : ℕ) (x : ℕ → V) :
    Option (ℕ → V) := do
  let d ← dft_batch h x
  let d ← divide_by_height (K := K) h d
  pure ((List.range' 1 (h / 2 - 1)).foldl (fun acc row => swapRows row (h - row) acc) d)

/-- The default inverse coset transform: invert, then multiply row i by shift^(-i). -/
def coset_idft_batch (idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)) (w h : ℕ) (x : ℕ → V)
    (shift : K) : Option (ℕ → V) := do
  let c ← idft_batch h x
  let s ← inverse shift
  coset_shift_cols w h c s

/-- The default low-degree extension with a transform of the coefficients.

It inverts, applies the transform, pads with zero rows to h 2^a, and runs the coset transform.

The padding asserts that 2^a and the new length h w 2^a fit in a word. -/
def coset_lde_batch_with_transform (idft_batch : ℕ → (ℕ → V) → Option (ℕ → V))
    (coset_dft_batch : ℕ → (ℕ → V) → K → Option (ℕ → V)) (w h a : ℕ) (shift : K)
    (transform : (ℕ → V) → ℕ → V) (x : ℕ → V) : Option (ℕ → V) := do
  let coeffs ← idft_batch h x
  let coeffs := transform coeffs
  if a < 64 ∧ h * w * 2 ^ a < 2 ^ 64 then
    coset_dft_batch (h * 2 ^ a) (fun i => if i < h then coeffs i else 0) shift
  else none

/-- A method on an algebra over the field: flatten each element to its coordinates, run the
base-field method, and rebuild the elements. -/
def via_base {W U : Type _} (flatten : W → U) (reconstitute : U → W)
    (base : (ℕ → U) → Option (ℕ → U)) (x : ℕ → W) : Option (ℕ → W) :=
  (base (flatten ∘ x)).map (reconstitute ∘ ·)

end p3_dft.traits.mirror

namespace p3_dft.radix_2_dit.mirror

open p3_dft.mirror p3_dft.butterflies.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The twiddles of a transform of size 2^log_h: the first half of the powers of the generator. -/
def Radix2Dit.get_or_compute_twiddles (G : Gen K) (log_h : ℕ) : Option (List K) :=
  (G.get log_h).map fun root => powersList root (2 ^ log_h / 2)

/-- One layer: blocks of 2^(layer+1) rows, and pair ind of each block uses twiddle ind 2^(log_h - 1 - layer).

Pair 0 uses the butterfly without a twiddle. -/
def dit_layer (h layer : ℕ) (twiddles : List K) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  if layer + 1 ≤ log_h then
    let layer_rev := log_h - 1 - layer
    let half_block_size := 2 ^ layer
    pure (pairLoop (blocks (h / (2 * half_block_size)) half_block_size) half_block_size
      (fun _ ind => if ind = 0 then TwiddleFreeButterfly.apply
        else DitButterfly.apply (twiddles.getD (ind * 2 ^ layer_rev) 0)) x)
  else none

/-- The radix-2 decimation-in-time transform: bit-reverse the rows, then run layers 0 to log_h - 1. -/
def Radix2Dit.dft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let twiddles ← Radix2Dit.get_or_compute_twiddles G log_h
  (List.range log_h).foldlM (fun acc layer => dit_layer h layer twiddles acc) (revRows log_h x)

/-- The low-degree extension: invert, transform the coefficients, shift them, pad with zeros and transform. -/
def Radix2Dit.coset_lde_batch_with_transform (G : Gen K) (w h a : ℕ) (shift : K)
    (transform : (ℕ → V) → ℕ → V) (x : ℕ → V) : Option (ℕ → V) := do
  let coeffs ← p3_dft.traits.mirror.idft_batch (K := K) (Radix2Dit.dft_batch G) h x
  let coeffs := transform coeffs
  let coeffs ← p3_dft.util.mirror.coset_shift_cols w h coeffs shift
  if a < 64 ∧ w * (h * 2 ^ a) < 2 ^ 64 then
    Radix2Dit.dft_batch G (h * 2 ^ a) (fun i => if i < h then coeffs i else 0)
  else none

end p3_dft.radix_2_dit.mirror

namespace p3_dft.radix_2_bowers.mirror

open p3_dft.mirror p3_dft.butterflies.mirror

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- One layer of the Bowers networks: blocks of 2 half rows, and block b uses the butterfly of entry b.

Block 0 uses the butterfly without a twiddle. -/
def butterfly_layer (h half_block_size : ℕ) (fly : ℕ → V → V → V × V) (x : ℕ → V) : ℕ → V :=
  pairLoop (blocks (h / (2 * half_block_size)) half_block_size) half_block_size
    (fun block _ => if block = 0 then TwiddleFreeButterfly.apply else fly block) x

/-- The Bowers G network: decimation-in-frequency layers with half blocks 1, 2, 4, and so on.

Its twiddles are the first half of the powers of the generator, in bit-reversed order. -/
def bowers_g (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let root ← G.get log_h
  let twiddles := revIndex (h / 2) (powersList root (h / 2))
  pure ((List.range log_h).foldl (fun acc l =>
    butterfly_layer h (2 ^ l) (fun b => DifButterfly.apply (twiddles.getD b 0)) acc) x)

/-- The Bowers G^T network: decimation-in-time layers with half blocks 2^(log_h - 1) down to 1.

Its twiddles are the first half of the powers of the inverse generator, in bit-reversed order. -/
def bowers_g_t (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let root ← G.get log_h
  let twiddles := revIndex (h / 2) (powersList root⁻¹ (h / 2))
  pure (((List.range log_h).reverse).foldl (fun acc l =>
    butterfly_layer h (2 ^ l) (fun b => DitButterfly.apply (twiddles.getD b 0)) acc) x)

/-- The forward transform: bit-reverse the rows, then run G. -/
def Radix2Bowers.dft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  bowers_g G h (revRows log_h x)

/-- The inverse: run G^T, divide by the height, then bit-reverse the rows. -/
def Radix2Bowers.idft_batch (G : Gen K) (h : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let y ← bowers_g_t G h x
  let y ← p3_dft.util.mirror.divide_by_height (K := K) h y
  let log_h ← log2Strict h
  pure (revRows log_h y)

/-- Bit-reversed zero padding: row i goes to row i 2^a, and every other row is zero. -/
def bit_reversed_zero_pad (h a : ℕ) (x : ℕ → V) : ℕ → V :=
  if a = 0 then x
  else fun i => if i % 2 ^ a = 0 ∧ i / 2 ^ a < h then x (i / 2 ^ a) else 0

/-- The extension: G^T, divide by the height, bit-reversed zero padding, then G. -/
def Radix2Bowers.lde_batch (G : Gen K) (h a : ℕ) (x : ℕ → V) : Option (ℕ → V) := do
  let y ← bowers_g_t G h x
  let y ← p3_dft.util.mirror.divide_by_height (K := K) h y
  bowers_g G (h * 2 ^ a) (bit_reversed_zero_pad h a y)

/-- The coset extension: G^T, then row i times the bit-reversed weight 2^(-log_h) shift^i, padding, then G. -/
def Radix2Bowers.coset_lde_batch (G : Gen K) (h a : ℕ) (shift : K) (x : ℕ → V) :
    Option (ℕ → V) := do
  let log_h ← log2Strict h
  let h_inv := ((2 : K) ^ log_h)⁻¹
  let y ← bowers_g_t G h x
  let weights := revIndex h (shiftedPowersList shift h_inv h)
  let y := fun i => weights.getD i 0 • y i
  bowers_g G (h * 2 ^ a) (bit_reversed_zero_pad h a y)

/-- The coset extension with a transform: the scaling by 2^(-log_h) happens before the transform,
which sees the coefficients in bit-reversed order, and the shift powers after it. -/
def Radix2Bowers.coset_lde_batch_with_transform (G : Gen K) (h a : ℕ) (shift : K)
    (transform : (ℕ → V) → ℕ → V) (x : ℕ → V) : Option (ℕ → V) := do
  let log_h ← log2Strict h
  let h_inv := ((2 : K) ^ log_h)⁻¹
  let y ← bowers_g_t G h x
  let y := transform (scaleRows h_inv y)
  let shift_powers := revIndex h (powersList shift h)
  let y := fun i => shift_powers.getD i 0 • y i
  bowers_g G (h * 2 ^ a) (bit_reversed_zero_pad h a y)

end p3_dft.radix_2_bowers.mirror
