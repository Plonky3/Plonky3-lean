/-
Transcriptions of the circle FFT's row order.

What a transcription abstracts:

* reverse_bits_len(x, k) is the k-bit reversal of x, which it is for k > 0 or x = 0, and the order calls it on x < 2^k only;
* the callers pass an index below 2^log_n, where the subtraction stays in range;
* a matrix of height h is its rows, a function from row indices, as in p3-dft's model;
* an index past the end and a length that is not a power of two panic, and a panic is none.

Loops and the order of operations are kept.
-/
module

public import P3Dft.Model

@[expose] public section

namespace p3_circle.ordering.mirror

open p3_dft.mirror

/-- The circle FFT order: an even index 2 i reads row i, an odd index 2 i + 1 reads row 2^log_n - 1 - i, then the log_n-bit reversal. -/
def cfft_permute_index (index log_n : ℕ) : ℕ :=
  let (i, lsb) := (index / 2, index % 2)
  bitRev log_n (if lsb = 0 then i else 2 ^ log_n - i - 1)

/-- The slice in circle FFT order: entry i is entry cfft_permute_index(i). -/
def cfft_permute_slice {α : Type _} (xs : List α) : Option (List α) := do
  let log_n ← log2Strict xs.length
  (List.range xs.length).mapM fun i => xs[cfft_permute_index i log_n]?

/-- The in-place permutation of chunks: chunk i swaps with chunk j = cfft_permute_index(i) when i < j.

It asserts that the length is a multiple of the chunk size. -/
def cfft_permute_slice_chunked_in_place {V : Type _} (n_chunks : ℕ) (rows : ℕ → V) : Option (ℕ → V) := do
  let log_n ← log2Strict n_chunks
  some ((List.range n_chunks).foldl (fun acc i =>
    let j := cfft_permute_index i log_n
    if i < j then swapRows i j acc else acc) rows)

end p3_circle.ordering.mirror
