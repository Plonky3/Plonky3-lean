/-
Transcriptions of the default methods of the additive NTT interface of p3-binary-dft.

A backend is its three overridable methods, each on a matrix of n rows of width elements.

Rows past the height read as zero, which is how a zero-padded copy looks.
-/
module

public import P3BinaryDft.Model

@[expose] public section

namespace p3_binary_dft.traits.mirror

open p3_binary_dft.mirror p3_dft.mirror p3_commit.encoder.mirror

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-- The methods a transform provides.

They are forward and inverse over a coset, and the padded forward transform. -/
structure Backend (F V : Type _) where
  shifted_ntt_batch : ℕ → ℕ → (ℕ → V) → F → Option (ℕ → V)
  shifted_intt_batch : ℕ → ℕ → (ℕ → V) → F → Option (ℕ → V)
  ntt_batch_padded : ℕ → ℕ → (ℕ → V) → ℕ → Option (ℕ → V)

/-- The default padded transform.

The padding must not exceed the height, then the whole matrix is transformed. -/
def ntt_batch_padded (B : Backend F V) (width n : ℕ) (x : ℕ → V) (log_inv_rate : ℕ) :
    Option (ℕ → V) := do
  let log_n ← log2Strict n
  if log_n < log_inv_rate then none else B.shifted_ntt_batch width n x 0

/-- The length of a buffer zero-padded by a number of domain dimensions.

It panics on overflow. -/
def padded_len (len added_bits : ℕ) : Option ℕ := paddedLen len added_bits

/-- The rows of a matrix of n rows, with zeros below. -/
def zeroBelow (n : ℕ) (x : ℕ → V) : ℕ → V := fun r => if r < n then x r else 0

/-- The default borrowed transform.

It copies into a zeroed matrix 2^r times as tall, for r the log inverse rate.

Then it runs the padded transform. -/
def ntt_batch_borrowed (B : Backend F V) (width n : ℕ) (x : ℕ → V) (log_inv_rate : ℕ) :
    Option (ℕ → V) := do
  let len ← padded_len (n * width) log_inv_rate
  B.ntt_batch_padded width (heightOf len width) (zeroBelow n x) log_inv_rate

/-- The default extension over a coset: back to coefficients, zero-pad, and forward on the larger coset.

The height must be a power of two within the level.

With no added bits the matrix is returned as it is. -/
def shifted_lde_batch (L : Level F) (B : Backend F V) (width n : ℕ) (x : ℕ → V)
    (added_bits : ℕ) (shift : F) : Option (ℕ → V) := do
  let log_n ← log2Strict n
  if 2 ^ L.logBits < log_n then none else
  if added_bits = 0 then pure x else
  let coeffs ← B.shifted_intt_batch width n x shift
  let len ← padded_len (n * width) added_bits
  B.shifted_ntt_batch width (heightOf len width) (zeroBelow n coeffs) shift

end p3_binary_dft.traits.mirror
