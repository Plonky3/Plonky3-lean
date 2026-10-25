/-
Transcriptions of the Reed-Solomon encoder of p3-binary-dft.
-/
module

public import P3BinaryDft.Traits

@[expose] public section

namespace p3_binary_dft.encoder.mirror

open p3_binary_dft.mirror p3_binary_dft.traits.mirror p3_commit.encoder.mirror

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-- Encode: zero-pad the coefficients to the codeword length, then the padded transform. -/
def encode_batch (B : Backend F V) (width n : ℕ) (x : ℕ → V) (log_inv_rate : ℕ) :
    Option (ℕ → V) := do
  let len ← padded_len (n * width) log_inv_rate
  B.ntt_batch_padded width (heightOf len width) (zeroBelow n x) log_inv_rate

/-- Encode an already padded matrix: the padded transform. -/
def encode_batch_padded (B : Backend F V) (width n : ℕ) (x : ℕ → V) (log_inv_rate : ℕ) :
    Option (ℕ → V) := B.ntt_batch_padded width n x log_inv_rate

end p3_binary_dft.encoder.mirror
