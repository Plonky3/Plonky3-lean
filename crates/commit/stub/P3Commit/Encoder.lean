/-
Transcriptions of the column-wise linear codes.

What a transcription abstracts:

* a matrix is its height, width and entries, and its flat length is height times width;
* a length is a word below 2^64, and the shift amount goes through a 32-bit conversion first;
* the transform backend is a parameter of p3-dft's shape, which panics on a height that is not a power of two;
* a panic is none.

Branches and the order of checks are kept.
-/
module

public import P3Commit.Types
public import P3Dft.Model

@[expose] public section

namespace p3_commit.encoder.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror

variable {K : Type _} [Field K]

/-- The padded length len 2^r: the shift must fit the 32-bit conversion and the word, and shifting back must recover len. -/
def paddedLen (len log_inv_rate : ℕ) : Option ℕ :=
  if 2 ^ 32 ≤ log_inv_rate then none
  else if 64 ≤ log_inv_rate then none
  else
    let padded := len * 2 ^ log_inv_rate % 2 ^ 64
    if padded / 2 ^ log_inv_rate = len then some padded else none

/-- The height of a flat buffer of the given length read at a width: zero for width zero. -/
def heightOf (len width : ℕ) : ℕ := if width = 0 then 0 else len / width

/-- The message zero-padded to 2^r times its length. -/
def zero_padded (message : Mat K) (log_inv_rate : ℕ) : Option (Mat K) := do
  let padded_len ← paddedLen (message.height * message.width) log_inv_rate
  pure ⟨heightOf padded_len message.width, message.width, fun r c =>
    if r < message.height then message.entry r c else 0⟩

/-- Reed-Solomon over the subgroup: pad with zero rows when the rate is positive, then transform. -/
def encode_batch (dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (message : Mat K) (log_inv_rate : ℕ) : Option (Mat K) := do
  let message ← if log_inv_rate > 0 then
      (paddedLen (message.height * message.width) log_inv_rate).map fun padded_len =>
        (⟨heightOf padded_len message.width, message.width, fun r c =>
          if r < message.height then message.entry r c else 0⟩ : Mat K)
    else some message
  let out ← dft message.width message.height message.entry
  pure ⟨message.height, message.width, out⟩

/-- The default padded encoding: the height must be a power of two at least 2^r, then the rate-zero encoding. -/
def encode_batch_padded (dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (message : Mat K) (log_inv_rate : ℕ) : Option (Mat K) := do
  let log_height ← log2Strict message.height
  if log_inv_rate ≤ log_height then encode_batch dft message 0 else none

/-- The default borrowed encoding: zero-pad, then the padded encoding. -/
def encode_batch_borrowed (dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (message : Mat K) (log_inv_rate : ℕ) : Option (Mat K) := do
  let padded ← zero_padded message log_inv_rate
  encode_batch_padded dft padded log_inv_rate

end p3_commit.encoder.mirror
