/-
The objects the transcriptions of p3-binary-dft are written in.

A tower level is a field F with its bit width 2^b, its element size in bytes, and its Cantor basis table.

Asking the table for an index at or past the bit width panics, as the Rust asserts.

A matrix of height h is its rows, a function from row indices to a vector space V over F.

For a matrix of width w, V is the space of rows Fin w -> F.

A packed value is a row, so the packed and scalar kernels are one kernel on rows.

A panic is none.
-/
module

public import P3Commit.Encoder

@[expose] public section

namespace p3_binary_dft.mirror

/-- What the transcriptions read of a tower level: log_2 of its bit width, its size, and its Cantor basis. -/
structure Level (F : Type _) where
  logBits : ℕ
  bytes : ℕ
  cantor : ℕ → F

/-- The Cantor basis vector of an index, which asserts the index is below the bit width. -/
def Level.cantorBasis {F : Type _} (L : Level F) (i : ℕ) : Option F :=
  if i < 2 ^ L.logBits then some (L.cantor i) else none

/-- The trailing zeros of a word: 64 for zero. -/
def trailingZeros (n : ℕ) : ℕ :=
  if n = 0 then 64 else if n % 2 = 1 then 0 else trailingZeros (n / 2) + 1
decreasing_by omega

end p3_binary_dft.mirror
