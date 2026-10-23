/-
Transcriptions of the butterfly kernels of p3-binary-dft.

Two runs of rows are positions lo, lo + 1, ... and hi, hi + 1, ... of a matrix.

A packed value is a row, so the packed prefix and the scalar tail run one loop.

The subfield kernels multiply by a twiddle typed as an element of a subfield S, through an embedding of S.
-/
module

public import P3BinaryDft.Model

@[expose] public section

namespace p3_binary_dft.butterfly.mirror

open p3_binary_dft.mirror p3_dft.mirror

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-- The work on one pair of the butterfly over values, with the zero twiddle taken apart. -/
def pairOp (inverse : Bool) (t : F) (zero : Bool) (u v : V) : V × V :=
  if zero then (u, v + u)
  else if inverse then
    let v := v + u
    (u + t • v, v)
  else
    let u := u + t • v
    (u, v + u)

/-- The butterfly over values: m pairs, the run at lo against the run at hi, in order. -/
def butterfly_values (inverse : Bool) (lo hi m : ℕ) (t : F) (zero : Bool) (x : ℕ → V) : ℕ → V :=
  (List.range m).foldl (fun acc s => bfly (pairOp inverse t zero) (lo + s) (hi + s) acc) x

/-- The butterfly over the packed prefix, then the scalar tail: one run of values here. -/
def packed_butterfly [DecidableEq F] (inverse : Bool) (lo hi m : ℕ) (t : F) (x : ℕ → V) :
    ℕ → V :=
  butterfly_values inverse lo hi m t (t = 0) x

/-- The plain butterfly, which asserts the two runs have the same length. -/
def plain_butterfly [DecidableEq F] (inverse : Bool) (lo hi mLo mHi : ℕ) (t : F) (x : ℕ → V) :
    Option (ℕ → V) :=
  if mLo = mHi then some (packed_butterfly inverse lo hi mLo t x) else none

/-- The butterfly with a twiddle typed as an element of a subfield, scaled through its embedding. -/
def typed_butterfly {S : Type _} (ι : S → F) (inverse : Bool) (lo hi m : ℕ) (t : S)
    (x : ℕ → V) : ℕ → V :=
  (List.range m).foldl (fun acc s => bfly (fun u v =>
      if inverse then
        let v := v + u
        (u + ι t • v, v)
      else
        let u := u + ι t • v
        (u, v + u)) (lo + s) (hi + s) acc) x

end p3_binary_dft.butterfly.mirror
