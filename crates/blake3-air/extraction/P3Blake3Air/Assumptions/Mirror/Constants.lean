/-
Transcriptions of the constants of p3-blake3-air: the limb size, the IV and the message permutation.

They are also extracted, as arrays of machine words.

Here they are lists of natural numbers, for the transcribed AIRs to read.
-/
module

public import Mathlib.Data.List.GetD

@[expose] public section

namespace p3_blake3_air.mirror

/-- The bits of a limb. -/
def BITS_PER_LIMB : ℕ := 16

/-- The limbs of a 32-bit word. -/
def U32_LIMBS : ℕ := 32 / BITS_PER_LIMB

/-- The eight IV words, each as its low and high 16-bit halves. -/
def IV : List (List ℕ) :=
  [[0xE667, 0x6A09],
   [0xAE85, 0xBB67],
   [0xF372, 0x3C6E],
   [0xF53A, 0xA54F],
   [0x527F, 0x510E],
   [0x688C, 0x9B05],
   [0xD9AB, 0x1F83],
   [0xCD19, 0x5BE0]]

/-- Half `l` of IV word `i`. -/
def ivHalf (i l : ℕ) : ℕ := (IV.getD i []).getD l 0

/-- The index map of the message permutation. -/
def MSG_PERMUTATION : List ℕ := [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-- Apply the message permutation to an array of 16 entries: entry i becomes entry `MSG_PERMUTATION[i]`. -/
def permute {T : Type _} (m : ℕ → T) : ℕ → T := fun i => m (MSG_PERMUTATION.getD i 0)

end p3_blake3_air.mirror
