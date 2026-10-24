module

public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# BLAKE2s, from RFC 7693

Words are 32-bit vectors and messages are lists of bytes.

Section numbers are those of RFC 7693 (November 2015).

* **Constants** (2.6, 2.7): the initialization vector and the ten message schedule rows.
* **The mixing function** (3.1): G, with the BLAKE2s rotations 16, 12, 8 and 7 of section 2.1.
* **The compression function** (3.2): ten rounds of columns then diagonals.
  The counter and the final-block flag enter the working vector, and the output feeds forward.
* **The hash** (3.3): the parameter block, then the key block and the message blocks.
  The digest is the little-endian bytes of the chaining value.

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Blake2s

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- A byte. -/
abbrev Byte := BitVec 8

/-! ## 2.6 and 2.7: constants -/

/-- The initialization vector, the same eight words as SHA-256's. -/
def IV : List Word :=
  [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- The message schedule: row `i` is the permutation `SIGMA[i]`. -/
def SIGMA : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-! ## 3.1: the mixing function -/

/-- G on the working vector, mixing words `a`, `b`, `c`, `d` with message words `x` and `y`. -/
def G (v : List Word) (a b c d : ℕ) (x y : Word) : List Word :=
  let v := v.set a (v.getD a 0 + v.getD b 0 + x)
  let v := v.set d ((v.getD d 0 ^^^ v.getD a 0).rotateRight 16)
  let v := v.set c (v.getD c 0 + v.getD d 0)
  let v := v.set b ((v.getD b 0 ^^^ v.getD c 0).rotateRight 12)
  let v := v.set a (v.getD a 0 + v.getD b 0 + y)
  let v := v.set d ((v.getD d 0 ^^^ v.getD a 0).rotateRight 8)
  let v := v.set c (v.getD c 0 + v.getD d 0)
  v.set b ((v.getD b 0 ^^^ v.getD c 0).rotateRight 7)

/-! ## 3.2: the compression function -/

/-- Round `i`: the four columns, then the four diagonals, reading the schedule row `SIGMA[i mod 10]`. -/
def round (m v : List Word) (i : ℕ) : List Word :=
  let s := SIGMA.getD (i % 10) []
  let x (j : ℕ) : Word := m.getD (s.getD j 0) 0
  let v := G v 0 4 8 12 (x 0) (x 1)
  let v := G v 1 5 9 13 (x 2) (x 3)
  let v := G v 2 6 10 14 (x 4) (x 5)
  let v := G v 3 7 11 15 (x 6) (x 7)
  let v := G v 0 5 10 15 (x 8) (x 9)
  let v := G v 1 6 11 12 (x 10) (x 11)
  let v := G v 2 7 8 13 (x 12) (x 13)
  G v 3 4 9 14 (x 14) (x 15)

/-- The working vector after the first `r` rounds. -/
def rounds (m v : List Word) (r : ℕ) : List Word := (List.range r).foldl (round m) v

/-- The working vector before the rounds: the chaining value, the IV, the counter and the flag. -/
def init (h : List Word) (t : ℕ) (f : Bool) : List Word :=
  let v := h ++ IV
  let v := v.set 12 (v.getD 12 0 ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v.getD 13 0 ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (~~~v.getD 14 0) else v

/-- F: compress block `m` into chaining value `h`, with byte counter `t` and final-block flag `f`.

BLAKE2s takes `t` modulo `2^64`, as two words. -/
def compress (h m : List Word) (t : ℕ) (f : Bool) : List Word :=
  let v := rounds m (init h t f) 10
  (List.range 8).map fun i => h.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0

/-! ## 3.3: the hash -/

/-- The word whose little-endian bytes are `b₀ b₁ b₂ b₃`. -/
def wordOfBytes (b₀ b₁ b₂ b₃ : Byte) : Word := b₃ ++ b₂ ++ b₁ ++ b₀

/-- The 16 words of a block of up to 64 bytes, zero padded. -/
def blockWords (bytes : List Byte) : List Word :=
  (List.range 16).map fun i =>
    wordOfBytes (bytes.getD (4 * i) 0) (bytes.getD (4 * i + 1) 0) (bytes.getD (4 * i + 2) 0)
      (bytes.getD (4 * i + 3) 0)

/-- The little-endian bytes of a word. -/
def bytesOfWord (w : Word) : List Byte :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- The blocks of 64 bytes, the last one possibly shorter. -/
def chunks (bytes : List Byte) : List (List Byte) :=
  (List.range ((bytes.length + 63) / 64)).map fun i => (bytes.drop (64 * i)).take 64

/-- The `nn`-byte digest of `msg` under a key of at most 32 bytes.

- The key, zero padded to a block, comes first when it is not empty.
- An empty input is one block of zeros.
- The counter of the last block counts the message bytes, plus 64 for a key block. -/
def hash (key msg : List Byte) (nn : ℕ) : List Byte :=
  let kk := key.length
  let ll := msg.length
  let d := (if kk = 0 then [] else [key]) ++ chunks msg
  let d := if d = [] then [[]] else d
  let h := IV.set 0 (IV.getD 0 0 ^^^ 0x01010000 ^^^ (BitVec.ofNat 32 kk <<< 8) ^^^ BitVec.ofNat 32 nn)
  let h := (List.range (d.length - 1)).foldl
    (fun h i => compress h (blockWords (d.getD i [])) ((i + 1) * 64) false) h
  let t := if kk = 0 then ll else ll + 64
  let h := compress h (blockWords (d.getD (d.length - 1) [])) t true
  ((h.map bytesOfWord).flatten).take nn

end Plonky3Lean.Spec.Blake2s
