module

public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# SHA-256, from FIPS 180-4

Words are 32-bit vectors and messages are lists of bytes, with section numbers from FIPS 180-4 (August 2015).

* **Functions and constants** (4.1.2, 4.2.2, 5.3.3): the six logical functions, the 64 round constants and the initial hash value.
* **The compression function** (6.2.2): the message schedule, 64 rounds over the working variables, and the addition back into the hash value.
* **The hash** (5.1.1, 5.2.1, 6.2): padding, parsing into blocks, and the digest as big-endian bytes.

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Sha256

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- A byte. -/
abbrev Byte := BitVec 8

/-! ## 4.1.2: functions -/

def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

def bigSigma1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

def smallSigma0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

def smallSigma1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-! ## 4.2.2 and 5.3.3: constants -/

/-- The round constants `K_0, …, K_63`. -/
def K : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value `H^(0)`. -/
def H0 : List Word :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## 6.2.2: the compression function -/

/-- One more word of the message schedule, `W_t` for `t` the current length. -/
def extend (W : List Word) : List Word :=
  let t := W.length
  W ++ [smallSigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 + smallSigma0 (W.getD (t - 15) 0) +
    W.getD (t - 16) 0]

/-- The message schedule `W_0, …, W_63` of a block of 16 words. -/
def schedule (M : List Word) : List Word := extend^[48] M

/-- The working variables `a, …, h`. -/
structure Vars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
deriving DecidableEq

/-- One round, with round constant `k` and schedule word `w`. -/
def round (v : Vars) (k w : Word) : Vars :=
  let t1 := v.h + bigSigma1 v.e + ch v.e v.f v.g + k + w
  let t2 := bigSigma0 v.a + maj v.a v.b v.c
  ⟨t1 + t2, v.a, v.b, v.c, v.d + t1, v.e, v.f, v.g⟩

/-- The working variables loaded from a hash value. -/
def Vars.ofList (H : List Word) : Vars :=
  ⟨H.getD 0 0, H.getD 1 0, H.getD 2 0, H.getD 3 0, H.getD 4 0, H.getD 5 0, H.getD 6 0, H.getD 7 0⟩

def Vars.toList (v : Vars) : List Word := [v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]

/-- The working variables after the first `n` rounds on schedule `W`. -/
def rounds (W : List Word) (v : Vars) (n : Nat) : Vars :=
  (List.range n).foldl (fun v t => round v (K.getD t 0) (W.getD t 0)) v

/-- The next hash value, from hash value `H` and a block of 16 words `M`. -/
def compress (H M : List Word) : List Word :=
  List.zipWith (· + ·) H (rounds (schedule M) (Vars.ofList H) 64).toList

/-! ## 3.1 and 5.2.1: words and bytes, big-endian -/

/-- The word whose big-endian bytes are `b₀ b₁ b₂ b₃`. -/
def wordOfBytes (b₀ b₁ b₂ b₃ : Byte) : Word := b₀ ++ b₁ ++ b₂ ++ b₃

/-- The words of a list of bytes, four bytes each, big-endian. -/
def wordsOfBytes : List Byte → List Word
  | b₀ :: b₁ :: b₂ :: b₃ :: rest => wordOfBytes b₀ b₁ b₂ b₃ :: wordsOfBytes rest
  | _ => []

/-- The big-endian bytes of a word. -/
def bytesOfWord (w : Word) : List Byte :=
  [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

def bytesOfWords (ws : List Word) : List Byte := ws.flatMap bytesOfWord

/-! ## 5.1.1, 5.2.1 and 6.2: the hash -/

/-- The padded message: a one bit, zeros to 56 bytes modulo 64, and the bit length in 64 bits. -/
def pad (msg : List Byte) : List Byte :=
  let zeros := (119 - msg.length % 64) % 64
  msg ++ [0x80] ++ List.replicate zeros 0 ++ bytesOfWords [BitVec.ofNat 32 (8 * msg.length / 2 ^ 32),
    BitVec.ofNat 32 (8 * msg.length)]

/-- At most `n` blocks of 64 bytes, from the front. -/
def blocksAux : Nat → List Byte → List (List Byte)
  | 0, _ => []
  | n + 1, bytes => if bytes.isEmpty then [] else bytes.take 64 :: blocksAux n (bytes.drop 64)

/-- The 64-byte blocks of a padded message. -/
def blocks (bytes : List Byte) : List (List Byte) := blocksAux bytes.length bytes

/-- The SHA-256 digest of a message. -/
def digest (msg : List Byte) : List Byte :=
  bytesOfWords ((blocks (pad msg)).foldl (fun H B => compress H (wordsOfBytes B)) H0)

end Plonky3Lean.Spec.Sha256
