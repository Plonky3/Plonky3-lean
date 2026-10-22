module

public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# BLAKE3, from the BLAKE3 paper

Words are 32-bit vectors and messages are lists of bytes, following the BLAKE3 paper (version 20211102), section 2, and its reference implementation.

* **The compression function** (2.2): the quarter-round `g`, seven rounds of columns then diagonals, the message permutation between rounds, and the output feed-forward.
* **Chunks** (2.3): a chunk of up to 1024 bytes is compressed block by block, the first block flagged `CHUNK_START` and the last `CHUNK_END`.
* **The tree** (2.1): the left subtree of `n > 1` chunks holds the largest power of two of them below `n`; parents compress the two children's chaining values.
* **The hash** (2.5): the root node, flagged `ROOT`, compressed with counter `0`; its first 32 bytes, little-endian.

Only the hash mode is specified: the key is the IV and the mode flags are `0`.

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Blake3

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- A byte. -/
abbrev Byte := BitVec 8

/-! ## Constants (2.2, table 1 and 3) -/

/-- The IV, the first 32 bits of the fractional parts of the square roots of the first eight primes. -/
def IV : List Word :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The message word permutation, applied between rounds. -/
def MSG_PERMUTATION : List ℕ := [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

def CHUNK_START : Word := 1 <<< 0
def CHUNK_END : Word := 1 <<< 1
def PARENT : Word := 1 <<< 2
def ROOT : Word := 1 <<< 3

/-! ## The compression function (2.2) -/

/-- The quarter-round on state words `a`, `b`, `c`, `d`, with message words `mx` and `my`. -/
def g (s : List Word) (a b c d : ℕ) (mx my : Word) : List Word :=
  let s := s.set a (s.getD a 0 + s.getD b 0 + mx)
  let s := s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 16)
  let s := s.set c (s.getD c 0 + s.getD d 0)
  let s := s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 12)
  let s := s.set a (s.getD a 0 + s.getD b 0 + my)
  let s := s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 8)
  let s := s.set c (s.getD c 0 + s.getD d 0)
  s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 7)

/-- One round: the four columns, then the four diagonals. -/
def round (s m : List Word) : List Word :=
  let s := g s 0 4 8 12 (m.getD 0 0) (m.getD 1 0)
  let s := g s 1 5 9 13 (m.getD 2 0) (m.getD 3 0)
  let s := g s 2 6 10 14 (m.getD 4 0) (m.getD 5 0)
  let s := g s 3 7 11 15 (m.getD 6 0) (m.getD 7 0)
  let s := g s 0 5 10 15 (m.getD 8 0) (m.getD 9 0)
  let s := g s 1 6 11 12 (m.getD 10 0) (m.getD 11 0)
  let s := g s 2 7 8 13 (m.getD 12 0) (m.getD 13 0)
  g s 3 4 9 14 (m.getD 14 0) (m.getD 15 0)

/-- The message words in the order of the next round. -/
def permute (m : List Word) : List Word := MSG_PERMUTATION.map fun i => m.getD i 0

/-- `n` rounds, permuting the message after each. -/
def rounds : ℕ → List Word → List Word → List Word
  | 0, s, _ => s
  | n + 1, s, m => rounds n (round s m) (permute m)

/-- The 16-word output of compressing `block` under chaining value `cv`. -/
def compress (cv block : List Word) (counter : ℕ) (blockLen flags : Word) : List Word :=
  let s := cv ++ IV.take 4 ++
    [BitVec.ofNat 32 counter, BitVec.ofNat 32 (counter / 2 ^ 32), blockLen, flags]
  let s := rounds 7 s block
  (List.range 8).map (fun i => s.getD i 0 ^^^ s.getD (i + 8) 0) ++
    (List.range 8).map fun i => s.getD (i + 8) 0 ^^^ cv.getD i 0

/-! ## Words and bytes, little-endian -/

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

/-! ## Chunks (2.3) -/

/-- What a node compresses last: chaining value, block, counter, block length and flags. -/
structure Output where
  cv : List Word
  block : List Word
  counter : ℕ
  blockLen : Word
  flags : Word

/-- The chaining value a node passes to its parent. -/
def Output.chainingValue (o : Output) : List Word :=
  (compress o.cv o.block o.counter o.blockLen o.flags).take 8

/-- The first 32 bytes of the root node's output. -/
def Output.rootBytes (o : Output) : List Byte :=
  (((compress o.cv o.block 0 o.blockLen (o.flags ||| ROOT)).take 8).map bytesOfWord).flatten

/-- At most `n` pieces of `k` bytes, from the front. -/
def piecesAux (k : ℕ) : ℕ → List Byte → List (List Byte)
  | 0, _ => []
  | n + 1, bytes => if bytes.isEmpty then [] else bytes.take k :: piecesAux k n (bytes.drop k)

/-- The pieces of `k` bytes of a message, the last possibly shorter; one empty piece for an empty
message. -/
def pieces (k : ℕ) (bytes : List Byte) : List (List Byte) :=
  if bytes.isEmpty then [[]] else piecesAux k bytes.length bytes

/-- The output of chunk number `counter`: every block but the last compressed into the chaining
value. -/
def chunkOutput (chunk : List Byte) (counter : ℕ) : Output :=
  let blocks := pieces 64 chunk
  let n := blocks.length
  let cv := (List.range (n - 1)).foldl (fun cv i =>
      (compress cv (blockWords (blocks.getD i [])) counter 64
        (if i = 0 then CHUNK_START else 0)).take 8) IV
  let lastBlock := blocks.getD (n - 1) []
  { cv := cv, block := blockWords lastBlock, counter := counter,
    blockLen := BitVec.ofNat 32 lastBlock.length,
    flags := (if n = 1 then CHUNK_START else 0) ||| CHUNK_END }

/-! ## The tree (2.1) -/

/-- The parent of two chaining values. -/
def parentOutput (left right : List Word) : Output :=
  { cv := IV, block := left ++ right, counter := 0, blockLen := 64, flags := PARENT }

/-- The largest power of two below `n`, for `n ≥ 2`, found among the first `fuel` powers. -/
def pow2Below : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, n => if 2 * pow2Below fuel n < n then 2 * pow2Below fuel n else pow2Below fuel n

/-- The output of the subtree over `chunks`, the first of which is chunk number `start`; `fuel`
bounds the depth. -/
def subtreeOutput : ℕ → List (List Byte) → ℕ → Output
  | 0, chunks, start => chunkOutput (chunks.getD 0 []) start
  | fuel + 1, chunks, start =>
    if chunks.length ≤ 1 then chunkOutput (chunks.getD 0 []) start
    else
      let left := pow2Below chunks.length chunks.length
      parentOutput (subtreeOutput fuel (chunks.take left) start).chainingValue
        (subtreeOutput fuel (chunks.drop left) (start + left)).chainingValue

/-! ## The hash (2.5) -/

/-- The 32-byte BLAKE3 digest of a message. -/
def digest (msg : List Byte) : List Byte :=
  let chunks := pieces 1024 msg
  (subtreeOutput chunks.length chunks 0).rootBytes

end Plonky3Lean.Spec.Blake3
