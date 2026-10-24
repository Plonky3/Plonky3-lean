module

public import Plonky3Lean.Proofs.Hash.Keccak.Lanes

@[expose] public section

/-!
# Keccak-256 and SHA3-256 on bytes and lanes

FIPS 202's sponge works on bit strings.

On a byte message the bit string is a whole number of 136-byte blocks:

```text
    [ message bytes | d | 0x00 ... 0x00 | 0x80 ]      d = 0x01 for Keccak-256, 0x06 for SHA3-256
                      ^                   ^
                 len % 136               135
```

When the message ends one byte short of a block, both marks share the byte, d ^ 0x80.

Each block XORs into the first 17 lanes as little-endian words.

The digest is the first 32 bytes of lanes 0 to 3.
-/

namespace Plonky3Lean.Proofs.Keccak

open Plonky3Lean.Spec.Keccak

/-! ## Bytes, words and bits -/

/-- The word of up to 8 bytes, little-endian, missing bytes read as zero. -/
def wordOfBytes (bs : List Byte) : Word :=
  BitVec.ofFnLE fun z : Fin 64 => (bs.getD (z.val / 8) 0).getLsbD (z.val % 8)

/-- The first n words of a byte string, 8 bytes each. -/
def wordsOfBytes (bs : List Byte) (n : ℕ) : List Word :=
  (List.range n).map fun k => wordOfBytes ((bs.drop (8 * k)).take 8)

/-- The 8 little-endian bytes of a word. -/
def bytesOfWord (w : Word) : List Byte := (List.range 8).map fun j => w.extractLsb' (8 * j) 8

/-- Lanes XORed word by word. -/
def xorLanes (L W : List Word) : List Word := List.zipWith (· ^^^ ·) L W

/-- The bytes that complete the last block of a message of k bytes mod 136.

They hold the marks d and 0x80. -/
def padTail (d : Byte) (k : ℕ) : List Byte :=
  ((List.replicate (136 - k) 0).modify 0 (· ^^^ d)).modify (135 - k) (· ^^^ 0x80)

/-- The message and its padding, a whole number of 136-byte blocks. -/
def padBytes (d : Byte) (M : List Byte) : List Byte := M ++ padTail d (M.length % 136)

/-- The sponge on lanes: XOR each block into the first 17 lanes, permute, and keep 32 bytes. -/
def spongeBytes (d : Byte) (M : List Byte) : List Byte :=
  let P := padBytes d M
  let L := (List.range (P.length / 136)).foldl
    (fun L i => keccakFL (xorLanes L (wordsOfBytes ((P.drop (136 * i)).take 136) 17 ++ List.replicate 8 0)))
    (List.replicate 25 0)
  (L.take 4).flatMap bytesOfWord

/-! ## The padding -/

/-- The tail bytes of Keccak-256 are pad10*1, for each of the 136 positions the message can end at. -/
theorem padTail_keccak : ∀ k : Fin 136, bitsOfBytes (padTail 0x01 k) = pad101 1088 (8 * k) := by
  decide +kernel

/-- The tail bytes of SHA3-256 are the suffix 01 followed by pad10*1. -/
theorem padTail_sha3 : ∀ k : Fin 136, bitsOfBytes (padTail 0x06 k) = [false, true] ++ pad101 1088 (8 * k + 2) := by
  decide +kernel

theorem pad101_mod (x m : ℕ) : pad101 x m = pad101 x (m % x) := by
  rw [pad101, pad101, Nat.add_mod m 2, Nat.add_mod (m % x) 2, Nat.mod_mod]

theorem length_padTail (d : Byte) (k : ℕ) : (padTail d k).length = 136 - k := by
  simp [padTail]

theorem length_padBytes (d : Byte) (M : List Byte) : (padBytes d M).length = 136 * (M.length / 136 + 1) := by
  rw [padBytes, List.length_append, length_padTail]
  have := Nat.mod_lt M.length (show 136 > 0 by decide)
  have := Nat.div_add_mod M.length 136
  omega

theorem bitsOfBytes_append (l l' : List Byte) : bitsOfBytes (l ++ l') = bitsOfBytes l ++ bitsOfBytes l' := by
  simp [bitsOfBytes]

theorem length_bitsOfBytes (l : List Byte) : (bitsOfBytes l).length = 8 * l.length := by
  simp [bitsOfBytes, List.length_flatMap, Nat.mul_comm]

/-- Keccak-256's padded message, in bits, is the message followed by pad10*1. -/
theorem bits_padBytes_keccak (M : List Byte) :
    bitsOfBytes (padBytes 0x01 M) = bitsOfBytes M ++ pad101 1088 (bitsOfBytes M).length := by
  rw [padBytes, bitsOfBytes_append, padTail_keccak ⟨_, Nat.mod_lt _ (by decide)⟩, length_bitsOfBytes,
    pad101_mod _ (8 * M.length), pad101_mod _ (8 * (M.length % 136))]
  congr 2
  omega

/-- SHA3-256's padded message, in bits, is the message, the suffix 01, and pad10*1. -/
theorem bits_padBytes_sha3 (M : List Byte) :
    bitsOfBytes (padBytes 0x06 M) =
      (bitsOfBytes M ++ [false, true]) ++ pad101 1088 (bitsOfBytes M ++ [false, true]).length := by
  rw [padBytes, bitsOfBytes_append, padTail_sha3 ⟨_, Nat.mod_lt _ (by decide)⟩, List.append_assoc,
    List.length_append, length_bitsOfBytes, pad101_mod _ (8 * M.length + _), pad101_mod _ (8 * (M.length % 136) + 2)]
  congr 3
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## Bit strings of bytes and of lanes -/

theorem bitsOfBytes_drop (l : List Byte) (k : ℕ) : bitsOfBytes (l.drop k) = (bitsOfBytes l).drop (8 * k) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil => simp [bitsOfBytes]
    | cons b l =>
      rw [List.drop_succ_cons, ih, show 8 * (k + 1) = 8 + 8 * k by omega, ← List.drop_drop]
      simp [bitsOfBytes]

theorem bitsOfBytes_take (l : List Byte) (k : ℕ) : bitsOfBytes (l.take k) = (bitsOfBytes l).take (8 * k) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil => simp [bitsOfBytes]
    | cons b l =>
      rw [List.take_succ_cons, show 8 * (k + 1) = 8 + 8 * k by omega]
      simpa [bitsOfBytes, List.take_add] using ih l

theorem toBits_append (L L' : List Word) : toBits (L ++ L') = toBits L ++ toBits L' := by
  simp [toBits]

theorem toBits_replicate (n : ℕ) : toBits (List.replicate n 0) = List.replicate (64 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, show 64 * (n + 1) = 64 + 64 * n by omega, ← List.replicate_append_replicate]
    simp [toBits] at ih ⊢
    exact ih

theorem toBits_xorLanes (L W : List Word) (h : L.length = W.length) :
    toBits (xorLanes L W) = List.zipWith (· ^^ ·) (toBits L) (toBits W) := by
  induction L generalizing W with
  | nil => cases W <;> simp_all [xorLanes, toBits]
  | cons w L ih =>
    cases W with
    | nil => simp at h
    | cons v W =>
      simp only [xorLanes, List.zipWith_cons_cons, toBits, List.flatMap_cons] at ih ⊢
      rw [List.zipWith_append (by simp), ih W (by simpa using h)]
      congr 1
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp

theorem toBits_take (L : List Word) (k : ℕ) : (toBits L).take (64 * k) = toBits (L.take k) := by
  induction k generalizing L with
  | zero => simp [toBits]
  | succ k ih =>
    cases L with
    | nil => simp [toBits]
    | cons w L =>
      rw [List.take_succ_cons, show 64 * (k + 1) = 64 + 64 * k by omega]
      simpa [toBits, List.take_add] using ih L

theorem getLsbD_wordOfBytes (bs : List Byte) (z : ℕ) (hz : z < 64) :
    (wordOfBytes bs).getLsbD z = (bs.getD (z / 8) 0).getLsbD (z % 8) :=
  BitVec.getLsb_ofFnLE _ ⟨z, hz⟩

/-- The words of a byte string carry its bits in order. -/
theorem toBits_wordsOfBytes (B : List Byte) (n : ℕ) (hB : B.length = 8 * n) :
    toBits (wordsOfBytes B n) = bitsOfBytes B := by
  apply List.ext_getElem (by simp [length_toBits, length_bitsOfBytes, wordsOfBytes, hB]; omega)
  intro k h1 h2
  rw [length_bitsOfBytes, hB] at h2
  rw [← List.getD_eq_getElem _ false, ← List.getD_eq_getElem _ false, toBits, bitsOfBytes,
    getD_flatMap_uniform (m := 64) _ _ (fun _ => by simp) _ _ 0 (by simp [wordsOfBytes]; omega),
    getD_flatMap_uniform (m := 8) _ _ (fun _ => by simp) _ _ 0 (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn]
  have hk : k / 64 < n := by omega
  rw [List.getElem?_eq_getElem (show k % 64 < (List.finRange 64).length by simp; omega),
    List.getElem_finRange, dite_eq_left (Nat.mod_lt _ (by decide)), wordsOfBytes, List.getElem?_map,
    List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, Fin.val_cast]
  rw [getLsbD_wordOfBytes _ _ (Nat.mod_lt _ (by decide)), ← List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  have e1 : (k % 64 / 8 < 8) := by omega
  have e2 : 8 * (k / 64) + k % 64 / 8 = k / 8 := by omega
  have e3 : k % 64 % 8 = k % 8 := by omega
  simp [e1, e2, e3]

theorem getLsbD_ofFnLE {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (BitVec.ofFnLE f).getLsbD i = f ⟨i, hi⟩ :=
  BitVec.getLsb_ofFnLE f ⟨i, hi⟩

/-- The bytes of the bit string of lanes are the little-endian bytes of each lane. -/
theorem bytesOfBits_toBits (L : List Word) : bytesOfBits (toBits L) = L.flatMap bytesOfWord := by
  apply List.ext_getElem (by simp [bytesOfBits, length_toBits, List.length_flatMap, bytesOfWord]; omega)
  intro i h1 h2
  simp only [bytesOfBits, length_toBits, List.length_map, List.length_range] at h1
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0,
    getD_flatMap_uniform (m := 8) _ _ (fun _ => by simp [bytesOfWord]) _ _ 0 (by omega)]
  simp only [bytesOfBits, length_toBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i < 64 * L.length / 8 by omega),
    List.getElem?_range (show i % 8 < 8 by omega), Option.map_some, Option.getD_some, bytesOfWord]
  ext j hj
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, getLsbD_ofFnLE _ _ hj, BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and]
  rw [← List.getD_eq_getElem?_getD, toBits,
    getD_flatMap_uniform (m := 64) _ _ (fun _ => by simp) _ _ 0 (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show (8 * i + j) % 64 < (List.finRange 64).length by simp; omega)]
  simp only [List.getElem_finRange, Option.map_some, Option.getD_some, Fin.val_cast, List.getD_eq_getElem?_getD]
  have e1 : (8 * i + j) / 64 = i / 8 := by omega
  have e2 : (8 * i + j) % 64 = 8 * (i % 8) + j := by omega
  rw [e1, e2]

theorem length_xorLanes (L W : List Word) : (xorLanes L W).length = min L.length W.length := by
  simp [xorLanes]

/-- One absorption: XOR a block of 136 bytes into the rate, then permute. -/
theorem absorb_eq (L : List Word) (hL : L.length = 25) (B : List Byte) (hB : B.length = 136) :
    keccakF (List.zipWith (· ^^ ·) (toBits L) (bitsOfBytes B ++ List.replicate 512 false)) =
      toBits (keccakFL (xorLanes L (wordsOfBytes B 17 ++ List.replicate 8 0))) := by
  have hW : (wordsOfBytes B 17 ++ List.replicate 8 0).length = 25 := by simp [wordsOfBytes]
  rw [← toBits_wordsOfBytes B 17 hB, show 512 = 64 * 8 by rfl, ← toBits_replicate, ← toBits_append,
    ← toBits_xorLanes _ _ (by rw [hL, hW]), keccakF_toBits _ (by rw [length_xorLanes, hL, hW]; rfl)]

/-- The sponge of FIPS 202 on a message whose padded bits are the bits of a padded byte message. -/
theorem keccakC_eq (d : Byte) (M : List Byte) (N : List Bool)
    (hN : bitsOfBytes (padBytes d M) = N ++ pad101 1088 N.length) :
    bytesOfBits (keccakC 512 N 256) = spongeBytes d M := by
  simp only [keccakC, sponge, spongeBytes]
  rw [show 1600 - 512 = 1088 by rfl, show 1600 - 1088 = 512 by rfl, ← hN, length_bitsOfBytes,
    length_padBytes]
  rw [show 8 * (136 * (M.length / 136 + 1)) / 1088 = 136 * (M.length / 136 + 1) / 136 by omega]
  generalize hn : 136 * (M.length / 136 + 1) / 136 = n
  have hPb := length_padBytes d M
  -- The absorbed state, as lanes, at every step.
  have key : ∀ ts : List ℕ, (∀ t ∈ ts, t < n) → ∀ L : List Word, L.length = 25 →
      ts.foldl (fun S i => keccakF (List.zipWith (· ^^ ·) S
          (((bitsOfBytes (padBytes d M)).drop (i * 1088)).take 1088 ++ List.replicate 512 false))) (toBits L) =
        toBits (ts.foldl (fun L i => keccakFL (xorLanes L
          (wordsOfBytes (((padBytes d M).drop (136 * i)).take 136) 17 ++ List.replicate 8 0))) L) := by
    intro ts
    induction ts with
    | nil => intro _ L _; rfl
    | cons t ts ih =>
      intro hts L hL
      have ht := hts t (by simp)
      simp only [List.foldl_cons]
      rw [show t * 1088 = 8 * (136 * t) by omega, show 1088 = 8 * 136 by rfl, ← bitsOfBytes_drop,
        ← bitsOfBytes_take, absorb_eq L hL _ (by simp; omega)]
      exact ih (fun t' h => hts t' (by simp [h])) _ (length_keccakFL _ (by simp [length_xorLanes, hL, wordsOfBytes]))
  have h0 : List.replicate 1600 false = toBits (List.replicate 25 0) := by rw [toBits_replicate]
  rw [h0, key _ (fun t h => by simpa using h) _ (by simp), show 256 / 1088 + 1 = 1 by rfl, squeeze, squeeze,
    List.append_nil, List.take_take, show min 256 1088 = 64 * 4 by rfl, toBits_take, bytesOfBits_toBits]

/-- Keccak-256 of a byte message is the sponge on lanes with first padding byte 0x01. -/
theorem keccak256_eq (M : List Byte) : keccak256 M = spongeBytes 0x01 M :=
  keccakC_eq _ _ _ (bits_padBytes_keccak M)

/-- SHA3-256 of a byte message is the sponge on lanes with first padding byte 0x06. -/
theorem sha3_256_eq (M : List Byte) : sha3_256 M = spongeBytes 0x06 M :=
  keccakC_eq _ _ _ (bits_padBytes_sha3 M)

end Plonky3Lean.Proofs.Keccak