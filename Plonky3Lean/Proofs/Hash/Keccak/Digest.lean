module

public import Plonky3Lean.Proofs.Hash.Keccak.Batch

@[expose] public section

/-!
# p3-keccak: each digest of the batched hash is Keccak-256 or SHA3-256

The lanes the batch computes for one message are the lanes of the sponge on bytes.

A whole block XORs its 17 little-endian words into the rate.

The final block XORs the leftover bytes, the first padding byte and the closing mark `0x80`:

```text
    word k / 8:   [ leftover bytes | d | 0 ... 0 ]          (k / 8 < 16)
    word 16:      [ 0 ... 0 | 0x80 ]

    word 16:      [ leftover bytes | d | 0 ... 0 | 0x80 ]   (k / 8 = 16, d ^ 0x80 when k = 135)
```
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Keccak Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Keccak

/-! ## Lanes, word by word -/

theorem getD_xorAt (L : List Std.U64) (w j : ℕ) (x : Std.U64) (hw : w < L.length) :
    (xorAt L w x).getD j 0#u64 = if j = w then L.getD w 0#u64 ^^^ x else L.getD j 0#u64 := by
  unfold xorAt
  by_cases h : j = w
  · subst h
    simp [List.getD_eq_getElem?_getD, hw]
  · simp [List.getD_eq_getElem?_getD, h, Ne.symm h]

theorem absorbL_getD (L : List Std.U64) (input : Slice Std.U8) (q n j : ℕ) (hn : n ≤ L.length) :
    (absorbL L input q n).getD j 0#u64 =
      if j < n then L.getD j 0#u64 ^^^ wordAt input (q + 8 * j) else L.getD j 0#u64 := by
  induction n with
  | zero => simp [absorbL]
  | succ n ih =>
    rw [absorbL_succ, getD_xorAt _ _ _ _ (by rw [length_absorbL]; omega)]
    by_cases hj : j = n
    · subst hj
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ih (by omega)]
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj), ih (by omega)]
      split_ifs <;> first | omega | rfl

/-- The bytes of a slice as bit vectors. -/
def bvs (input : Slice Std.U8) : List (BitVec 8) := input.val.map UScalar.bv

theorem wordAt_bv (input : Slice Std.U8) (q : ℕ) (hq : q + 8 ≤ input.val.length) :
    (wordAt input q).bv = wordOfBytes (((bvs input).drop q).take 8) := by
  rw [wordAt, u64_from_le_bytes_bv, bytes8_val _ _ hq, bvs, List.map_take, List.map_drop]

theorem getD_wordsOfBytes (B : List (BitVec 8)) (n j : ℕ) (hj : j < n) :
    (wordsOfBytes B n).getD j 0 = wordOfBytes ((B.drop (8 * j)).take 8) := by
  simp [wordsOfBytes, List.getD_eq_getElem?_getD, hj]

theorem getD_xorLanes (A B : List Word) (j : ℕ) (hA : j < A.length) (hB : j < B.length) :
    (xorLanes A B).getD j 0 = A.getD j 0 ^^^ B.getD j 0 := by
  simp [xorLanes, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hA,
    List.getElem?_eq_getElem hB]

/-- Two lists of 25 lanes are equal when every lane is. -/
theorem lanes_ext {A B : List Word} (hA : A.length = 25) (hB : B.length = 25)
    (h : ∀ j < 25, A.getD j 0 = B.getD j 0) : A = B := by
  apply List.ext_getElem (by rw [hA, hB])
  intro j h1 h2
  have := h j (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem getD_map_bv (L : List Std.U64) (j : ℕ) : (L.map UScalar.bv).getD j 0 = (L.getD j 0#u64).bv := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

theorem u64_xor_bv (x y : Std.U64) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl

theorem getD_replicate_zero (n i : ℕ) : (List.replicate n (0 : Word)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A whole block: the rate XORed with the 17 little-endian words of 136 bytes. -/
theorem absorbL_bv (L : List Std.U64) (hL : L.length = 25) (input : Slice Std.U8) (q : ℕ)
    (hq : q + 136 ≤ input.val.length) :
    (absorbL L input q 17).map UScalar.bv =
      xorLanes (L.map UScalar.bv) (wordsOfBytes (((bvs input).drop q).take 136) 17 ++ List.replicate 8 0) := by
  apply lanes_ext (by simp [length_absorbL, hL]) (by simp [length_xorLanes, hL, wordsOfBytes])
  intro j hj
  rw [getD_map_bv, absorbL_getD _ _ _ _ _ (by omega),
    getD_xorLanes _ _ _ (by simp [hL]; omega) (by simp [wordsOfBytes]; omega), getD_map_bv]
  by_cases h17 : j < 17
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h17), List.getD_append _ _ _ _ (by simp [wordsOfBytes]; omega),
      getD_wordsOfBytes _ _ _ h17]
    show (L.getD j 0#u64).bv ^^^ (wordAt input (q + 8 * j)).bv = _
    rw [wordAt_bv _ _ (by omega), List.drop_take, List.drop_drop, List.take_take]
    congr 3
    omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h17), List.getD_append_right _ _ _ _ (by simp [wordsOfBytes]; omega)]
    rw [getD_replicate_zero]
    exact (BitVec.xor_zero).symm

/-! ## The padding bytes -/

theorem padTail_getD (d : BitVec 8) (k m : ℕ) (hk : k < 136) (hm : m < 136 - k) :
    (padTail d k).getD m 0 = (if m = 0 then d else 0) ^^^ (if m = 135 - k then 0x80 else 0) := by
  simp only [padTail, List.getD_eq_getElem?_getD, List.getElem?_modify, List.getElem?_replicate]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
  by_cases h0 : m = 0 <;> by_cases h1 : m = 135 - k <;> simp [h0, h1]
  · split <;> simp
  · split <;> simp
  · omega

theorem closing_bit : ∀ z : Fin 64, closing.bv.getLsbD z = (z.val == 63) := by decide

theorem mark_bit : ∀ i : Fin 8, (0x80#8 : BitVec 8).getLsbD i = (i.val == 7) := by decide

/-- A word equals the word of a byte list when bit `z` is bit `z % 8` of byte `z / 8`. -/
theorem eq_wordOfBytes (x : Word) (l : List (BitVec 8))
    (h : ∀ z < 64, x.getLsbD z = (l.getD (z / 8) 0).getLsbD (z % 8)) : x = wordOfBytes l := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_wordOfBytes _ _ hz, h z hz]

/-- The word the final block XORs at its leftover word, as the word of its eight bytes. -/
theorem tail_word_bv (input : Slice Std.U8) (p t : ℕ) (d : Std.U8) (c : Prop) [Decidable c] :
    (Aeneas.Std.core.num.U64.from_le_bytes (tailBytes input p t) ^^^
        (if c then (⟨(UScalar.cast .U64 d).bv <<< (8 * t)⟩ : Std.U64) ^^^ closing
          else ⟨(UScalar.cast .U64 d).bv <<< (8 * t)⟩)).bv =
      wordOfBytes ((List.range 8).map fun i =>
        (if i < t then (input.val.getD (p + i) 0#u8).bv else 0) ^^^ (if i = t then d.bv else 0) ^^^
          (if c ∧ i = 7 then 0x80 else 0)) := by
  apply eq_wordOfBytes
  intro z hz
  have hz8 : z / 8 < 8 := by omega
  -- The three summands, bit by bit.
  have hx : (Aeneas.Std.core.num.U64.from_le_bytes (tailBytes input p t)).bv.getLsbD z =
      (if z / 8 < t then (input.val.getD (p + z / 8) 0#u8).bv else 0).getLsbD (z % 8) := by
    rw [u64_from_le_bytes_bv, getLsbD_wordOfBytes _ _ hz]
    simp only [tailBytes, Std.Array.from_val, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hz8, Option.map_some, Option.getD_some, Function.comp]
    split <;> rfl
  have hs : ((⟨(UScalar.cast .U64 d).bv <<< (8 * t)⟩ : Std.U64)).bv.getLsbD z =
      (if z / 8 = t then d.bv else 0).getLsbD (z % 8) := by
    show ((UScalar.cast .U64 d).bv <<< (8 * t)).getLsbD z = _
    rw [BitVec.getLsbD_shiftLeft]
    simp only [UScalar.cast, BitVec.getLsbD_setWidth]
    have h64 : z < UScalarTy.U64.numBits := hz
    rcases Nat.lt_trichotomy (z / 8) t with h | h | h
    · simp [show z < 8 * t by omega, show ¬ z / 8 = t by omega]
    · simp [show ¬ z < 8 * t by omega, h, show z - 8 * t = z % 8 by omega, hz, show z % 8 < 64 by omega]
    · simp [show ¬ z / 8 = t by omega, BitVec.getLsbD_of_ge d.bv (z - 8 * t) (by omega)]
  have hc : closing.bv.getLsbD z = (if z / 8 = 7 then (0x80#8 : BitVec 8) else 0).getLsbD (z % 8) := by
    rw [closing_bit ⟨z, hz⟩]
    split
    · rw [mark_bit ⟨z % 8, by omega⟩]; simp; omega
    · simp; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz8, Option.map_some,
    Option.getD_some]
  by_cases hcd : c
  · simp only [hcd, ite_true, true_and]
    show (_ ^^^ (_ ^^^ closing.bv)).getLsbD z = _
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hx, hs, hc, BitVec.getLsbD_xor, BitVec.getLsbD_xor]
    simp [List.getD_eq_getElem?_getD]
  · simp only [hcd, ite_false, false_and]
    show ((_ : BitVec 64) ^^^ _).getLsbD z = _
    rw [BitVec.getLsbD_xor, hx, hs, BitVec.getLsbD_xor, BitVec.getLsbD_xor]
    simp [List.getD_eq_getElem?_getD]

theorem wordOfBytes_congr {l1 l2 : List (BitVec 8)} (h : ∀ i < 8, l1.getD i 0 = l2.getD i 0) :
    wordOfBytes l1 = wordOfBytes l2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_wordOfBytes _ _ hz, getLsbD_wordOfBytes _ _ hz, h _ (by omega)]

theorem getD_drop_take (l : List (BitVec 8)) (a i : ℕ) (hi : i < 8) :
    ((l.drop a).take 8).getD i 0 = l.getD (a + i) 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Byte `m` of the last padded block: a leftover byte, or a byte of the padding. -/
theorem getD_lastBlock (input : Slice Std.U8) (q k : ℕ) (d : BitVec 8) (hq : q + k ≤ input.val.length)
    (m : ℕ) :
    (((bvs input).drop q).take k ++ padTail d k).getD m 0 =
      if m < k then (bvs input).getD (q + m) 0 else (padTail d k).getD (m - k) 0 := by
  have hlen : (((bvs input).drop q).take k).length = k := by simp [bvs]; omega
  split
  · rw [List.getD_append _ _ _ _ (by omega)]
    have : q + m < (bvs input).length := by simp [bvs]; omega
    simp [List.getD_eq_getElem?_getD, *]
  · rw [List.getD_append_right _ _ _ _ (by omega), hlen]

theorem closing_bytes : closing.bv = wordOfBytes ((List.range 8).map fun i => if i = 7 then 0x80 else 0) := by
  decide +kernel

theorem zero_bytes : (0 : Word) = wordOfBytes ((List.range 8).map fun _ => 0) := by
  decide +kernel

theorem bvs_getD (input : Slice Std.U8) (m : ℕ) : (bvs input).getD m 0 = (input.val.getD m 0#u8).bv := by
  simp only [bvs, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases input.val[m]? <;> rfl

theorem getD_map_range8 (f : ℕ → BitVec 8) (i : ℕ) (hi : i < 8) : ((List.range 8).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The word the final block XORs at its leftover word. -/
def tailWord (input : Slice Std.U8) (q k : ℕ) (d : Std.U8) : Std.U64 :=
  Aeneas.Std.core.num.U64.from_le_bytes (tailBytes input (q + 8 * (k / 8)) (k % 8)) ^^^
    (if k / 8 = 16 then (⟨(UScalar.cast .U64 d).bv <<< (8 * (k % 8))⟩ : Std.U64) ^^^ closing
      else ⟨(UScalar.cast .U64 d).bv <<< (8 * (k % 8))⟩)

theorem u64_xor_zero (x : Std.U64) : x ^^^ 0#u64 = x :=
  U64.bv_eq_imp_eq _ _ (by show UScalar.bv x ^^^ UScalar.bv (0#u64 : Std.U64) = UScalar.bv x; simp)

theorem finalL_getD (L : List Std.U64) (hL : L.length = 25) (input : Slice Std.U8) (q k : ℕ) (hk : k < 136)
    (d : Std.U8) (j : ℕ) :
    (finalL L input q k d).getD j 0#u64 = L.getD j 0#u64 ^^^
      (if j < k / 8 then wordAt input (q + 8 * j) else if j = k / 8 then tailWord input q k d
        else if j = 16 then closing else 0#u64) := by
  have hw : k / 8 ≤ 16 := by omega
  have hab : (absorbL L input q (k / 8)).length = 25 := by rw [length_absorbL, hL]
  have hdef : finalL L input q k d = if k / 8 ≠ 16 then
      xorAt (xorAt (absorbL L input q (k / 8)) (k / 8) (tailWord input q k d)) 16 closing
      else xorAt (absorbL L input q (k / 8)) (k / 8) (tailWord input q k d) := rfl
  rw [hdef]
  have hL2 : (xorAt (absorbL L input q (k / 8)) (k / 8) (tailWord input q k d)).length = 25 := by
    rw [length_xorAt, hab]
  have h1 : ∀ j', (xorAt (absorbL L input q (k / 8)) (k / 8) (tailWord input q k d)).getD j' 0#u64 =
      L.getD j' 0#u64 ^^^ (if j' < k / 8 then wordAt input (q + 8 * j') else if j' = k / 8 then tailWord input q k d
        else 0#u64) := by
    intro j'
    rw [getD_xorAt _ _ _ _ (by rw [hab]; omega), absorbL_getD _ _ _ _ _ (by omega),
      absorbL_getD _ _ _ _ _ (by omega)]
    by_cases ha : j' < k / 8
    · simp [ha, show ¬ j' = k / 8 by omega]
    · by_cases hb : j' = k / 8
      · subst hb; simp
      · simp [ha, hb, u64_xor_zero]
  by_cases h16 : k / 8 = 16
  · simp only [h16, ne_eq, not_true_eq_false, ite_false]
    rw [← h16, h1]
    by_cases ha : j < k / 8
    · simp [ha]
    · by_cases hb : j = k / 8
      · simp [hb]
      · simp [ha, hb]
  · simp only [h16, ne_eq, not_false_eq_true, ite_true]
    rw [getD_xorAt _ _ _ _ (by rw [hL2]; decide), h1, h1]
    by_cases hj : j = 16
    · subst hj
      simp [show ¬ 16 < k / 8 by omega, Ne.symm h16, u64_xor_zero]
    · simp [hj]

/-- The final block: the rate XORed with the words of the leftover bytes and the padding. -/
theorem finalL_bv (L : List Std.U64) (hL : L.length = 25) (input : Slice Std.U8) (q k : ℕ) (hk : k < 136)
    (hq : q + k ≤ input.val.length) (d : Std.U8) :
    (finalL L input q k d).map UScalar.bv =
      xorLanes (L.map UScalar.bv)
        (wordsOfBytes (((bvs input).drop q).take k ++ padTail d.bv k) 17 ++ List.replicate 8 0) := by
  have hk8 := Nat.div_add_mod k 8
  have ht := Nat.mod_lt k (show 8 > 0 by decide)
  have hw : k / 8 ≤ 16 := by omega
  apply lanes_ext (by simp [length_finalL, hL]) (by simp [length_xorLanes, hL, wordsOfBytes])
  intro j hj
  rw [getD_map_bv, getD_xorLanes _ _ _ (by simp [hL]; omega) (by simp [wordsOfBytes]; omega), getD_map_bv]
  -- The block side.
  have hblock : (wordsOfBytes (((bvs input).drop q).take k ++ padTail d.bv k) 17 ++ List.replicate 8 0).getD j 0 =
      if j < 17 then wordOfBytes ((List.range 8).map fun i =>
        (((bvs input).drop q).take k ++ padTail d.bv k).getD (8 * j + i) 0) else 0 := by
    split
    · rw [List.getD_append _ _ _ _ (by simp [wordsOfBytes]; omega), getD_wordsOfBytes _ _ _ (by omega)]
      apply wordOfBytes_congr
      intro i hi
      rw [getD_drop_take _ _ _ hi]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [List.getD_append_right _ _ _ _ (by simp [wordsOfBytes]; omega), getD_replicate_zero]
  rw [hblock, finalL_getD L hL input q k hk d j]
  show (L.getD j 0#u64).bv ^^^ (if j < k / 8 then wordAt input (q + 8 * j) else if j = k / 8 then tailWord input q k d
    else if j = 16 then closing else 0#u64).bv = _
  congr 1
  have hlast := getD_lastBlock input q k d.bv hq
  by_cases ha : j < k / 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ha), ite_eq_left_of_eq_true _ _ (eq_true (by omega : j < 17)),
      wordAt_bv _ _ (by omega)]
    apply wordOfBytes_congr
    intro i hi
    rw [getD_drop_take _ _ _ hi, getD_map_range8 _ _ hi, hlast, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      Nat.add_assoc]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
    by_cases hb : j = k / 8
    · subst hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), tailWord]
      refine (tail_word_bv input _ _ d (k / 8 = 16)).trans ?_
      apply wordOfBytes_congr
      intro i hi
      rw [getD_map_range8 _ _ hi, getD_map_range8 _ _ hi, hlast]
      by_cases hit : i < k % 8
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : 8 * (k / 8) + i < k)), bvs_getD]
        simp [hit, show ¬ i = k % 8 by omega, show ¬ (k / 8 = 16 ∧ i = 7) by omega, ← Nat.add_assoc]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ 8 * (k / 8) + i < k)),
          padTail_getD _ _ _ hk (by omega)]
        have e1 : (8 * (k / 8) + i - k = 0) ↔ (i = k % 8) := by constructor <;> intro <;> omega
        have e2 : (8 * (k / 8) + i - k = 135 - k) ↔ (k / 8 = 16 ∧ i = 7) := by
          constructor
          · intro; omega
          · rintro ⟨_, _⟩; omega
        simp [hit, e1, e2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
      by_cases h16 : j = 16
      · subst h16
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (by decide)),
          closing_bytes]
        apply wordOfBytes_congr
        intro i hi
        rw [getD_map_range8 _ _ hi, getD_map_range8 _ _ hi, hlast,
          ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ 8 * 16 + i < k)),
          padTail_getD _ k (8 * 16 + i - k) hk (by omega)]
        have e1 : ¬ (8 * 16 + i - k = 0) := by omega
        have e2 : (8 * 16 + i - k = 135 - k) ↔ (i = 7) := by constructor <;> intro <;> omega
        simp [e1, e2]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h16)]
        split
        · show (0 : Word) = _
          rw [zero_bytes]
          apply wordOfBytes_congr
          intro i hi
          rw [getD_map_range8 _ _ hi, getD_map_range8 _ _ hi, hlast,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ 8 * j + i < k)),
            padTail_getD _ k (8 * j + i - k) hk (by omega)]
          have e1 : ¬ (8 * j + i - k = 0) := by omega
          have e2 : ¬ (8 * j + i - k = 135 - k) := by omega
          simp [e1, e2]
        · rfl

/-! ## One digest -/

/-- The sponge's lanes after the first `b` blocks of the padded message. -/
def spongeLanes (P : List (BitVec 8)) (b : ℕ) : List Word :=
  (List.range b).foldl
    (fun L i => keccakFL (xorLanes L (wordsOfBytes ((P.drop (136 * i)).take 136) 17 ++ List.replicate 8 0)))
    (List.replicate 25 0)

theorem spongeLanes_succ (P : List (BitVec 8)) (b : ℕ) :
    spongeLanes P (b + 1) =
      keccakFL (xorLanes (spongeLanes P b) (wordsOfBytes ((P.drop (136 * b)).take 136) 17 ++ List.replicate 8 0)) := by
  rw [spongeLanes, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← spongeLanes]

/-- The whole blocks of the batch are the first blocks of the sponge. -/
theorem blocksL_bv (input : Slice Std.U8) (p len : ℕ) (d : BitVec 8) (hp : p + len ≤ input.val.length) (b : ℕ)
    (hb : b ≤ len / 136) :
    (blocksL input p b).map UScalar.bv = spongeLanes (padBytes d (((bvs input).drop p).take len)) b := by
  induction b with
  | zero => simp [blocksL, spongeLanes]
  | succ b ih =>
    rw [blocksL_succ, spongeLanes_succ, ← ih (by omega)]
    rw [(rounds_eq _ (by rw [length_absorbL, length_blocksL])).1, absorbL_bv _ (length_blocksL _ _ _) _ _ (by omega)]
    congr 4
    rw [padBytes, List.drop_append_of_le_length (by simp [bvs]; omega),
      List.take_append_of_le_length (by simp [bvs]; omega)]
    rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega), Nat.mul_comm]

/-- The lanes of one message are the sponge's lanes after every block of its padded bytes. -/
theorem msgLanes_bv (input : Slice Std.U8) (p len : ℕ) (d : Std.U8) (hp : p + len ≤ input.val.length) :
    (msgLanes input p len d).map UScalar.bv =
      spongeLanes (padBytes d.bv (((bvs input).drop p).take len)) (len / 136 + 1) := by
  have hk8 := Nat.div_add_mod len 136
  have hk := Nat.mod_lt len (show 136 > 0 by decide)
  rw [msgLanes, spongeLanes_succ, ← blocksL_bv input p len d.bv hp _ le_rfl,
    (rounds_eq _ (by rw [length_finalL, length_blocksL])).1,
    finalL_bv _ (length_blocksL _ _ _) _ _ _ hk (by omega)]
  congr 4
  have hM : (((bvs input).drop p).take len).length = len := by simp [bvs]; omega
  have hlast : ((padBytes d.bv (((bvs input).drop p).take len)).drop (136 * (len / 136))).take 136 =
      ((bvs input).drop (p + len / 136 * 136)).take (len % 136) ++ padTail d.bv (len % 136) := by
    rw [padBytes, List.drop_append_of_le_length (by omega), List.take_of_length_le (by
      simp only [List.length_append, List.length_drop, hM, length_padTail]; omega), hM, List.drop_take,
      List.drop_drop]
    congr 2
    · omega
    · rw [Nat.mul_comm]
  exact hlast.symm

theorem digestAt_bv (L : List Std.U64) (hL : L.length = 25) :
    (digestAt L 32).val.map UScalar.bv = ((L.map UScalar.bv).take 4).flatMap bytesOfWord := by
  apply List.ext_getElem (by simp [digestAt, List.length_flatMap, bytesOfWord, hL])
  intro i h1 h2
  simp only [digestAt, Std.Array.from_val, List.length_map, List.length_range] at h1
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0,
    getD_flatMap_uniform (m := 8) _ _ (fun _ => by simp [bytesOfWord]) _ _ 0 (by simp [hL]; omega)]
  simp only [digestAt, Std.Array.from_val, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h1, Option.map_some, Option.getD_some, Function.comp, ite_eq_left_of_eq_true _ _ (eq_true h1), byteOf]
  rw [List.getElem?_take, ite_eq_left_of_eq_true _ _ (eq_true (by omega : i / 8 < 4)), List.getElem?_map]
  cases L[i / 8]? <;> rfl

/-- Digest `j` of the batch is the sponge on its message, with first padding byte `d`. -/
theorem length_msgLanes (input : Slice Std.U8) (p len : ℕ) (d : Std.U8) : (msgLanes input p len d).length = 25 :=
  (rounds_eq _ (by rw [length_finalL, length_blocksL])).2

theorem digestOf_bv (input : Slice Std.U8) (len : ℕ) (d : Std.U8) (j : ℕ) (hj : j * len + len ≤ input.val.length) :
    (digestOf input len d j).val.map UScalar.bv = spongeBytes d.bv (((bvs input).drop (j * len)).take len) := by
  rw [digestOf, digestAt_bv _ (length_msgLanes _ _ _ _), msgLanes_bv _ _ _ _ hj,
    spongeBytes]
  have hM : (((bvs input).drop (j * len)).take len).length = len := by simp [bvs]; omega
  rw [length_padBytes, hM, Nat.mul_div_cancel_left _ (by decide)]
  rfl

/-- The state array of 25 words: lane `(x, y)` is word `x + 5 y`, and `A[x, y, z]` is its bit `z`. -/
def stateOfWords (w : List Std.U64) : State := fun x y z => (w.getD (x.val + 5 * y.val) 0#u64).bv.getLsbD z.val

theorem stateOfWords_eq (w : List Std.U64) : stateOfWords w = ofLanes (w.map UScalar.bv) := by
  funext x y z
  rw [ofLanes_val, lane, getD_map_bv]
  rfl

/-! ## The two batched hashes -/

/-- With `n > 0` digests requested and an input of `n * len` bytes, digest `j` is `H` of bytes `j len` to `(j + 1) len - 1`. -/
theorem hash_many_digests (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize)) (len : ℕ)
    (hn : 0 < out.val.length) (hlen : input.val.length = out.val.length * len) :
    ∃ r, p3_keccak.hax_reshaped.hash_many_with_domain d input out = .ok r ∧ r.val.length = out.val.length ∧
      ∀ j (hj : j < r.val.length), (r.val[j]).val.map UScalar.bv =
        spongeBytes d.bv (((bvs input).drop (j * len)).take len) := by
  refine ⟨_, hash_many_eq d input out len hn hlen, length_outAt _ _ _, fun j hj => ?_⟩
  have hj' : j < out.val.length := by rwa [length_outAt] at hj
  simp only [outAt_val, List.getElem_map, List.getElem_range, hj', ite_true]
  exact digestOf_bv _ _ _ _ (by rw [hlen]; nlinarith)

end Plonky3Lean.Proofs.Keccak
