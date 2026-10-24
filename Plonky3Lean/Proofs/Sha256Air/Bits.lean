module

public import Plonky3Lean.Proofs.Sha256Air.Add
public import Plonky3Lean.Proofs.KeccakAir.Words
public import Plonky3Lean.Spec.Sha256
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Words of bits

A word lies in a row as 32 cells, its bits, least significant first.

On such cells the AIR's packings, sigma columns, Ch and Maj are those of FIPS 180-4, limb by limb.

```text
    limb 0 = bits 0 .. 15  = w mod 2^16
    limb 1 = bits 16 .. 31 = w / 2^16
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.builder.mirror p3_sha256_air.mirror Plonky3Lean.Spec.Sha256
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF bitsum bitsum_lt bitsum_testBit)

variable {F : Type} [Field F]

/-- The low limb of a word. -/
def lo (w : BitVec 32) : ℕ := w.toNat % 65536

/-- The high limb of a word. -/
def hi (w : BitVec 32) : ℕ := w.toNat / 65536

/-- The cells hold the bits of the word. -/
def Holds (bits : ℕ → F) (w : BitVec 32) : Prop := ∀ b < 32, bits b = bitF (w.getLsbD b)

/-! ## Folding bits -/

theorem foldl_double (G : ℕ → Bool) (k s : ℕ) (acc : F) :
    (List.range' s k).reverse.foldl (fun acc z => acc + acc + bitF (G z)) acc =
      2 ^ k * acc + ((bitsum (fun j => G (s + j)) k : ℕ) : F) := by
  induction k generalizing s acc with
  | zero => simp [bitsum]
  | succ k ih =>
    rw [List.range'_succ, List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, bitsum, Nat.add_zero]
    push_cast
    simp only [show ∀ j, s + 1 + j = s + (j + 1) from fun j => by omega]
    ring

theorem bitsum_limb (w : BitVec 32) (limb : ℕ) (hl : limb < 2) :
    bitsum (fun j => w.getLsbD (limb * 16 + j)) 16 = if limb = 0 then lo w else hi w := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitsum_testBit]
  interval_cases limb
  · simp only [↓reduceIte, lo]
    rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow, BitVec.testBit_toNat, Nat.zero_mul, Nat.zero_add]
  · simp only [one_ne_zero, ↓reduceIte, hi]
    rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_div_two_pow, BitVec.testBit_toNat, Nat.one_mul, Nat.add_comm]
    by_cases hj : j < 16
    · simp [hj]
    · simp [hj, BitVec.getLsbD_of_ge w (j + 16) (by omega)]

/-- A limb folded from the cells of a word is the word's limb. -/
theorem fold_limb {g : ℕ → F} {w : BitVec 32} (h : Holds g w) (limb : ℕ) (hl : limb < 2) :
    (List.range' (limb * 16) 16).reverse.foldl (fun acc z => acc + acc + g z) 0 =
      ((if limb = 0 then lo w else hi w : ℕ) : F) := by
  have e : ∀ z ∈ (List.range' (limb * 16) 16).reverse, g z = bitF (w.getLsbD z) := fun z hz => by
    simp only [List.mem_reverse, List.mem_range'] at hz
    exact h z (by omega)
  rw [List.foldl_ext _ (fun acc z => acc + acc + bitF (w.getLsbD z)) _ (fun acc z hz => by rw [e z hz]),
    foldl_double, mul_zero, zero_add,
    bitsum_limb w limb hl]

theorem pack_bits_le_eq (l : List F) :
    pack_bits_le fieldOps l = l.reverse.foldl (fun acc e => acc + acc + e) 0 := by
  unfold pack_bits_le
  cases l.reverse with
  | nil => rfl
  | cons x rest => simp [fieldOps, double]

theorem packF_eq {g : ℕ → F} {w : BitVec 32} (h : Holds g w) (limb : ℕ) (hl : limb < 2) :
    packF g limb = ((if limb = 0 then lo w else hi w : ℕ) : F) := by
  rw [packF, pack_word, pack_bits_le_eq, ← List.map_reverse, List.foldl_map]
  exact fold_limb h limb hl

/-! ## Bitwise formulas -/

theorem xor_bitF (a b : Bool) : xor fieldOps (bitF a : F) (bitF b) = bitF (a ^^ b) := by
  cases a <;> cases b <;> simp [p3_sha256_air.mirror.xor, fieldOps, double, bitF]

theorem xor3_bitF (a b c : Bool) :
    xor3 fieldOps (bitF a : F) (bitF b) (bitF c) = bitF (a ^^ b ^^ c) := by
  simp only [xor3, xor_bitF]

theorem ch_bitF (e f g : Bool) :
    (bitF e : F) * bitF f + (1 - bitF e) * bitF g = bitF ((e && f) ^^ (!e && g)) := by
  cases e <;> cases f <;> cases g <;> simp [bitF]

theorem maj_bitF (a b c : Bool) :
    (bitF a : F) * bitF b + bitF c * xor fieldOps (bitF a) (bitF b) =
      bitF ((a && b) ^^ (a && c) ^^ (b && c)) := by
  rw [xor_bitF]; cases a <;> cases b <;> cases c <;> simp [bitF]

theorem rotr_bit (x : BitVec 32) {r : ℕ} (hr : r < 32) {i : ℕ} (hi : i < 32) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  simp only [Nat.mod_eq_of_lt hr]
  split <;> rename_i h
  · congr 1; omega
  · simp only [hi, decide_true, Bool.true_and]; congr 1; omega

/-- The word a sigma function computes. -/
def sigmaWord : SigmaSpec → BitVec 32 → BitVec 32
  | .BigSigma0 => bigSigma0
  | .BigSigma1 => bigSigma1
  | .SmallSigma0 => smallSigma0
  | .SmallSigma1 => smallSigma1

theorem hmod {g : ℕ → F} {w : BitVec 32} (h : Holds g w) (n : ℕ) :
    g (n % 32) = bitF (w.getLsbD (n % 32)) := h _ (Nat.mod_lt _ (by norm_num))

theorem sigmaF_eq {g : ℕ → F} {w : BitVec 32} (h : Holds g w) (spec : SigmaSpec) (limb : ℕ)
    (hl : limb < 2) : sigmaF g spec limb = ((if limb = 0 then lo (sigmaWord spec w) else
      hi (sigmaWord spec w) : ℕ) : F) := by
  cases spec <;> simp only [sigmaF, sigma_params, BITS_PER_LIMB]
  · refine fold_limb (fun b hb => ?_) limb hl
    simp only [WORD_BITS, hmod h, xor3_bitF, sigmaWord, bigSigma0, BitVec.getLsbD_xor,
      rotr_bit w (by norm_num : 2 < 32) hb, rotr_bit w (by norm_num : 13 < 32) hb,
      rotr_bit w (by norm_num : 22 < 32) hb]
  · refine fold_limb (fun b hb => ?_) limb hl
    simp only [WORD_BITS, hmod h, xor3_bitF, sigmaWord, bigSigma1, BitVec.getLsbD_xor,
      rotr_bit w (by norm_num : 6 < 32) hb, rotr_bit w (by norm_num : 11 < 32) hb,
      rotr_bit w (by norm_num : 25 < 32) hb]
  · refine fold_limb (fun b hb => ?_) limb hl
    simp only [WORD_BITS, hmod h, sigmaWord, smallSigma0, BitVec.getLsbD_xor,
      rotr_bit w (by norm_num : 7 < 32) hb, rotr_bit w (by norm_num : 18 < 32) hb,
      BitVec.getLsbD_ushiftRight]
    by_cases h3 : b + 3 < 32
    · simp only [h3, ↓reduceIte, h _ h3, xor3_bitF, Nat.add_comm 3]
    · simp only [h3, ↓reduceIte]
      rw [show (0 : F) = bitF false by simp [bitF], xor3_bitF, BitVec.getLsbD_of_ge w (3 + b) (by omega)]
  · refine fold_limb (fun b hb => ?_) limb hl
    simp only [WORD_BITS, hmod h, sigmaWord, smallSigma1, BitVec.getLsbD_xor,
      rotr_bit w (by norm_num : 17 < 32) hb, rotr_bit w (by norm_num : 19 < 32) hb,
      BitVec.getLsbD_ushiftRight]
    by_cases h3 : b + 10 < 32
    · simp only [h3, ↓reduceIte, h _ h3, xor3_bitF, Nat.add_comm 10]
    · simp only [h3, ↓reduceIte]
      rw [show (0 : F) = bitF false by simp [bitF], xor3_bitF, BitVec.getLsbD_of_ge w (10 + b) (by omega)]

theorem chF_eq {e f g : ℕ → F} {we wf wg : BitVec 32} (he : Holds e we) (hf : Holds f wf)
    (hg : Holds g wg) (limb : ℕ) (hl : limb < 2) :
    chF e f g limb = ((if limb = 0 then lo (ch we wf wg) else hi (ch we wf wg) : ℕ) : F) := by
  refine fold_limb (fun b hb => ?_) limb hl
  rw [he b hb, hf b hb, hg b hb, ch_bitF]
  simp [ch, hb]

theorem majF_eq {a b c : ℕ → F} {wa wb wc : BitVec 32} (ha : Holds a wa) (hb : Holds b wb)
    (hc : Holds c wc) (limb : ℕ) (hl : limb < 2) :
    majF a b c limb = ((if limb = 0 then lo (maj wa wb wc) else hi (maj wa wb wc) : ℕ) : F) := by
  refine fold_limb (fun i hi => ?_) limb hl
  rw [ha i hi, hb i hi, hc i hi, maj_bitF]
  simp [maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]

end Plonky3Lean.Proofs.Sha256Air
