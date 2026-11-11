module

public import Plonky3Lean.Proofs.Sha256Air.Binary.Row
public import Plonky3Lean.Proofs.Sha256Air.GenSat

@[expose] public section

/-!
# Bitwise formulas in characteristic 2

On bits, in characteristic 2, the AIR's sums of rotated bits are the sigma functions.

Its Ch and Maj constraints make the witness columns the bits of Ch and Maj.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_sha256_air.mirror.binary Plonky3Lean.Spec.Sha256
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds rotr_bit)

variable {F : Type} [Field F] (h2 : (2 : F) = 0)
include h2

theorem holds_rot {x : ℕ → F} {X : BitVec 32} (hx : Holds x X) {r0 r1 r2 : ℕ} (h0 : r0 < 32)
    (h1 : r1 < 32) (h2' : r2 < 32) :
    Holds (xor3_rot fieldOps x r0 r1 r2) (X.rotateRight r0 ^^^ X.rotateRight r1 ^^^ X.rotateRight r2) := by
  intro b hb
  simp only [xor3_rot, rotr_index, fo_add, hx _ (Nat.mod_lt _ (by norm_num : 0 < 32)), add_bitF h2,
    BitVec.getLsbD_xor, rotr_bit X h0 hb, rotr_bit X h1 hb, rotr_bit X h2' hb]

theorem holds_shift {x : ℕ → F} {X : BitVec 32} (hx : Holds x X) {r0 r1 s : ℕ} (h0 : r0 < 32)
    (h1 : r1 < 32) : Holds (xor3_shift fieldOps x r0 r1 s) (X.rotateRight r0 ^^^ X.rotateRight r1 ^^^ X >>> s) := by
  intro b hb
  simp only [xor3_shift, rotr_index, fo_add, hx _ (Nat.mod_lt _ (by norm_num : 0 < 32)), add_bitF h2,
    BitVec.getLsbD_xor, rotr_bit X h0 hb, rotr_bit X h1 hb, BitVec.getLsbD_ushiftRight]
  split_ifs with hs
  · rw [hx _ hs, add_bitF h2, Nat.add_comm s]
  · rw [BitVec.getLsbD_of_ge X (s + b) (by omega), Bool.xor_false]

theorem holds_ch {e f g c : ℕ → F} {E Fw G : BitVec 32} (he : Holds e E) (hf : Holds f Fw)
    (hg : Holds g G) (h : ∀ i < 32, e i * (f i + g i) + g i + c i = 0) : Holds c (ch E Fw G) := by
  intro i hi
  have := eq_of_add_eq_zero h2 (h i hi)
  rw [← this, he i hi, hf i hi, hg i hi, add_bitF h2, mul_bitF, add_bitF h2]
  simp only [ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and]
  cases E.getLsbD i <;> cases Fw.getLsbD i <;> cases G.getLsbD i <;> rfl

theorem holds_maj {a b c m : ℕ → F} {A B C : BitVec 32} (ha : Holds a A) (hb : Holds b B)
    (hc : Holds c C) (h : ∀ i < 32, maj fieldOps (a i) (b i) (c i) + m i = 0) : Holds m (maj A B C) := by
  intro i hi
  have := eq_of_add_eq_zero h2 (h i hi)
  rw [← this, ha i hi, hb i hi, hc i hi, maj_bitF h2]
  simp only [Plonky3Lean.Spec.Sha256.maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;> rfl

end Plonky3Lean.Proofs.Sha256Air.Binary
