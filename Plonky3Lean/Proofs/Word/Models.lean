module

public import Plonky3Lean.Proofs.Word.System

@[expose] public section

/-!
# The two word widths as models

At 32 and at 64 bits, every operation of the word instance is a plain function on bit vectors.

A term is valid when neither of its two movements panics.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

/-- The full product of two 32-bit words, as its low and high words. -/
def mul32 (a b : word.Word32) : word.Word32 × word.Word32 :=
  (⟨BitVec.ofNat 32 (a.val * b.val)⟩, ⟨BitVec.ofNat 32 (a.val * b.val / 2 ^ 32)⟩)

/-- The full product of two 64-bit words, as its low and high words. -/
def mul64 (a b : word.Word64) : word.Word64 × word.Word64 :=
  (⟨BitVec.ofNat 64 (a.val * b.val)⟩, ⟨BitVec.ofNat 64 (a.val * b.val / 2 ^ 64)⟩)

theorem wide_mul32_eq (a b : word.Word32) :
    word.Word32.Insts.P3_wordWordSealedSealed.wide_mul a b = .ok (mul32 a b) := by
  obtain ⟨lo, hi, h, hl, hh⟩ := W32.wide_mul_spec a b
  rw [h]
  congr 2 <;> apply UScalar.eq_of_val_eq
  · rw [hl]; show _ = (BitVec.ofNat 32 _).toNat; simp
  · rw [hh]; show _ = (BitVec.ofNat 32 _).toNat; simp
    have ha : a.val < 2 ^ 32 := a.hBounds
    have hb : b.val < 2 ^ 32 := b.hBounds
    exact (Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)).symm

theorem wide_mul64_eq (a b : word.Word64) :
    word.Word64.Insts.P3_wordWordSealedSealed.wide_mul a b = .ok (mul64 a b) := by
  obtain ⟨lo, hi, h, hl, hh⟩ := W64.wide_mul_spec a b
  rw [h]
  congr 2 <;> apply UScalar.eq_of_val_eq
  · rw [hl]; show _ = (BitVec.ofNat 64 _).toNat; simp
  · rw [hh]; show _ = (BitVec.ofNat 64 _).toNat; simp
    have ha : a.val < 2 ^ 64 := a.hBounds
    have hb : b.val < 2 ^ 64 := b.hBounds
    exact (Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)).symm

/-- The 32-bit word instance, as plain functions on bit vectors. -/
def M32 : Model I32w where
  zero := 0#u32
  xorf a b := ⟨a.bv ^^^ b.bv⟩
  andf a b := ⟨a.bv &&& b.bv⟩
  mulf := mul32
  term t w := ⟨sem32 (svOuter t).kind (svOuter t).amount.val
    (sem32 (svInner t).kind (svInner t).amount.val w.bv)⟩
  valid t := ¬ panics32 (svInner t).kind (svInner t).amount.val ∧
    ¬ panics32 (svOuter t).kind (svOuter t).amount.val
  hzero := by show RustM.ok _ = _; unfold word.Word32.Insts.P3_wordWordWord.ZERO; rfl
  hxor := W32.xor_eq
  hand := W32.and_eq
  hmul := wide_mul32_eq
  heq _ _ := rfl
  happly t w h := by rw [sv_apply32_eq, ite_eq_right (by tauto)]

/-- The 64-bit word instance, as plain functions on bit vectors. -/
def M64 : Model I64w where
  zero := 0#u64
  xorf a b := ⟨a.bv ^^^ b.bv⟩
  andf a b := ⟨a.bv &&& b.bv⟩
  mulf := mul64
  term t w := ⟨sem64 (svOuter t).kind (svOuter t).amount.val
    (sem64 (svInner t).kind (svInner t).amount.val w.bv)⟩
  valid t := ¬ panics64 (svInner t).kind (svInner t).amount.val ∧
    ¬ panics64 (svOuter t).kind (svOuter t).amount.val
  hzero := by show RustM.ok _ = _; unfold word.Word64.Insts.P3_wordWordWord.ZERO; rfl
  hxor := W64.xor_eq
  hand := W64.and_eq
  hmul := wide_mul64_eq
  heq _ _ := rfl
  happly t w h := by rw [sv_apply64_eq, ite_eq_right (by tauto)]

theorem ofNat32_val (n : ℕ) : (⟨BitVec.ofNat 32 n⟩ : word.Word32).val = n % 2 ^ 32 :=
  BitVec.toNat_ofNat _ _

theorem ofNat64_val (n : ℕ) : (⟨BitVec.ofNat 64 n⟩ : word.Word64).val = n % 2 ^ 64 :=
  BitVec.toNat_ofNat _ _

/-- The product relation at 32 bits is the integer identity `a * b = lo + 2^32 * hi`. -/
theorem mul32_iff (a b lo hi : word.Word32) :
    mul32 a b = (lo, hi) ↔ a.val * b.val = lo.val + 2 ^ 32 * hi.val := by
  have hl : lo.val < 2 ^ 32 := lo.hBounds
  have hh : hi.val < 2 ^ 32 := hi.hBounds
  have hab : a.val * b.val < 2 ^ 64 := by
    have : a.val < 2 ^ 32 := a.hBounds
    have : b.val < 2 ^ 32 := b.hBounds
    nlinarith
  simp only [mul32, Prod.mk.injEq, UScalar.eq_equiv, ofNat32_val]
  generalize a.val * b.val = n at hab ⊢
  omega

/-- The product relation at 64 bits is the integer identity `a * b = lo + 2^64 * hi`. -/
theorem mul64_iff (a b lo hi : word.Word64) :
    mul64 a b = (lo, hi) ↔ a.val * b.val = lo.val + 2 ^ 64 * hi.val := by
  have hl : lo.val < 2 ^ 64 := lo.hBounds
  have hh : hi.val < 2 ^ 64 := hi.hBounds
  have hab : a.val * b.val < 2 ^ 128 := by
    have : a.val < 2 ^ 64 := a.hBounds
    have : b.val < 2 ^ 64 := b.hBounds
    nlinarith
  simp only [mul64, Prod.mk.injEq, UScalar.eq_equiv, ofNat64_val]
  generalize a.val * b.val = n at hab ⊢
  omega

end Plonky3Lean.Proofs.Word
