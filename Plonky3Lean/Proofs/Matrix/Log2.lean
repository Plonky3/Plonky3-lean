module

public import Plonky3Lean.Proofs.Matrix.BitRev
public import P3Matrix
public import Plonky3Lean.Lib.RustM

@[expose] public section

/-!
# p3-util: the strict logarithm and bit reversal

The strict base-2 logarithm of 2^k is k, and it panics on other inputs, 0 included.

Reversing the k low bits of x < 2^k gives rev_k(x).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open Plonky3Lean.Spec.Matrix Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Matrix

theorem trailing_zeros_two_pow {k : ℕ} (hk : k < UScalarTy.Usize.numBits) (n : Std.Usize)
    (hn : n.val = 2 ^ k) : core.num.Usize.trailing_zeros n ⦃ t => t.val = k ⦄ := by
  unfold core.num.Usize.trailing_zeros
  have : (List.range UScalarTy.Usize.numBits).find? (fun i => n.val.testBit i) = some k := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp [hn, Nat.testBit_two_pow_self], k, by simpa using hk, by simp,
      fun j hj => ?_⟩
    simp [hn, Nat.testBit_two_pow]; omega
  have hb : UScalarTy.Usize.numBits ≤ 64 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  simp only [this, Option.getD_some, WP.spec_ok]
  show (BitVec.ofNat 32 k).toNat = k
  rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
  calc k < 64 := by omega
    _ ≤ 2 ^ 32 := by norm_num

theorem numBits_le : UScalarTy.Usize.numBits ≤ 64 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

theorem numBits_ge : 32 ≤ UScalarTy.Usize.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

/-- The strict base-2 logarithm of 2^k is k. -/
theorem log2_strict_usize_two_pow {k : ℕ} (hk : k < UScalarTy.Usize.numBits) (n : Std.Usize)
    (hn : n.val = 2 ^ k) : p3_util.log2_strict_usize n ⦃ r => r.val = k ⦄ := by
  unfold p3_util.log2_strict_usize
  obtain ⟨t, ht, htv⟩ := spec_imp_exists (trailing_zeros_two_pow hk n hn)
  rw [ht, bind_ok]
  simp only [core.num.Usize.wrapping_shr, bind_ok]
  have hshr : Std.core.num.Usize.wrapping_shr n t = 1#usize := by
    apply UScalar.eq_of_val_eq
    have hk' : t.val % System.Platform.numBits = k := by rw [htv]; exact Nat.mod_eq_of_lt hk
    simp only [UScalar.val, Std.core.num.Usize.wrapping_shr_bv_eq]
    show (n.bv >>> (t.bv.toNat % System.Platform.numBits)).toNat = (1#usize).bv.toNat
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, UScalar.bv_toNat, hk', hn,
      Nat.shiftRight_eq_div_pow, Nat.div_self (by positivity)]
    rfl
  simp only [hshr, massert, ite_true, bind_ok]
  step*
  have hni : n = i1 := by
    apply UScalar.eq_of_val_eq
    rw [i1_post, hn, htv, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
    have : Usize.size = 2 ^ System.Platform.numBits := by simp [Usize.size, Usize.numBits]
    rw [this]; exact Nat.pow_lt_pow_right (by norm_num) hk
  simp only [hni, decide_true, core.hint.assert_unchecked, ite_true, bind_ok, WP.spec_ok]
  simp only [UScalar.cast_val_eq]
  rw [htv, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le hk (Nat.lt_two_pow_self).le

theorem usize_val_lt (n : Std.Usize) : n.val < 2 ^ UScalarTy.Usize.numBits := by
  have := n.hBounds; simpa [Usize.size, Usize.numBits, UScalarTy.numBits] using this

/-- The strict base-2 logarithm panics unless its input is a power of two, 0 included. -/
theorem shr_trailing_ne_one (n : Std.Usize) (hn : ∀ k, n.val ≠ 2 ^ k) (o : Option ℕ)
    (hf : List.find? (fun i => n.val.testBit i) (List.range System.Platform.numBits) = o) :
    Std.core.num.Usize.wrapping_shr n ⟨BitVec.ofNat 32 (o.getD System.Platform.numBits)⟩
      ≠ 1#usize := by
    have hN := numBits_le
    have hN' : System.Platform.numBits ≤ 64 := hN
    intro heq
    have hv := congrArg UScalar.val heq
    simp only [UScalar.val, Std.core.num.Usize.wrapping_shr_bv_eq] at hv
    change (n.bv >>> ((BitVec.ofNat 32 (o.getD System.Platform.numBits)).toNat %
      System.Platform.numBits)).toNat = (1#usize).bv.toNat at hv
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, UScalar.bv_toNat] at hv
    cases o with
    | none =>
      have h0 : n.val = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        by_cases hi : i < System.Platform.numBits
        · have := List.find?_eq_none.mp hf i (by simpa using hi); simpa using this
        · simp only [Nat.zero_testBit]
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (usize_val_lt n)
            (Nat.pow_le_pow_right (by omega) (by simpa [UScalarTy.numBits] using hi)))
      rw [h0] at hv; simp at hv
    | some j =>
      rw [List.find?_eq_some_iff_getElem] at hf
      obtain ⟨hj, i, hi, hij, hmin⟩ := hf
      simp only [List.getElem_range] at hij
      subst hij
      simp only [List.length_range] at hi
      have hjv : (BitVec.ofNat 32 i).toNat % System.Platform.numBits = i := by
        have h32 : i < 2 ^ 32 := by omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
        exact Nat.mod_eq_of_lt hi
      have h1 : (1#usize : Std.Usize).val = 1 := by simp
      rw [Option.getD_some, hjv, Nat.shiftRight_eq_div_pow, h1] at hv
      apply hn i
      apply Nat.eq_of_testBit_eq; intro b
      rw [Nat.testBit_two_pow]
      by_cases hb : b < i
      · have := hmin b hb; simp only [List.getElem_range] at this
        simp [show i ≠ b by omega]; simpa using this
      · have := Nat.testBit_div_two_pow n.val (b - i) (n := i)
        rw [hv, show b - i + i = b by omega] at this
        rw [← this, show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
        by_cases hbi : b = i
        · simp [hbi]
        · simp [show b - i ≠ 0 by omega, show i ≠ b by omega]

/-- The strict base-2 logarithm panics unless its input is a power of two, 0 included. -/
theorem log2_strict_usize_panics (n : Std.Usize) (hn : ∀ k, n.val ≠ 2 ^ k) :
    p3_util.log2_strict_usize n = fail .panic := by
  unfold p3_util.log2_strict_usize core.num.Usize.trailing_zeros
  simp only [bind_ok, core.num.Usize.wrapping_shr, massert]
  split
  · rename_i h; exact absurd h (shr_trailing_ne_one n hn _ rfl)
  · simp

/-- Reversing the k low bits of x < 2^k gives rev_k(x), for k at most the word size. -/
theorem reverse_bits_len_eq (x k : Std.Usize) (hk : k.val ≤ UScalarTy.Usize.numBits)
    (hx : x.val < 2 ^ k.val) :
    p3_util.reverse_bits_len x k ⦃ y => y.val = bitRev k.val x.val ⦄ := by
  unfold p3_util.reverse_bits_len
  simp only [core.num.Usize.reverse_bits, core.num.Usize.overflowing_shr, bind_ok]
  have hN := numBits_le
  step*
  have hi2 : i2.val = k.val := by
    rw [i2_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by
      calc k.val ≤ 64 := by omega
        _ < 2 ^ UScalarTy.U32.numBits := by simp [UScalarTy.numBits])
  have hsh : i3.val % System.Platform.numBits = (System.Platform.numBits - k.val) %
      System.Platform.numBits := by rw [i3_post, hi2]; rfl
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitRev]
  simp only [UScalar.val, Std.core.num.Usize.wrapping_shr_bv_eq]
  change (x.bv.reverse >>> (i3.bv.toNat % System.Platform.numBits)).toNat.testBit j = _
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight, UScalar.bv_toNat, hsh]
  simp only [UScalar.bv_toNat]
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  have hN' : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
  rcases Nat.eq_zero_or_pos k.val with h0 | h0
  · have hx0 : x.val = 0 := by rw [h0] at hx; omega
    simp [h0, BitVec.getLsbD, UScalar.bv_toNat, hx0]
  · rw [Nat.mod_eq_of_lt (by omega), BitVec.getLsbD, UScalar.bv_toNat]
    by_cases hj : j < k.val
    · simp [hj, show System.Platform.numBits - k.val + j < System.Platform.numBits by omega,
        show System.Platform.numBits - 1 - (System.Platform.numBits - k.val + j) = k.val - 1 - j
          by omega]
    · simp [hj, show ¬ System.Platform.numBits - k.val + j < System.Platform.numBits by omega]

end Plonky3Lean.Proofs.Matrix
