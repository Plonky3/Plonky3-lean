module

public import Plonky3Lean.Proofs.Field.Binary.Ghash
public import Plonky3Lean.Proofs.Field.Binary.Statements
public import Plonky3Lean.Proofs.Field.Binary.Extension

@[expose] public section

/-!
# The change of basis between the tower and a polynomial basis

`clmul::basis` relates the tower's basis to the polynomial basis `1, x, …, x^(n-1)` of
`GF(2)[x] / (x^n + tail)`. This file proves the arithmetic it is built from.

`poly_mul` multiplies in `GF(2)[x] / (x^n + tail)` bit-serially, from the top bit of the second
operand down: each round multiplies by `x`, folds the bit leaving the top back in as `tail`, and
adds the first operand when the current bit is set.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The modulus `x^n + tail`. -/
noncomputable def modPoly (n tail : ℕ) : (ZMod 2)[X] := X ^ n + natPoly tail

/-- Multiplying by `x`: shift, and fold the bit leaving the top back in as `tail`. -/
theorem mk_shift_fold {n tail acc : ℕ} (hn : 1 ≤ n) (hacc : acc < 2 ^ n) :
    AdjoinRoot.mk (modPoly n tail)
      (natPoly ((acc <<< 1) % 2 ^ n ^^^ (if acc.testBit (n - 1) then tail else 0))) =
      AdjoinRoot.mk (modPoly n tail) (X * natPoly acc) := by
  have hsplit := natPoly_split (acc <<< 1) n
  rw [natPoly_shiftLeft, pow_one] at hsplit
  have htop : (acc <<< 1) >>> n = if acc.testBit (n - 1) then 1 else 0 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2, mul_comm acc 2, Nat.mul_div_mul_left _ _ (by norm_num), Nat.testBit_eq_decide_div_mod_eq]
    have hlt : acc / 2 ^ (n - 1) < 2 := Nat.div_lt_of_lt_mul (by rw [mul_comm, ← h2]; exact hacc)
    generalize acc / 2 ^ (n - 1) = q at hlt ⊢
    interval_cases q <;> simp
  rw [htop] at hsplit
  rw [natPoly_xor, AdjoinRoot.mk_eq_mk]
  unfold modPoly
  by_cases ht : acc.testBit (n - 1)
  · simp only [ht, ↓reduceIte, natPoly_one, mul_one] at hsplit ⊢
    exact ⟨1, by linear_combination (-1 : (ZMod 2)[X]) * hsplit + (-X ^ n) * ZMod2Poly.two_eq_zero⟩
  · simp only [ht, Bool.false_eq_true, ↓reduceIte, natPoly_zero, mul_zero, zero_add] at hsplit ⊢
    exact ⟨0, by rw [hsplit]; ring⟩

/-- The bits of `b` from `i - 1` up are those from `i` up, times `x`, plus bit `i - 1`. -/
theorem natPoly_shiftRight_pred (b i : ℕ) (hi : 1 ≤ i) :
    natPoly (b >>> (i - 1)) = X * natPoly (b >>> i) + (if b.testBit (i - 1) then 1 else 0) := by
  rw [natPoly_split (b >>> (i - 1)) 1, pow_one, ← Nat.shiftRight_add, Nat.sub_add_cancel hi]
  have h : (b >>> (i - 1)) % 2 ^ 1 = if b.testBit (i - 1) then 1 else 0 := by
    rw [pow_one, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ (i - 1)) with h | h <;> simp [h]
  rw [h]
  split_ifs <;> simp [natPoly_one, natPoly_zero]

theorem poly_mul_loop_spec (a b tail mask top : Std.U128) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 128)
    (hmask : mask.val = 2 ^ n - 1) (htop : top.val = 2 ^ (n - 1)) (ha : a.val < 2 ^ n)
    (ht : tail.val < 2 ^ n) (acc : Std.U128) (i : Std.Usize) (hi : i.val ≤ n)
    (hacc : acc.val < 2 ^ n)
    (hinv : AdjoinRoot.mk (modPoly n tail.val) (natPoly acc.val) =
      AdjoinRoot.mk (modPoly n tail.val) (natPoly a.val * natPoly (b.val >>> i.val))) :
    clmul.basis.poly_mul_loop a b tail mask top acc i ⦃ r => r.val < 2 ^ n ∧
      AdjoinRoot.mk (modPoly n tail.val) (natPoly r.val) =
        AdjoinRoot.mk (modPoly n tail.val) (natPoly a.val * natPoly b.val) ⦄ := by
  unfold clmul.basis.poly_mul_loop
  refine loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ n ∧ p.1.val < 2 ^ n ∧
      AdjoinRoot.mk (modPoly n tail.val) (natPoly p.1.val) =
        AdjoinRoot.mk (modPoly n tail.val) (natPoly a.val * natPoly (b.val >>> p.2.val))) _ _ _ ?_
    ⟨hi, hacc, hinv⟩
  rintro ⟨ac, k⟩ ⟨hk, hac, hinv⟩
  dsimp only at hk hac hinv ⊢
  unfold clmul.basis.poly_mul_loop.body
  step*
  case h2 =>
    have hk0 : k.val = 0 := by
      have := ‹¬k > 0#usize›
      simp only [gt_iff_lt, not_lt] at this
      have : k.val ≤ 0 := this
      omega
    rw [hk0, Nat.shiftRight_zero] at hinv
    exact ⟨hac, hinv⟩
  have hacc1 : acc1.val = (ac.val <<< 1) % 2 ^ n := by
    rw [acc1_post, UScalar.val_and, i3_post, hmask, Nat.and_two_pow_sub_one_eq_mod,
      show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)]
  have hi2 : (i2 != 0#u128) = ac.val.testBit (n - 1) := by
    have hv : i2.val = ac.val &&& 2 ^ (n - 1) := by rw [i2_post, UScalar.val_and, htop]
    have hz : ac.val &&& 2 ^ (n - 1) = if ac.val.testBit (n - 1) then 2 ^ (n - 1) else 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      split_ifs with h
      · rw [Nat.testBit_two_pow]; by_cases hj : n - 1 = j
        · subst hj; simp [h]
        · simp [hj]
      · simp only [Nat.zero_testBit]; by_cases hj : n - 1 = j
        · subst hj; simp at h; simp [h]
        · simp [hj]
    cases htb : ac.val.testBit (n - 1)
    · have : i2 = 0#u128 := UScalar.eq_of_val_eq (by rw [hv, hz, htb]; rfl)
      simp [this]
    · have : i2.val ≠ 0 := by rw [hv, hz, htb]; simp
      have : i2 ≠ 0#u128 := fun h => this (by rw [h]; rfl)
      simp [this]
  rw [hi2]
  have hk1 : 1 ≤ k.val := i1_post1
  have hfold := mk_shift_fold (tail := tail.val) hn1 hac
  have hbit := natPoly_shiftRight_pred b.val k.val hk1
  have hfl : (ac.val <<< 1) % 2 ^ n ^^^ (if ac.val.testBit (n - 1) then tail.val else 0) < 2 ^ n :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (by split_ifs <;> simp_all)
  refine WP.spec_bind (Pₘ := fun c => c.val =
    (ac.val <<< 1) % 2 ^ n ^^^ (if ac.val.testBit (n - 1) then tail.val else 0)) ?_
    fun acc2 h2 => ?_
  · split
    · rw [WP.spec_ok, UScalar.val_xor, hacc1]
    · rw [WP.spec_ok, hacc1]; simp_all
  rw [← h2] at hfold hfl
  have hb5' : ∀ i4 i5 : Std.U128, i4.val = b.val >>> (k.val - 1) → i5.val = (i4 &&& 1#u128).val →
      i5.val = if b.val.testBit (k.val - 1) then 1 else 0 := fun i4 i5 h4 h5 => by
    rw [h5, UScalar.val_and, h4, show (1#u128 : Std.U128).val = 1 from rfl]
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (b.val / 2 ^ (k.val - 1)) with h | h <;> simp [h]
  step*
  case h2 =>
    have hb5 := hb5' i4 i5 (by rw [i4_post, i1_post]) i5_post
    have h5 := ‹¬i5 = 1#u128›
    have htb : b.val.testBit (k.val - 1) = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [hc] at hb5
      exact h5 (UScalar.eq_of_val_eq (by rw [hb5]; rfl))
    refine ⟨by omega, hfl, ?_, by omega⟩
    rw [i1_post, hbit, htb]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, map_mul] at hfold hinv ⊢
    linear_combination hfold + (AdjoinRoot.mk (modPoly n tail.val) X) * hinv
  have hb5 := hb5' i4 i5 (by rw [i4_post, i1_post]) i5_post
  have h5 := ‹i5 = 1#u128›
  have htb : b.val.testBit (k.val - 1) = true := by
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    rw [hc, h5] at hb5
    exact absurd hb5 (by decide)
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [acc3_post, UScalar.val_xor]; exact Nat.xor_lt_two_pow hfl ha
  · rw [acc3_post, UScalar.val_xor, natPoly_xor, i1_post, hbit, htb]
    simp only [↓reduceIte, map_add, map_mul, map_one] at hfold hinv ⊢
    linear_combination hfold + (AdjoinRoot.mk (modPoly n tail.val) X) * hinv

/-- `poly_mul a b n tail` is the product of `a` and `b` in `GF(2)[x] / (x^n + tail)`. -/
theorem poly_mul_spec (a b tail : Std.U128) (bits : Std.Usize) (h1 : 1 ≤ bits.val)
    (h128 : bits.val ≤ 128) (ha : a.val < 2 ^ bits.val) (hb : b.val < 2 ^ bits.val)
    (ht : tail.val < 2 ^ bits.val) :
    clmul.basis.poly_mul a b bits tail ⦃ r => r.val < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly r.val) =
        AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly a.val * natPoly b.val) ⦄ := by
  unfold clmul.basis.poly_mul
  step*
  refine poly_mul_loop_spec a b tail mask top bits.val h1 h128 ?_ ?_ ha ht 0#u128 bits le_rfl
    (by simp) ?_
  · rw [mask_post, i_post, show U128.rMax = 2 ^ 128 - 1 from rfl, two_pow_sub_one_shiftRight]
    congr 2; omega
  · rw [top_post, i1_post, Nat.one_shiftLeft,
      show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  · rw [show (0#u128 : Std.U128).val = 0 from rfl, natPoly_zero,
      (shiftRight_eq_zero_iff_lt _ _).mpr hb, natPoly_zero, mul_zero]

end Plonky3Lean.Proofs.Binary
