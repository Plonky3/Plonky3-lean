import CompPoly.Fields.Binary.BF128Ghash.Impl
import Mathlib.FieldTheory.Finite.Basic
import Plonky3Lean.Proofs.Field.Binary.Compact

/-!
# `GF(2^128)` modulo the GHASH polynomial

The portable multiplication, squaring and scaling of p3-binary-field's `Ghash128`, against
CompPoly's `BF128Ghash`.

- A 256-bit product reduces in two folds of `x^128 = x^7 + x^2 + x + 1`.
- The first fold spills the top seven bits over `x^128`, and the second lands below `x^14`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## Truncated shifts -/

theorem shiftLeft_shiftRight_of_le (H k w : ℕ) (hk : k ≤ w) :
    (H <<< k) >>> w = H >>> (w - k) := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [show w = (w - k) + k by omega, pow_add, Nat.mul_div_mul_right _ _ (by positivity)]

/-- A shift truncated to `w` bits drops the terms that crossed `X ^ w`. -/
theorem natPoly_shiftLeft_mod (H k w : ℕ) (hk : k ≤ w) :
    natPoly ((H <<< k) % 2 ^ w) = X ^ k * natPoly H + X ^ w * natPoly (H >>> (w - k)) := by
  have h := natPoly_split (H <<< k) w
  rw [natPoly_shiftLeft, shiftLeft_shiftRight_of_le H k w hk] at h
  linear_combination (-1 : (ZMod 2)[X]) * h -
    X ^ w * natPoly (H >>> (w - k)) * ZMod2Poly.two_eq_zero

/-! ## The reduction -/

/-- The value `reduce_128` computes, on natural numbers. -/
def reduce128Nat (L H : ℕ) : ℕ :=
  let folded := (H <<< 7) % 2 ^ 128 ^^^ (H <<< 2) % 2 ^ 128 ^^^ (H <<< 1) % 2 ^ 128 ^^^ H
  let spill := H >>> 121 ^^^ H >>> 126 ^^^ H >>> 127
  L ^^^ folded ^^^
    ((spill <<< 7) % 2 ^ 128 ^^^ (spill <<< 2) % 2 ^ 128 ^^^ (spill <<< 1) % 2 ^ 128 ^^^ spill)

theorem reduce128Nat_lt {L H : ℕ} (hL : L < 2 ^ 128) (hH : H < 2 ^ 128) :
    reduce128Nat L H < 2 ^ 128 := by
  have hs : H >>> 121 ^^^ H >>> 126 ^^^ H >>> 127 < 2 ^ 128 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.shiftRight_le _ _) hH)
      (lt_of_le_of_lt (Nat.shiftRight_le _ _) hH)) (lt_of_le_of_lt (Nat.shiftRight_le _ _) hH)
  unfold reduce128Nat
  simp only
  repeat' apply Nat.xor_lt_two_pow
  all_goals first
    | assumption
    | exact Nat.mod_lt _ (by norm_num)
    | exact lt_of_le_of_lt (Nat.shiftRight_le _ _) hH

/-- `reduce_128` never panics and returns the reduction. -/
theorem reduce_128_eq (low high : Std.U128) :
    clmul.reduce_128 low high = .ok ⟨BitVec.ofNat 128 (reduce128Nat low.val high.val)⟩ := by
  unfold clmul.reduce_128
  simp (disch := decide) only [shiftLeft_i32_eq, shiftRight_i32_eq, lift_eq, bind_tc_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, xor_bv, BitVec.toNat_xor, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, UScalarTy.U128_numBits_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (reduce128Nat_lt low.bv.isLt high.bv.isLt)]
  rfl

/-- The spill: the coefficients of `H · tail` from `X ^ 128` up. -/
def spillNat (H : ℕ) : ℕ := H >>> 121 ^^^ H >>> 126 ^^^ H >>> 127

theorem spillNat_lt {H : ℕ} (hH : H < 2 ^ 128) : spillNat H < 2 ^ 7 := by
  unfold spillNat
  apply Nat.xor_lt_two_pow (Nat.xor_lt_two_pow _ _) <;>
    rw [Nat.shiftRight_eq_div_pow] <;> apply Nat.div_lt_of_lt_mul <;> rw [← pow_add] <;>
    exact lt_of_lt_of_le hH (Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- The reduction adds a multiple of the GHASH polynomial to `L + X ^ 128 · H`. -/
theorem natPoly_reduce128Nat {L H : ℕ} (hH : H < 2 ^ 128) :
    natPoly (reduce128Nat L H) =
      natPoly L + natPoly H * ghashTail + natPoly (spillNat H) * ghashPoly := by
  have hs := spillNat_lt hH
  have hk : ∀ k ≤ 7, (spillNat H <<< k) % 2 ^ 128 = spillNat H <<< k := by
    intro k hk
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc spillNat H * 2 ^ k < 2 ^ 7 * 2 ^ 7 :=
          Nat.mul_lt_mul_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) hk) (by positivity)
      _ ≤ 2 ^ 128 := by norm_num
  unfold reduce128Nat
  simp only
  rw [show H >>> 121 ^^^ H >>> 126 ^^^ H >>> 127 = spillNat H from rfl, hk 7 (by norm_num),
    hk 2 (by norm_num), hk 1 (by norm_num)]
  simp only [natPoly_xor, natPoly_shiftLeft, natPoly_shiftLeft_mod H _ 128 (by norm_num : 7 ≤ 128),
    natPoly_shiftLeft_mod H _ 128 (by norm_num : 2 ≤ 128),
    natPoly_shiftLeft_mod H _ 128 (by norm_num : 1 ≤ 128), spillNat, ghashTail,
    ghashPoly_eq_X_pow_add_tail]
  norm_num
  ring

/-- In `GF(2)[x] / (ghashPoly)`, the reduction is `L + X ^ 128 · H`. -/
theorem mk_natPoly_reduce128Nat {L H : ℕ} (hH : H < 2 ^ 128) :
    AdjoinRoot.mk ghashPoly (natPoly (reduce128Nat L H)) =
      AdjoinRoot.mk ghashPoly (natPoly L + X ^ 128 * natPoly H) := by
  rw [AdjoinRoot.mk_eq_mk, natPoly_reduce128Nat hH, ghashPoly_eq_X_pow_add_tail]
  exact ⟨natPoly H + natPoly (spillNat H), by
    linear_combination (-(X ^ 128 * natPoly H)) * ZMod2Poly.two_eq_zero⟩

end Plonky3Lean.Proofs.Binary

namespace Plonky3Lean.Proofs.Binary

theorem mod_128_of_lt_64 {x : ℕ} (h : x < 2 ^ 64) : x % 2 ^ 128 = x :=
  Nat.mod_eq_of_lt (lt_trans h (by norm_num))

theorem shiftLeft_64_mod_128 {x : ℕ} (h : x < 2 ^ 64) : (x <<< 64) % 2 ^ 128 = x <<< 64 := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  calc x * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right h (by positivity)
    _ = 2 ^ 128 := by norm_num

theorem lt_64_of_xor {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x ^^^ y < 2 ^ 64 :=
  Nat.xor_lt_two_pow hx hy

/-- `wide_mul_128` never panics and returns the 256-bit carry-less product, by Karatsuba. -/
theorem wide_mul_128_spec (a b : Std.U128) :
    ∃ lo hi : Std.U128, clmul.portable.wide_mul_128 a b = .ok (lo, hi) ∧
      natPoly lo.val + X ^ 128 * natPoly hi.val = natPoly a.val * natPoly b.val := by
  unfold clmul.portable.wide_mul_128
  simp (disch := decide) only [clmul_64x64_halves_eq, shiftLeft_i32_eq, shiftRight_i32_eq, lift_eq,
    bind_tc_ok]
  refine ⟨_, _, rfl, ?_⟩
  simp only [UScalar.val, or_bv, xor_bv, cast_bv, BitVec.toNat_or, BitVec.toNat_xor,
    BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, show I32.toNat 64#i32 = 64 from rfl]
  have ha := natPoly_split a.bv.toNat 64
  have hb := natPoly_split b.bv.toNat 64
  have hA1 : a.bv.toNat >>> 64 % 2 ^ 64 = a.bv.toNat >>> 64 :=
    Nat.mod_eq_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by
      have := a.bv.isLt; norm_num at this ⊢; omega))
  have hB1 : b.bv.toNat >>> 64 % 2 ^ 64 = b.bv.toNat >>> 64 :=
    Nat.mod_eq_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by
      have := b.bv.isLt; norm_num at this ⊢; omega))
  have eA0 : (BitVec.setWidth 64 a.bv).toNat = a.bv.toNat % 2 ^ 64 := BitVec.toNat_setWidth _ _
  have eB0 : (BitVec.setWidth 64 b.bv).toNat = b.bv.toNat % 2 ^ 64 := BitVec.toNat_setWidth _ _
  have eA1 : (BitVec.setWidth 64 (a.bv >>> 64)).toNat = a.bv.toNat >>> 64 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hA1]
  have eB1 : (BitVec.setWidth 64 (b.bv >>> 64)).toNat = b.bv.toNat >>> 64 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hB1]
  rw [hA1, hB1, ← eA0, ← eB0, ← eA1, ← eB1, ← BitVec.toNat_xor, ← BitVec.toNat_xor, ha, hb,
    ← eA0, ← eB0, ← eA1, ← eB1]
  clear ha hb hA1 hB1 eA0 eB0 eA1 eB1
  generalize BitVec.setWidth 64 a.bv = A0
  generalize BitVec.setWidth 64 b.bv = B0
  generalize BitVec.setWidth 64 (a.bv >>> 64) = A1
  generalize BitVec.setWidth 64 (b.bv >>> 64) = B1
  have hL := natPoly_halves A0 B0
  have hH := natPoly_halves A1 B1
  have hM := natPoly_halves (A0 ^^^ A1) (B0 ^^^ B1)
  have l0 := bmulNat_lt A0.toNat B0.toNat
  have l1 := highNat_lt A0 B0
  have h0 := bmulNat_lt A1.toNat B1.toNat
  have h1 := highNat_lt A1 B1
  have m0 := bmulNat_lt (A0 ^^^ A1).toNat (B0 ^^^ B1).toNat
  have m1 := highNat_lt (A0 ^^^ A1) (B0 ^^^ B1)
  generalize bmulNat A0.toNat B0.toNat = L0 at *
  generalize highNat A0 B0 = L1 at *
  generalize bmulNat A1.toNat B1.toNat = H0 at *
  generalize highNat A1 B1 = H1 at *
  generalize bmulNat (A0 ^^^ A1).toNat (B0 ^^^ B1).toNat = M0 at *
  generalize highNat (A0 ^^^ A1) (B0 ^^^ B1) = M1 at *
  rw [BitVec.toNat_xor, BitVec.toNat_xor, natPoly_xor, natPoly_xor] at hM
  simp only [Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt m0, Nat.mod_eq_of_lt m1]
  rw [mod_128_of_lt_64 l0, mod_128_of_lt_64 h1, shiftLeft_64_mod_128 h1,
    mod_128_of_lt_64 (lt_64_of_xor l1 (lt_64_of_xor (lt_64_of_xor m0 l0) h0)),
    shiftLeft_64_mod_128 (lt_64_of_xor l1 (lt_64_of_xor (lt_64_of_xor m0 l0) h0)),
    mod_128_of_lt_64 (lt_64_of_xor h0 (lt_64_of_xor (lt_64_of_xor m1 l1) h1)),
    natPoly_or_shiftLeft l0,
    natPoly_or_shiftLeft (lt_64_of_xor h0 (lt_64_of_xor (lt_64_of_xor m1 l1) h1))]
  simp only [natPoly_xor]
  linear_combination hL + X ^ 128 * hH + X ^ 64 * (hM + hL + hH) +
    X ^ 64 * (natPoly A0.toNat * natPoly B0.toNat + natPoly A1.toNat * natPoly B1.toNat) *
      ZMod2Poly.two_eq_zero

/-! ## The product -/

/-- In `GF(2)[x] / (ghashPoly)`, an integer is the element `toQuot` reads it as. -/
theorem toQuot_eq_mk (x : Std.U128) :
    toQuot x.bv = AdjoinRoot.mk ghashPoly (natPoly x.val) := by
  rw [toQuot, toPoly_eq_natPoly]
  rfl

/-- A reduced pair `(low, high)` is the element `low + X ^ 128 · high`. -/
theorem reduce_128_toQuot (low high : Std.U128) :
    clmul.reduce_128 low high ⦃ r =>
      toQuot r.bv = AdjoinRoot.mk ghashPoly (natPoly low.val + X ^ 128 * natPoly high.val) ⦄ := by
  rw [reduce_128_eq, WP.spec_ok, toQuot_eq_mk, ← mk_natPoly_reduce128Nat (u128_val_lt high)]
  congr 2
  show (BitVec.ofNat 128 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (reduce128Nat_lt (u128_val_lt _) (u128_val_lt _))]

/-- `poly_mul_128` never panics and multiplies in `GF(2)[x] / (ghashPoly)`. -/
theorem poly_mul_128_toQuot (a b : Std.U128) :
    clmul.portable.poly_mul_128 a b ⦃ r => toQuot r.bv = toQuot a.bv * toQuot b.bv ⦄ := by
  obtain ⟨lo, hi, e, hp⟩ := wide_mul_128_spec a b
  unfold clmul.portable.poly_mul_128
  refine spec_bind_pair_of_eq e ?_
  apply WP.spec_mono (reduce_128_toQuot lo hi)
  intro r hr
  rw [hr, hp, toQuot_eq_mk, toQuot_eq_mk, map_mul]

/-- The reduced product is CompPoly's: the result is determined by its image in the field. -/
theorem eq_of_toQuot (r : Std.U128) (x : ConcreteBF128Ghash) (h : toQuot r.bv = toQuot x) :
    r.bv = x :=
  toQuot_injective h

/-- `poly_mul_128` never panics and returns CompPoly's product in `ConcreteBF128Ghash`. -/
theorem poly_mul_128_spec (a b : Std.U128) :
    clmul.portable.poly_mul_128 a b ⦃ r => r.bv = reduce_clMul (clMul a.bv b.bv) ⦄ := by
  apply WP.spec_mono (poly_mul_128_toQuot a b)
  intro r hr
  apply toQuot_injective
  rw [hr]
  exact (toQuot_mul a.bv b.bv).symm

/-! ## Squaring -/

/-- One round of the bit spread: chunks of `2 s` bits split into chunks of `s`. -/
theorem spread_round (s : ℕ) (hs : s = 32 ∨ s = 16 ∨ s = 8 ∨ s = 4 ∨ s = 2 ∨ s = 1)
    {x v M : ℕ}
    (hx : ∀ k < 128, x.testBit k =
      (decide (k / (2 * s) % 2 = 0) && v.testBit (k / (4 * s) * (2 * s) + k % (2 * s))))
    (hM : ∀ k < 128, M.testBit k = decide (k / s % 2 = 0)) :
    ∀ k < 128, ((x ||| (x <<< s) % 2 ^ 128) &&& M).testBit k =
      (decide (k / s % 2 = 0) && v.testBit (k / (2 * s) * s + k % s)) := by
  intro k hk
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, hM k hk,
    hx k hk]
  by_cases h1 : k / s % 2 = 0
  · by_cases h2 : k / (2 * s) % 2 = 0
    · have e1 : k / (4 * s) * (2 * s) + k % (2 * s) = k / (2 * s) * s + k % s := by
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      have e2 : s ≤ k → ¬ (k - s) / (2 * s) % 2 = 0 := by
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      by_cases h3 : s ≤ k
      · rw [hx (k - s) (by omega)]
        simp [h1, h2, e1, h3, e2 h3, hk]
      · simp [h1, h2, e1, h3]
    · have h3 : s ≤ k := by rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      have e2 : (k - s) / (2 * s) % 2 = 0 := by rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      have e1 : (k - s) / (4 * s) * (2 * s) + (k - s) % (2 * s) = k / (2 * s) * s + k % s := by
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      rw [hx (k - s) (by omega)]
      simp [h1, h2, e1, h3, e2, hk]
  · simp [h1]

/-- The value `spread_bits_64` computes, on natural numbers. -/
def spreadNat (v : ℕ) : ℕ :=
  let x := v
  let x := (x ||| (x <<< 32) % 2 ^ 128) &&& 0x0000_0000_ffff_ffff_0000_0000_ffff_ffff
  let x := (x ||| (x <<< 16) % 2 ^ 128) &&& 0x0000_ffff_0000_ffff_0000_ffff_0000_ffff
  let x := (x ||| (x <<< 8) % 2 ^ 128) &&& 0x00ff_00ff_00ff_00ff_00ff_00ff_00ff_00ff
  let x := (x ||| (x <<< 4) % 2 ^ 128) &&& 0x0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f
  let x := (x ||| (x <<< 2) % 2 ^ 128) &&& 0x3333_3333_3333_3333_3333_3333_3333_3333
  (x ||| (x <<< 1) % 2 ^ 128) &&& 0x5555_5555_5555_5555_5555_5555_5555_5555

theorem spreadNat_lt (v : ℕ) : spreadNat v < 2 ^ 128 := by
  unfold spreadNat
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- Bit `2 i` of the spread is bit `i`, and the odd bits are clear. -/
theorem testBit_spreadNat {v : ℕ} (hv : v < 2 ^ 64) {k : ℕ} (hk : k < 128) :
    (spreadNat v).testBit k = (decide (k % 2 = 0) && v.testBit (k / 2)) := by
  have h0 : ∀ k < 128, v.testBit k =
      (decide (k / (2 * 32) % 2 = 0) && v.testBit (k / (4 * 32) * (2 * 32) + k % (2 * 32))) := by
    intro k hk
    by_cases h : k < 64
    · rw [show k / (2 * 32) % 2 = 0 by omega, show k / (4 * 32) * (2 * 32) + k % (2 * 32) = k by
        omega]
      simp
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp [show ¬ k / (2 * 32) % 2 = 0 by omega]
  have h1 := spread_round 32 (by omega) h0 (M := 0x0000_0000_ffff_ffff_0000_0000_ffff_ffff)
    (by decide)
  have h2 := spread_round 16 (v := v) (by omega) (fun k hk => (h1 k hk).trans (by norm_num))
    (M := 0x0000_ffff_0000_ffff_0000_ffff_0000_ffff) (by decide)
  have h3 := spread_round 8 (v := v) (by omega) (fun k hk => (h2 k hk).trans (by norm_num))
    (M := 0x00ff_00ff_00ff_00ff_00ff_00ff_00ff_00ff) (by decide)
  have h4 := spread_round 4 (v := v) (by omega) (fun k hk => (h3 k hk).trans (by norm_num))
    (M := 0x0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f) (by decide)
  have h5 := spread_round 2 (v := v) (by omega) (fun k hk => (h4 k hk).trans (by norm_num))
    (M := 0x3333_3333_3333_3333_3333_3333_3333_3333) (by decide)
  have h6 := spread_round 1 (v := v) (by omega) (fun k hk => (h5 k hk).trans (by norm_num))
    (M := 0x5555_5555_5555_5555_5555_5555_5555_5555) (by decide)
  have := h6 k hk
  simp only [Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero] at this
  exact this

/-- The spread is the square of the polynomial. -/
theorem natPoly_spreadNat {v : ℕ} (hv : v < 2 ^ 64) : natPoly (spreadNat v) = natPoly v ^ 2 := by
  rw [← ZMod.expand_card]
  ext k
  rw [coeff_natPoly, coeff_expand (by norm_num), coeff_natPoly]
  by_cases hk : k < 128
  · rw [testBit_spreadNat hv hk]
    by_cases h2 : 2 ∣ k
    · simp [h2, show k % 2 = 0 by omega]
    · simp [h2, show ¬ k % 2 = 0 by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (spreadNat_lt v)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

/-- `spread_bits_64` never panics and returns the spread. -/
theorem spread_bits_64_eq (v : Std.U64) :
    clmul.portable.spread_bits_64 v = .ok ⟨BitVec.ofNat 128 (spreadNat v.val)⟩ := by
  unfold clmul.portable.spread_bits_64
  simp (disch := decide) only [shiftLeft_i32_eq, lift_eq, bind_tc_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, and_bv, or_bv, cast_bv, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, UScalarTy.U128_numBits_eq,
    UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt (spreadNat_lt _),
    Nat.mod_eq_of_lt (lt_trans v.bv.isLt (by norm_num : 2 ^ 64 < 2 ^ 128))]
  rfl

theorem toNat_lo (a : Std.U128) : (UScalar.cast .U64 a).val = a.val % 2 ^ 64 := by
  simp only [UScalar.val, cast_bv, BitVec.toNat_setWidth, UScalarTy.U64_numBits_eq]

theorem shiftRight_64_lt (a : Std.U128) : a.val >>> 64 < 2 ^ 64 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by have := u128_val_lt a; norm_num at this ⊢; omega)

/-- `poly_square_128` never panics and squares in `GF(2)[x] / (ghashPoly)`. -/
theorem poly_square_128_toQuot (a : Std.U128) :
    clmul.portable.poly_square_128 a ⦃ r => toQuot r.bv = toQuot a.bv * toQuot a.bv ⦄ := by
  unfold clmul.portable.poly_square_128
  simp (disch := decide) only [spread_bits_64_eq, shiftRight_i32_eq, lift_eq, bind_tc_ok]
  apply WP.spec_mono (reduce_128_toQuot _ _)
  intro r hr
  rw [hr, toQuot_eq_mk, ← map_mul]
  refine congrArg _ ?_
  have hlo : (UScalar.cast .U64 a).val < 2 ^ 64 := u64_val_lt _
  have hhi : (UScalar.cast .U64 (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128)).val < 2 ^ 64 :=
    u64_val_lt _
  have e1 : (⟨BitVec.ofNat 128 (spreadNat (UScalar.cast .U64 a).val)⟩ : Std.U128).val =
      spreadNat (UScalar.cast .U64 a).val := by
    show (BitVec.ofNat 128 _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (spreadNat_lt _)]
  have e2 : (⟨BitVec.ofNat 128 (spreadNat (UScalar.cast .U64
      (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128)).val)⟩ : Std.U128).val =
      spreadNat (UScalar.cast .U64 (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128)).val := by
    show (BitVec.ofNat 128 _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (spreadNat_lt _)]
  rw [e1, e2, natPoly_spreadNat hlo, natPoly_spreadNat hhi, toNat_lo, toNat_lo]
  have e3 : (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128).val = a.val >>> 64 := by
    show (a.bv >>> I32.toNat 64#i32).toNat = _
    rw [BitVec.toNat_ushiftRight]
    rfl
  rw [e3, Nat.mod_eq_of_lt (shiftRight_64_lt a), natPoly_split a.val 64]
  linear_combination (-(X ^ 64 * natPoly (a.val >>> 64) * natPoly (a.val % 2 ^ 64))) *
    ZMod2Poly.two_eq_zero

/-! ## Scaling by a 64-bit polynomial -/

/-- `clmul_64x64` never panics and returns the carry-less product. -/
theorem clmul_64x64_ok (a b : Std.U64) :
    ∃ r : Std.U128, clmul.portable.clmul_64x64 a b = .ok r ∧
      natPoly r.val = natPoly a.val * natPoly b.val := by
  obtain ⟨r, e, h⟩ := WP.spec_imp_exists (clmul_64x64_spec a b)
  refine ⟨r, e, ?_⟩
  rw [← poly_eq_natPoly, ← poly_eq_natPoly, ← poly_eq_natPoly]
  exact h

/-- `poly_mul_128_by_64` never panics and multiplies in `GF(2)[x] / (ghashPoly)`. -/
theorem poly_mul_128_by_64_toQuot (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r =>
      toQuot r.bv = toQuot a.bv * AdjoinRoot.mk ghashPoly (natPoly b.val) ⦄ := by
  obtain ⟨lo, elo, hlo⟩ := clmul_64x64_ok (UScalar.cast .U64 a) b
  obtain ⟨mid, emid, hmid⟩ :=
    clmul_64x64_ok (UScalar.cast .U64 (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128)) b
  unfold clmul.portable.poly_mul_128_by_64
  simp (disch := decide) only [lift_eq, shiftLeft_i32_eq, shiftRight_i32_eq, bind_tc_ok, elo,
    emid]
  apply WP.spec_mono (reduce_128_toQuot _ _)
  intro r hr
  rw [hr, toQuot_eq_mk, ← map_mul]
  refine congrArg _ ?_
  have e1 : (lo ^^^ (⟨mid.bv <<< I32.toNat 64#i32⟩ : Std.U128)).val =
      lo.val ^^^ (mid.val <<< 64) % 2 ^ 128 := by
    show (lo.bv ^^^ mid.bv <<< I32.toNat 64#i32).toNat = _
    rw [BitVec.toNat_xor, BitVec.toNat_shiftLeft]
    rfl
  have e2 : (⟨mid.bv >>> I32.toNat 64#i32⟩ : Std.U128).val = mid.val >>> 64 := by
    show (mid.bv >>> I32.toNat 64#i32).toNat = _
    rw [BitVec.toNat_ushiftRight]
    rfl
  have e3 : (⟨a.bv >>> I32.toNat 64#i32⟩ : Std.U128).val = a.val >>> 64 := by
    show (a.bv >>> I32.toNat 64#i32).toNat = _
    rw [BitVec.toNat_ushiftRight]
    rfl
  rw [e1, e2, natPoly_xor, natPoly_shiftLeft_mod _ _ _ (by norm_num), hlo, hmid, toNat_lo,
    toNat_lo, e3, Nat.mod_eq_of_lt (shiftRight_64_lt a), natPoly_split a.val 64]
  linear_combination (X ^ 128 * natPoly (mid.val >>> (128 - 64))) * ZMod2Poly.two_eq_zero

/-! ## Square roots -/

/-- The even-indexed coefficients of a 128-bit polynomial, gathered. -/
def evenNat (a : ℕ) : ℕ := compactNat (a % 2 ^ 64) ||| compactNat (a >>> 64 % 2 ^ 64) <<< 32

theorem testBit_evenNat {a : ℕ} (ha : a < 2 ^ 128) (i : ℕ) :
    (evenNat a).testBit i = a.testBit (2 * i) := by
  have hlo : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hhi : a >>> 64 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  rw [evenNat, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_compactNat hlo,
    testBit_compactNat hhi, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h1 : i < 32
  · simp [h1, show 2 * i < 64 by omega]
  · by_cases h2 : i < 64
    · simp [h1, show 32 ≤ i by omega, show 2 * (i - 32) < 64 by omega,
        show 64 + 2 * (i - 32) = 2 * i by omega, show i - 32 < 32 by omega]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp [h1, show ¬ i - 32 < 32 by omega]

/-- The odd-indexed coefficients of a 128-bit polynomial, gathered. -/
def oddNat (a : ℕ) : ℕ :=
  compactNat ((a % 2 ^ 64) >>> 1) ||| compactNat ((a >>> 64 % 2 ^ 64) >>> 1) <<< 32

theorem testBit_oddNat {a : ℕ} (ha : a < 2 ^ 128) (i : ℕ) :
    (oddNat a).testBit i = a.testBit (2 * i + 1) := by
  have hlo : (a % 2 ^ 64) >>> 1 < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.mod_lt _ (by norm_num))
  have hhi : (a >>> 64 % 2 ^ 64) >>> 1 < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.mod_lt _ (by norm_num))
  rw [oddNat, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_compactNat hlo,
    testBit_compactNat hhi, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h1 : i < 32
  · simp [h1, show 2 * i + 1 < 64 by omega, show ¬ 32 ≤ i by omega, Nat.add_comm 1]
  · by_cases h2 : i < 64
    · simp [h1, show 32 ≤ i by omega, show 2 * (i - 32) + 1 < 64 by omega,
        show 64 + (2 * (i - 32) + 1) = 2 * i + 1 by omega, show i - 32 < 32 by omega,
        Nat.add_comm 1]
    · simp [h1, show ¬ i - 32 < 32 by omega]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
        (by omega)))

/-- A polynomial is its even part squared plus `X` times its odd part squared. -/
theorem natPoly_even_odd {a : ℕ} (ha : a < 2 ^ 128) :
    natPoly a = natPoly (evenNat a) ^ 2 + X ^ 1 * natPoly (oddNat a) ^ 2 := by
  rw [← ZMod.expand_card, ← ZMod.expand_card]
  ext k
  rw [coeff_add, coeff_X_pow_mul', coeff_expand (by norm_num), coeff_natPoly, coeff_natPoly]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have h1 : 2 ∣ 2 * j := ⟨j, rfl⟩
    have h2 : ¬ (1 ≤ 2 * j ∧ 2 ∣ 2 * j - 1) := by omega
    rw [testBit_evenNat ha]
    by_cases hj : 1 ≤ 2 * j
    · rw [coeff_expand (by norm_num)]
      simp [h1, show ¬ 2 ∣ 2 * j - 1 by omega, hj]
    · simp [h1, hj]
  · have h1 : ¬ 2 ∣ 2 * j + 1 := by omega
    rw [coeff_expand (by norm_num), coeff_natPoly, testBit_oddNat ha]
    simp [h1]

theorem natPoly_two : natPoly 2 = X := by
  ext k
  have h : (2 ^ 1 : ℕ).testBit k = decide (1 = k) := Nat.testBit_two_pow
  rw [coeff_natPoly, coeff_X]
  simp only [pow_one] at h
  rw [h]
  by_cases h1 : 1 = k <;> simp [h1]

set_option maxRecDepth 4000 in
/-- The square root of `X` modulo the GHASH polynomial, as `sqrt.rs` pins it. -/
theorem root_x_sq :
    AdjoinRoot.mk ghashPoly (natPoly clmul.sqrt.ROOT_X.val) ^ 2 = AdjoinRoot.mk ghashPoly X := by
  have h := verify_square_step_correct clmul.sqrt.ROOT_X.bv
    (BitVec.ofNat 128 0x4104104104104104104104104104106) (BitVec.ofNat 128 2)
    (by unfold clmul.sqrt.ROOT_X; rfl)
  rw [← ghashPoly_eq_P_val] at h
  simp only [toPoly_eq_natPoly] at h
  rw [← map_pow, show clmul.sqrt.ROOT_X.val = clmul.sqrt.ROOT_X.bv.toNat from rfl, h,
    show (BitVec.ofNat 128 2).toNat = 2 from rfl, natPoly_two, AdjoinRoot.mk_eq_mk]
  exact ⟨natPoly (to256 (BitVec.ofNat 128 0x4104104104104104104104104104106)).toNat, by ring⟩

theorem compactNat_mod_64 (x : ℕ) : compactNat x % 2 ^ 64 = compactNat x :=
  Nat.mod_eq_of_lt (lt_trans (compactNat_lt _) (by norm_num))

theorem compactNat_shift_mod_64 (x : ℕ) : (compactNat x <<< 32) % 2 ^ 64 = compactNat x <<< 32 := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := compactNat_lt x
  omega

theorem evenNat_lt (a : ℕ) : evenNat a < 2 ^ 64 :=
  Nat.or_lt_two_pow (lt_trans (compactNat_lt _) (by norm_num))
    (by rw [Nat.shiftLeft_eq]; have := compactNat_lt (a >>> 64 % 2 ^ 64); omega)

theorem oddNat_lt (a : ℕ) : oddNat a < 2 ^ 64 :=
  Nat.or_lt_two_pow (lt_trans (compactNat_lt _) (by norm_num))
    (by rw [Nat.shiftLeft_eq]; have := compactNat_lt ((a >>> 64 % 2 ^ 64) >>> 1); omega)

/-- `unshuffle` never panics and returns the even and odd coefficients. -/
theorem unshuffle_eq (a : Std.U128) :
    clmul.sqrt.unshuffle a =
      .ok (⟨BitVec.ofNat 64 (evenNat a.val)⟩, ⟨BitVec.ofNat 64 (oddNat a.val)⟩) := by
  unfold clmul.sqrt.unshuffle
  simp (disch := decide) only [compact_even_eq, shiftLeft_i32_eq, shiftRight_i32_eq, lift_eq,
    bind_tc_ok]
  congr 2 <;> apply UScalar.eq_of_val_eq <;>
  simp only [or_bv, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, cast_bv, BitVec.toNat_setWidth, UScalarTy.U64_numBits_eq,
    UScalarTy.U128_numBits_eq, UScalar.val, show I32.toNat 32#i32 = 32 from rfl,
    show I32.toNat 64#i32 = 64 from rfl, show I32.toNat 1#i32 = 1 from rfl,
    Nat.mod_eq_of_lt (evenNat_lt _), Nat.mod_eq_of_lt (oddNat_lt _), compactNat_mod_64,
    compactNat_shift_mod_64]
  · rfl
  · rfl

theorem two_eq_zero_quot : (2 : AdjoinRoot ghashPoly) = 0 := by
  calc (2 : AdjoinRoot ghashPoly) = AdjoinRoot.mk ghashPoly 2 := (map_ofNat _ 2).symm
    _ = AdjoinRoot.mk ghashPoly 0 := by rw [ZMod2Poly.two_eq_zero]
    _ = 0 := map_zero _

/-- `poly_sqrt_128` never panics and returns a square root in `GF(2)[x] / (ghashPoly)`. -/
theorem poly_sqrt_128_toQuot (a : Std.U128) :
    clmul.sqrt.poly_sqrt_128 a ⦃ r => toQuot r.bv * toQuot r.bv = toQuot a.bv ⦄ := by
  unfold clmul.sqrt.poly_sqrt_128
  refine spec_bind_pair_of_eq (unshuffle_eq a) ?_
  obtain ⟨m, em, hm⟩ := WP.spec_imp_exists
    (poly_mul_128_by_64_toQuot clmul.sqrt.ROOT_X ⟨BitVec.ofNat 64 (oddNat a.val)⟩)
  simp only [from_u64_u128_eq, bind_tc_ok, em, WP.spec_ok]
  have he : toQuot (UScalar.cast .U128 (⟨BitVec.ofNat 64 (evenNat a.val)⟩ : Std.U64) ^^^ m).bv =
      AdjoinRoot.mk ghashPoly (natPoly (evenNat a.val)) + toQuot m.bv := by
    rw [toQuot_eq_mk, toQuot_eq_mk, ← map_add, ← natPoly_xor]
    congr 2
    show (BitVec.setWidth 128 (BitVec.ofNat 64 _) ^^^ m.bv).toNat = _
    rw [BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (evenNat_lt _), Nat.mod_eq_of_lt (lt_trans (evenNat_lt _) (by norm_num))]
    rfl
  have ho : (⟨BitVec.ofNat 64 (oddNat a.val)⟩ : Std.U64).val = oddNat a.val := by
    show (BitVec.ofNat 64 _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (oddNat_lt _)]
  rw [he, hm, ho, toQuot_eq_mk, toQuot_eq_mk, natPoly_even_odd (u128_val_lt a)]
  simp only [map_add, map_mul, map_pow]
  rw [← sq, ← root_x_sq]
  linear_combination (AdjoinRoot.mk ghashPoly (natPoly (evenNat a.val)) *
    (AdjoinRoot.mk ghashPoly (natPoly clmul.sqrt.ROOT_X.val) *
      AdjoinRoot.mk ghashPoly (natPoly (oddNat a.val)))) * two_eq_zero_quot

end Plonky3Lean.Proofs.Binary
