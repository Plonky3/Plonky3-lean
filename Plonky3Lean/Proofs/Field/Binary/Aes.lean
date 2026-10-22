module

public import Plonky3Lean.Proofs.Field.Binary.Clmul
public import Plonky3Lean.Lib.Scalar

@[expose] public section

/-!
# The block cipher's field

`GF(2^8)` modulo `X^8 + X^4 + X^3 + X + 1`, as p3-binary-field's `aes` module computes it.

- `carryless` multiplies two bytes in `GF(2)[X]`, one bit of the second operand per round.
- `mul_bytes` folds the high half down twice by the modulus's tail, `X^4 + X^3 + X + 1`.
- `invert_byte` raises to the power `254` by an addition chain.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The carry-less product -/

/-- The carry-less product of `a` with the low `n` bits of `b`, one bit per round. -/
def clAcc (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => clAcc a b n ^^^ (if b.testBit n then a <<< n else 0)

/-- The low `n + 1` bits are the low `n` bits and bit `n`. -/
theorem mod_two_pow_succ_xor (b n : ℕ) :
    b % 2 ^ (n + 1) = b % 2 ^ n ^^^ (if b.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  split_ifs with h
  · rw [Nat.testBit_two_pow]
    by_cases hi : i = n
    · subst hi; simp [h]
    · by_cases hi' : i < n
      · simp [hi', show i < n + 1 by omega, Ne.symm hi]
      · simp [hi', show ¬ i < n + 1 by omega, Ne.symm hi]
  · simp only [Nat.zero_testBit, Bool.xor_false]
    by_cases hi : i = n
    · subst hi; simp [h]
    · by_cases hi' : i < n
      · simp [hi', show i < n + 1 by omega]
      · simp [hi', show ¬ i < n + 1 by omega]

theorem natPoly_clAcc (a b : ℕ) : ∀ n, natPoly (clAcc a b n) = natPoly a * natPoly (b % 2 ^ n)
  | 0 => by simp [clAcc, natPoly_zero, Nat.mod_one]
  | n + 1 => by
    rw [clAcc, natPoly_xor, natPoly_clAcc a b n, mod_two_pow_succ_xor, natPoly_xor, mul_add]
    split_ifs
    · rw [natPoly_shiftLeft, natPoly_two_pow]; ring
    · rw [natPoly_zero, mul_zero]

theorem clAcc_lt {a b : ℕ} (ha : a < 2 ^ 8) : ∀ n, n ≤ 8 → clAcc a b n < 2 ^ 15
  | 0, _ => by simp [clAcc]
  | n + 1, hn => by
    rw [clAcc]
    apply Nat.xor_lt_two_pow (clAcc_lt ha n (by omega))
    split_ifs
    · rw [Nat.shiftLeft_eq]
      calc a * 2 ^ n < 2 ^ 8 * 2 ^ n := Nat.mul_lt_mul_of_pos_right ha (by positivity)
        _ = 2 ^ (8 + n) := by rw [pow_add]
        _ ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
    · positivity

/-- Bit `k` of `b`, as `(b >> k) & 1` reads it. -/
theorem shiftRight_and_one (b k : ℕ) : (b >>> k) &&& 1 = if b.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ k) with h | h <;> simp [h]

/-- `x & 0u16.wrapping_sub(bit)` keeps `x` when the bit is set, and clears it otherwise. -/
theorem and_select {x : ℕ} (hx : x < 2 ^ 16) (c : Bool) :
    x &&& (0 + 2 ^ 16 - (if c then 1 else 0)) % 2 ^ 16 = if c then x else 0 := by
  cases c
  · simp
  · simp only [↓reduceIte]
    rw [show (0 + 2 ^ 16 - 1) % 2 ^ 16 = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hx]

theorem carryless_loop_spec (b : Std.U8) (a : Std.U16) (ha : a.val < 2 ^ 8) (acc : Std.U16)
    (i : Std.I32) (h0 : 0 ≤ i.val) (hi : i.val ≤ 8) (hacc : acc.val = clAcc a.val b.val i.toNat) :
    aes.carryless_loop b a acc i ⦃ r => r.val = clAcc a.val b.val 8 ⦄ := by
  unfold aes.carryless_loop
  refine loop.spec_decr_nat (fun p => 8 - p.2.toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 8 ∧ p.1.val = clAcc a.val b.val p.2.toNat) _ _ _ ?_
    ⟨h0, hi, hacc⟩
  rintro ⟨acc, i⟩ ⟨h0, hi, hacc⟩
  unfold aes.carryless_loop.body
  step*
  · scalar_tac
  · have hk : i.toNat < 8 := by scalar_tac
    have hi6 : i6.toNat = i.toNat + 1 := by scalar_tac
    have hsh : a.val <<< i.toNat < 2 ^ 16 := by
      rw [Nat.shiftLeft_eq]
      calc a.val * 2 ^ i.toNat < 2 ^ 8 * 2 ^ 8 :=
            Nat.mul_lt_mul_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
              (by positivity)
        _ = 2 ^ 16 := by norm_num
    refine ⟨by scalar_tac, by scalar_tac, ?_, by omega⟩
    simp only at hacc
    have hi3 : i3.val = if b.val.testBit i.toNat then 1 else 0 := by
      rw [i3_post, UScalar.cast_val_eq, i2_post, UScalar.val_and, i1_post,
        show (1#u8).val = 1 from rfl]
      rw [shiftRight_and_one]
      split_ifs <;> rfl
    rw [acc1_post, UScalar.val_xor, i5_post, UScalar.val_and, selected_post, i4_post, hi3, hi6,
      clAcc, hacc, show U16.size = 2 ^ 16 by simp [U16.size_def, U16.numBits_def]]
    rw [Nat.mod_eq_of_lt hsh, and_select hsh]

theorem carryless_spec (a b : Std.U8) :
    aes.carryless a b ⦃ r => r.val = clAcc a.val b.val 8 ⦄ := by
  unfold aes.carryless
  simp only [lift_eq, Aeneas.Std.bind_ok]
  have ha := a.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha
  have hc : (UScalar.cast .U16 a).val = a.val := by
    rw [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.mod_eq_of_lt (by omega)]
  have h := carryless_loop_spec b (UScalar.cast .U16 a) (hc ▸ ha) 0#u16 0#i32 (by decide)
    (by decide) (by rw [hc]; rfl)
  rwa [hc] at h

/-! ## The reduction -/

/-- `fold_tail`: the product with the modulus's tail `X^4 + X^3 + X + 1`. -/
def foldNat (v : ℕ) : ℕ := v <<< 4 ^^^ v <<< 3 ^^^ v <<< 1 ^^^ v

theorem foldNat_lt {v k : ℕ} (hv : v < 2 ^ k) : foldNat v < 2 ^ (k + 4) := by
  have h : ∀ j ≤ 4, v <<< j < 2 ^ (k + 4) := fun j hj => by
    rw [Nat.shiftLeft_eq]
    calc v * 2 ^ j < 2 ^ k * 2 ^ j := Nat.mul_lt_mul_of_pos_right hv (by positivity)
      _ = 2 ^ (k + j) := by rw [pow_add]
      _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold foldNat
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (h 4 le_rfl) (h 3 (by omega)))
    (h 1 (by omega))) ?_
  simpa using h 0 (by omega)

theorem natPoly_foldNat (v : ℕ) : natPoly (foldNat v) = (X ^ 4 + X ^ 3 + X + 1) * natPoly v := by
  simp only [foldNat, natPoly_xor, natPoly_shiftLeft]
  ring

theorem fold_tail_eq (v : Std.U16) (hv : v.val < 2 ^ 12) :
    aes.fold_tail v = .ok ⟨BitVec.ofNat 16 (foldNat v.val)⟩ := by
  unfold aes.fold_tail
  simp (disch := decide) only [shiftLeft_i32_eq, lift_eq, Aeneas.Std.bind_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  have hf := foldNat_lt hv
  simp only [UScalar.val, xor_bv, BitVec.toNat_xor, BitVec.toNat_shiftLeft,
    UScalarTy.U16_numBits_eq, BitVec.toNat_ofNat]
  have hv' : v.bv.toNat < 2 ^ 12 := hv
  have hs : ∀ j ≤ 4, v.bv.toNat <<< j < 2 ^ 16 := fun j hj => by
    rw [Nat.shiftLeft_eq]
    calc v.bv.toNat * 2 ^ j < 2 ^ 12 * 2 ^ j := Nat.mul_lt_mul_of_pos_right hv' (by positivity)
      _ = 2 ^ (12 + j) := by rw [pow_add]
      _ ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show I32.toNat 4#i32 = 4 from rfl, show I32.toNat 3#i32 = 3 from rfl,
    show I32.toNat 1#i32 = 1 from rfl, Nat.mod_eq_of_lt (hs 4 le_rfl),
    Nat.mod_eq_of_lt (hs 3 (by omega)), Nat.mod_eq_of_lt (hs 1 (by omega)),
    Nat.mod_eq_of_lt (show foldNat v.bv.toNat < 2 ^ 16 from hf)]
  rfl

/-- The product `mul_bytes` computes, on natural numbers. -/
def mulBytesNat (a b : ℕ) : ℕ :=
  let p := clAcc a b 8
  let f := foldNat (p >>> 8)
  (p ^^^ f ^^^ foldNat (f >>> 8)) % 2 ^ 8

theorem mul_bytes_spec (a b : Std.U8) :
    aes.mul_bytes a b ⦃ r => r.val = mulBytesNat a.val b.val ⦄ := by
  unfold aes.mul_bytes
  refine WP.spec_bind (carryless_spec a b) fun p hp => ?_
  have ha := a.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha
  have hp15 : p.val < 2 ^ 15 := hp ▸ clAcc_lt ha 8 le_rfl
  rw [shiftRight_i32_eq _ _ (by decide) (by decide), Aeneas.Std.bind_ok]
  have hH : (⟨p.bv >>> I32.toNat 8#i32⟩ : Std.U16).val = p.val >>> 8 := by
    show (p.bv >>> 8).toNat = _
    rw [BitVec.toNat_ushiftRight]; rfl
  have hH7 : p.val >>> 8 < 2 ^ 7 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [fold_tail_eq _ (by rw [hH]; omega), Aeneas.Std.bind_ok, lift_eq, Aeneas.Std.bind_ok, hH]
  have hf : foldNat (p.val >>> 8) < 2 ^ 11 := foldNat_lt hH7
  rw [shiftRight_i32_eq _ _ (by decide) (by decide), Aeneas.Std.bind_ok]
  have hF : (⟨(BitVec.ofNat 16 (foldNat (p.val >>> 8))) >>> I32.toNat 8#i32⟩ : Std.U16).val =
      foldNat (p.val >>> 8) >>> 8 := by
    show ((BitVec.ofNat 16 (foldNat (p.val >>> 8))) >>> 8).toNat = _
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hF3 : foldNat (p.val >>> 8) >>> 8 < 2 ^ 3 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [fold_tail_eq _ (by rw [hF]; omega), Aeneas.Std.bind_ok, lift_eq, Aeneas.Std.bind_ok, hF,
    WP.spec_ok]
  have hg : foldNat (foldNat (p.val >>> 8) >>> 8) < 2 ^ 7 := foldNat_lt hF3
  unfold mulBytesNat
  rw [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, UScalar.val_xor, UScalar.val_xor, ← hp]
  show (p.val ^^^ (BitVec.ofNat 16 (foldNat (p.val >>> 8))).toNat ^^^
    (BitVec.ofNat 16 (foldNat (foldNat (p.val >>> 8) >>> 8))).toNat) % 2 ^ 8 = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show foldNat (p.val >>> 8) < 2 ^ 16 by omega),
    Nat.mod_eq_of_lt (show foldNat (foldNat (p.val >>> 8) >>> 8) < 2 ^ 16 by omega)]

/-- Two folds by the tail reduce the carry-less product modulo `X^8 + X^4 + X^3 + X + 1`. -/
theorem mk_natPoly_mulBytesNat {a b : ℕ} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    AdjoinRoot.mk AesField.modulus (natPoly (mulBytesNat a b)) =
      AdjoinRoot.mk AesField.modulus (natPoly a) * AdjoinRoot.mk AesField.modulus (natPoly b) := by
  have hp15 := clAcc_lt (b := b) ha 8 le_rfl
  have hp : natPoly (clAcc a b 8) = natPoly a * natPoly b := by
    rw [natPoly_clAcc, Nat.mod_eq_of_lt hb]
  unfold mulBytesNat
  simp only
  generalize clAcc a b 8 = p at hp15 hp ⊢
  have hH7 : p >>> 8 < 2 ^ 7 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hf := foldNat_lt hH7
  have hF3 : foldNat (p >>> 8) >>> 8 < 2 ^ 3 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hg := foldNat_lt hF3
  have hsh : (p ^^^ foldNat (p >>> 8) ^^^ foldNat (foldNat (p >>> 8) >>> 8)) >>> 8 =
      p >>> 8 ^^^ foldNat (p >>> 8) >>> 8 := by
    rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_xor_distrib,
      Nat.shiftRight_eq_div_pow (foldNat (foldNat (p >>> 8) >>> 8)) 8,
      Nat.div_eq_of_lt (by omega), Nat.xor_zero]
  have hsplit := natPoly_split (p ^^^ foldNat (p >>> 8) ^^^ foldNat (foldNat (p >>> 8) >>> 8)) 8
  rw [hsh, natPoly_xor, natPoly_xor, natPoly_xor, natPoly_foldNat, natPoly_foldNat] at hsplit
  rw [← map_mul, ← hp, AdjoinRoot.mk_eq_mk]
  refine ⟨natPoly (p >>> 8) + natPoly (foldNat (p >>> 8) >>> 8), ?_⟩
  unfold AesField.modulus
  linear_combination -hsplit + (-(X ^ 8 * (natPoly (p >>> 8) +
    natPoly (foldNat (p >>> 8) >>> 8)))) * ZMod2Poly.two_eq_zero

/-! ## In CompPoly's `AesField` -/

/-- A byte, in `GF(2)[X] / (X^8 + X^4 + X^3 + X + 1)`, is the class of its bit polynomial. -/
theorem toQuot_aes (x : Std.U8) :
    CompPoly.Extension.Ext.toQuot (aes x) = AdjoinRoot.mk AesField.params.poly (natPoly x.val) := by
  rw [CompPoly.Extension.Ext.toQuot_eq_mk, show x.val = x.bv.toNat from rfl, ← toPoly_eq_natPoly]
  show AdjoinRoot.mk _ (∑ i : Fin 8, C (CompPoly.Extension.Ext.coeff (aes x) i) * X ^ (i : ℕ)) = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aes, AesField.coeff_ofBitVec]
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split_ifs <;> simp

/-- `mul_bytes` is multiplication in the block cipher's field. -/
theorem mul_bytes_aes (a b : Std.U8) :
    aes.mul_bytes a b ⦃ r => aes r = aes a * aes b ⦄ := by
  have ha := a.hBounds
  have hb := b.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha hb
  refine WP.spec_mono (mul_bytes_spec a b) fun r h => ?_
  apply CompPoly.Extension.Ext.toQuot_injective
  rw [CompPoly.Extension.Ext.toQuot_mul, toQuot_aes, toQuot_aes, toQuot_aes, AesField.params_poly,
    h, mk_natPoly_mulBytesNat ha hb]

/-- `x^254` is the inverse in the block cipher's field, and `0` at `0`. -/
theorem aes_pow_254 (x : AesField) : x ^ 254 = x⁻¹ := by
  have : Finite AesField := Nat.finite_of_card_ne_zero (by rw [AesField.nat_card]; norm_num)
  let := Fintype.ofFinite AesField
  have hcard : Fintype.card AesField = 256 := by
    rw [← Nat.card_eq_fintype_card, AesField.nat_card]
  by_cases hx : x = 0
  · rw [hx, inv_zero, zero_pow (by norm_num)]
  · have h := FiniteField.pow_card x
    rw [hcard, show (256 : ℕ) = 254 + 1 + 1 by norm_num, pow_succ, pow_succ] at h
    have h1 : x ^ 254 * x = 1 := by
      have := congrArg (· * x⁻¹) h
      simpa [mul_assoc, mul_inv_cancel₀ hx] using this
    exact eq_inv_of_mul_eq_one_left h1

/-- `invert_byte` is inversion in the block cipher's field, with `0` sent to `0`. -/
theorem invert_byte_aes (a : Std.U8) :
    aes.invert_byte a ⦃ r => aes r = (aes a)⁻¹ ⦄ := by
  unfold aes.invert_byte
  refine WP.spec_bind (mul_bytes_aes _ _) fun x2 h2 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x3 h3 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x6 h6 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x12 h12 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x15 h15 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x30 h30 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x60 h60 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x120 h120 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x240 h240 => ?_
  refine WP.spec_bind (mul_bytes_aes _ _) fun x252 h252 => ?_
  refine WP.spec_mono (mul_bytes_aes _ _) fun r hr => ?_
  rw [hr, h252, h240, h120, h60, h30, h15, h12, h6, h3, h2, ← aes_pow_254]
  ring

end Plonky3Lean.Proofs.Binary
