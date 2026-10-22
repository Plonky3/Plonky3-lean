import Plonky3Lean.Proofs.Field.Binary.Ghash
import ToCompPoly.Fields.Binary.Poly64.Basic
import Plonky3Lean.Lib.Iter

/-!
# `GF(2^64)` modulo `x^64 + x^4 + x^3 + x + 1`

The portable multiplication, squaring and square root of p3-binary-field's `Poly64`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The reduction -/

/-- The value `reduce_64` computes, on natural numbers. -/
def reduce64Nat (p : ℕ) : ℕ :=
  let low := p % 2 ^ 64
  let high := p >>> 64 % 2 ^ 64
  let folded := high ^^^ high >>> 63 ^^^ high >>> 61 ^^^ high >>> 60
  low ^^^ folded ^^^ (folded <<< 1) % 2 ^ 64 ^^^ (folded <<< 3) % 2 ^ 64 ^^^
    (folded <<< 4) % 2 ^ 64

theorem reduce64Nat_lt (p : ℕ) : reduce64Nat p < 2 ^ 64 := by
  have hh : p >>> 64 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hs : ∀ k, (p >>> 64 % 2 ^ 64) >>> k < 2 ^ 64 := fun k =>
    lt_of_le_of_lt (Nat.shiftRight_le _ _) hh
  unfold reduce64Nat
  simp only
  repeat' apply Nat.xor_lt_two_pow
  all_goals first
    | exact Nat.mod_lt _ (by norm_num)
    | exact hh
    | exact hs _

/-- `reduce_64` never panics and returns the reduction. -/
theorem reduce_64_eq (p : Std.U128) :
    clmul.reduce_64 p = .ok ⟨BitVec.ofNat 64 (reduce64Nat p.val)⟩ := by
  unfold clmul.reduce_64
  simp (disch := decide) only [shiftLeft_i32_eq, shiftRight_i32_eq, lift_eq, bind_tc_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, xor_bv, cast_bv, BitVec.toNat_xor, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, UScalarTy.U64_numBits_eq,
    UScalarTy.U128_numBits_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (reduce64Nat_lt _)]
  rfl

/-- The spill of the first fold: the coefficients of `H · tail` from `X^64` up. -/
def spill64 (H : ℕ) : ℕ := H >>> 63 ^^^ H >>> 61 ^^^ H >>> 60

theorem spill64_lt {H : ℕ} (hH : H < 2 ^ 64) : spill64 H < 2 ^ 4 := by
  unfold spill64
  apply Nat.xor_lt_two_pow (Nat.xor_lt_two_pow _ _) <;>
    rw [Nat.shiftRight_eq_div_pow] <;> apply Nat.div_lt_of_lt_mul <;> rw [← pow_add] <;>
    exact lt_of_lt_of_le hH (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem shiftRight_xor_spill {H : ℕ} (hH : H < 2 ^ 64) {k : ℕ} (hk : 4 ≤ k) :
    (H ^^^ spill64 H) >>> k = H >>> k := by
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow (spill64 H),
    Nat.div_eq_of_lt (lt_of_lt_of_le (spill64_lt hH) (Nat.pow_le_pow_right (by norm_num) hk)),
    Nat.xor_zero]

/-- The reduction adds a multiple of the modulus to `L + X^64 · H`. -/
theorem natPoly_reduce64Nat (p : ℕ) :
    natPoly (reduce64Nat p) = natPoly (p % 2 ^ 64) + natPoly (p >>> 64 % 2 ^ 64) * Poly64.tail +
      natPoly (spill64 (p >>> 64 % 2 ^ 64)) * Poly64.modulus := by
  have hH : p >>> 64 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  unfold reduce64Nat
  simp only
  generalize p >>> 64 % 2 ^ 64 = H at hH ⊢
  rw [show H ^^^ H >>> 63 ^^^ H >>> 61 ^^^ H >>> 60 = H ^^^ spill64 H by
    simp only [spill64, Nat.xor_assoc]]
  simp only [natPoly_xor, natPoly_shiftLeft_mod _ _ 64 (by norm_num : 1 ≤ 64),
    natPoly_shiftLeft_mod _ _ 64 (by norm_num : 3 ≤ 64),
    natPoly_shiftLeft_mod _ _ 64 (by norm_num : 4 ≤ 64), Nat.reduceSub]
  rw [shiftRight_xor_spill hH (k := 63) (by norm_num), shiftRight_xor_spill hH (k := 61) (by norm_num),
    shiftRight_xor_spill hH (k := 60) (by norm_num)]
  simp only [natPoly_xor, Poly64.tail, Poly64.modulus_eq_X_pow_add_tail, spill64]
  norm_num
  ring

/-- In `GF(2)[x] / (modulus)`, the reduction is `L + X^64 · H`. -/
theorem mk_natPoly_reduce64Nat {p : ℕ} (hp : p < 2 ^ 128) :
    AdjoinRoot.mk Poly64.modulus (natPoly (reduce64Nat p)) =
      AdjoinRoot.mk Poly64.modulus (natPoly p) := by
  have hhi : p >>> 64 % 2 ^ 64 = p >>> 64 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by norm_num at hp ⊢; omega)
  rw [AdjoinRoot.mk_eq_mk, natPoly_reduce64Nat, natPoly_split p 64, hhi,
    Poly64.modulus_eq_X_pow_add_tail]
  exact ⟨natPoly (p >>> 64) + natPoly (spill64 (p >>> 64)), by
    linear_combination (-(X ^ 64 * natPoly (p >>> 64))) * ZMod2Poly.two_eq_zero⟩

/-! ## Products -/

/-- The carry-less product of two 64-bit numbers, as `clmul_64x64` assembles it. -/
def clmul64Nat (a b : ℕ) : ℕ :=
  bmulNat a b ||| highNat (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) <<< 64

theorem clmul64Nat_lt (a b : ℕ) : clmul64Nat a b < 2 ^ 128 :=
  Nat.or_lt_two_pow (lt_trans (bmulNat_lt _ _) (by norm_num))
    (by rw [Nat.shiftLeft_eq]; have := highNat_lt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b); omega)

theorem natPoly_clmul64Nat {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    natPoly (clmul64Nat a b) = natPoly a * natPoly b := by
  have h := natPoly_halves (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  rw [clmul64Nat, natPoly_or_shiftLeft (bmulNat_lt _ _), h]

/-- The product modulo `x^64 + x^4 + x^3 + x + 1`, as `poly_mul_64` computes it. -/
def mulMod64 (a b : ℕ) : ℕ := reduce64Nat (clmul64Nat a b)

theorem mulMod64_lt (a b : ℕ) : mulMod64 a b < 2 ^ 64 := reduce64Nat_lt _

theorem mk_mulMod64 {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    AdjoinRoot.mk Poly64.modulus (natPoly (mulMod64 a b)) =
      AdjoinRoot.mk Poly64.modulus (natPoly a) * AdjoinRoot.mk Poly64.modulus (natPoly b) := by
  rw [mulMod64, mk_natPoly_reduce64Nat (clmul64Nat_lt _ _), natPoly_clmul64Nat ha hb, map_mul]

theorem toQuot64_eq (x : Std.U64) : toQuot64 x = AdjoinRoot.mk Poly64.modulus (natPoly x.val) := by
  rw [toQuot64, poly_eq_natPoly]

theorem val_ofNat_64 {n : ℕ} (h : n < 2 ^ 64) : (⟨BitVec.ofNat 64 n⟩ : Std.U64).val = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `poly_mul_64` never panics and returns the reduced product. -/
theorem poly_mul_64_eq (a b : Std.U64) :
    clmul.gf64.poly_mul_64 a b = .ok ⟨BitVec.ofNat 64 (mulMod64 a.val b.val)⟩ := by
  unfold clmul.gf64.poly_mul_64 clmul.gf64.composed_mul_64
  rw [clmul_64x64_eq, bind_tc_ok, reduce_64_eq]
  congr 3
  show reduce64Nat (BitVec.ofNat 128 _).toNat = _
  have e : bmulNat a.val b.val ||| highNat a.bv b.bv <<< 64 = clmul64Nat a.val b.val := by
    simp only [clmul64Nat, UScalar.val, BitVec.ofNat_toNat]
    congr 3
  rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt (clmul64Nat_lt a.val b.val)]
  rfl

/-- `poly_square_64` never panics and returns the reduced square. -/
theorem poly_square_64_eq (a : Std.U64) :
    clmul.gf64.poly_square_64 a = .ok ⟨BitVec.ofNat 64 (mulMod64 a.val a.val)⟩ := by
  unfold clmul.gf64.poly_square_64 clmul.gf64.composed_square_64
  rw [show clmul.portable.clmul_64x64 a a >>= clmul.reduce_64 =
    clmul.gf64.composed_mul_64 a a from rfl]
  exact poly_mul_64_eq a a

/-- `poly_mul_64` multiplies in `GF(2)[x] / (modulus)`. -/
theorem poly_mul_64_toQuot (a b : Std.U64) :
    clmul.gf64.poly_mul_64 a b ⦃ r => toQuot64 r = toQuot64 a * toQuot64 b ⦄ := by
  rw [poly_mul_64_eq, WP.spec_ok, toQuot64_eq, toQuot64_eq, toQuot64_eq,
    val_ofNat_64 (mulMod64_lt _ _), mk_mulMod64 (u64_val_lt a) (u64_val_lt b)]

/-- `poly_square_64` squares in `GF(2)[x] / (modulus)`. -/
theorem poly_square_64_toQuot (a : Std.U64) :
    clmul.gf64.poly_square_64 a ⦃ r => toQuot64 r = toQuot64 a * toQuot64 a ⦄ := by
  rw [poly_square_64_eq, WP.spec_ok, toQuot64_eq, toQuot64_eq,
    val_ofNat_64 (mulMod64_lt _ _), mk_mulMod64 (u64_val_lt a) (u64_val_lt a)]

/-! ## Repeated squaring and inversion -/

/-- One squaring, as `poly_square_64` returns it. -/
def sq64 (y : Std.U64) : Std.U64 := ⟨BitVec.ofNat 64 (mulMod64 y.val y.val)⟩

theorem toQuot64_sq64 (y : Std.U64) : toQuot64 (sq64 y) = toQuot64 y ^ 2 := by
  rw [sq64, toQuot64_eq, toQuot64_eq, val_ofNat_64 (mulMod64_lt _ _),
    mk_mulMod64 (u64_val_lt y) (u64_val_lt y), sq]

theorem toQuot64_iterate_sq64 (k : ℕ) (y : Std.U64) :
    toQuot64 (sq64^[k] y) = toQuot64 y ^ 2 ^ k := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, toQuot64_sq64, ← pow_mul, pow_succ, Nat.mul_comm]

/-- `square_times` never panics and squares `K` times. -/
theorem square_times_eq (K : Std.Usize) (x : Std.U64) :
    clmul.gf64.square_times K x = .ok (sq64^[K.val] x) := by
  unfold clmul.gf64.square_times
  exact iter_fold_loop_range _ () sq64 (fun b i => by
    show (do let r ← clmul.gf64.poly_square_64 b; RustM.ok (r, ())) = _
    rw [poly_square_64_eq, bind_tc_ok]
    rfl) K.val 0#usize K x (by simp)

theorem toQuot64_mulMod64 (a b : Std.U64) :
    toQuot64 ⟨BitVec.ofNat 64 (mulMod64 a.val b.val)⟩ = toQuot64 a * toQuot64 b := by
  rw [toQuot64_eq, toQuot64_eq, toQuot64_eq, val_ofNat_64 (mulMod64_lt _ _),
    mk_mulMod64 (u64_val_lt a) (u64_val_lt b)]

/-- `poly_inverse_64` never panics and raises to the power `2^64 - 2` in `GF(2)[x] / (modulus)`. -/
theorem poly_inverse_64_toQuot (x : Std.U64) :
    clmul.gf64.poly_inverse_64 x ⦃ r => toQuot64 r = toQuot64 x ^ (2 ^ 64 - 2) ⦄ := by
  unfold clmul.gf64.poly_inverse_64
  simp only [poly_square_64_eq, poly_mul_64_eq, square_times_eq, bind_tc_ok, WP.spec_ok]
  simp only [toQuot64_mulMod64, ← sq64.eq_def, toQuot64_sq64, toQuot64_iterate_sq64]
  simp only [← pow_mul, ← pow_succ, ← pow_add]
  norm_num

end Plonky3Lean.Proofs.Binary
