module

public import Plonky3Lean.Proofs.Field.Binary.TowerField
public import Plonky3Lean.Lib.Scalar

@[expose] public section

/-!
# The tower's linear maps, by halves

`linear.rs` builds byte tables for squaring and square roots from two recursions on the
width, `mul_alpha` and `square`. On a value of `2^k` bits they split it into halves and
recurse at width `2^(k-1)`:

- `mul_alpha` multiplies by the level's generator `Z k`;
- `square` uses `(a + b X)^2 = (a^2 + b^2) + Z (b^2) X`, the cross term vanishing in
  characteristic 2.

On natural numbers both are `towerMul`: `mulAlphaNat_eq` and `sqNat_eq`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Binary

/-- `linear::mul_alpha` at width `2^k`, on natural numbers. -/
def mulAlphaNat : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a =>
    a >>> 2 ^ k ||| (a % 2 ^ 2 ^ k ^^^ mulAlphaNat k (a >>> 2 ^ k)) <<< 2 ^ k

/-- `linear::square` at width `2^k`, on natural numbers. -/
def sqNat : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a =>
    (sqNat k (a % 2 ^ 2 ^ k) ^^^ sqNat k (a >>> 2 ^ k)) |||
      mulAlphaNat k (sqNat k (a >>> 2 ^ k)) <<< 2 ^ k

/-- The high half of a value of `2^(k+1)` bits fits in `2^k` bits. -/
theorem shiftRight_lt_of_lt {a k : ℕ} (ha : a < 2 ^ 2 ^ (k + 1)) : a >>> 2 ^ k < 2 ^ 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, ← two_mul, ← pow_succ']
  exact ha

theorem mulAlphaNat_eq : ∀ (k : ℕ) {a : ℕ}, a < 2 ^ 2 ^ k →
    mulAlphaNat k a = towerMul k a (zNat k)
  | 0, a, ha => by
    rw [mulAlphaNat, show zNat 0 = 1 from rfl, towerMul_one 0 ha]
  | k + 1, a, ha => by
    have hhi := shiftRight_lt_of_lt ha
    rw [mulAlphaNat, towerMul_zNat_succ, and_sub_one_mod, mod_two_pow_two_pow_of_lt ha,
      mulAlphaNat_eq k hhi, Nat.lor_comm]

/-- Squaring is additive in characteristic 2. -/
theorem towerMul_sq_xor (k : ℕ) {a b : ℕ} (ha : a < 2 ^ 2 ^ k) (hb : b < 2 ^ 2 ^ k) :
    towerMul k (a ^^^ b) (a ^^^ b) = towerMul k a a ^^^ towerMul k b b := by
  set x : ConcreteBTField k := fromNat a
  set y : ConcreteBTField k := fromNat b
  have hx : x.toNat = a := by rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt ha]
  have hy : y.toNat = b := by rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hb]
  have h : (x + y) * (x + y) = x * x + y * y := by
    rw [add_mul_self_eq, mul_assoc, CharTwo.two_eq_zero, zero_mul, add_zero]
  have h' := congrArg ConcreteBTField.toNat h
  rw [toNat_add, show (x + y) * (x + y) = concrete_mul (x + y) (x + y) from rfl,
    toNat_concrete_mul, toNat_add, show x * x = concrete_mul x x from rfl,
    show y * y = concrete_mul y y from rfl, toNat_concrete_mul, toNat_concrete_mul, hx,
    hy] at h'
  exact h'

theorem sqNat_eq : ∀ (k : ℕ) {a : ℕ}, a < 2 ^ 2 ^ k → sqNat k a = towerMul k a a
  | 0, a, _ => by simp [sqNat, towerMul]
  | k + 1, a, ha => by
    have hhi := shiftRight_lt_of_lt ha
    have hlo : a % 2 ^ 2 ^ k < 2 ^ 2 ^ k := Nat.mod_lt _ (by positivity)
    rw [sqNat, sqNat_eq k hlo, sqNat_eq k hhi,
      mulAlphaNat_eq k (towerMul_lt k hhi hhi), towerMul]
    simp only [and_sub_one_mod, mod_two_pow_two_pow_of_lt ha]
    rw [towerMul_sq_xor k hhi hlo, Nat.lor_comm]
    congr 2
    generalize towerMul k (a >>> 2 ^ k) (a >>> 2 ^ k) = s1
    generalize towerMul k (a % 2 ^ 2 ^ k) (a % 2 ^ 2 ^ k) = s0
    rw [Nat.xor_comm s0 s1, Nat.xor_self, Nat.zero_xor]

/-! ## The extracted recursions -/

/-- The width `2^k`, as a `usize`. -/
def widthUsize (k : ℕ) : Std.Usize := ⟨BitVec.ofNat _ (2 ^ k)⟩

/-- A run of `m` ones, shifted right by `n`, is a run of `m - n` ones. -/
theorem two_pow_sub_one_shiftRight {m n : ℕ} : (2 ^ m - 1) >>> n = 2 ^ (m - n) - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  apply decide_eq_decide.mpr
  omega

/-- `mulAlphaNat k` stays within the level. -/
theorem mulAlphaNat_lt {k a : ℕ} (ha : a < 2 ^ 2 ^ k) : mulAlphaNat k a < 2 ^ 2 ^ k := by
  rw [mulAlphaNat_eq k ha]
  exact towerMul_lt k ha (zNat_lt k)

/-- `sqNat k` stays within the level. -/
theorem sqNat_lt {k a : ℕ} (ha : a < 2 ^ 2 ^ k) : sqNat k a < 2 ^ 2 ^ k := by
  rw [sqNat_eq k ha]
  exact towerMul_lt k ha ha

/-- A value below `2^(2^k)`, shifted left by `2^k`, stays below `2^(2^(k+1))`. -/
theorem shiftLeft_lt_of_lt {x k : ℕ} (hx : x < 2 ^ 2 ^ k) : x <<< 2 ^ k < 2 ^ 2 ^ (k + 1) := by
  rw [Nat.shiftLeft_eq, pow_succ, pow_mul, sq]
  exact Nat.mul_lt_mul_of_pos_right hx (by positivity)

theorem widthUsize_val {k : ℕ} (hk : k ≤ 7) : (widthUsize k).val = 2 ^ k := by
  show (BitVec.ofNat _ (2 ^ k)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
    _ < 2 ^ System.Platform.numBits := by
      rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> norm_num

theorem widthUsize_half {k : ℕ} (hk : k + 1 ≤ 7) {half : Std.Usize}
    (h : half.val = (widthUsize (k + 1)).val / 2) : half = widthUsize k := by
  apply UScalar.eq_of_val_eq
  rw [h, widthUsize_val hk, widthUsize_val (by omega), pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem mul_alpha_spec : ∀ (k : ℕ), k ≤ 7 → ∀ (a : Std.U128), a.val < 2 ^ 2 ^ k →
    linear.mul_alpha a (widthUsize k) ⦃ r => r.val = mulAlphaNat k a.val ⦄
  | 0, _, a, _ => by
    unfold linear.mul_alpha
    rw [ite_eq_left (UScalar.eq_of_val_eq (by rw [widthUsize_val (by omega)]; rfl)), WP.spec_ok]
    rfl
  | k + 1, hk, a, ha => by
    have hw := widthUsize_val hk
    have hw' := widthUsize_val (k := k) (by omega)
    have hk64 : 2 ^ k ≤ 64 := by
      calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num
    have hpos : 0 < 2 ^ k := by positivity
    have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    unfold linear.mul_alpha
    step*
    have hh : half = widthUsize k := widthUsize_half hk half_post
    subst hh
    have hhi : hi.val < 2 ^ 2 ^ k := by rw [hi_post, hw']; exact shiftRight_lt_of_lt ha
    refine WP.spec_bind (mul_alpha_spec k (by omega) hi hhi) fun r hr => ?_
    step*
    have hmask : i1.val = 2 ^ 2 ^ k - 1 := by
      rw [i1_post, i_post, hw', show U128.rMax = 2 ^ 128 - 1 from rfl, two_pow_sub_one_shiftRight]
      congr 2
      omega
    have hlo : lo.val = a.val % 2 ^ 2 ^ k := by
      rw [lo_post, UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
    have hr' : r.val < 2 ^ 2 ^ k := hr ▸ mulAlphaNat_lt hhi
    have hi3 : i3.val < 2 ^ 2 ^ k := by
      rw [i3_post, UScalar.val_xor, hlo]
      exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hr'
    have h128 : 2 ^ 2 ^ (k + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by
      calc 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 128 := by norm_num)
    rw [UScalar.val_or, i4_post, hw', show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (lt_of_lt_of_le (shiftLeft_lt_of_lt hi3) h128), i3_post, UScalar.val_xor,
      hlo, hr, hi_post, hw', mulAlphaNat]

theorem square_spec : ∀ (k : ℕ), k ≤ 7 → ∀ (a : Std.U128), a.val < 2 ^ 2 ^ k →
    linear.square a (widthUsize k) ⦃ r => r.val = sqNat k a.val ⦄
  | 0, _, a, _ => by
    unfold linear.square
    rw [ite_eq_left (UScalar.eq_of_val_eq (by rw [widthUsize_val (by omega)]; rfl)), WP.spec_ok]
    rfl
  | k + 1, hk, a, ha => by
    have hw := widthUsize_val hk
    have hw' := widthUsize_val (k := k) (by omega)
    have hk64 : 2 ^ k ≤ 64 := by
      calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num
    have hpos : 0 < 2 ^ k := by positivity
    have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    unfold linear.square
    step*
    have hh : half = widthUsize k := widthUsize_half hk half_post
    subst hh
    have hmask : i1.val = 2 ^ 2 ^ k - 1 := by
      rw [i1_post, i_post, hw', show U128.rMax = 2 ^ 128 - 1 from rfl, two_pow_sub_one_shiftRight]
      congr 2
      omega
    have hlo : i2.val = a.val % 2 ^ 2 ^ k := by
      rw [i2_post, UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
    have hlo' : i2.val < 2 ^ 2 ^ k := hlo ▸ Nat.mod_lt _ (by positivity)
    refine WP.spec_bind (square_spec k (by omega) i2 hlo') fun lo hlo_eq => ?_
    step*
    · rw [i3_post, hw']; exact shiftRight_lt_of_lt ha
    have hhi : i3.val < 2 ^ 2 ^ k := by rw [i3_post, hw']; exact shiftRight_lt_of_lt ha
    have hhi' : hi.val < 2 ^ 2 ^ k := hi_post ▸ sqNat_lt hhi
    refine WP.spec_bind (mul_alpha_spec k (by omega) hi hhi') fun i5 hi5 => ?_
    step*
    have h128 : 2 ^ 2 ^ (k + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by
      calc 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 128 := by norm_num)
    have hi5' : i5.val < 2 ^ 2 ^ k := hi5 ▸ mulAlphaNat_lt hhi'
    rw [UScalar.val_or, i4_post, UScalar.val_xor, i6_post, hw',
      show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (lt_of_lt_of_le (shiftLeft_lt_of_lt hi5') h128), hi5, hlo_eq, hi_post,
      hlo, i3_post, hw', sqNat]

end Plonky3Lean.Proofs.Binary
