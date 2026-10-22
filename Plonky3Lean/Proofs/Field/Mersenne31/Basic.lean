import Plonky3Lean.Lib.Scalar.Signed
import Plonky3Lean.Spec.Mersenne31

/-!
# Mersenne31: constructors and scalar arithmetic
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-! ## The modulus -/

theorem mersenne_31.P.eq : mersenne_31.P = .ok 2147483647#u32 := by
  unfold mersenne_31.P; rfl

theorem ORDER_U32.eq :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.ORDER_U32 = .ok 2147483647#u32 := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.ORDER_U32
  exact mersenne_31.P.eq

theorem fieldSize_eq : Mersenne31.fieldSize = 2147483647 := rfl

/-! ## Bit masks and shifts on literals -/

theorem and_mask31_u32 (x : Std.U32) : (x &&& 2147483647#u32).val = x.val % 2 ^ 31 := by
  rw [UScalar.val_and, show (2147483647#u32).val = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem and_mask31_u64 (x : Std.U64) (m : Std.U64) (hm : m.val = 2 ^ 31 - 1) :
    (x &&& m).val = x.val % 2 ^ 31 := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem one_shl_u64 (n : ℕ) (hn : n < 64) : 1 <<< n % U64.size = 2 ^ n := by
  rw [U64.size_def, Nat.one_shiftLeft, U64.numBits_def, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hn)

theorem one_shl_u32 (n : ℕ) (hn : n < 32) : 1 <<< n % U32.size = 2 ^ n := by
  rw [U32.size_def, Nat.one_shiftLeft, U32.numBits_def, UScalarTy.U32_numBits_eq]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hn)

/-! ## Rotations of 31-bit values -/

/-- A left rotation of a 31-bit value by `k`, as `mul_2exp_u64` computes it. -/
theorem rotl31 (v k : ℕ) (hv : v < 2 ^ 31) (hk : k ≤ 31) :
    (v * 2 ^ k % 2 ^ 32 % 2 ^ 31 ||| v / 2 ^ (31 - k)) < 2 ^ 31 ∧
    (v * 2 ^ k % 2 ^ 32 % 2 ^ 31 ||| v / 2 ^ (31 - k)) % 2147483647 = v * 2 ^ k % 2147483647 := by
  have e31 : (2 : ℕ) ^ 31 = 2 ^ (31 - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpk' : 0 < 2 ^ (31 - k) := Nat.two_pow_pos _
  have hmod : v * 2 ^ k % 2 ^ 32 % 2 ^ 31 = v * 2 ^ k % 2 ^ 31 :=
    Nat.mod_mod_of_dvd _ (by norm_num)
  have hl : v * 2 ^ k % 2 ^ 31 = (v % 2 ^ (31 - k)) * 2 ^ k := by
    rw [e31, Nat.mul_mod_mul_right]
  have hq : v * 2 ^ k / 2 ^ 31 = v / 2 ^ (31 - k) := by
    rw [e31, Nat.mul_div_mul_right _ _ hpk]
  have hr : v / 2 ^ (31 - k) < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul hpk', Nat.mul_comm, ← e31]; exact hv
  have hor : (v % 2 ^ (31 - k)) * 2 ^ k ||| v / 2 ^ (31 - k) =
      (v % 2 ^ (31 - k)) * 2 ^ k + v / 2 ^ (31 - k) := by
    rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hr]
  have hlb : (v % 2 ^ (31 - k)) * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    rw [e31, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ hpk')
  rw [hmod, hl, hor]
  refine ⟨by omega, ?_⟩
  have hdm := Nat.div_add_mod (v * 2 ^ k) (2 ^ 31)
  rw [hq, hl] at hdm
  generalize v / 2 ^ (31 - k) = q at hdm ⊢
  generalize v % 2 ^ (31 - k) * 2 ^ k = r at hdm ⊢
  rw [← hdm]
  omega

theorem two_pow_mod (e : ℕ) : 2 ^ e % 2147483647 = 2 ^ (e % 31) % 2147483647 := by
  conv_lhs => rw [← Nat.div_add_mod e 31, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-! ## `new_reduced` -/

/-- `new_reduced(v)` stores `v` unchanged, and panics in a debug build unless `v < 2^31`. -/
@[step]
theorem new_reduced.spec (v : Std.U32) (h : v.val < 2 ^ 31) :
    mersenne_31.Mersenne31.new_reduced v ⦃ r => r.value = v ⦄ := by
  unfold mersenne_31.Mersenne31.new_reduced
  step*
  rw [not_not]
  apply UScalar.eq_of_val_eq
  rw [i_post1, Nat.shiftRight_eq_div_pow]
  show _ = 0
  omega

/-! ## `Add` -/

theorem add.spec (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add a b
      ⦃ r => Valid r ∧ r.value.val =
        if a.value.val + b.value.val < 2 ^ 31 then a.value.val + b.value.val
        else a.value.val + b.value.val - 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add
  rw [ORDER_U32.eq]
  obtain ⟨h1, h2⟩ := i32_overflowing_add_of_u32 a.value b.value ha hb
  simp only [lift, bind_tc_ok, CoreModels.core.num.I32.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_i32]
  generalize hr : IScalar.overflowing_add (UScalar.hcast .I32 a.value) (UScalar.hcast .I32 b.value) = r at h1 h2
  obtain ⟨s, ov⟩ := r
  simp only at h1 h2 ⊢
  step*
  subst h2
  have ha' : a.value.val < 2 ^ 31 := ha
  have hb' : b.value.val < 2 ^ 31 := hb
  by_cases hc : 2 ^ 31 ≤ a.value.val + b.value.val
  · simp only [hc, decide_true, if_true, bind_tc_ok]
    have : sum_corr.val = a.value.val + b.value.val - 2147483647 := by
      rw [sum_corr_post, h1]; omega
    step*
    simp only [Valid, r_post, this, if_neg (Nat.not_lt.mpr hc)]
    exact ⟨by omega, trivial⟩
  · simp only [hc, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
    step*
    simp only [Valid, r_post, h1, if_pos (Nat.lt_of_not_le hc)]
    exact ⟨by omega, trivial⟩

/-! ## `Sub` and `Neg` -/

theorem sub.spec (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithSubMersenne31Mersenne31.sub a b
      ⦃ r => Valid r ∧ r.value.val =
        if b.value.val ≤ a.value.val then a.value.val - b.value.val
        else a.value.val + 2147483647 - b.value.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreOpsArithSubMersenne31Mersenne31.sub
  rw [ORDER_U32.eq]
  have ha' : a.value.val < 2 ^ 31 := ha
  have hb' : b.value.val < 2 ^ 31 := hb
  step*
  · rw [i_post, sub_post1]
    by_cases h : a.value.val < b.value.val
    · simp only [h, decide_true, Bool.toNat_true]; omega
    · simp only [h, decide_false, Bool.toNat_false]; omega
  · rw [i2_post1, and_mask31_u32]; omega
  · have hi2 := i2_post1
    rw [and_mask31_u32] at hi2
    simp only [Valid, r_post, hi2, sub1_post1, i_post, sub_post2, sub_post1]
    by_cases h : a.value.val < b.value.val
    · simp only [h, decide_true, Bool.toNat_true, if_neg (Nat.not_le.mpr h)]; omega
    · simp only [h, decide_false, Bool.toNat_false, if_pos (Nat.le_of_not_lt h)]; omega

theorem neg.spec (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithNegMersenne31.neg a
      ⦃ r => Valid r ∧ r.value.val = 2147483647 - a.value.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreOpsArithNegMersenne31.neg
  rw [ORDER_U32.eq]
  have ha' : a.value.val < 2 ^ 31 := ha
  step*
  simp only [Valid, r_post, i1_post1]
  exact ⟨by omega, trivial⟩

/-! ## `from_u62` and `Mul` -/

theorem from_u62.spec (x : Std.U64) (hx : x.val < 2 ^ 62) :
    mersenne_31.from_u62 x ⦃ r => Valid r ∧ r.value.val % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.from_u62
  step*
  all_goals
    have hi1 : i1.val = 2 ^ 31 := by rw [i1_post1]; exact one_shl_u64 31 (by norm_num)
    have hlo : input_lo.val = x.val % 2 ^ 31 := by
      rw [input_lo_post, cast_u64_u32_val, i3_post1, and_mask31_u64 x i2 (by omega)]; omega
    have hhi : input_high.val = x.val / 2 ^ 31 := by
      rw [input_high_post, cast_u64_u32_val, i4_post1, Nat.shiftRight_eq_div_pow]; omega
  · omega
  · omega
  · have hm : Valid m := by simp only [Valid, m_post, hlo]; omega
    have hm1 : Valid m1 := by simp only [Valid, m1_post, hhi]; omega
    refine WP.spec_mono (add.spec m m1 hm hm1) ?_
    rintro r ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hr, m_post, m1_post, hlo, hhi]
    split_ifs <;> omega

theorem mul.spec (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul a b
      ⦃ r => Valid r ∧ r.value.val % 2147483647 = a.value.val * b.value.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul
  have ha' : a.value.val < 2 ^ 31 := ha
  have hb' : b.value.val < 2 ^ 31 := hb
  step*
  have hp : prod.val < 2 ^ 62 := by
    rw [prod_post, i_post, i1_post]
    calc a.value.val * b.value.val < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' ha' hb'
      _ = 2 ^ 62 := by norm_num
  refine WP.spec_mono (from_u62.spec prod hp) ?_
  rintro r ⟨hv, hr⟩
  rw [prod_post, i_post, i1_post] at hr
  exact ⟨hv, hr⟩

/-! ## Constructors -/

theorem new.spec (x : Std.U32) :
    mersenne_31.Mersenne31.new x ⦃ r => r.value.val = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.new
  rw [mersenne_31.P.eq]
  step*

theorem new_checked.spec (x : Std.U32) :
    mersenne_31.Mersenne31.new_checked x ⦃ r =>
      r = if x.val < 2 ^ 31 then .Some { value := x } else .None ⦄ := by
  unfold mersenne_31.Mersenne31.new_checked
  step*
  · have : i.val = 0 := by simp [*]
    rw [i_post1, Nat.shiftRight_eq_div_pow] at this
    rw [if_pos (by omega)]
  · have : i.val ≠ 0 := fun h => by apply ‹¬i = 0#u32›; exact UScalar.eq_of_val_eq h
    rw [i_post1, Nat.shiftRight_eq_div_pow] at this
    rw [if_neg (by omega)]

/-! ## Reading an element -/

@[step]
theorem as_canonical_u32.spec (a : Element) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.as_canonical_u32 a
      ⦃ r => r.val = if a.value.val = 2147483647 then 0 else a.value.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.as_canonical_u32
  rw [ORDER_U32.eq]
  step*

theorem is_zero.spec (a : Element) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.is_zero a
      ⦃ r => r = decide (a.value.val = 0 ∨ a.value.val = 2147483647) ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldField.is_zero
  rw [ORDER_U32.eq]
  step*

theorem eq.spec (a b : Element) :
    mersenne_31.Mersenne31.Insts.CoreCmpPartialEqMersenne31.eq a b ⦃ r =>
      r = decide ((if a.value.val = 2147483647 then 0 else a.value.val) =
        (if b.value.val = 2147483647 then 0 else b.value.val)) ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreCmpPartialEqMersenne31.eq
  step*

theorem cmp.spec (a b : Element) :
    mersenne_31.Mersenne31.Insts.CoreCmpOrd.cmp a b ⦃ r =>
      r = match compare (if a.value.val = 2147483647 then 0 else a.value.val)
          (if b.value.val = 2147483647 then 0 else b.value.val) with
        | .lt => .Less
        | .eq => .Equal
        | .gt => .Greater ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreCmpOrd.cmp
  step*
  rw [core.U32.Insts.CoreCmpOrd.cmp.eq, ← i_post, ← i1_post]
  rfl

/-! ## Constants -/

theorem NEG_ONE.eq :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE =
      .ok { value := 2147483646#u32 } := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE
  rw [ORDER_U32.eq]; rfl

/-! ## `PrimeCharacteristicRing` methods -/

/-- `halve_u32::<P>(x)` for `x ≤ P < 2^31`: `x / 2` if `x` is even, `x / 2 + (P + 1) / 2` if odd. -/
@[step]
theorem halve_u32.spec (P x : Std.U32) (hP : P.val < 2 ^ 31) (hx : x.val ≤ P.val) :
    p3_field.helpers.halve_u32 P x ⦃ r =>
      r.val = if x.val % 2 = 0 then x.val / 2 else x.val / 2 + (P.val + 1) / 2 ⦄ := by
  unfold p3_field.helpers.halve_u32
  step*
  all_goals
    have hlo : i1.val = x.val % 2 := by
      rw [i1_post1, UScalar.val_and, show (1#u32).val = 1 from rfl, Nat.and_one_is_mod]
    have hsh : shift.val = (P.val + 1) / 2 := by
      rw [shift_post1, Nat.shiftRight_eq_div_pow, i_post]
    have hh : half.val = x.val / 2 := by rw [half_post1, Nat.shiftRight_eq_div_pow]
  · have : i1.val = 0 := by simp [*]
    rw [if_pos (by omega), hh]
  · scalar_tac
  · have : i1.val ≠ 0 := fun h => ‹¬i1 = 0#u32› (UScalar.eq_of_val_eq h)
    rw [if_neg (by omega), r_post, hh, hsh]

theorem from_bool.spec (b : Bool) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b
      ⦃ r => r.value.val = b.toNat ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  step*
  cases b <;> simp_all

theorem halve.spec (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a
      ⦃ r => Valid r ∧ r.value.val * 2 % 2147483647 = a.value.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
  have ha' : a.value.val < 2 ^ 31 := ha
  step*
  · split_ifs at i_post <;> omega
  · simp only [Valid, r_post]
    split_ifs at i_post <;> exact ⟨by omega, by omega⟩

theorem mul_2exp_u64.spec (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e
      ⦃ r => Valid r ∧ r.value.val % 2147483647 = a.value.val * 2 ^ e.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64
  have ha' : a.value.val < 2 ^ 31 := ha
  step*
  all_goals
    have hk : exp1.val ≤ 30 := by omega
    have hi2 : i2.val = 2 ^ 31 - 1 := by rw [i2_post1, i1_post1, one_shl_u32 31 (by norm_num)]
    have hrot : rotated.val =
        (a.value.val * 2 ^ exp1.val % 2 ^ 32 % 2 ^ 31 ||| a.value.val / 2 ^ (31 - exp1.val)) := by
      rw [rotated_post1, UScalar.val_or, left_post1, UScalar.val_and, hi2,
        Nat.and_two_pow_sub_one_eq_mod, i_post1, Nat.shiftLeft_eq, U32.size_def, U32.numBits_def,
        UScalarTy.U32_numBits_eq, right_post1, Nat.shiftRight_eq_div_pow, i3_post1]
    have hr := rotl31 a.value.val exp1.val ha' (by omega)
  · rw [hrot]; exact hr.1
  · simp only [Valid, r_post]
    rw [hrot]
    refine ⟨hr.1, ?_⟩
    have h2 : 2 ^ exp1.val % 2147483647 = 2 ^ e.val % 2147483647 := by
      rw [two_pow_mod e.val, exp1_post]
    rw [hr.2, Nat.mul_mod, h2, ← Nat.mul_mod]

theorem div_2exp_u64.spec (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e
      ⦃ r => Valid r ∧ r.value.val * 2 ^ e.val % 2147483647 = a.value.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64
  have ha' : a.value.val < 2 ^ 31 := ha
  step*
  all_goals
    have he : exp1.val = e.val % 31 := by
      rw [exp1_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, i_post]; omega
    have hi4 : i4.val = 2 ^ 31 - 1 := by rw [i4_post1, i3_post1, one_shl_u32 31 (by norm_num)]
    have hrot : rotated.val =
        (a.value.val * 2 ^ (31 - exp1.val) % 2 ^ 32 % 2 ^ 31 |||
          a.value.val / 2 ^ (31 - (31 - exp1.val))) := by
      rw [rotated_post1, UScalar.val_or, right_post1, UScalar.val_and, hi4,
        Nat.and_two_pow_sub_one_eq_mod, i2_post1, Nat.shiftLeft_eq, U32.size_def, U32.numBits_def,
        UScalarTy.U32_numBits_eq, left_post1, Nat.shiftRight_eq_div_pow, i1_post1,
        show 31 - (31 - exp1.val) = exp1.val by omega, Nat.or_comm]
    have hr := rotl31 a.value.val (31 - exp1.val) ha' (by omega)
  · rw [hrot]; exact hr.1
  · simp only [Valid, r_post]
    rw [hrot]
    refine ⟨hr.1, ?_⟩
    rw [Nat.mul_mod, hr.2, ← Nat.mul_mod, Nat.mul_assoc, ← pow_add, Nat.mul_mod, two_pow_mod,
      show (31 - exp1.val + e.val) % 31 = 0 by omega]
    simp

end Plonky3Lean.Proofs.Mersenne31
