import Plonky3Lean.Proofs.Field.Goldilocks.Basic

/-!
# Goldilocks: scalar arithmetic on any stored `u64`

`reduce128` and the operators it serves, for every `u64` input, canonical or not.
Each statement says the operation never fails and gives its result's residue mod `p`.
Never failing includes every overflow-checked operation and every `assert_unchecked`.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.Goldilocks

@[step]
theorem add_no_canon.spec (x y : Std.U64) (h : x.val + y.val < 2 ^ 64 + 18446744069414584321) :
    goldilocks.add_no_canonicalize_trashing_input x y ⦃ r =>
      r.val % 18446744069414584321 = (x.val + y.val) % 18446744069414584321 ⦄ := by
  unfold goldilocks.add_no_canonicalize_trashing_input
  rw [NEG_ORDER.eq]
  have hx := u64_lt x; have hy := u64_lt y
  step*
  all_goals
    have h4 : (4294967295#u64).val = 4294967295 := rfl
    by_cases hc : 2 ^ 64 ≤ x.val + y.val <;>
      simp only [hc, decide_true, decide_false] at res_wrapped_post1 <;>
      subst res_wrapped_post1 <;> simp only [if_true, Bool.false_eq_true, if_false] at i_post <;>
      simp only [U64.max_eq, h4] at * <;> omega

/-- The arithmetic of `reduce128`: `x = lo + 2^64 (hl + 2^32 hh)` is congruent to
`lo - hh + hl (2^32 - 1)`, since `2^64 ≡ 2^32 - 1` and `2^96 ≡ -1`. -/
theorem reduce128_core (x : ℕ) (hx : x < 2 ^ 128) :
    let lo := x % 2 ^ 64
    let hh := x / 2 ^ 64 / 2 ^ 32
    let hl := x / 2 ^ 64 % 2 ^ 32
    let t0 := (lo + 2 ^ 64 - hh) % 2 ^ 64
    (lo < hh → 4294967295 ≤ t0 ∧
      (t0 - 4294967295 + hl * 4294967295) % 18446744069414584321 = x % 18446744069414584321) ∧
    (¬ lo < hh →
      (t0 + hl * 4294967295) % 18446744069414584321 = x % 18446744069414584321) := by
  intro lo hh hl t0
  have hx' : x = lo + 2 ^ 64 * (hl + 2 ^ 32 * hh) := by omega
  have hhh : hh < 2 ^ 32 := by omega
  have hlo : lo < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hhl : hl < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  clear_value lo hh hl
  subst hx'
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have ht0 : t0 = lo + 2 ^ 64 - hh := Nat.mod_eq_of_lt (by omega)
    refine ⟨by omega, ?_⟩
    rw [show lo + 2 ^ 64 * (hl + 2 ^ 32 * hh) = (t0 - 4294967295 + hl * 4294967295) +
      18446744069414584321 * (hl + 4294967297 * hh - 1) by omega, Nat.add_mul_mod_self_left]
  · have ht0 : t0 = lo - hh := by
      show (lo + 2 ^ 64 - hh) % 2 ^ 64 = lo - hh
      rw [show lo + 2 ^ 64 - hh = (lo - hh) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [show lo + 2 ^ 64 * (hl + 2 ^ 32 * hh) = (t0 + hl * 4294967295) +
      18446744069414584321 * (hl + 4294967297 * hh) by omega, Nat.add_mul_mod_self_left]

@[step]
theorem split.spec (x : Std.U128) :
    goldilocks.split x ⦃ r => r.1.val = x.val % 2 ^ 64 ∧ r.2.val = x.val / 2 ^ 64 ⦄ := by
  unfold goldilocks.split
  have hx := x.hBounds
  rw [UScalarTy.U128_numBits_eq] at hx
  step*
  rw [i2_post, i_post, cast_u128_u64_val, cast_u128_u64_val, i1_post1, Nat.shiftRight_eq_div_pow]
  exact ⟨rfl, Nat.mod_eq_of_lt (by omega)⟩

@[step]
theorem reduce128.spec (x : Std.U128) :
    goldilocks.reduce128 x ⦃ r => r.value.val % 18446744069414584321 = x.val % 18446744069414584321 ⦄ := by
  unfold goldilocks.reduce128
  rw [NEG_ORDER.eq, branch_hint.eq]
  have hx := x.hBounds
  rw [UScalarTy.U128_numBits_eq] at hx
  step*
  have hhh : x_hi_hi.val = x_hi.val / 2 ^ 32 := by
    rw [x_hi_hi_post1, Nat.shiftRight_eq_div_pow]
  have hhl : x_hi_lo.val = x_hi.val % 2 ^ 32 := by
    rw [x_hi_lo_post1, UScalar.val_and, show (4294967295#u64).val = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have h4 : (4294967295#u64).val = 4294967295 := rfl
  have hhi := u64_lt x_hi

  by_cases hb : x_lo.val < x_hi_hi.val
  · simp only [hb, decide_true] at t0_post1
    subst t0_post1
    simp only [if_true]
    step*
    all_goals
      have hc := reduce128_core x.val hx
      simp only at hc
      rw [← x_lo_post2, ← hhh, ← hhl, ← x_lo_post1, ← t0_post2] at hc
    · rw [h4]; exact (hc.1 hb).1
    · rw [r_post, t2_post, t01_post1, t1_post]; exact (hc.1 hb).2
  · simp only [hb, decide_false] at t0_post1
    subst t0_post1
    simp only [Bool.false_eq_true, if_false]
    have hfin : (t0.val + x_hi_lo.val * 4294967295) % 18446744069414584321 =
        x.val % 18446744069414584321 := by
      have hc := reduce128_core x.val hx
      simp only at hc
      rw [← x_lo_post2, ← hhh, ← hhl, ← x_lo_post1, ← t0_post2] at hc
      exact hc.2 hb
    have ht0 := u64_lt t0
    have hl32 : x_hi_lo.val < 2 ^ 32 := by rw [hhl]; exact Nat.mod_lt _ (by norm_num)
    clear x_hi_lo_post1 x_hi_lo_post2 x_hi_hi_post2 t0_post2 x_hi_hi_post1 hhl hhh x_lo_post1
      x_lo_post2
    step*

theorem add.spec (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add a b ⦃ r =>
      r.value.val % 18446744069414584321 = (a.value.val + b.value.val) % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add
  rw [NEG_ORDER.eq, branch_hint.eq, ORDER_U64.eq]
  have ha := u64_lt a.value
  have hb := u64_lt b.value
  have h4 : (4294967295#u64).val = 4294967295 := rfl
  have hp : (18446744069414584321#u64).val = 18446744069414584321 := rfl
  step*
  all_goals
    by_cases hs : 2 ^ 64 ≤ a.value.val + b.value.val <;>
      simp only [hs, decide_true, decide_false] at sum_post1 <;> subst sum_post1 <;>
      simp only [if_true, Bool.false_eq_true, if_false] at i_post
  · simp only [U64.max_eq, h4, i_post]; omega
  · simp only [U64.max_eq, h4, i_post]; omega
  all_goals
    by_cases hd : 2 ^ 64 ≤ sum.val + i2.val <;>
      simp only [hd, decide_true, decide_false] at sum1_post1 <;> subst sum1_post1 <;>
      simp only [if_true, Bool.false_eq_true, if_false]
  · -- Both additions overflow: `a, b > p`, and the third addition does not.
    have hap : a.value > 18446744069414584321#u64 := by
      rw [gt_iff_lt, UScalar.lt_equiv, hp]; omega
    have hbp : b.value > 18446744069414584321#u64 := by
      rw [gt_iff_lt, UScalar.lt_equiv, hp]; omega
    simp only [hap, hbp, if_true, decide_true, bind_tc_ok, assert_unchecked_true]
    have hi2 : i2.val = 4294967295 := by omega
    have hsum : sum.val = a.value.val + b.value.val - 2 ^ 64 := by omega
    have hsum1 : sum1.val = a.value.val + b.value.val + 4294967295 - 2 ^ 65 := by omega
    clear sum_post2 sum1_post2 i2_post i_post hap hbp
    step*
    · simp only [U64.max_eq, h4]; omega
    · rw [r_post, sum2_post, hsum1]
      exact (mod_p_of_eq _ _ 2 (by omega)).symm
  · have hsum1 : sum1.val = a.value.val + b.value.val - 18446744069414584321 := by
      have hsv : sum.val = a.value.val + b.value.val - 2 ^ 64 := by rw [sum_post2]; omega
      rw [i2_post, i_post, hsv] at hd
      rw [sum1_post2, i2_post, i_post, hsv]; omega
    clear sum_post2 sum1_post2 i2_post
    step*
  · exfalso
    rw [i2_post, i_post, sum_post2, Nat.mod_eq_of_lt (by omega)] at hd
    omega
  · have hsum1 : sum1.val = a.value.val + b.value.val := by
      rw [sum1_post2, i2_post, i_post, sum_post2, Nat.mod_eq_of_lt (by omega), Nat.zero_mul,
        Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    clear sum_post2 sum1_post2 i2_post
    step*

theorem sub.spec (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithSubGoldilocksGoldilocks.sub a b ⦃ r =>
      (r.value.val + b.value.val) % 18446744069414584321 = a.value.val % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreOpsArithSubGoldilocksGoldilocks.sub
  rw [NEG_ORDER.eq, branch_hint.eq, ORDER_U64.eq]
  have ha := u64_lt a.value
  have hb := u64_lt b.value
  have h4 : (4294967295#u64).val = 4294967295 := rfl
  have hp : (18446744069414584321#u64).val = 18446744069414584321 := rfl
  step*
  all_goals
    by_cases hs : a.value.val < b.value.val <;>
      simp only [hs, decide_true, decide_false] at diff_post1 <;> subst diff_post1 <;>
      simp only [if_true, Bool.false_eq_true, if_false] at i_post
  · simp only [U64.max_eq, h4, i_post]; omega
  · simp only [U64.max_eq, h4, i_post]; omega
  all_goals
    by_cases hd : diff.val < i2.val <;>
      simp only [hd, decide_true, decide_false] at diff1_post1 <;> subst diff1_post1 <;>
      simp only [if_true, Bool.false_eq_true, if_false]
  · -- Both subtractions underflow: `b > a + p`, so `a < 2^32 - 2` and `b > p`.
    have hdv : diff.val = a.value.val + 2 ^ 64 - b.value.val := by rw [diff_post2]; omega
    rw [hdv, i2_post, i_post] at hd
    have hd1 : diff1.val = a.value.val + 2 ^ 65 - 4294967295 - b.value.val := by
      rw [diff1_post2, hdv, i2_post, i_post]; omega
    have hi3 : (4294967295#u64 - 1#u64) = RustM.ok 4294967294#u64 := by
      have : (4294967295#u64 - 1#u64) ⦃ r => r.val = 4294967294 ⦄ := by step*
      obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists this
      rw [hr]; congr; exact UScalar.eq_of_val_eq hrv
    have hap : a.value < 4294967294#u64 := by
      rw [UScalar.lt_equiv, show (4294967294#u64).val = 4294967294 from rfl]; omega
    have hbp : b.value > 18446744069414584321#u64 := by
      rw [gt_iff_lt, UScalar.lt_equiv, hp]; omega
    simp only [hi3, hap, hbp, if_true, decide_true, bind_tc_ok, assert_unchecked_true]
    clear diff_post2 diff1_post2 i2_post i_post hap hbp hi3
    step*
    · simp only [h4]; omega
    · rw [r_post, diff2_post1]; exact mod_p_of_eq _ _ 2 (by omega)
  · have hdv : diff.val = a.value.val + 2 ^ 64 - b.value.val := by rw [diff_post2]; omega
    rw [hdv, i2_post, i_post] at hd
    have hd1 : diff1.val = a.value.val + 2 ^ 64 - 4294967295 - b.value.val := by
      rw [diff1_post2, hdv, i2_post, i_post]; omega
    clear diff_post2 diff1_post2 i2_post
    step*
    rw [r_post]; exact mod_p_of_eq _ _ 1 (by omega)
  · exfalso
    rw [i2_post, i_post] at hd
    omega
  · have hd1 : diff1.val = a.value.val - b.value.val := by
      rw [diff1_post2, i2_post, i_post, diff_post2]; omega
    clear diff_post2 diff1_post2 i2_post
    step*

@[step]
theorem mul_wide.spec (x y : Std.U64) :
    goldilocks.mul_wide x y ⦃ r => r.val = x.val * y.val ⦄ := by
  unfold goldilocks.mul_wide
  have hx := u64_lt x; have hy := u64_lt y
  step*

theorem mul.spec (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithMulGoldilocksGoldilocks.mul a b ⦃ r =>
      r.value.val % 18446744069414584321 = (a.value.val * b.value.val) % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreOpsArithMulGoldilocksGoldilocks.mul
  step*

@[step]
theorem as_canonical_u64.spec (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 a ⦃ r =>
      r.val = a.value.val % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64
  rw [ORDER_U64.eq]
  have ha := u64_lt a.value
  have hp : (18446744069414584321#u64).val = 18446744069414584321 := rfl
  split
  · rename_i h
    rw [ge_iff_le, UScalar.le_equiv, hp] at h
    step*
  · rename_i h
    rw [ge_iff_le, UScalar.le_equiv, hp] at h
    simp only [WP.spec_ok]
    omega

theorem neg.spec (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithNegGoldilocks.neg a ⦃ r =>
      (r.value.val + a.value.val) % 18446744069414584321 = 0 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreOpsArithNegGoldilocks.neg
  rw [ORDER_U64.eq]
  have hp : (18446744069414584321#u64).val = 18446744069414584321 := rfl
  step*

theorem eq.spec (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreCmpPartialEqGoldilocks.eq a b ⦃ r =>
      r = decide (a.value.val % 18446744069414584321 = b.value.val % 18446744069414584321) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreCmpPartialEqGoldilocks.eq
  step*

theorem cmp.spec (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreCmpOrd.cmp a b ⦃ r =>
      r = (match compare (a.value.val % 18446744069414584321) (b.value.val % 18446744069414584321) with
        | .lt => core.cmp.Ordering.Less
        | .eq => core.cmp.Ordering.Equal
        | .gt => core.cmp.Ordering.Greater) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreCmpOrd.cmp
  step*
  simp only [CoreModels.core.U64.Insts.CoreCmpOrd, CoreModels.core.mkUOrd, WP.spec_ok, i_post, i1_post]
  rfl

theorem is_zero.spec (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.is_zero a ⦃ r =>
      r = decide (a.value.val % 18446744069414584321 = 0) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldField.is_zero
  rw [ORDER_U64.eq]
  have ha := u64_lt a.value
  split
  · rename_i h
    simp only [h, WP.spec_ok]
    simp
  · rename_i h
    simp only [WP.spec_ok, decide_eq_decide]
    have h0 : a.value.val ≠ 0 := fun h' => h (UScalar.eq_of_val_eq h')
    constructor
    · intro h'; rw [h']; rfl
    · intro h'
      apply UScalar.eq_of_val_eq
      show a.value.val = 18446744069414584321
      omega

@[step]
theorem HALF_P_PLUS_1.spec :
    goldilocks.PrimeCharacteristicRingGoldilocks.halve.HALF_P_PLUS_1 ⦃ r => r.val = 9223372034707292161 ⦄ := by
  unfold goldilocks.PrimeCharacteristicRingGoldilocks.halve.HALF_P_PLUS_1 goldilocks.P
  step*

theorem halve.spec (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a ⦃ r =>
      (2 * r.value.val) % 18446744069414584321 = a.value.val % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
  have ha := u64_lt a.value
  step*
  have hlo : lo_bit.val = a.value.val % 2 := by
    rw [lo_bit_post1, UScalar.val_and, show (1#u64).val = 1 from rfl, Nat.and_one_is_mod]
  have hhalf : half.val = a.value.val / 2 := by
    rw [half_post1, Nat.shiftRight_eq_div_pow, pow_one]
  have hi1 : i1.val = if a.value.val % 2 = 0 then 0 else 9223372034707292161 := by
    rw [i1_post1, UScalar.val_and, mask_post, hlo, i_post]
    split
    · rename_i h; rw [h]; simp
    · rename_i h
      rw [show (0 + 2 ^ 64 - a.value.val % 2) % 2 ^ 64 = 2 ^ 64 - 1 by omega, Nat.land_comm,
        Nat.and_two_pow_sub_one_eq_mod]
  have hah : a.value.val / 2 < 2 ^ 63 := by omega
  rw [r_post, i2_post, hhalf, hi1]
  clear lo_bit_post1 lo_bit_post2 half_post1 half_post2 mask_post i1_post1 i1_post2 i2_post r_post
    hlo hhalf hi1
  by_cases h : a.value.val % 2 = 0
  · rw [if_pos h, Nat.add_zero, Nat.mod_eq_of_lt (a := a.value.val / 2) (by omega)]
    congr 1; omega
  · rw [if_neg h, Nat.mod_eq_of_lt (a := a.value.val / 2 + 9223372034707292161) (by omega)]
    exact mod_p_of_eq _ _ 1 (by omega)

end Plonky3Lean.Proofs.Goldilocks
