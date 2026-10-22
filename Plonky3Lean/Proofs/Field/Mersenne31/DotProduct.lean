import Plonky3Lean.Proofs.Field.Mersenne31.Basic

/-!
# Mersenne31: delayed reduction and `dot_product`
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-- The arithmetic of `reduce_64`: two folds of the top bits onto the low 31, then one conditional subtraction of `p`. -/
theorem reduce_64_nat (x : ℕ) (hx : x < 2 ^ 64) :
    min ((x % 2 ^ 31 + x / 2 ^ 31) % 2 ^ 31 + (x % 2 ^ 31 + x / 2 ^ 31) / 2 ^ 31)
      (((x % 2 ^ 31 + x / 2 ^ 31) % 2 ^ 31 + (x % 2 ^ 31 + x / 2 ^ 31) / 2 ^ 31 + 2 ^ 32 -
        2147483647) % 2 ^ 32) = x % 2147483647 := by
  have e1 := Nat.div_add_mod x (2 ^ 31)
  have m1 := Nat.mod_lt x (Nat.two_pow_pos 31)
  generalize x / 2 ^ 31 = q1 at *
  generalize x % 2 ^ 31 = r1 at *
  subst e1
  have e2 := Nat.div_add_mod (r1 + q1) (2 ^ 31)
  have m2 := Nat.mod_lt (r1 + q1) (Nat.two_pow_pos 31)
  generalize (r1 + q1) / 2 ^ 31 = q2 at *
  generalize (r1 + q1) % 2 ^ 31 = r2 at *
  have hq1 : q1 < 2 ^ 33 := by omega
  by_cases hs : 2147483647 ≤ r2 + q2
  · rw [show (r2 + q2 + 2 ^ 32 - 2147483647) % 2 ^ 32 = r2 + q2 - 2147483647 by omega]
    omega
  · rw [show (r2 + q2 + 2 ^ 32 - 2147483647) % 2 ^ 32 = r2 + q2 + 2 ^ 32 - 2147483647 by omega]
    omega

theorem partial_reduce.spec (x : Std.U64) :
    mersenne_31.partial_reduce x ⦃ r =>
      r.val = x.val % 2 ^ 31 + x.val / 2 ^ 31 ∧ r.val % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.partial_reduce
  rw [mersenne_31.P.eq]
  step*
  all_goals
    have hx := u64_lt x
    have hlo : lo.val = x.val % 2 ^ 31 := by
      rw [lo_post, cast_u64_u32_val, i2_post1, and_mask31_u64 x i1 (by rw [i1_post]; rfl)]; omega
    have hhi : hi.val = x.val / 2 ^ 31 := by rw [hi_post1, Nat.shiftRight_eq_div_pow]
    have hi3 : i3.val = x.val % 2 ^ 31 := by rw [i3_post, cast_u32_u64_val, hlo]
  · scalar_tac
  · rw [r_post, hi3, hhi]
    omega

theorem reduce_64.spec (x : Std.U64) :
    mersenne_31.reduce_64 x ⦃ r => r.val = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.reduce_64
  rw [mersenne_31.P.eq]
  step*
  all_goals
    have hx := u64_lt x
    have hlo : lo.val = x.val % 2 ^ 31 := by
      rw [lo_post, cast_u64_u32_val, i2_post1, and_mask31_u64 x i1 (by rw [i1_post]; rfl)]; omega
    have hhi : hi.val = x.val / 2 ^ 31 := by rw [hi_post1, Nat.shiftRight_eq_div_pow]
    have hi3 : i3.val = x.val % 2 ^ 31 := by rw [i3_post, cast_u32_u64_val, hlo]
  · scalar_tac
  all_goals
    have hs1 : sum1.val = x.val % 2 ^ 31 + x.val / 2 ^ 31 := by rw [sum1_post, hi3, hhi]
    have hlo2 : lo2.val = sum1.val % 2 ^ 31 := by
      rw [lo2_post, cast_u64_u32_val, i5_post1, and_mask31_u64 sum1 i4 (by rw [i4_post]; rfl)]; omega
    have hhi2 : hi2.val = sum1.val / 2 ^ 31 := by
      rw [hi2_post, cast_u64_u32_val, i6_post1, Nat.shiftRight_eq_div_pow]; omega
  · scalar_tac
  · rw [r_post, i7_post, sum2_post, hlo2, hhi2, hs1]
    exact reduce_64_nat x.val hx

end Plonky3Lean.Proofs.Mersenne31
