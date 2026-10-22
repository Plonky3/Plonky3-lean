module

public import CompPoly.Fields.Mersenne31
public import Plonky3Lean.Proofs.Field.Mersenne31.Conversions
public import Plonky3Lean.Proofs.Util.GcdInversion

@[expose] public section

/-!
# Mersenne31: `try_inverse`

`try_inverse` calls p3-util's GCD inversion, whose output is `2^60 a^{-1} mod p` as an `i64`.

That congruence is the only property of the GCD it uses: every `i64` converts correctly, so its size does not matter.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.P3Mersenne31

/-- The documented output of `gcd_inversion_prime_field_32::<31>(a, p)` for `0 < a < p`: an `i64` congruent to `2^60 a^{-1}` modulo `p`. -/
def GcdInversionContract : Prop :=
  ∀ a : Std.U32, 0 < a.val → a.val < 2147483647 →
    p3_util.gcd_inversion_prime_field_32 31#u32 a 2147483647#u32 ⦃ v =>
      (v.val * a.val) % 2147483647 = 2 ^ 60 % 2147483647 ⦄

theorem two_ne_zero' : (2 : ZMod 2147483647) ≠ 0 := by decide

theorem try_inverse.spec (hg : GcdInversionContract) (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      match r with
      | .None => a.value.val = 0 ∨ a.value.val = 2147483647
      | .Some y => Valid y ∧ (y.value.val * a.value.val) % 2147483647 = 1 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldField.try_inverse
  rw [mersenne_31.P.eq]
  have ha' : a.value.val < 2 ^ 31 := ha
  step*
  rename_i h
  rw [b_post] at h
  simp only [decide_eq_true_eq, not_or] at h
  have hv := hg a.value (by omega) (by omega)
  step with hv as ⟨v, hv'⟩
  step*
  refine ⟨m1_post, ?_⟩
  have hpr : Nat.Prime 2147483647 := Mersenne31.is_prime
  have : Fact (Nat.Prime 2147483647) := ⟨hpr⟩
  have e1 : ((m1.value.val : ℤ) : ZMod 2147483647) * 2 ^ 60 = (m.value.val : ℤ) := by
    have := (ZMod.intCast_eq_intCast_iff' ((m1.value.val : ℤ) * 2 ^ 60) (m.value.val : ℤ)
      2147483647).mpr (by exact_mod_cast m1_post1)
    push_cast at this ⊢; exact this
  have e2 : ((m.value.val : ℤ) : ZMod 2147483647) = (v.val : ZMod 2147483647) :=
    (ZMod.intCast_eq_intCast_iff' _ _ 2147483647).mpr m_post1
  have e3 : ((v.val : ℤ) : ZMod 2147483647) * (a.value.val : ℤ) = 2 ^ 60 := by
    have := (ZMod.intCast_eq_intCast_iff' (v.val * a.value.val) (2 ^ 60) 2147483647).mpr hv'
    push_cast at this ⊢; exact this
  have h2 : (2 : ZMod 2147483647) ^ 60 ≠ 0 := pow_ne_zero _ two_ne_zero'
  have key : ((m1.value.val * a.value.val : ℕ) : ZMod 2147483647) = 1 := by
    have : ((m1.value.val : ℤ) : ZMod 2147483647) * (a.value.val : ℤ) * 2 ^ 60 = 2 ^ 60 := by
      rw [mul_right_comm, e1, e2, e3]
    have := mul_right_cancel₀ h2 (this.trans (one_mul _).symm)
    push_cast at this ⊢; exact this
  have := congrArg ZMod.val key
  rwa [ZMod.val_natCast, ZMod.val_one] at this

/-- The GCD inversion meets its contract at `p = 2^31 - 1`. -/
theorem gcdInversionContract : GcdInversionContract := by
  intro a ha0 hap
  refine WP.spec_mono (Proofs.Util.gcd_inversion_prime_field_32.spec_prime a 2147483647#u32
    Mersenne31.is_prime (by decide) (by decide) ha0 hap) ?_
  rintro v ⟨-, hv⟩
  exact hv

end Plonky3Lean.Proofs.P3Mersenne31
