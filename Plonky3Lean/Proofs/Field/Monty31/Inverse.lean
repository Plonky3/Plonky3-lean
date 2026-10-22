import Plonky3Lean.Proofs.Field.Monty31.PowersOfTwo
import Plonky3Lean.Proofs.Util.GcdInversion
import Mathlib.FieldTheory.Finite.Basic

/-!
# Monty31: inversion, for any valid parameters with `p > 2^30`
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {FP : Type} {inst : data_traits.FieldParameters FP} {p mu : Std.U32}

/-- The arithmetic of inversion: from the GCD's `v · a ≡ 2^60`, the reduction's
`r · 2^32 ≡ p · 2^30 + v` and the final `c ≡ r · 2^36`, the result satisfies `c · a ≡ 2^64`. -/
theorem inv_core {P r c a sumu : ℕ} {v : ℤ} [hF : Fact P.Prime] (hodd : P % 2 = 1)
    (hc : c ≡ r * 2 ^ 36 [MOD P]) (hr : r * 2 ^ 32 % P = sumu % P)
    (hs : (sumu : ℤ) = P * 2 ^ 30 + v) (hv : v * a ≡ 2 ^ 60 [ZMOD P]) :
    c * a ≡ 2 ^ 64 [MOD P] := by
  have h2 : (2 : ZMod P) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod P) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hF.out.two_le
    omega
  have hc' : (c : ZMod P) = r * 2 ^ 36 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ P).mpr hc
    rw [this]; push_cast; ring
  have hr' : (r : ZMod P) * 2 ^ 32 = v := by
    have h1 := (ZMod.natCast_eq_natCast_iff' (r * 2 ^ 32) sumu P).mpr hr
    have h3 := congrArg (fun z : ℤ => (z : ZMod P)) hs
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_pow, ZMod.natCast_self,
      zero_mul, zero_add, Int.cast_ofNat] at h3
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
    rw [h1, h3]
  have hv' : (v : ZMod P) * a = 2 ^ 60 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ P).mpr hv
    rw [← Int.cast_natCast, ← Int.cast_mul, this]; push_cast; ring
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h32 : (2 : ZMod P) ^ 32 ≠ 0 := pow_ne_zero _ h2
  apply mul_right_cancel₀ h32
  calc (c : ZMod P) * a * 2 ^ 32 = ((r : ZMod P) * 2 ^ 32) * a * 2 ^ 36 := by rw [hc']; ring
    _ = ((v : ZMod P) * a) * 2 ^ 36 := by rw [hr']
    _ = 2 ^ 64 * 2 ^ 32 := by rw [hv']; ring

/-- `try_inverse(a)` of a canonical `a` is `None` when `a` is zero.

Otherwise it is `Some(c)`, with `c` canonical and `c · a ≡ 2^64 (mod p)` on the stored values.

That congruence says the field elements multiply to `1`, since each stored value carries a factor `2^32`. -/
theorem monty_31.MontyField31.try_inverse.spec (hv : FieldValid inst p mu)
    (hd : FieldDefaults inst) (hprime : Nat.Prime p.val) (hp30 : 2 ^ 30 ≤ p.val)
    (a : monty_31.MontyField31 FP) (ha : a.value.val < p.val) :
    monty_31.MontyField31.try_inverse inst a ⦃ r =>
      (a.value.val = 0 → r = none) ∧
      (a.value.val ≠ 0 → ∃ c, r = some c ∧ c.value.val < p.val ∧
        c.value.val * a.value.val ≡ 2 ^ 64 [MOD p.val]) ⦄ := by
  unfold monty_31.MontyField31.try_inverse
  have hm := hv.monty
  rw [hd.zero]
  have hp := hm.lt
  have hodd := hm.odd
  step*
  case h1 => simp [zero_post]
  rename_i hne
  have ha0 : a.value.val ≠ 0 := by
    intro h; apply hne; apply UScalar.eq_of_val_eq; rw [h, zero_post]; simp
  rw [hm.prime, hm.bits]
  -- The GCD result: its congruence, and the range of `p · 2^30 + v`.
  obtain ⟨v, hv_eq, hvb, hvc⟩ := WP.spec_imp_exists
    (Util.gcd_inversion_prime_field_32.spec_prime a.value p hprime hodd hp
      (Nat.pos_of_ne_zero ha0) ha)
  obtain ⟨v', hv'_eq, hr1, hr2⟩ := WP.spec_imp_exists
    (Util.gcd_inversion_prime_field_32.pos_inverse a.value p hp30 hp)
  rw [hv_eq] at hv'_eq; cases hv'_eq
  simp only [bind_tc_ok, hv_eq]
  have hvabs := abs_le.mp hvb
  have hshift : ∀ sh : Std.I64,
      sh.val = ((UScalar.hcast .I64 p).val <<< 30).bmod I64.size → sh.val = p.val * 2 ^ 30 := by
    intro sh h
    have hs : I64.size = 2 ^ 64 := by simp [I64.size, I64.numBits]
    have hc : (UScalar.hcast .I64 p).val = p.val := by
      rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    rw [h, hc, Int.shiftLeft_eq, hs]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have hpos : ∀ s : Std.I64, 0 < s.val → (IScalar.hcast .U64 s).val = s.val.toNat := by
    intro s hs
    rw [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq,
      Int.emod_eq_of_lt hs.le (by have := s.hBounds; simp at this; omega)]
  step*
  all_goals have hsh := hshift shifted shifted_post1
  have hexp : (UScalar.cast .U64 exp).val = 36 := by
    rw [cast_u32_u64_val, exp_post1, three_bits_post]
  have hsum : ((IScalar.hcast .U64 sum).val : ℤ) = p.val * 2 ^ 30 + v.val := by
    rw [hpos sum (by omega), sum_post, hsh, Int.toNat_of_nonneg (by omega)]
  step with monty_31.MontyField31.mul_2exp_u64.spec_lt hv hd uncorrected_value
    (by rw [uncorrected_value_post]; exact r_post1) _ (by rw [hexp]; norm_num)
    (by rw [hexp]; norm_num)
  refine ⟨fun h => absurd h ha0, fun _ => ⟨_, rfl, v_post1, ?_⟩⟩
  haveI := Fact.mk hprime
  rw [hexp, uncorrected_value_post] at v_post2
  exact inv_core hodd v_post2 r_post2 hsum hvc

end Plonky3Lean.Proofs.Monty31
