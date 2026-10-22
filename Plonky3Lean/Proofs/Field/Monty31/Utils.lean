module

public import Plonky3Lean.Lib.Scalar
public import Plonky3Lean.Spec.Monty31

@[expose] public section

/-!
# Monty31: the `u32` helpers, for any valid parameters

The arithmetic of `monty-31/src/utils.rs`.

Each theorem holds for every parameter set that passes `MontyField31::new`'s checks.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-! ## Montgomery reduction, on natural numbers -/

/-- The quotient `t = x · mu mod 2^32` of Montgomery reduction satisfies `t · p ≡ x (mod 2^32)`. -/
theorem monty_t_cong (x P MU : ℕ) (hinv : P * MU % 2 ^ 32 = 1) :
    (x * MU % 2 ^ 64 % 2 ^ 32) * P % 2 ^ 32 = x % 2 ^ 32 := by
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64), Nat.mod_mul_mod, Nat.mul_assoc,
    Nat.mul_mod, Nat.mul_comm MU, hinv, Nat.mul_one, Nat.mod_mod]

/-- Montgomery reduction on naturals, for `x < 2^32 p`, `t < 2^32` and `t · p ≡ x (mod 2^32)`.

The value it computes is the canonical `r` with `r · 2^32 ≡ x (mod p)`. -/
theorem monty_core (x t P : ℕ) (hP : 0 < P) (hP31 : P < 2 ^ 31) (hx : x < 2 ^ 32 * P)
    (ht : t < 2 ^ 32) (hcong : t * P % 2 ^ 32 = x % 2 ^ 32) :
    let r := ((x + 2 ^ 64 - t * P) % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 +
      (if x < t * P then P else 0)) % 2 ^ 32
    r < P ∧ r * 2 ^ 32 % P = x % P := by
  intro r
  -- `x - t · p` is a multiple of `2^32`, say `± k · 2^32`, with `k < p`.
  by_cases hlt : x < t * P
  · -- Negative case: the `u64` subtraction wraps, and adding `p` back gives `p - k`.
    obtain ⟨k, hk⟩ : ∃ k, t * P - x = k * 2 ^ 32 := ⟨(t * P - x) / 2 ^ 32, by omega⟩
    have h1 : (x + 2 ^ 64 - t * P) % 2 ^ 64 / 2 ^ 32 = 2 ^ 32 - k := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hk0 : 0 < k := by omega
    have htP : t * P < 2 ^ 32 * P := Nat.mul_lt_mul_of_pos_right ht hP
    have hkp : k < P := Nat.lt_of_mul_lt_mul_right (a := 2 ^ 32) (by rw [Nat.mul_comm P]; omega)
    have hr : r = P - k := by
      simp only [r, h1, ite_eq_left hlt, Nat.mod_eq_of_lt (by omega : 2 ^ 32 - k < 2 ^ 32)]
      rw [show 2 ^ 32 - k + P = (P - k) + 2 ^ 32 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hr]; refine ⟨by omega, ?_⟩
    have : (P - k) * 2 ^ 32 + t * P = x + P * 2 ^ 32 := by
      rw [Nat.sub_mul]; omega
    have h2 : ((P - k) * 2 ^ 32 + t * P) % P = (x + P * 2 ^ 32) % P := by rw [this]
    simpa [Nat.add_mul_mod_self_left, Nat.mul_mod_left] using h2
  · -- Nonnegative case: the high half of `x - t · p` is `k` itself.
    rw [not_lt] at hlt
    obtain ⟨k, hk⟩ : ∃ k, x - t * P = k * 2 ^ 32 := ⟨(x - t * P) / 2 ^ 32, by omega⟩
    have hkp : k < P := Nat.lt_of_mul_lt_mul_right (a := 2 ^ 32) (by rw [Nat.mul_comm P]; omega)
    have hr : r = k := by
      simp only [r, ite_eq_right (not_lt.mpr hlt)]
      rw [show x + 2 ^ 64 - t * P = k * 2 ^ 32 + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : k * 2 ^ 32 < 2 ^ 64), Nat.mul_div_cancel _ (by norm_num),
        Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    rw [hr]; refine ⟨hkp, ?_⟩
    have : k * 2 ^ 32 + t * P = x := by omega
    rw [← this, Nat.add_mul_mod_self_right]

/-! ## The helpers -/

/-- `monty_reduce(x)`, for `x < 2^32 · p`, is the canonical `r` with `r · 2^32 ≡ x (mod p)`.

It never panics on such an input: the product `t · p` is below `2^63`. -/
@[step]
theorem utils.monty_reduce.spec (hv : Valid inst p mu) (x : Std.U64)
    (hx : x.val < 2 ^ 32 * p.val) :
    utils.monty_reduce inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ := by
  unfold utils.monty_reduce
  rw [hv.monty_mu, hv.mask, hv.prime, hv.bits]
  have hp := hv.lt
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hmu : mu.val < 2 ^ 32 := by have := mu.hBounds; simpa using this
  step*
  all_goals
    have hi1 : i1.val = mu.val := by
      rw [i1_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]; omega
    have hi6 : i6.val = p.val := by
      rw [i6_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]; omega
    have ht : t.val = x.val * mu.val % 2 ^ 64 % 2 ^ 32 := by
      rw [t_post, UScalar.val_and, i4_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
        show (4294967295#u32).val % 2 ^ 64 = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
        i2_post, hi1]
    have htlt : t.val < 2 ^ 32 := by rw [ht]; exact Nat.mod_lt _ (by norm_num)
  case h_fail =>
    rw [hi6]
    have : t.val * p.val < 2 ^ 32 * 2 ^ 31 := Nat.mul_lt_mul'' htlt hp
    scalar_tac
  have hcore := monty_core x.val t.val p.val hp0 hp hx htlt
    (by rw [ht]; exact monty_t_cong x.val p.val mu.val hv.inv)
  have hu : u.val = t.val * p.val := by rw [u_post, hi6]
  have hhi : x_sub_u_hi.val = (x.val + 2 ^ 64 - t.val * p.val) % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
    rw [x_sub_u_hi_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i8_post,
      Nat.shiftRight_eq_div_pow, x_sub_u_post, hu]
  rw [over_post, hu]
  by_cases hlt : x.val < t.val * p.val
  · simp only [hlt, decide_true, ite_true]
    step*
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
    step*
/-- `from_monty(x)` takes `x` out of Montgomery form: the canonical `r` with `r · 2^32 ≡ x (mod p)`.

Every `u32` is accepted, canonical or not. -/
@[step]
theorem utils.from_monty.spec (hv : Valid inst p mu) (x : Std.U32) :
    utils.from_monty inst x ⦃ r => r.val < p.val ∧ r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ := by
  unfold utils.from_monty
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hx : x.val < 2 ^ 32 * p.val :=
    lt_of_lt_of_le (u32_lt x) (Nat.le_mul_of_pos_right _ hp0)
  step*

/-- `add(a, b)` of canonical `a`, `b` is `(a + b) mod p`.

The `u32` sum cannot overflow, since `a + b < 2p < 2^32`. -/
@[step]
theorem utils.add.spec (hv : Valid inst p mu) (a b : Std.U32) (ha : a.val < p.val)
    (hb : b.val < p.val) :
    utils.add inst a b ⦃ r => r.val = (a.val + b.val) % p.val ⦄ := by
  unfold utils.add
  rw [hv.prime]
  have hp := hv.lt
  step*
  all_goals
    rename_i h
    simp only [over_post, decide_eq_true_eq] at h
    have hs := sum_post
    have hc := corr_sum_post
    rcases Nat.lt_or_ge (a.val + b.val) p.val with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega

/-- `sub(a, b)` of canonical `a`, `b` is `(a - b) mod p`, as `(a + p - b) mod p`. -/
@[step]
theorem utils.sub.spec (hv : Valid inst p mu) (a b : Std.U32) (ha : a.val < p.val)
    (hb : b.val < p.val) :
    utils.sub inst a b ⦃ r => r.val = (a.val + p.val - b.val) % p.val ⦄ := by
  unfold utils.sub
  have hp := hv.lt
  rw [hv.prime]
  step*
  rw [over_post]
  by_cases h : a.val < b.val
  · simp only [h, decide_true, ite_true]
    step*
    rw [r_post, diff_post, Nat.mod_eq_of_lt (by omega : a.val + 2 ^ 32 - b.val < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : a.val + p.val - b.val < p.val)]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    step*
    rw [r_post, diff_post, Nat.add_zero,
      show a.val + p.val - b.val = (a.val - b.val) + p.val by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : a.val - b.val < p.val)]
    omega

/-- `halve_u32(a)` of a canonical `a` is the canonical `r` with `2r ≡ a (mod p)`.

It is `a / 2` when `a` is even, and `a / 2 + (p + 1) / 2` when it is odd. -/
@[step]
theorem utils.halve_u32.spec {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (a : Std.U32) (ha : a.val < p.val) :
    utils.halve_u32 inst a ⦃ r => r.val < p.val ∧ r.val * 2 % p.val = a.val ⦄ := by
  unfold utils.halve_u32
  obtain ⟨h, hh, hhv⟩ := hv.half
  have hp := hv.monty.lt
  have hodd := hv.monty.odd
  rw [hh]
  have hshr : ∀ shr : Std.U32, shr.val = a.val >>> 1 → shr.val = a.val / 2 := by
    intro shr h; rw [h, Nat.shiftRight_eq_div_pow, pow_one]
  have hlo : ∀ lo : Std.U32, lo.val = (a &&& 1#u32).val → lo.val = a.val % 2 := by
    intro lo h; rw [h, UScalar.val_and, show (1#u32).val = 1 from rfl, Nat.and_one_is_mod]
  have ha32 := u32_lt a
  step*
  case h1 h0 =>
    have : lo_bit.val = 0 := by rw [h0]; rfl
    rw [hlo lo_bit lo_bit_post] at this
    rw [hshr shr shr_post]
    refine ⟨by omega, ?_⟩
    rw [show a.val / 2 * 2 = a.val by omega, Nat.mod_eq_of_lt ha]
  case h2 h0 =>
    have : lo_bit.val ≠ 0 := fun h' => h0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
    rw [hlo lo_bit lo_bit_post] at this
    rw [shr_corr_post, hshr shr shr_post, hhv]
    refine ⟨by omega, ?_⟩
    rw [show (a.val / 2 + (p.val + 1) / 2) * 2 = a.val + p.val by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ha]

/-- `to_monty(x)` puts any `u32` into Montgomery form: `x · 2^32 mod p`.

The shift is done in `u64`, where `x · 2^32 < 2^64`. -/
@[step]
theorem utils.to_monty.spec (hv : Valid inst p mu) (x : Std.U32) :
    utils.to_monty inst x ⦃ r => r.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold utils.to_monty
  rw [hv.bits, hv.prime]
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hx := u32_lt x
  step*

end Plonky3Lean.Proofs.Monty31
