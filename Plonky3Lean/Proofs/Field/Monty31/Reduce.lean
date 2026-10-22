import Plonky3Lean.Proofs.Field.Monty31.Convert

/-!
# Monty31: the wide Montgomery reductions, for any valid parameters

`large_monty_reduce` accepts twice the range of `monty_reduce`.

`monty_reduce_u128` reduces a 96-bit accumulator, as the long dot products produce.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-- `large_monty_reduce(x)`, for `x < 2 · 2^32 · p`, gives the canonical `r` with `r · 2^32 ≡ x`.

It first subtracts `p · 2^32` when `x` reaches it.

Then it reduces as the plain Montgomery reduction does. -/
@[step]
theorem utils.large_monty_reduce.spec (hv : Valid inst p mu) (x : Std.U64)
    (hx : x.val < 2 * 2 ^ 32 * p.val) :
    utils.large_monty_reduce inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ := by
  unfold utils.large_monty_reduce
  rw [hv.monty_mu, hv.mask, hv.prime, hv.bits]
  have hp := hv.lt
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hmu : mu.val < 2 ^ 32 := u32_lt mu
  step*
  all_goals
    have hi1 : i1.val = mu.val := by rw [i1_post, cast_u32_u64_val]
    have hi6 : i6.val = p.val := by rw [i6_post, cast_u32_u64_val]
    have ht : t.val = x.val * mu.val % 2 ^ 64 % 2 ^ 32 := by
      rw [t_post1, UScalar.val_and, i4_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
        show (4294967295#u32).val % 2 ^ 64 = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
        i2_post, hi1]
    have htlt : t.val < 2 ^ 32 := by rw [ht]; exact Nat.mod_lt _ (by norm_num)
  case h_fail =>
    rw [hi6]
    have : t.val * p.val < 2 ^ 32 * 2 ^ 31 := Nat.mul_lt_mul'' htlt hp
    scalar_tac
  have hu : u.val = t.val * p.val := by rw [u_post, hi6]
  have hi9 : i9.val = p.val * 2 ^ 32 := by
    have hs : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
    rw [i9_post1, i7_post, cast_u32_u64_val, Nat.shiftLeft_eq, hs]
    exact Nat.mod_eq_of_lt (by omega)
  have hcong : t.val * p.val % 2 ^ 32 = x.val % 2 ^ 32 := by
    rw [ht]; exact monty_t_cong x.val p.val mu.val hv.inv
  rw [x_prime_post1, hi9]
  by_cases hlt : x.val < p.val * 2 ^ 32
  · simp only [hlt, decide_true, if_true, bind_tc_ok]
    have hcore := monty_core x.val t.val p.val hp0 hp (by omega) htlt hcong
    step*
    have hhi : x_sub_u_hi.val = (x.val + 2 ^ 64 - t.val * p.val) % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
      rw [x_sub_u_hi_post, cast_u64_u32_val, i10_post1, Nat.shiftRight_eq_div_pow, x_sub_u_post2, hu]
    rw [x_sub_u_post1, hu]
    by_cases hlt2 : x.val < t.val * p.val
    · simp only [hlt2, decide_true, if_true, bind_tc_ok]
      step*
    · simp only [hlt2, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
      step*
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
    have hxp : x_prime.val = x.val - p.val * 2 ^ 32 := by
      rw [x_prime_post2, hi9, show x.val + 2 ^ 64 - p.val * 2 ^ 32 = (x.val - p.val * 2 ^ 32) + 2 ^ 64 by
        omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := u64_lt x; omega)]
    have hcong' : t.val * p.val % 2 ^ 32 = x_prime.val % 2 ^ 32 := by
      rw [hcong, hxp]; omega
    have hcore := monty_core x_prime.val t.val p.val hp0 hp (by omega) htlt hcong'
    have hmod : x_prime.val % p.val = x.val % p.val := by
      rw [hxp, show x.val = (x.val - p.val * 2 ^ 32) + p.val * 2 ^ 32 by omega,
        Nat.add_mul_mod_self_left, Nat.add_sub_cancel]
    rw [← hmod]
    step*
    have hhi : x_sub_u_hi.val =
        (x_prime.val + 2 ^ 64 - t.val * p.val) % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
      rw [x_sub_u_hi_post, cast_u64_u32_val, i10_post1, Nat.shiftRight_eq_div_pow, x_sub_u_post2, hu]
    rw [x_sub_u_post1, hu]
    by_cases hlt2 : x_prime.val < t.val * p.val
    · simp only [hlt2, decide_true, if_true, bind_tc_ok]
      step*
    · simp only [hlt2, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
      step*

/-- `monty_reduce_u128(x)`, for `x < 2^96`, gives the canonical `r` with `r · 2^32 ≡ x`.

# Why `p >= 2^30`

The low 64 bits are brought below `2 · 2^32 · p` by one subtraction of that bound.

One subtraction is enough only when `2^64 <= 4 · 2^32 · p`.

That is `p >= 2^30`, which `MontyField31::new` does not check.

For a smaller prime, some inputs stay out of range, and the result is wrong. -/
@[step]
theorem utils.monty_reduce_u128.spec (hv : Valid inst p mu) (hp30 : 2 ^ 30 ≤ p.val)
    (x : Std.U128) (hx : x.val < 2 ^ 96) :
    utils.monty_reduce_u128 inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ := by
  unfold utils.monty_reduce_u128
  rw [hv.bits, hv.prime]
  have hp := hv.lt
  have hp0 : 0 < p.val := by have := hv.odd; omega
  step*
  have hs64 : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
  have htwo : two_rp.val = 2 * 2 ^ 32 * p.val := by
    rw [two_rp_post1, i5_post1, i4_post, cast_u32_u64_val, Nat.shiftLeft_eq, Nat.shiftLeft_eq, hs64,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    ring
  have hlo : lo.val = x.val % 2 ^ 64 := by rw [lo_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
  have hhi : hi.val = x.val / 2 ^ 64 := by
    rw [hi_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i2_post1, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  -- Split `x = hi · 2^64 + lo`, with `hi < 2^32` since `x < 2^96`.
  have hl := u64_lt lo
  have hx_split : x.val = x.val / 2 ^ 64 * 2 ^ 64 + x.val % 2 ^ 64 := (Nat.div_add_mod' _ _).symm
  -- The result `(hi · 2^32 + r1) mod p`, with `r1 · 2^32 ≡ lo' ≡ lo`, is `x · 2^(-32)`.
  have hfinish : ∀ (r r1 lr : Std.U32) (lrv : ℕ), r.val = (hi.val * 2 ^ 32 % p.val + r1.val) % p.val →
      r1.val * 2 ^ 32 % p.val = lrv % p.val → lrv % p.val = lo.val % p.val →
      r.val < p.val ∧ r.val * 2 ^ 32 % p.val = x.val % p.val := by
    intro r r1 lr lrv hr hr1 hlr
    refine ⟨by rw [hr]; exact Nat.mod_lt _ hp0, ?_⟩
    have e1 : r.val * 2 ^ 32 ≡ hi.val * 2 ^ 32 * 2 ^ 32 + r1.val * 2 ^ 32 [MOD p.val] := by
      rw [hr]; exact ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).add_right _)).mul_right _
        |>.trans (by rw [Nat.add_mul])
    have e2 : r1.val * 2 ^ 32 ≡ lo.val [MOD p.val] := hr1.trans hlr
    have e3 := e1.trans (Nat.ModEq.add_left _ e2)
    rw [hhi, hlo] at e3
    unfold Nat.ModEq at e3
    rw [e3]; congr 1; rw [hx_split]; ring_nf; omega
  -- One subtraction of `2 · 2^32 · p` brings `lo` into the inner reduction's domain.
  --
  --     lo < 2^64 <= 4 · 2^32 · p      (this is where p >= 2^30 is used)
  by_cases hge : two_rp.val ≤ lo.val
  · simp only [ge_iff_le, UScalar.le_equiv, hge, if_true]
    step*
    rename_i r1 _ _
    refine hfinish r r1 (0#u32) lo_reduced.val (by rw [r_post, hi_r_mod_p_post]) r_post2 ?_
    rw [lo_reduced_post1, htwo, show lo.val = (lo.val - 2 * 2 ^ 32 * p.val) + (2 * 2 ^ 32) * p.val by
      omega, Nat.add_mul_mod_self_right, Nat.add_sub_cancel]
  · simp only [ge_iff_le, UScalar.le_equiv, hge, if_false]
    step*

end Plonky3Lean.Proofs.Monty31
