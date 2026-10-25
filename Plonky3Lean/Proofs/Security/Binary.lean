module

public import Plonky3Lean.Proofs.Security.Budget
public import Plonky3Lean.Lib.Range

@[expose] public section

/-!
# p3-security's binary PCS schedule

# Overview

A schedule has `n` binary folds, a log inverse rate `r` and a `K`-bit challenge field.

Fold `j` works on words of length `N = 2^(r + j)`, for `j = 1, ..., n`.

It costs two errors:

- the proximity error, `N + 1`;
- the quadratic-sumcheck error, `2`.

The field-error numerator is their sum over the folds.

The field security bits are `K - ceil(log_2 numerator)`.

On an accepted schedule, none of these functions panics.
-/

open Aeneas Aeneas.Std CoreModels p3_security
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Security.Binary

/-- The schedules the constructor accepts. -/
def Valid (K n r f q : ℕ) : Prop :=
  8 ≤ K ∧ K ≤ 128 ∧ K.isPowerOfTwo ∧ n ≠ 0 ∧ r ≠ 0 ∧ n + r < 64 ∧ f ≠ 0 ∧ f ≤ n ∧ q ≠ 0

/-- The fold and sumcheck errors, summed over the folds. -/
def numeratorSpec (n r : ℕ) : ℕ := ∑ j ∈ Finset.range n, (2 ^ (r + j + 1) + 1 + 2)

theorem numeratorSpec_closed (n r : ℕ) :
    numeratorSpec n r + 2 * 2 ^ r = 2 * 2 ^ (n + r) + 3 * n := by
  induction n with
  | zero => simp [numeratorSpec]
  | succ n ih =>
    rw [numeratorSpec, Finset.sum_range_succ, ← numeratorSpec]
    have : 2 ^ (n + 1 + r) = 2 * 2 ^ (n + r) := by rw [← pow_succ']; congr 1; omega
    have h2 : 2 ^ (r + n + 1) = 2 * 2 ^ (n + r) := by rw [← pow_succ']; congr 1; omega
    rw [this, h2]; omega

/-- The field-error numerator never panics when `n + r < 64`.

It is the sum of the fold and sumcheck errors. -/
@[step]
theorem field_error_numerator_spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) :
    binary.BinaryPcsRegime.field_error_numerator reg ⦃ y =>
      y.val = numeratorSpec reg.num_variables.val reg.log_inv_rate.val ⦄ := by
  unfold binary.BinaryPcsRegime.field_error_numerator
  have hc := numeratorSpec_closed reg.num_variables.val reg.log_inv_rate.val
  have hp : (2 : ℕ) ^ (reg.num_variables.val + reg.log_inv_rate.val) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hr : (2 : ℕ) ^ reg.log_inv_rate.val ≤ 2 ^ (reg.num_variables.val + reg.log_inv_rate.val) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  step as ⟨i, hi⟩
  step as ⟨a, ha⟩
  have hav : a.val = 2 * 2 ^ (reg.num_variables.val + reg.log_inv_rate.val) := by
    rw [ha, hi, Nat.shiftLeft_eq, U128.size, U128.numBits, mul_comm]
    exact Nat.mod_eq_of_lt (by simp; omega)
  step as ⟨b, hb⟩
  have hbv : b.val = 2 * 2 ^ reg.log_inv_rate.val := by
    rw [hb, Nat.shiftLeft_eq, U128.size, U128.numBits, mul_comm]
    exact Nat.mod_eq_of_lt (by simp; omega)
  step*

/-- The leading zeros of a nonzero 128-bit `x` number `127 - log_2 x`. -/
@[step]
theorem leading_zeros128_spec (x : Std.U128) (hx : x.val ≠ 0) :
    CoreModels.core.num.U128.leading_zeros x ⦃ i => i.val = 127 - Nat.log2 x.val ⦄ := by
  simp only [CoreModels.core.num.U128.leading_zeros,
    CoreModels.rust_primitives.arithmetic.leading_zeros_u128, WP.spec_ok,
    Aeneas.Std.core.num.U128.leading_zeros, BitVec.leadingZeros]
  have h0 : x.bv ≠ 0 := fun h => hx (by simp [UScalar.val, h])
  simp only [h0, ↓reduceIte]
  show (BitVec.ofNat 32 (128 - Nat.log 2 x.bv.toNat - 1)).toNat = 127 - Nat.log2 x.val
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat, Nat.log2_eq_log_two]
  omega

@[step]
theorem usize_saturating_sub_spec (x y : Std.Usize) :
    core.num.Usize.saturating_sub_exposed x y ⦃ z => z.val = x.val - y.val ⦄ := by
  simp only [core.num.Usize.saturating_sub_exposed, WP.spec_ok]
  show (BitVec.ofNat _ (x.val - y.val)).toNat = _
  have := x.hBounds
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem numeratorSpec_ge (n r : ℕ) (hn : n ≠ 0) (hr : r ≠ 0) : 7 ≤ numeratorSpec n r := by
  have hc := numeratorSpec_closed n r
  have : 2 ^ r ≤ 2 ^ (n + r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (n + r) = 2 * 2 ^ (n + r - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The field security bits never panic on an accepted schedule.

The field error `numerator / 2^K` is then at most `2^-bits`, unless `bits = 0`. -/
theorem field_security_bits_spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) (hr : reg.log_inv_rate.val ≠ 0)
    (hn : reg.num_variables.val ≠ 0) :
    binary.BinaryPcsRegime.field_security_bits reg ⦃ y =>
      y.val = reg.challenge_field_bits.val - (Nat.log2 (numeratorSpec reg.num_variables.val
        reg.log_inv_rate.val - 1) + 1) ∧
      (y.val = 0 ∨ numeratorSpec reg.num_variables.val reg.log_inv_rate.val * 2 ^ y.val ≤
        2 ^ reg.challenge_field_bits.val) ⦄ := by
  unfold binary.BinaryPcsRegime.field_security_bits
  have hN := numeratorSpec_ge reg.num_variables.val reg.log_inv_rate.val hn hr
  set N := numeratorSpec reg.num_variables.val reg.log_inv_rate.val with hNdef
  have hc := numeratorSpec_closed reg.num_variables.val reg.log_inv_rate.val
  have hp : (2 : ℕ) ^ (reg.num_variables.val + reg.log_inv_rate.val) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hNlt : N < 2 ^ 66 := by omega
  have hlog : Nat.log2 (N - 1) < 66 := by rw [Nat.log2_lt (by omega)]; omega
  have hbits : (core.num.U128.BITS : Std.U32).val = 128 := by simp [core.num.U128.BITS]
  step*
  have hiv : i.val = N - 1 := by rw [i_post, numerator_post]
  have hi2 : i2.val = Nat.log2 (N - 1) + 1 := by
    rw [i2_post, i1_post, hiv, UScalarTy.U128_numBits_eq]; omega
  have hi3 : i3.val = Nat.log2 (N - 1) + 1 := by
    rw [i3_post, UScalar.cast_val_mod_pow_of_inBounds_eq, hi2]
    have h32 : (2 : ℕ) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
      rw [UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with h | h <;> simp [h]
    omega
  have hy : y.val = reg.challenge_field_bits.val - (Nat.log2 (N - 1) + 1) := by rw [y_post, hi3]
  refine ⟨hy, ?_⟩
  rcases Nat.eq_zero_or_pos y.val with h0 | hpos
  · exact Or.inl h0
  · right
    have hlt : N - 1 < 2 ^ (Nat.log2 (N - 1) + 1) := Nat.lt_log2_self
    calc N * 2 ^ y.val ≤ 2 ^ (Nat.log2 (N - 1) + 1) * 2 ^ y.val :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ reg.challenge_field_bits.val := by rw [← pow_add]; congr 1; omega

/-- Whether the queries are exhaustive never panics once the folding factor fits and the shift fits a word.

It says whether 2^(n + r - f) queries are asked, the cosets of the first batch. -/
theorem queries_are_exhaustive_spec (reg : binary.BinaryPcsRegime)
    (hnr : reg.num_variables.val + reg.log_inv_rate.val ≤ Usize.max)
    (hf : reg.log_folding_factor.val ≤ reg.num_variables.val + reg.log_inv_rate.val)
    (hw : reg.num_variables.val + reg.log_inv_rate.val - reg.log_folding_factor.val <
      UScalarTy.Usize.numBits) :
    binary.BinaryPcsRegime.queries_are_exhaustive reg ⦃ b =>
      b = decide (2 ^ (reg.num_variables.val + reg.log_inv_rate.val - reg.log_folding_factor.val) ≤
        reg.num_queries.val) ⦄ := by
  unfold binary.BinaryPcsRegime.queries_are_exhaustive
  step*
  have hv : i2.val = 2 ^ (reg.num_variables.val + reg.log_inv_rate.val -
      reg.log_folding_factor.val) := by
    rw [i2_post, Nat.one_shiftLeft, i1_post, i_post]
    exact Nat.mod_eq_of_lt (by
      rw [Usize.size, Usize.numBits_def]
      exact Nat.pow_lt_pow_right (by norm_num) hw)
  simp only [ge_iff_le, UScalar.le_equiv, hv]

/-- The security ceiling keeps one bit for the queries, unless they are exhaustive.

It never panics once the field security bits and the exhaustiveness check return. -/
theorem max_security_bits_spec (reg : binary.BinaryPcsRegime) (fsb : Std.Usize) (b : Bool)
    (hf : binary.BinaryPcsRegime.field_security_bits reg = .ok fsb)
    (hb : binary.BinaryPcsRegime.queries_are_exhaustive reg = .ok b) :
    binary.BinaryPcsRegime.max_security_bits reg ⦃ y =>
      y.val = fsb.val - if b then 0 else 1 ⦄ := by
  unfold binary.BinaryPcsRegime.max_security_bits
  rw [hf, hb]
  cases b <;> simp only [bind_ok, Bool.false_eq_true, ↓reduceIte] <;>
    exact usize_saturating_sub_spec fsb _

/-- On an accepted schedule whose first-batch exponent fits a word, the ceiling never panics.

It is the field security bits less one, unless the queries are exhaustive. -/
theorem max_security_bits_accepted (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) (hr : reg.log_inv_rate.val ≠ 0)
    (hn : reg.num_variables.val ≠ 0)
    (hf : reg.log_folding_factor.val ≤ reg.num_variables.val + reg.log_inv_rate.val)
    (hw : reg.num_variables.val + reg.log_inv_rate.val - reg.log_folding_factor.val <
      UScalarTy.Usize.numBits) :
    binary.BinaryPcsRegime.max_security_bits reg ⦃ y =>
      y.val = reg.challenge_field_bits.val - (Nat.log2 (numeratorSpec reg.num_variables.val
        reg.log_inv_rate.val - 1) + 1) -
        if 2 ^ (reg.num_variables.val + reg.log_inv_rate.val - reg.log_folding_factor.val) ≤
          reg.num_queries.val then 0 else 1 ⦄ := by
  obtain ⟨fsb, hfsb, hfv, -⟩ := spec_imp_exists (field_security_bits_spec reg h hr hn)
  have hmax : reg.num_variables.val + reg.log_inv_rate.val ≤ Usize.max := by
    have := usize_max_ge (n := 64) (by norm_num)
    simp only [Usize.max, UScalar.max, Usize.numBits_def] at *
    omega
  obtain ⟨b, hb, rfl⟩ := spec_imp_exists (queries_are_exhaustive_spec reg hmax hf hw)
  have := max_security_bits_spec reg fsb _ hfsb hb
  rw [← hfv]
  simpa using this

end Plonky3Lean.Proofs.Security.Binary
