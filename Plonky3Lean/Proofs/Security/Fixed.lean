module

public import P3Security
public import Plonky3Lean.Lib.RustM
public import Plonky3Lean.Proofs.Security.FixedLog
import all Aeneas.Std.Scalar.SaturatingOps

@[expose] public section

/-!
# `p3_security::fixed`: the extracted fixed-point logarithm

`floor_log2` computes `FixedLog.flog`, so it never exceeds `2^16 · log2 x`
(`FixedLog.flog_le`), and panics exactly at `x = 0`. `ceil_log2` is exact on powers of two and
`floor_log2 x + 1` elsewhere, which falls below `2^16 · log2 x` at `x = 14917`.
-/

open Aeneas Aeneas.Std CoreModels p3_security
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Security.Fixed

open FixedLog

theorem or_two_pow_of_mul (q k : ℕ) : q * 2 ^ (k + 1) ||| 2 ^ k = q * 2 ^ (k + 1) + 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  have h : q * 2 ^ (k + 1) + 2 ^ k = 2 ^ k * (2 * q + 1) := by ring
  have h2 : q * 2 ^ (k + 1) = 2 ^ k * (2 * q) := by ring
  rw [h, h2, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
  by_cases hik : k ≤ i
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hik
    simp
    rcases j with _ | j
    · simp
    · simp [Nat.testBit_succ]; congr 1; omega
  · simp [hik]; omega

/-- One iteration of the extracted loop body is `FixedLog.step`, and the loop stops after bit 15. -/
theorem body_spec (x : ℕ) (r : Std.U64) (m : Std.U128) (b : Std.U32) (hb : b.val ≤ 16)
    (hinv : Inv x b.val (r.val, m.val, b.val)) :
    fixed.floor_log2_loop.body r m b ⦃ c => match c with
      | .done y => b.val = 16 ∧ y = r
      | .cont (r', m', b') => b.val < 16 ∧
          (r'.val, m'.val, b'.val) = step (r.val, m.val, b.val) ⦄ := by
  obtain ⟨-, h1, h2, F, hF, hr, -⟩ := hinv
  simp only at h1 h2 hr
  unfold fixed.floor_log2_loop.body
  simp only [fixed.FRACTIONAL_BITS]
  by_cases hlt : b < 16#u32
  · have hb' : b.val < 16 := by scalar_tac
    simp only [hlt, ↓reduceIte]
    step*
    have hi1 : i1.val = 2 ^ 33 := by
      rw [i1_post, Nat.shiftLeft_eq, U128.size, U128.numBits]; norm_num
    have hm1 : mantissa1.val = m.val * m.val / 2 ^ 32 := by
      rw [mantissa1_post, i_post, Nat.shiftRight_eq_div_pow]
    by_cases hc : mantissa1 ≥ i1
    · have hc' : 2 ^ 33 ≤ m.val * m.val / 2 ^ 32 := by rw [← hm1, ← hi1]; scalar_tac
      simp only [hc, ↓reduceIte]
      step as ⟨m3, hm3⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨r2, hr2⟩
      step as ⟨b1, hb1⟩
      refine ⟨hb', ?_⟩
      have hi3v : i3.val = 15 - b.val := by rw [hi3, hi2]
      have hi4v : i4.val = 2 ^ (15 - b.val) := by
        rw [hi4, hi3v, Nat.shiftLeft_eq, one_mul, U64.size, U64.numBits]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by simp; omega))
      have hr2v : r2.val = r.val + 2 ^ (15 - b.val) := by
        rw [hr2, UScalar.val_or, hi4v, hr]
        have : x.log2 * 2 ^ 16 + F * 2 ^ (16 - b.val) =
            (x.log2 * 2 ^ b.val + F) * 2 ^ (15 - b.val + 1) := by
          rw [show 15 - b.val + 1 = 16 - b.val by omega, add_mul, mul_assoc, ← pow_add,
            show b.val + (16 - b.val) = 16 by omega]
        rw [this, or_two_pow_of_mul]
      simp only [step, hc', ↓reduceIte, Prod.mk.injEq]
      refine ⟨hr2v, ?_, hb1⟩
      rw [hm3, hm1, Nat.shiftRight_eq_div_pow, pow_one]
    · have hc' : ¬ 2 ^ 33 ≤ m.val * m.val / 2 ^ 32 := by rw [← hm1, ← hi1]; scalar_tac
      simp only [hc, ↓reduceIte]
      step as ⟨b1, hb1⟩
      refine ⟨hb', ?_⟩
      simp only [step, hc', ↓reduceIte, Prod.mk.injEq]
      exact ⟨trivial, hm1, hb1⟩
  · have hb' : b.val = 16 := by scalar_tac
    simp only [hlt, ↓reduceIte, WP.spec_ok]
    exact ⟨hb', trivial⟩

theorem log2_lt_64 (x : Std.U64) : Nat.log2 x.val < 64 := by
  rcases Nat.eq_zero_or_pos x.val with h | h
  · simp [h]
  · rw [Nat.log2_lt (by omega)]; exact x.hBounds

/-- The loop runs the remaining iterations of `FixedLog.iter` and returns `flog x`. -/
theorem loop_spec (x : Std.U64) (hx : 0 < x.val) (r : Std.U64) (m : Std.U128) (b : Std.U32)
    (hb : b.val ≤ 16) (h : (r.val, m.val, b.val) = iter x.val b.val) :
    fixed.floor_log2_loop r m b ⦃ y => y.val = flog x.val ⦄ := by
  unfold fixed.floor_log2_loop
  apply loop.spec_decr_nat (fun s => 16 - s.2.2.val)
    (fun s => s.2.2.val ≤ 16 ∧ (s.1.val, s.2.1.val, s.2.2.val) = iter x.val s.2.2.val)
  · rintro ⟨r', m', b'⟩ ⟨hb', hs⟩
    simp only at hb' hs
    have hinv : Inv x.val b'.val (r'.val, m'.val, b'.val) := by
      rw [hs]; exact iter_inv x.val hx _ hb'
    refine WP.spec_mono (body_spec x.val r' m' b' hb' hinv) ?_
    rintro (⟨r'', m'', b''⟩ | y) hc
    · obtain ⟨hlt, hstep⟩ := hc
      have hb'' : b''.val = b'.val + 1 := by
        have := congrArg (fun s => s.2.2) hstep
        simp only [step] at this; split_ifs at this <;> simpa using this
      refine ⟨⟨by simp only; omega, ?_⟩, by simp only; omega⟩
      simp only
      rw [hstep, hs, hb'']; rfl
    · obtain ⟨h16, rfl⟩ := hc
      rw [flog, ← h16, ← hs]
  · exact ⟨hb, h⟩

/-- `u64::leading_zeros` of a nonzero value is `63 - log2 x`. -/
@[step]
theorem leading_zeros_spec (x : Std.U64) (hx : x.val ≠ 0) :
    CoreModels.core.num.U64.leading_zeros x ⦃ i => i.val = 63 - Nat.log2 x.val ⦄ := by
  simp only [CoreModels.core.num.U64.leading_zeros,
    CoreModels.rust_primitives.arithmetic.leading_zeros_u64, WP.spec_ok,
    Aeneas.Std.core.num.U64.leading_zeros, BitVec.leadingZeros]
  have h0 : x.bv ≠ 0 := fun h => hx (by simp [UScalar.val, h])
  simp only [h0, ↓reduceIte]
  show (BitVec.ofNat 32 (64 - Nat.log 2 x.bv.toNat - 1)).toNat = 63 - Nat.log2 x.val
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat, Nat.log2_eq_log_two]
  omega

/-- `floor_log2 x` is `flog x` for every nonzero `x`. -/
@[step]
theorem floor_log2_spec (x : Std.U64) (hx : x.val ≠ 0) :
    fixed.floor_log2 x ⦃ y => y.val = flog x.val ⦄ := by
  unfold fixed.floor_log2
  simp only [fixed.FRACTIONAL_BITS]
  have hlog := log2_lt_64 x
  step as ⟨hu⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = 63 - Nat.log2 x.val := by rw [hi1]; simp [UScalar.cast_val_eq, hi]; omega
  step as ⟨ip, hip⟩
  have hipv : ip.val = Nat.log2 x.val := by omega
  step as ⟨res, hres⟩
  have hresv : res.val = Nat.log2 x.val * 2 ^ 16 := by
    rw [hres, hipv, Nat.shiftLeft_eq, U64.size, U64.numBits]
    exact Nat.mod_eq_of_lt (by simp; omega)
  have hlo : 2 ^ Nat.log2 x.val ≤ x.val := Nat.log2_self_le hx
  have hhi : x.val < 2 ^ (Nat.log2 x.val + 1) := Nat.lt_log2_self
  by_cases hc : ip ≥ 32#u64
  · have hc0 : (32#u64 : Std.U64).val ≤ ip.val := hc
    have hc' : 32 ≤ Nat.log2 x.val := by simp at hc0; omega
    simp only [hc, ↓reduceIte]
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨mant, hmant⟩
    apply loop_spec x (by omega) res mant 0#u32 (by simp)
    rw [show (0#u32 : Std.U32).val = 0 from rfl, iter, init]
    simp only [hc', ↓reduceIte, Prod.mk.injEq]
    refine ⟨hresv, ?_, trivial⟩
    rw [hmant, Nat.shiftRight_eq_div_pow, hi3, hipv, hi2]
    simp
  · have hc0 : ¬ (32#u64 : Std.U64).val ≤ ip.val := hc
    have hc' : ¬ 32 ≤ Nat.log2 x.val := by simp at hc0; omega
    simp only [hc, ↓reduceIte]
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨mant, hmant⟩
    apply loop_spec x (by omega) res mant 0#u32 (by simp)
    rw [show (0#u32 : Std.U32).val = 0 from rfl, iter, init]
    simp only [hc', ↓reduceIte, Prod.mk.injEq]
    refine ⟨hresv, ?_, trivial⟩
    have hi2v : i2.val = x.val := by rw [hi2]; simp
    rw [hmant, hi2v, hi3, hipv, Nat.shiftLeft_eq, U128.size, U128.numBits]
    apply Nat.mod_eq_of_lt
    have h33 : x.val * 2 ^ (32 - Nat.log2 x.val) <
        2 ^ (Nat.log2 x.val + 1) * 2 ^ (32 - Nat.log2 x.val) :=
      Nat.mul_lt_mul_of_pos_right hhi (by positivity)
    rw [← pow_add, show Nat.log2 x.val + 1 + (32 - Nat.log2 x.val) = 33 by omega] at h33
    calc _ < 2 ^ 33 := h33
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by simp)

/-- `floor_log2 0` panics. -/
theorem floor_log2_zero : fixed.floor_log2 0#u64 = .fail .panic := by
  simp [fixed.floor_log2, massert]

/-- `u64::is_power_of_two`: the test `x ≠ 0 ∧ x &&& (x - 1) = 0`. -/
@[step]
theorem is_power_of_two_spec (x : Std.U64) :
    CoreModels.core.num.U64.is_power_of_two x ⦃ b =>
      b = true ↔ x.val ≠ 0 ∧ x.val &&& (x.val - 1) = 0 ⦄ := by
  unfold CoreModels.core.num.U64.is_power_of_two
  by_cases h0 : x.val = 0
  · have : (x != 0#u64) = false := by simp; scalar_tac
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp [h0]
  · have : (x != 0#u64) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte]
    step*

/-- `u64::trailing_zeros` of `2^k` is `k`. -/
@[step]
theorem trailing_zeros_pow (x : Std.U64) (k : ℕ) (hk : k < 64) (hx : x.val = 2 ^ k) :
    CoreModels.core.num.U64.trailing_zeros x ⦃ i => i.val = k ⦄ := by
  simp only [CoreModels.core.num.U64.trailing_zeros, WP.spec_ok]
  have : ((List.range 64).find? fun i => x.val.testBit i) = some k := by
    rw [List.find?_range_eq_some, hx]
    refine ⟨by simp, by simp [hk], fun j hj => ?_⟩
    simp [Nat.testBit_two_pow]; omega
  rw [this]
  show (BitVec.ofNat 32 k).toNat = k
  rw [BitVec.toNat_ofNat]; omega

/-- `from_bits b = b · 2^16`. -/
@[step]
theorem from_bits_spec (b : Std.U32) : fixed.from_bits b ⦃ y => y.val = b.val * 2 ^ 16 ⦄ := by
  unfold fixed.from_bits
  simp only [fixed.FRACTIONAL_BITS]
  step*

/-- `flog x < 64 · 2^16` for a `u64`. -/
theorem flog_lt (x : Std.U64) (hx : x.val ≠ 0) : flog x.val < 64 * 2 ^ 16 := by
  have h := flog_le x.val (by omega)
  have hx' : x.val ^ 2 ^ 16 < (2 ^ 64) ^ 2 ^ 16 :=
    Nat.pow_lt_pow_left x.hBounds (by positivity)
  rw [← pow_mul] at hx'
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h hx')

/-- `ceil_log2 x` is `clog x` for every nonzero `x`: exact on a power of two, `floor_log2 x + 1`
elsewhere. -/
@[step]
theorem ceil_log2_spec (x : Std.U64) (h0 : x.val ≠ 0) :
    fixed.ceil_log2 x ⦃ y => y.val = clog x.val ⦄ := by
  unfold fixed.ceil_log2
  have := flog_lt x h0
  step as ⟨b, hb⟩
  by_cases hp : x.val &&& (x.val - 1) = 0
  · have hbt : b = true := hb.mpr ⟨h0, hp⟩
    have h2 := eq_two_pow_of_and x.val h0 hp
    simp only [hbt, ↓reduceIte]
    step as ⟨i, hi⟩
    · exact log2_lt_64 x
    step as ⟨y, hy⟩
    simp [clog, hp, hy, hi]
  · have hbf : b = false := by
      cases b
      · rfl
      · exact absurd (hb.mp rfl).2 hp
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    step*
    simp [clog, *]

/-- `ceil_log2 0` panics. -/
theorem ceil_log2_zero : fixed.ceil_log2 0#u64 = .fail .panic := by
  simp [fixed.ceil_log2, CoreModels.core.num.U64.is_power_of_two, fixed.floor_log2, massert]

/-- **`ceil_log2` does not round up.** At `x = 14917` it returns `908635`, and
`2^908635 < 14917^(2^16)`: the result is below `2^16 · log2 14917`. -/
theorem ceil_log2_14917 :
    fixed.ceil_log2 14917#u64 ⦃ y => y.val = 908635 ∧ 2 ^ y.val < 14917 ^ 2 ^ 16 ⦄ := by
  refine WP.spec_mono (ceil_log2_spec 14917#u64 (by decide)) ?_
  intro y hy
  have hc : clog 14917 = 908635 := by
    simp only [clog, show (14917 &&& (14917 - 1) = 0) = False by decide, ite_false, flog_14917]
  rw [show (14917#u64 : Std.U64).val = 14917 from rfl, hc] at hy
  exact ⟨hy, hy ▸ log2_14917_bounds.1⟩

/-- `u64::saturating_sub` is truncated subtraction. -/
@[step]
theorem u64_saturating_sub_spec (x y : Std.U64) :
    CoreModels.core.num.U64.saturating_sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  simp only [CoreModels.core.num.U64.saturating_sub,
    CoreModels.rust_primitives.arithmetic.saturating_sub_u64, WP.spec_ok, UScalar.saturating_sub]
  show (BitVec.ofNat 64 (max 0 (x.val - y.val))).toNat = _
  have := x.hBounds
  rw [BitVec.toNat_ofNat]; simp only [Nat.zero_max]
  exact Nat.mod_eq_of_lt (by simp at this ⊢; omega)

/-- `bits_per_query` never panics, and computes `FixedLog.bpq`. -/
theorem bits_per_query_spec (b : Std.U32) (f : Std.U64) :
    fixed.bits_per_query b f ⦃ y => y.val = bpq b.val f.val ⦄ := by
  unfold fixed.bits_per_query
  have hmax : (core.num.U32.MAX : Std.U32).val = 2 ^ 32 - 1 := by
    simp [core.num.U32.MAX, U32.rMax]
  by_cases hb : b = 0#u32
  · simp [hb, bpq]
  · by_cases hf : f = 0#u64
    · simp [hb, hf, bpq]
    · simp only [hb, hf, ↓reduceIte]
      have hb0 : b.val ≠ 0 := fun h => hb (by scalar_tac)
      have hf0 : f.val ≠ 0 := fun h => hf (by scalar_tac)
      step as ⟨m, hm⟩
      have hmv : m.val = (2 ^ 32 - 1) * 2 ^ 16 := by rw [hm]; simp [U32.rMax]
      by_cases hgt : f > m
      · have hlt : (2 ^ 32 - 1) * 2 ^ 16 < f.val := by rw [← hmv]; scalar_tac
        simp only [hgt, ↓reduceIte, WP.spec_ok]
        simp [bpq, hb0, hf0]; omega
      · have hle : f.val ≤ (2 ^ 32 - 1) * 2 ^ 16 := by rw [← hmv]; scalar_tac
        simp only [hgt, ↓reduceIte]
        have hbb : b.val < 2 ^ 32 := b.hBounds
        unfold fixed.LOG2_E
        step as ⟨u, hu⟩
        step as ⟨i1, hi1⟩
        step as ⟨num, hnum⟩
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        have hmono : flog f.val ≤ clog num.val :=
          le_trans (flog_mono _ _ (by omega)) (flog_le_clog _ (by omega))
        step as ⟨c, hc⟩
        step as ⟨y, hy⟩
        have hnot : ¬ (b.val = 0 ∨ f.val = 0 ∨ (2 ^ 32 - 1) * 2 ^ 16 < f.val) := by omega
        rw [bpq, ite_eq_right_of_eq_false _ _ (eq_false hnot), hy, hc, hi2, hi3, hu, hnum, hi1, hu]

end Plonky3Lean.Proofs.Security.Fixed
