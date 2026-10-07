import Plonky3Lean.Proofs.Field.BabyBear.Constants

/-!
# BabyBear: scalar arithmetic

The `u32` arithmetic of p3-monty-31's `utils` (`add`, `sub`, `monty_reduce`,
`halve_u32`, `from_monty`), extracted, at BabyBear's parameters; and the
`MontyField31` operators that wrap them (`Add`, `Sub`, `Mul`, `Neg`,
`Field::halve`), transcribed in `P3Monty31.Assumptions.Mirror`, read through
`Plonky3Lean.Spec.BabyBear.toField`: each is the field operation, and keeps
values canonical.

The `utils` statements use the literal `p = 2013265921`; the claims restate
them with `BabyBear.fieldSize`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear

namespace Plonky3Lean.Proofs.BabyBear

/-! ## The `u32` helpers -/

/-- The arithmetic core of `monty_reduce`, when `x - t·p` underflows. -/
theorem monty_core_lt (x t : ℕ) (hx : x < 2 ^ 32 * 2013265921) (htlt : t < 2 ^ 32)
    (ht : (t * 2013265921) % 2 ^ 32 = x % 2 ^ 32) (hlt : x < t * 2013265921) :
    ((x + 2 ^ 64 - t * 2013265921) / 2 ^ 32 % 2 ^ 32 + 2013265921) % 2 ^ 32 < 2013265921 ∧
    (((x + 2 ^ 64 - t * 2013265921) / 2 ^ 32 % 2 ^ 32 + 2013265921) % 2 ^ 32 * 2 ^ 32)
      % 2013265921 = x % 2013265921 := by
  obtain ⟨k, hk⟩ : ∃ k, t * 2013265921 - x = k * 2 ^ 32 :=
    ⟨(t * 2013265921 - x) / 2 ^ 32, by omega⟩
  have h1 : (x + 2 ^ 64 - t * 2013265921) / 2 ^ 32 = 2 ^ 32 - k := by omega
  have hk0 : 0 < k := by omega
  have hkp : k < 2013265921 := by omega
  rw [h1, Nat.mod_eq_of_lt (by omega : 2 ^ 32 - k < 2 ^ 32),
    show 2 ^ 32 - k + 2013265921 = (2013265921 - k) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega : 2013265921 - k < 2 ^ 32)]
  omega

theorem monty_core_ge (x t : ℕ) (hx : x < 2 ^ 32 * 2013265921)
    (ht : (t * 2013265921) % 2 ^ 32 = x % 2 ^ 32) (hge : ¬ x < t * 2013265921) :
    ((x - t * 2013265921) / 2 ^ 32 % 2 ^ 32 + 0) % 2 ^ 32 < 2013265921 ∧
    (((x - t * 2013265921) / 2 ^ 32 % 2 ^ 32 + 0) % 2 ^ 32 * 2 ^ 32) % 2013265921 =
      x % 2013265921 := by
  obtain ⟨k, hk⟩ : ∃ k, x - t * 2013265921 = k * 2 ^ 32 :=
    ⟨(x - t * 2013265921) / 2 ^ 32, by omega⟩
  have hkp : k < 2013265921 := by omega
  rw [hk, Nat.mul_div_cancel _ (by norm_num), Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32)]
  omega

theorem MontyParams.MONTY_MASK.eq : MontyParams.MONTY_MASK = .ok 4294967295#u32 := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS
  rfl

/-- `monty_reduce` on an input below `2 ^ 32 · p` returns `x · 2^(-32) mod p`,
fully reduced. -/
theorem utils.monty_reduce.spec (x : Std.U64) (hx : x.val < 2 ^ 32 * 2013265921) :
    p3_monty_31.utils.monty_reduce MontyParams x ⦃ r => r.val < 2013265921 ∧
      (r.val * 2 ^ 32) % 2013265921 = x.val % 2013265921 ⦄ := by
  unfold p3_monty_31.utils.monty_reduce
  rw [MontyParams.MONTY_MASK.eq]
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
    baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU
    baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS
  simp only [CoreModels.core.num.U64.wrapping_mul, CoreModels.rust_primitives.arithmetic.wrapping_mul_u64,
    CoreModels.core.num.U64.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u64,
    CoreModels.core.num.U32.wrapping_add, CoreModels.rust_primitives.arithmetic.wrapping_add_u32,
    uoverflowing_sub]
  have hsize : UScalar.size UScalarTy.U64 = 2 ^ 64 := by
    simp only [UScalar.size, UScalarTy.U64_numBits_eq]
  have hsize32 : UScalar.size UScalarTy.U32 = 2 ^ 32 := by
    simp only [UScalar.size, UScalarTy.U32_numBits_eq]
  have ht : ∀ (i1 i4 t : Std.U64), i1 = UScalar.cast .U64 2281701377#u32 →
      i4 = UScalar.cast .U64 4294967295#u32 → t.val = (x.wrapping_mul i1 &&& i4).val →
      t.val = x.val * 2281701377 % 2 ^ 64 % 2 ^ 32 := by
    rintro i1 i4 t rfl rfl h
    rw [h, UScalar.val_and, U64.wrapping_mul_val_eq, UScalar.cast_val_eq, UScalar.cast_val_eq,
      show (4294967295#u32).val % 2 ^ UScalarTy.U64.numBits = 2 ^ 32 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simp only [show (2281701377#u32).val % 2 ^ UScalarTy.U64.numBits = 2281701377 by rfl,
      hsize]
  step*
  · have := ht i1 i4 t i1_post i4_post t_post1
    rw [i6_post, UScalar.cast_val_eq, this]
    have : x.val * 2281701377 % 2 ^ 64 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    scalar_tac
  · have htv := ht i1 i4 t i1_post i4_post t_post1
    have hi6 : i6.val = 2013265921 := by rw [i6_post, UScalar.cast_val_eq]; rfl
    have hcong : (t.val * 2013265921) % 2 ^ 32 = x.val % 2 ^ 32 := by
      rw [htv, Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64), Nat.mod_mul_mod, Nat.mul_assoc,
        Nat.mul_mod, show 2281701377 * 2013265921 % 2 ^ 32 = 1 by norm_num]
      simp
    have htlt : t.val < 2 ^ 32 := by rw [htv]; exact Nat.mod_lt _ (by norm_num)
    rw [hi6] at u_post
    have hsub := UScalar.overflowing_sub_eq x u
    simp only [UScalar.overflowing_sub] at hsub
    split at hsub
    all_goals rename_i hlt
    all_goals obtain ⟨hsub, -⟩ := hsub
    · rw [hsize] at hsub
      simp only [hlt, decide_true, ↓reduceIte]
      step*
      have hi8 : i8.val = (x.val + 2 ^ 64 - t.val * 2013265921) / 2 ^ 32 := by
        rw [i8_post1, Nat.shiftRight_eq_div_pow]; congr 1; omega
      have hr : (x_sub_u_hi.wrapping_add 2013265921#u32).val =
          ((x.val + 2 ^ 64 - t.val * 2013265921) / 2 ^ 32 % 2 ^ 32 + 2013265921) % 2 ^ 32 := by
        rw [U32.wrapping_add_val_eq, x_sub_u_hi_post, UScalar.cast_val_eq, hi8]
        simp only [UScalarTy.U32_numBits_eq, hsize32]; rfl
      rw [hr]
      exact monty_core_lt x.val t.val hx htlt hcong (u_post ▸ hlt)
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      step*
      have hi8 : i8.val = (x.val - t.val * 2013265921) / 2 ^ 32 := by
        rw [i8_post1, Nat.shiftRight_eq_div_pow]; congr 1; omega
      have hr : (x_sub_u_hi.wrapping_add 0#u32).val =
          ((x.val - t.val * 2013265921) / 2 ^ 32 % 2 ^ 32 + 0) % 2 ^ 32 := by
        rw [U32.wrapping_add_val_eq, x_sub_u_hi_post, UScalar.cast_val_eq, hi8]
        simp only [UScalarTy.U32_numBits_eq, hsize32]; rfl
      rw [hr]
      exact monty_core_ge x.val t.val hx hcong (u_post ▸ hlt)


theorem size_u32 : UScalar.size UScalarTy.U32 = 2 ^ 32 := by
  simp only [UScalar.size, UScalarTy.U32_numBits_eq]

/-- `add` of two canonical values is their sum mod `p`. -/
theorem utils.add.spec (a b : Std.U32) (ha : a.val < 2013265921) (hb : b.val < 2013265921) :
    p3_monty_31.utils.add MontyParams a b ⦃ r => r.val = (a.val + b.val) % 2013265921 ⦄ := by
  unfold p3_monty_31.utils.add
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  simp only [CoreModels.core.num.U32.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u32]
  step*
  rcases h : uoverflowing_sub sum 2013265921#u32 with ⟨cs, ov⟩
  have hcs : cs = (UScalar.overflowing_sub sum 2013265921#u32).1 := by
    rw [show cs = (uoverflowing_sub sum 2013265921#u32).1 by rw [h]]; rfl
  have hov : ov = decide (sum.val < 2013265921) := by
    rw [show ov = (uoverflowing_sub sum 2013265921#u32).2 by rw [h]]; rfl
  have hsub := UScalar.overflowing_sub_eq sum 2013265921#u32
  dsimp only at hsub
  rw [← hcs, show (2013265921#u32).val = 2013265921 from rfl, size_u32] at hsub
  show (if ov = true then RustM.ok sum else RustM.ok cs) ⦃ r => r.val = (a.val + b.val) % 2013265921 ⦄
  subst hov
  split at hsub <;> rename_i hlt <;> obtain ⟨hsub, -⟩ := hsub
  · rw [if_pos (by simpa using hlt), Aeneas.Std.WP.spec_ok]
    omega
  · rw [if_neg (by simpa using hlt), Aeneas.Std.WP.spec_ok]
    omega

/-- `sub` of two canonical values is their difference mod `p`. -/
theorem utils.sub.spec (a b : Std.U32) (ha : a.val < 2013265921) (hb : b.val < 2013265921) :
    p3_monty_31.utils.sub MontyParams a b ⦃ r => r.val = (a.val + 2013265921 - b.val) % 2013265921 ⦄ := by
  unfold p3_monty_31.utils.sub
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  simp only [CoreModels.core.num.U32.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u32,
    CoreModels.core.num.U32.wrapping_add, CoreModels.rust_primitives.arithmetic.wrapping_add_u32, bind_tc_ok]
  rcases h : uoverflowing_sub a b with ⟨d, ov⟩
  have hd : d = (UScalar.overflowing_sub a b).1 := by
    rw [show d = (uoverflowing_sub a b).1 by rw [h]]; rfl
  have hov : ov = decide (a.val < b.val) := by
    rw [show ov = (uoverflowing_sub a b).2 by rw [h]]; rfl
  have hsub := UScalar.overflowing_sub_eq a b
  dsimp only at hsub
  rw [← hd, size_u32] at hsub
  show (do
      let corr ← if ov = true then RustM.ok 2013265921#u32 else RustM.ok 0#u32
      RustM.ok (d.wrapping_add corr)) ⦃ r => r.val = (a.val + 2013265921 - b.val) % 2013265921 ⦄
  subst hov
  split at hsub <;> rename_i hlt <;> obtain ⟨hsub, -⟩ := hsub
  · rw [if_pos (by simpa using hlt), bind_tc_ok, Aeneas.Std.WP.spec_ok, UScalar.wrapping_add_val_eq,
      size_u32, show (2013265921#u32).val = 2013265921 from rfl]
    omega
  · rw [if_neg (by simpa using hlt), bind_tc_ok, Aeneas.Std.WP.spec_ok, UScalar.wrapping_add_val_eq,
      size_u32, show (0#u32).val = 0 from rfl]
    omega

/-- `halve_u32` of a canonical value `a` is the canonical `r` with `2r ≡ a`. -/
theorem utils.halve_u32.spec (a : Std.U32) (ha : a.val < 2013265921) :
    p3_monty_31.utils.halve_u32 FieldParams a ⦃ r => r.val < 2013265921 ∧ (r.val * 2) % 2013265921 = a.val ⦄ := by
  unfold p3_monty_31.utils.halve_u32
  dsimp only
  have hP : (baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME).val = 2013265921 := by
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME; rfl
  step*
  case h_fail =>
    rw [i_post1, x_post, hP, shr_post1, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    scalar_tac
  case h1 hlo =>
    have : lo_bit.val = 0 := by rw [hlo]; rfl
    rw [lo_bit_post1, UScalar.val_and, show (1#u32).val = 1 from rfl, Nat.and_one_is_mod] at this
    rw [shr_post1, Nat.shiftRight_eq_div_pow]
    omega
  case h2 hlo =>
    have : lo_bit.val ≠ 0 := fun h => hlo (UScalar.eq_of_val_eq (by rw [h]; rfl))
    rw [lo_bit_post1, UScalar.val_and, show (1#u32).val = 1 from rfl, Nat.and_one_is_mod] at this
    rw [shr_corr_post, i_post1, x_post, hP, shr_post1, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    omega

/-- `from_monty x` is `monty_reduce x`, on an input below `2 ^ 32`. -/
theorem utils.from_monty.spec (x : Std.U32) :
    p3_monty_31.utils.from_monty MontyParams x ⦃ r => r.val < 2013265921 ∧
      (r.val * 2 ^ 32) % 2013265921 = x.val % 2013265921 ⦄ := by
  unfold p3_monty_31.utils.from_monty
  step
  have hc : (UScalar.cast UScalarTy.U64 x).val = x.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
  have := utils.monty_reduce.spec (UScalar.cast .U64 x) (by rw [hc]; scalar_tac)
  rw [hc] at this
  rw [i_post]
  exact this

/-! ## The operators, as field operations -/

theorem fieldSize_eq : BabyBear.fieldSize = 2013265921 := rfl

/-- Two naturals congruent mod `p` are equal in `BabyBear.Field`. -/
theorem natCast_eq_of_mod {a b : ℕ} (h : a % 2013265921 = b % 2013265921) :
    (a : BabyBear.Field) = b :=
  (ZMod.natCast_eq_natCast_iff' a b BabyBear.fieldSize).mpr h

theorem new_monty.spec (v : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new_monty MontyParams v ⦃ c => c.value = v ⦄ := by
  unfold p3_monty_31.monty_31.MontyField31.new_monty
  rw [Aeneas.Std.WP.spec_ok]

/-- `a + b`, for canonical `a` and `b`, is canonical and stands for
`toField a + toField b`. -/
theorem baby_bear.BabyBear.add.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.add MontyParams a b
      ⦃ c => Canonical c ∧ Spec.BabyBear.toField c = Spec.BabyBear.toField a + Spec.BabyBear.toField b ⦄ := by
  unfold Canonical at *
  rw [fieldSize_eq] at ha hb
  unfold p3_monty_31.monty_31.MontyField31.add
  refine Aeneas.Std.WP.spec_bind (utils.add.spec _ _ ha hb) fun v hv => ?_
  refine Aeneas.Std.WP.spec_mono (new_monty.spec v) fun c hc => ?_
  unfold Spec.BabyBear.toField
  rw [hc, hv]
  refine ⟨by rw [fieldSize_eq]; exact Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← add_mul, ← Nat.cast_add]
  congr 1
  exact natCast_eq_of_mod (Nat.mod_mod _ _)

/-- `a - b`, for canonical `a` and `b`, is canonical and stands for
`toField a - toField b`. -/
theorem baby_bear.BabyBear.sub.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.sub MontyParams a b
      ⦃ c => Canonical c ∧ Spec.BabyBear.toField c = Spec.BabyBear.toField a - Spec.BabyBear.toField b ⦄ := by
  unfold Canonical at *
  rw [fieldSize_eq] at ha hb
  unfold p3_monty_31.monty_31.MontyField31.sub
  refine Aeneas.Std.WP.spec_bind (utils.sub.spec _ _ ha hb) fun v hv => ?_
  refine Aeneas.Std.WP.spec_mono (new_monty.spec v) fun c hc => ?_
  unfold Spec.BabyBear.toField
  rw [hc, hv]
  refine ⟨by rw [fieldSize_eq]; exact Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← sub_mul]
  congr 1
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
    show ((2013265921 : ℕ) : BabyBear.Field) = 0 from ZMod.natCast_self _, add_zero]

/-- `a · b`, for canonical `a` and `b`, is canonical and stands for
`toField a · toField b`. -/
theorem baby_bear.BabyBear.mul.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.mul MontyParams a b
      ⦃ c => Canonical c ∧ Spec.BabyBear.toField c = Spec.BabyBear.toField a * Spec.BabyBear.toField b ⦄ := by
  unfold Canonical at *
  rw [fieldSize_eq] at ha hb
  unfold p3_monty_31.monty_31.MontyField31.mul
  have hca : (UScalar.cast UScalarTy.U64 a.value).val = a.value.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
  have hcb : (UScalar.cast UScalarTy.U64 b.value).val = b.value.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
  have hab : a.value.val * b.value.val < 2 ^ 32 * 2013265921 := by
    calc a.value.val * b.value.val < 2013265921 * 2013265921 := Nat.mul_lt_mul'' ha hb
      _ ≤ 2 ^ 32 * 2013265921 := by norm_num
  step*
  have hlp : long_prod.val = a.value.val * b.value.val := by
    rw [long_prod_post, i_post, i1_post, hca, hcb]
  refine Aeneas.Std.WP.spec_bind (utils.monty_reduce.spec long_prod (by rw [hlp]; exact hab))
    fun v hv => ?_
  refine Aeneas.Std.WP.spec_mono (new_monty.spec v) fun c hc => ?_
  unfold Spec.BabyBear.toField
  rw [hc]
  refine ⟨by rw [fieldSize_eq]; exact hv.1, ?_⟩
  have h := natCast_eq_of_mod hv.2
  rw [hlp] at h
  push_cast at h
  have h2 := two_pow_32_ne_zero
  field_simp
  linear_combination h

/-- `-a`, for canonical `a`, is canonical and stands for `-toField a`. -/
theorem baby_bear.BabyBear.neg.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.neg FieldParams a
      ⦃ c => Canonical c ∧ Spec.BabyBear.toField c = -Spec.BabyBear.toField a ⦄ := by
  unfold p3_monty_31.monty_31.MontyField31.neg
  refine Aeneas.Std.WP.spec_bind FieldParams.MONTY_ZERO.toField fun z hz => ?_
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.sub.toField z a hz.1 ha) fun c hc => ?_
  rw [hc.2, hz.2, zero_sub]
  exact ⟨hc.1, rfl⟩

/-- `a.halve()`, for canonical `a`, is canonical and stands for `toField a / 2`. -/
theorem baby_bear.BabyBear.halve.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.halve FieldParams a
      ⦃ c => Canonical c ∧ Spec.BabyBear.toField c * 2 = Spec.BabyBear.toField a ⦄ := by
  unfold Canonical at *
  rw [fieldSize_eq] at ha
  unfold p3_monty_31.monty_31.MontyField31.halve
  refine Aeneas.Std.WP.spec_bind (utils.halve_u32.spec _ ha) fun v hv => ?_
  refine Aeneas.Std.WP.spec_mono (new_monty.spec v) fun c hc => ?_
  unfold Spec.BabyBear.toField
  rw [hc]
  refine ⟨by rw [fieldSize_eq]; exact hv.1, ?_⟩
  have h := natCast_eq_of_mod (a := v.val * 2) (b := a.value.val) (by rw [hv.2, Nat.mod_eq_of_lt ha])
  push_cast at h
  rw [← h]
  ring

/-- `from_monty(a.value)`, the body of `as_canonical_u32`, is the canonical
`u32` for the field element `a` stands for. -/
theorem baby_bear.BabyBear.from_monty.toField (a : Element) :
    p3_monty_31.utils.from_monty MontyParams a.value
      ⦃ r => r.val < BabyBear.fieldSize ∧ (r.val : BabyBear.Field) = Spec.BabyBear.toField a ⦄ := by
  refine Aeneas.Std.WP.spec_mono (utils.from_monty.spec a.value) fun r hr => ?_
  refine ⟨by rw [fieldSize_eq]; exact hr.1, ?_⟩
  have h := natCast_eq_of_mod hr.2
  push_cast at h
  unfold Spec.BabyBear.toField
  rw [← h]
  field_simp [two_pow_32_ne_zero]
  norm_num

end Plonky3Lean.Proofs.BabyBear
