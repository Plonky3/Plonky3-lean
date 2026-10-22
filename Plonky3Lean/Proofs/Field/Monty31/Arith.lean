import Plonky3Lean.Proofs.Field.Monty31.Element

/-!
# Monty31: scalar arithmetic is field arithmetic, for any valid parameters

The `MontyField31` operators `Add`, `Sub`, `Mul`, `Neg` and `PrimeCharacteristicRing::halve`, and `from_monty`, read through `Plonky3Lean.Spec.Monty31.toField`.

The operators are transcribed in `P3Monty31.Assumptions.Mirror`.
The `u32` arithmetic they wrap is extracted.

Each operator, on canonical inputs, is the field operation and returns a canonical value.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

theorem monty_31.MontyField31.new_monty.spec (v : Std.U32) :
    monty_31.MontyField31.new_monty inst v ⦃ c => c.value = v ⦄ := by
  unfold monty_31.MontyField31.new_monty
  rw [WP.spec_ok]

/-- `x · 2^(-32)` is determined by `x mod P`. -/
theorem toField_congr {P : ℕ} {x y : Element MP} (h : (x.value.val : ZMod P) = y.value.val) :
    toField P x = toField P y := by
  unfold toField; rw [h]

/-- `a + b`, for canonical `a` and `b`, is canonical and stands for `toField a + toField b`. -/
theorem monty_31.MontyField31.add.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.add inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a + toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  unfold monty_31.MontyField31.add
  refine WP.spec_bind (utils.add.spec hv _ _ ha hb) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  have hp0 : 0 < p.val := by have := hv.odd; omega
  refine ⟨by rw [← hP, hc, hv']; exact Nat.mod_lt _ hp0, ?_⟩
  unfold Spec.Monty31.toField
  rw [hc, hv', ← add_mul, ← Nat.cast_add, hP, ZMod.natCast_mod]

/-- `a - b`, for canonical `a` and `b`, is canonical and stands for `toField a - toField b`. -/
theorem monty_31.MontyField31.sub.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.sub inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a - toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  unfold monty_31.MontyField31.sub
  refine WP.spec_bind (utils.sub.spec hv _ _ ha hb) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  have hp0 : 0 < p.val := by have := hv.odd; omega
  refine ⟨by rw [← hP, hc, hv']; exact Nat.mod_lt _ hp0, ?_⟩
  unfold Spec.Monty31.toField
  rw [hc, hv', ← sub_mul, hP, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ← hP,
    ZMod.natCast_self, add_zero]

/-- `a · b`, for canonical `a` and `b`, is canonical and stands for `toField a · toField b`.

The `u64` product is below `p^2 < 2^32 p`, which is `monty_reduce`'s precondition. -/
theorem monty_31.MontyField31.mul.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.mul inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a * toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  have hp := hv.lt
  unfold monty_31.MontyField31.mul
  have hab : a.value.val * b.value.val < 2 ^ 32 * p.val :=
    calc a.value.val * b.value.val < p.val * p.val := Nat.mul_lt_mul'' ha hb
      _ ≤ 2 ^ 32 * p.val := Nat.mul_le_mul_right _ (by omega)
  step*
  have hlp : long_prod.val = a.value.val * b.value.val := by
    rw [long_prod_post, i_post, i1_post, cast_u32_u64_val, cast_u32_u64_val]
  refine WP.spec_bind (utils.monty_reduce.spec hv long_prod (by rw [hlp]; exact hab))
    fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  refine ⟨by rw [← hP, hc]; exact hv'.1, ?_⟩
  have h : ((v.val * 2 ^ 32 : ℕ) : ZMod P) = ((a.value.val * b.value.val : ℕ) : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hv'.2, hlp, ZMod.natCast_mod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hu := ZMod.mul_inv_of_unit _ (two_pow_32_isUnit (P := P) (hP ▸ hv.odd))
  unfold Spec.Monty31.toField
  rw [hc]
  calc (v.val : ZMod P) * (2 ^ 32)⁻¹
      = (v.val : ZMod P) * 2 ^ 32 * (2 ^ 32)⁻¹ * (2 ^ 32)⁻¹ := by rw [mul_assoc _ (2 ^ 32), hu,
        mul_one]
    _ = _ := by rw [h]; ring

/-- `from_monty(a.value)`, the body of `as_canonical_u32`, is the canonical `u32` for the field element `a` stands for.

Every `a` is accepted, canonical or not. -/
theorem from_monty.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P) (a : Element MP) :
    utils.from_monty inst a.value
      ⦃ r => r.val < P ∧ (r.val : ZMod P) = toField P a ⦄ := by
  refine WP.spec_mono (utils.from_monty.spec hv a.value) fun r hr => ?_
  refine ⟨hP ▸ hr.1, ?_⟩
  have h : ((r.val * 2 ^ 32 : ℕ) : ZMod P) = (a.value.val : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hr.2, ZMod.natCast_mod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hu := ZMod.mul_inv_of_unit _ (two_pow_32_isUnit (P := P) (hP ▸ hv.odd))
  unfold Spec.Monty31.toField
  rw [← h, mul_assoc, hu, mul_one]

variable {FP : Type} {finst : data_traits.FieldParameters FP}

/-- `-a`, for canonical `a`, is canonical and stands for `-toField a`.

It is `MONTY_ZERO - a`, so it needs `MONTY_ZERO` to stand for `0`, which `hz` states. -/
theorem monty_31.MontyField31.neg.toField (hv : FieldValid finst p mu) {P : ℕ}
    (hP : p.val = P)
    (hz : finst.MONTY_ZERO ⦃ z => Canonical P z ∧ toField P z = 0 ⦄)
    (a : Element FP) (ha : Canonical P a) :
    monty_31.MontyField31.neg finst a ⦃ c => Canonical P c ∧ toField P c = -toField P a ⦄ := by
  unfold monty_31.MontyField31.neg
  refine WP.spec_bind hz fun z hz' => ?_
  refine WP.spec_mono (monty_31.MontyField31.sub.toField hv.monty hP z a hz'.1 ha) fun c hc => ?_
  rw [hc.2, hz'.2, zero_sub]
  exact ⟨hc.1, rfl⟩

/-- `a.halve()`, for canonical `a`, is canonical and stands for `toField a / 2`. -/
theorem monty_31.MontyField31.halve.toField (hv : FieldValid finst p mu) {P : ℕ}
    (hP : p.val = P) (a : Element FP) (ha : Canonical P a) :
    monty_31.MontyField31.halve finst a ⦃ c => Canonical P c ∧ toField P c * 2 = toField P a ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha
  unfold monty_31.MontyField31.halve
  refine WP.spec_bind (utils.halve_u32.spec hv _ ha) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  refine ⟨by rw [← hP, hc]; exact hv'.1, ?_⟩
  have h : ((v.val * 2 : ℕ) : ZMod P) = (a.value.val : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hv'.2]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold Spec.Monty31.toField
  rw [hc, ← h]
  ring

end Plonky3Lean.Proofs.Monty31
