module

public import Plonky3Lean.Proofs.Field.Binary.LinearSqrt
public import Plonky3Lean.Proofs.Field.Binary.TowerFrobenius

@[expose] public section

/-!
# Square roots at every level of the tower

From `GF(2^16)` up, `try_sqrt` reads the root off `linear.rs`'s byte tables (`sqrtNat`). Below,
it returns `a^(2^(BITS - 1))`, which squares to `a^(2^BITS) = a`. Every element has a root:
squaring is a bijection in characteristic 2.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- What `try_sqrt` returns at level `k`: a canonical square root. -/
def SqrtSpec (k : ℕ) {ty : UScalarTy} (a : UScalar ty) (r : core.option.Option (UScalar ty)) :
    Prop :=
  ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ k ∧ towerOf k c * towerOf k c = towerOf k a

/-- `sqrtNat` is a square root in the field. -/
theorem towerOf_sqrtNat {k : ℕ} {ty₁ ty₂ : UScalarTy} {a : UScalar ty₁} {c : UScalar ty₂}
    (ha : a.val < 2 ^ 2 ^ k) (hc : c.val = sqrtNat k a.val) :
    towerOf k c * towerOf k c = towerOf k a :=
  (towerOf_mul (by rw [hc, ← sqNat_eq k (sqrtNat_lt ha), sqNat_sqrtNat ha])).symm

/-! ## `GF(2)` -/

/-- `try_sqrt` at `GF(2)`, for a canonical `a`: every element is its own root. -/
theorem gf2_try_sqrt_spec (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 0 a r ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldField.try_sqrt
  rw [WP.spec_ok]
  exact ⟨a, rfl, hA, by rw [← pow_two, show 2 = 2 ^ 2 ^ 0 from rfl, pow_card_level]⟩

/-! ## `GF(2^2)` -/

theorem bf2_try_sqrt_spec (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 1 a r ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField2.BITS]
  rw [ite_eq_right (by decide)]
  step*
  refine WP.spec_bind (bf2_exp_power_of_2_spec a hA i) fun c ⟨hc, hpow⟩ => ?_
  rw [WP.spec_ok]
  refine ⟨c, rfl, hc, ?_⟩
  rw [hpow, i_post, ← pow_two, ← pow_mul, ← pow_succ]
  exact pow_card_level _

/-! ## `GF(2^4)` -/

theorem bf4_try_sqrt_spec (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 2 a r ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField4.BITS]
  rw [ite_eq_right (by decide)]
  step*
  refine WP.spec_bind (bf4_exp_power_of_2_spec a hA i) fun c ⟨hc, hpow⟩ => ?_
  rw [WP.spec_ok]
  refine ⟨c, rfl, hc, ?_⟩
  rw [hpow, i_post, ← pow_two, ← pow_mul, ← pow_succ]
  exact pow_card_level _

/-! ## `GF(2^8)` -/

theorem bf8_try_sqrt_spec (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 3 a r ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 3 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField8.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField8.BITS]
  rw [ite_eq_right (by decide)]
  step*
  refine WP.spec_bind (bf8_exp_power_of_2_spec a i) fun c ⟨hc, hpow⟩ => ?_
  rw [WP.spec_ok]
  refine ⟨c, rfl, hc, ?_⟩
  rw [hpow, i_post, ← pow_two, ← pow_mul, ← pow_succ]
  exact pow_card_level _

/-! ## `GF(2^16)` -/

theorem bf16_try_sqrt_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 4 a r ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField16.BITS]
  rw [ite_eq_left (by decide), show (16#usize : Std.Usize).val = 16 from rfl]
  refine WP.spec_bind (sqrt_16_spec a) fun i hi => ?_
  have hlt : i.val < 2 ^ 2 ^ 4 := hi ▸ sqrtNat_lt hA
  refine WP.spec_bind (bf16_from_repr_spec i) fun c hc => ?_
  rw [Nat.mod_eq_of_lt hlt] at hc
  rw [WP.spec_ok]
  exact ⟨c, rfl, hc ▸ hlt, towerOf_sqrtNat hA (hc.trans hi)⟩

/-! ## `GF(2^32)` -/

theorem bf32_try_sqrt_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 5 a r ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField32.BITS]
  rw [ite_eq_left (by decide), show (32#usize : Std.Usize).val = 32 from rfl]
  refine WP.spec_bind (sqrt_32_spec a) fun i hi => ?_
  have hlt : i.val < 2 ^ 2 ^ 5 := hi ▸ sqrtNat_lt hA
  refine WP.spec_bind (bf32_from_repr_spec i) fun c hc => ?_
  rw [Nat.mod_eq_of_lt hlt] at hc
  rw [WP.spec_ok]
  exact ⟨c, rfl, hc ▸ hlt, towerOf_sqrtNat hA (hc.trans hi)⟩

/-! ## `GF(2^64)` -/

theorem bf64_try_sqrt_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 6 a r ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField64.BITS]
  rw [ite_eq_left (by decide), show (64#usize : Std.Usize).val = 64 from rfl]
  refine WP.spec_bind (sqrt_64_spec a) fun i hi => ?_
  have hlt : i.val < 2 ^ 2 ^ 6 := hi ▸ sqrtNat_lt hA
  refine WP.spec_bind (bf64_from_repr_spec i) fun c hc => ?_
  rw [Nat.mod_eq_of_lt hlt] at hc
  rw [WP.spec_ok]
  exact ⟨c, rfl, hc ▸ hlt, towerOf_sqrtNat hA (hc.trans hi)⟩

/-! ## `GF(2^128)` -/

theorem bf128_try_sqrt_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldField.try_sqrt a ⦃ r => SqrtSpec 7 a r ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldField.try_sqrt
  simp only [tower.BinaryField128.BITS]
  rw [ite_eq_left (by decide), show (128#usize : Std.Usize).val = 128 from rfl]
  refine WP.spec_bind (sqrt_128_spec a) fun i hi => ?_
  have hlt : i.val < 2 ^ 2 ^ 7 := hi ▸ sqrtNat_lt hA
  refine WP.spec_bind (bf128_from_repr_spec i) fun c hc => ?_
  rw [Nat.mod_eq_of_lt hlt] at hc
  rw [WP.spec_ok]
  exact ⟨c, rfl, hc ▸ hlt, towerOf_sqrtNat hA (hc.trans hi)⟩

end Plonky3Lean.Proofs.Binary
