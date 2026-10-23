module

public import Plonky3Lean.Proofs.Field.Binary.TowerSquare
public import CompPoly.Fields.Binary.Tower.Concrete.CoordinateArithmetic

@[expose] public section

/-!
# Inversion at every level of the tower

Above `GF(2^8)`, `try_inverse` writes `x = a0 + a1 X` and returns
`((a0 + Z a1) + a1 X) / N` with `N = a0^2 + Z a0 a1 + a1^2`, inverting `N` at the level below.

This is CompPoly's `inv_eq_joinSucc`. The bridge from the integers is that the halves
`split` returns are CompPoly's `low` and `high`, and `join` is `joinSucc`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Two halves that fit join into a value that fits at the level above. -/
theorem join_lt {k lo hi : ℕ} (hlo : lo < 2 ^ 2 ^ k) (hhi : hi < 2 ^ 2 ^ k) :
    hi <<< 2 ^ k ||| lo < 2 ^ 2 ^ (k + 1) :=
  Nat.or_lt_two_pow (shiftLeft_lt_of_lt hhi)
    (lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; omega)))

/-- `join` of two halves that fit is CompPoly's `joinSucc`. -/
theorem towerOf_join {k : ℕ} {ty₁ ty₂ ty₃ : UScalarTy} {y : UScalar ty₁} {lo : UScalar ty₂}
    {hi : UScalar ty₃} (hlo : lo.val < 2 ^ 2 ^ k) (hhi : hi.val < 2 ^ 2 ^ k)
    (hy : y.val = hi.val <<< 2 ^ k ||| lo.val) :
    towerOf (k + 1) y = joinSucc k (towerOf k lo) (towerOf k hi) := by
  apply ConcreteBTField.toNat_injective
  have hlt := join_lt hlo hhi
  show _ = (join (k := k + 1) (by omega) (towerOf k hi) (towerOf k lo)).toNat
  rw [toNat_join]
  simp only [towerOf, ConcreteBTField.toNat_fromNat, hy, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlo,
    Nat.mod_eq_of_lt hhi, Nat.add_sub_cancel]

/-- The low half `split` returns is CompPoly's `low`. -/
theorem low_towerOf (k : ℕ) {ty : UScalarTy} (a : UScalar ty) :
    low k (towerOf (k + 1) a) = fromNat ((a.val &&& (2 ^ 2 ^ k - 1)) % 2 ^ 2 ^ k) := by
  apply ConcreteBTField.toNat_injective
  unfold low
  rw [split_eq]
  simp only [towerOf, ConcreteBTField.toNat_fromNat, Nat.add_sub_cancel,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The high half `split` returns is CompPoly's `high`. -/
theorem high_towerOf (k : ℕ) {ty : UScalarTy} (a : UScalar ty) :
    high k (towerOf (k + 1) a) = fromNat ((a.val >>> 2 ^ k) % 2 ^ 2 ^ k) := by
  apply ConcreteBTField.toNat_injective
  unfold high
  rw [split_eq]
  simp only [towerOf, ConcreteBTField.toNat_fromNat, Nat.add_sub_cancel, Nat.mod_mod]
  exact high_half_mod a.val k

/-- What `try_inverse` returns at level `k`: `None` for zero, and otherwise the inverse, in
canonical form. -/
def InvSpec (k : ℕ) {ty : UScalarTy} (a : UScalar ty) (r : core.option.Option (UScalar ty)) :
    Prop :=
  (towerOf k a = 0 → r = .None) ∧
    (towerOf k a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ k ∧ towerOf k c = (towerOf k a)⁻¹)

/-! ## `GF(2^8)` -/

theorem bf8_try_inverse_spec (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 3 a r ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldField.try_inverse tower.BinaryField8.table_try_inverse
  refine WP.spec_bind (tables_try_inverse_spec a) fun o ⟨h0, h1⟩ => ?_
  cases o with
  | none =>
    simp only [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (h1 h) (by simp)⟩
  | some c =>
    simp only [WP.spec_ok]
    refine ⟨fun h => absurd (h0 h) (by simp), fun h => ?_⟩
    obtain ⟨c', hc', hcc⟩ := h1 h
    cases hc'
    exact ⟨c, rfl, by have := c.hBounds; simpa using this, eq_inv_of_mul_eq_one_left hcc⟩

/-! ## `GF(2)` -/

/-- `try_inverse` at `GF(2)`, for a canonical `a` (`0` or `1`). -/
theorem gf2_try_inverse_spec (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 0 a r ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldField.try_inverse core.bool.Bool.then_some
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  rw [WP.spec_ok]
  rcases (by norm_num at hA; omega : a.val = 0 ∨ a.val = 1) with h | h
  · have ha1 : ¬ a = 1#u8 := fun e => by rw [e] at h; exact absurd h (by decide)
    have hz : towerOf 0 a = 0 := by
      apply ConcreteBTField.toNat_injective
      simp [towerOf, h]
      rfl
    simp only [ha1, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun _ => rfl, fun hn => absurd hz hn⟩
  · have ha1 : a = 1#u8 := UScalar.eq_of_val_eq (by rw [h]; rfl)
    have h1 : towerOf 0 a = 1 := by
      apply ConcreteBTField.toNat_injective
      simp [towerOf, h]
      rfl
    simp only [ha1, decide_true, ↓reduceIte]
    rw [ha1] at h1
    refine ⟨fun hz => absurd (h1.symm.trans hz) one_ne_zero,
      fun _ => ⟨_, rfl, by simp, ?_⟩⟩
    rw [h1, inv_one]

/-! ## `GF(2^2)` -/

theorem bf2_try_inverse_spec (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 1 a r ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField2.reference_try_inverse
  by_cases ha0 : a = 0#u8
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  case hx => tower_bound
  set x := towerOf 1 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 0 x = towerOf 0 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 0 x = towerOf 0 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have ha0l : a0.val < 2 ^ 2 ^ 0 := by rw [a0_post]; exact Nat.mod_lt _ (by positivity)
  have ha1l : a1.val < 2 ^ 2 ^ 0 := by rw [a0_post1]; exact Nat.mod_lt _ (by positivity)
  have hnorm : towerOf 0 norm = Coordinates.norm 0 x := by
    rw [towerOf_add norm_post, towerOf_add g3_post, towerOf_mul g_post, towerOf_mul_Z g2_post,
      towerOf_mul g1_post, towerOf_mul g4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  have hnlt : norm.val < 2 ^ 2 ^ 0 := by tower_bound
  refine WP.spec_bind (gf2_try_inverse_spec norm hnlt) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 0 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (gf2_mul_alpha_spec a1 ha1l) fun g5 h5 => ?_
  refine WP.spec_bind (gf2_add_spec a0 g5) fun g6 h6 => ?_
  refine WP.spec_bind (gf2_mul_spec g6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (gf2_mul_spec a1 c) fun m1 hm1 => ?_
  have h5l : g5.val < 2 ^ 2 ^ 0 := by rw [h5]; exact towerMul_lt _ ha1l (zNat_lt _)
  have h6l : g6.val < 2 ^ 2 ^ 0 := by rw [h6]; exact Nat.xor_lt_two_pow ha0l h5l
  have hm0l : m0.val < 2 ^ 2 ^ 0 := by rw [hm0]; exact towerMul_lt _ h6l hcl
  have hm1l : m1.val < 2 ^ 2 ^ 0 := by rw [hm1]; exact towerMul_lt _ ha1l hcl
  refine WP.spec_bind (bf2_join_spec m0 m1 hm0l hm1l) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt hm0l hm1l, ?_⟩⟩
  rw [towerOf_join hm0l hm1l hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring

/-! ## `GF(2^4)` -/

theorem bf4_try_inverse_spec (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 2 a r ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField4.reference_try_inverse
  by_cases ha0 : a = 0#u8
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  set x := towerOf 2 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 1 x = towerOf 1 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 1 x = towerOf 1 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have hnorm : towerOf 1 norm = Coordinates.norm 1 x := by
    rw [towerOf_add norm_post, towerOf_add bf3_post, towerOf_mul bf_post, towerOf_mul_Z bf2_post,
      towerOf_mul bf1_post, towerOf_mul bf4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  have hnlt : norm.val < 2 ^ 2 ^ 1 := by tower_bound
  refine WP.spec_bind (bf2_try_inverse_spec norm hnlt) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 1 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (bf2_mul_alpha_spec a1) fun bf5 h5 => ?_
  refine WP.spec_bind (bf2_add_spec a0 bf5) fun bf6 h6 => ?_
  refine WP.spec_bind (bf2_mul_spec bf6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (bf2_mul_spec a1 c) fun m1 hm1 => ?_
  have ha0l : a0.val < 2 ^ 2 ^ 1 := by rw [a0_post]; exact Nat.mod_lt _ (by positivity)
  have ha1l : a1.val < 2 ^ 2 ^ 1 := by rw [a0_post1]; exact Nat.mod_lt _ (by positivity)
  have h5l : bf5.val < 2 ^ 2 ^ 1 := by rw [h5]; exact towerMul_lt _ ha1l (zNat_lt _)
  have h6l : bf6.val < 2 ^ 2 ^ 1 := by rw [h6]; exact Nat.xor_lt_two_pow ha0l h5l
  have hm0l : m0.val < 2 ^ 2 ^ 1 := by rw [hm0]; exact towerMul_lt _ h6l hcl
  have hm1l : m1.val < 2 ^ 2 ^ 1 := by rw [hm1]; exact towerMul_lt _ ha1l hcl
  refine WP.spec_bind (bf4_join_spec m0 m1 hm0l hm1l) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt hm0l hm1l, ?_⟩⟩
  rw [towerOf_join hm0l hm1l hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring

/-! ## `GF(2^16)` -/

theorem bf16_try_inverse_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 4 a r ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField16.reference_try_inverse
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  by_cases ha0 : a = 0#u16
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  set x := towerOf 4 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 3 x = towerOf 3 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 3 x = towerOf 3 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have hnorm : towerOf 3 norm = Coordinates.norm 3 x := by
    rw [towerOf_add norm_post, towerOf_add bf3_post, towerOf_mul bf_post, towerOf_mul_Z bf2_post,
      towerOf_mul bf1_post, towerOf_mul bf4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  refine WP.spec_bind (bf8_try_inverse_spec norm) fun o ho => ?_
  obtain ⟨c, rfl, -, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 3 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (bf8_mul_alpha_spec a1) fun bf5 h5 => ?_
  refine WP.spec_bind (bf8_add_spec a0 bf5) fun bf6 h6 => ?_
  refine WP.spec_bind (bf8_mul_spec bf6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (bf8_mul_spec a1 c) fun m1 hm1 => ?_
  refine WP.spec_bind (bf16_join_spec m0 m1 (by scalar_tac) (by scalar_tac)) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt (by scalar_tac) (by scalar_tac), ?_⟩⟩
  rw [towerOf_join (by scalar_tac) (by scalar_tac) hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring

/-! ## `GF(2^32)` -/

theorem bf32_try_inverse_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 5 a r ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField32.reference_try_inverse
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  by_cases ha0 : a = 0#u32
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  set x := towerOf 5 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 4 x = towerOf 4 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 4 x = towerOf 4 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have hnorm : towerOf 4 norm = Coordinates.norm 4 x := by
    rw [towerOf_add norm_post, towerOf_add bf3_post, towerOf_mul bf_post, towerOf_mul_Z bf2_post,
      towerOf_mul bf1_post, towerOf_mul bf4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  refine WP.spec_bind (bf16_try_inverse_spec norm) fun o ho => ?_
  obtain ⟨c, rfl, -, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 4 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (bf16_mul_alpha_spec a1) fun bf5 h5 => ?_
  refine WP.spec_bind (bf16_add_spec a0 bf5) fun bf6 h6 => ?_
  refine WP.spec_bind (bf16_mul_spec bf6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (bf16_mul_spec a1 c) fun m1 hm1 => ?_
  refine WP.spec_bind (bf32_join_spec m0 m1 (by scalar_tac) (by scalar_tac)) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt (by scalar_tac) (by scalar_tac), ?_⟩⟩
  rw [towerOf_join (by scalar_tac) (by scalar_tac) hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring
/-! ## `GF(2^64)` -/

theorem bf64_try_inverse_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 6 a r ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField64.reference_try_inverse
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  by_cases ha0 : a = 0#u64
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  set x := towerOf 6 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 5 x = towerOf 5 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 5 x = towerOf 5 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have hnorm : towerOf 5 norm = Coordinates.norm 5 x := by
    rw [towerOf_add norm_post, towerOf_add bf3_post, towerOf_mul bf_post, towerOf_mul_Z bf2_post,
      towerOf_mul bf1_post, towerOf_mul bf4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  refine WP.spec_bind (bf32_try_inverse_spec norm) fun o ho => ?_
  obtain ⟨c, rfl, -, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 5 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (bf32_mul_alpha_spec a1) fun bf5 h5 => ?_
  refine WP.spec_bind (bf32_add_spec a0 bf5) fun bf6 h6 => ?_
  refine WP.spec_bind (bf32_mul_spec bf6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (bf32_mul_spec a1 c) fun m1 hm1 => ?_
  refine WP.spec_bind (bf64_join_spec m0 m1 (by scalar_tac) (by scalar_tac)) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt (by scalar_tac) (by scalar_tac), ?_⟩⟩
  rw [towerOf_join (by scalar_tac) (by scalar_tac) hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring
/-! ## `GF(2^128)` -/

theorem bf128_try_inverse_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldField.try_inverse a ⦃ r => InvSpec 7 a r ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField128.reference_try_inverse
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  by_cases ha0 : a = 0#u128
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd (by subst ha0; rfl) h⟩
  rw [ite_eq_right ha0]
  step*
  set x := towerOf 7 a with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h' := congrArg ConcreteBTField.toNat h
    rw [hxdef, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hA] at h'
    exact ha0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
  have hlo : low 6 x = towerOf 6 a0 := by rw [hxdef, low_towerOf, towerOf, a0_post]
  have hhi : high 6 x = towerOf 6 a1 := by rw [hxdef, high_towerOf, towerOf, a0_post1]
  have hnorm : towerOf 6 norm = Coordinates.norm 6 x := by
    rw [towerOf_add norm_post, towerOf_add bf3_post, towerOf_mul bf_post, towerOf_mul_Z bf2_post,
      towerOf_mul bf1_post, towerOf_mul bf4_post, Coordinates.norm_eq, hlo, hhi]
    ring
  refine WP.spec_bind (bf64_try_inverse_spec norm) fun o ho => ?_
  obtain ⟨c, rfl, -, hc⟩ := ho.2 (by rw [hnorm]; exact norm_ne_zero 6 x hx)
  simp only [CoreModels.core.option.Option.expect, clmul.HAS_HARDWARE_CLMUL, Aeneas.Std.bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (bf64_mul_alpha_spec a1) fun bf5 h5 => ?_
  refine WP.spec_bind (bf64_add_spec a0 bf5) fun bf6 h6 => ?_
  refine WP.spec_bind (bf64_mul_spec bf6 c) fun m0 hm0 => ?_
  refine WP.spec_bind (bf64_mul_spec a1 c) fun m1 hm1 => ?_
  refine WP.spec_bind (bf128_join_spec m0 m1 (by scalar_tac) (by scalar_tac)) fun r hr => ?_
  rw [WP.spec_ok]
  refine ⟨fun h => absurd h hx, fun _ => ⟨_, rfl, by rw [hr]; exact join_lt (by scalar_tac) (by scalar_tac), ?_⟩⟩
  rw [towerOf_join (by scalar_tac) (by scalar_tac) hr, inv_eq_joinSucc, towerOf_mul hm0,
    towerOf_mul hm1, towerOf_add h6, towerOf_mul_Z h5, hc, hnorm, hlo, hhi]
  congr 1 <;> ring

end Plonky3Lean.Proofs.Binary
