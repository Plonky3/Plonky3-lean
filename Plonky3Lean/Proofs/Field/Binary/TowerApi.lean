module

public import Plonky3Lean.Proofs.Field.Binary.TowerSqrt

@[expose] public section

/-!
# The rest of the field API at every level of the tower

Division and the compound assignments reduce to the arithmetic proved elsewhere; `inverse`
panics exactly at zero. `interpolation_node i` is `i` itself, and panics when `i` does not fit,
so that distinct indices give distinct nodes.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Canonical values with the same field element are equal. -/
theorem eq_of_towerOf_eq {k : ℕ} {ty : UScalarTy} {a b : UScalar ty} (ha : a.val < 2 ^ 2 ^ k)
    (hb : b.val < 2 ^ 2 ^ k) (h : towerOf k a = towerOf k b) : a = b := by
  have h' := congrArg ConcreteBTField.toNat h
  simp only [towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact UScalar.eq_of_val_eq h'

theorem towerOf_eq_zero_iff {k : ℕ} {ty : UScalarTy} {a : UScalar ty} (ha : a.val < 2 ^ 2 ^ k) :
    towerOf k a = 0 ↔ a.val = 0 := by
  constructor
  · intro h
    have h' := congrArg ConcreteBTField.toNat h
    simp only [towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt ha] at h'
    exact h'.trans rfl
  · intro h
    apply ConcreteBTField.toNat_injective
    simp only [towerOf, ConcreteBTField.toNat_fromNat, h, Nat.zero_mod]
    rfl

theorem towerOf_of_val {k : ℕ} {ty₁ ty₂ : UScalarTy} {a : UScalar ty₁} {b : UScalar ty₂}
    (h : a.val = b.val) : towerOf k a = towerOf k b := by
  simp only [towerOf, h]

/-! ## `GF(2^16)` -/

theorem bf16_inverse_spec (a : tower.BinaryField16) (ha : towerOf 4 a ≠ 0) :
    field_defaults.BinaryField16.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 4 ∧ towerOf 4 c = (towerOf 4 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField16.inverse field_defaults.BinaryField16.raw_inverse
  refine WP.spec_bind (bf16_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf16_inverse_zero (a : tower.BinaryField16) (ha : towerOf 4 a = 0) :
    field_defaults.BinaryField16.inverse a = .fail .panic := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  have h0 : a = 0#u16 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField16.inverse field_defaults.BinaryField16.raw_inverse
    tower.BinaryField16.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField16.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf16_div_spec (a b : tower.BinaryField16) (hb : towerOf 4 b ≠ 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a / towerOf 4 b ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div
  refine WP.spec_bind (bf16_inverse_spec b hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf16_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf16_div_zero (a b : tower.BinaryField16) (hb : towerOf 4 b = 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div a b = .fail .panic := by
  unfold tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div
  rw [bf16_inverse_zero b hb]
  simp

theorem bf16_mul_assign_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a * towerOf 4 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf16_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf16_add_assign_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a + towerOf 4 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf16_add_spec a b) fun r hr => towerOf_add hr

theorem bf16_sub_assign_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a - towerOf 4 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf16_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf16_div_assign_spec (a b : tower.BinaryField16) (hb : towerOf 4 b ≠ 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivAssignBinaryField16.div_assign a b ⦃ r =>
      towerOf 4 r = towerOf 4 a / towerOf 4 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithDivAssignBinaryField16.div_assign
  refine WP.spec_bind (bf16_inverse_spec b hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf16_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf16_eq_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreCmpPartialEqBinaryField16.eq a b ⦃ r =>
      (r = true ↔ towerOf 4 a = towerOf 4 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  have hB : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.CoreCmpPartialEqBinaryField16.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf16_bool_check_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 4 r = towerOf 4 a * towerOf 4 a + towerOf 4 a ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf16_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf16_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf16_bits_spec :
    tower.BinaryField16.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 4 ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldField.bits tower.BinaryField16.BITS
  rw [WP.spec_ok]; rfl

theorem bf16_from_bool_spec (b : Bool) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U16.Insts.CoreConvertFromBool.from]

theorem bf16_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 4) :
    tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  have hnb' := System.Platform.numBits_eq
  rw [ite_eq_right (by
    unfold tower.BinaryField16.BITS
    intro h
    have h' : i1.val ≤ 16 := h
    omega)]
  step*
  · simp only [tower.BinaryField16.BITS]
    show 16 < _
    omega
  · have hx : x.val = 2 ^ 16 := by
      rw [x_post]
      simp only [tower.BinaryField16.BITS, Usize.size, Usize.numBits]
      rcases hnb' with e | e <;> simp [e]
    intro h
    exact h (by scalar_tac)

/-- An index that does not fit panics: `interpolation_node` stays injective. -/
theorem bf16_interpolation_node_fail (i : Std.Usize) (hi : 2 ^ 2 ^ 4 ≤ i.val) :
    tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node
  have h16 : (16#usize : Std.Usize).val < UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; rcases hnb' with e | e <;> simp [e]
  obtain ⟨x, hsh, hx⟩ : ∃ x : Std.Usize, (1#usize <<< (16#usize : Std.Usize) : RustM Std.Usize) =
      .ok x ∧ x.val = 2 ^ 16 := by
    refine ⟨⟨(1#usize : Std.Usize).bv.shiftLeft 16⟩, ?_, ?_⟩
    · show UScalar.shiftLeft_UScalar _ _ = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [ite_eq_left h16]
      rfl
    · have h1 : (1#usize : Std.Usize).bv.toNat = 1 := rfl
      have e : ((1#usize : Std.Usize).bv.shiftLeft 16).toNat =
          (1#usize : Std.Usize).bv.toNat <<< 16 % 2 ^ UScalarTy.Usize.numBits :=
        BitVec.toNat_shiftLeft
      refine e.trans ?_
      rw [h1]
      simp only [UScalarTy.numBits] at h16 ⊢
      rcases hnb' with e | e <;> simp [e]
  have hi1 : ¬ (UScalar.cast UScalarTy.Usize core.num.Usize.BITS : Std.Usize).val ≤ 16 := by
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
    omega
  have hlt : ¬ i < x := by
    intro h
    have h' : i.val < x.val := h
    omega
  simp only [tower.BinaryField16.BITS, lift, Aeneas.Std.bind_ok, massert]
  rw [ite_eq_right (show ¬ UScalar.cast UScalarTy.Usize core.num.Usize.BITS ≤ 16#usize from hi1),
    hsh, Aeneas.Std.bind_ok, ite_eq_right hlt]
  simp

/-! ## `GF(2)` -/

theorem gf2_inverse_spec (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (ha : towerOf 0 a ≠ 0) :
    field_defaults.Gf2.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 0 ∧ towerOf 0 c = (towerOf 0 a)⁻¹ ⦄ := by
  unfold field_defaults.Gf2.inverse field_defaults.Gf2.raw_inverse
  refine WP.spec_bind (gf2_try_inverse_spec a hA) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem gf2_inverse_zero (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (ha : towerOf 0 a = 0) :
    field_defaults.Gf2.inverse a = .fail .panic := by
  have h0 : a = 0#u8 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.Gf2.inverse field_defaults.Gf2.raw_inverse
    gf2.Gf2.Insts.P3_fieldFieldField.try_inverse core.bool.Bool.then_some
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem gf2_div_spec (a b : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0)
    (hB : b.val < 2 ^ 2 ^ 0) (hb : towerOf 0 b ≠ 0) :
    gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 0 ∧ towerOf 0 r = towerOf 0 a / towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div
  refine WP.spec_bind (gf2_inverse_spec b hB hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (gf2_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem gf2_div_zero (a b : gf2.Gf2) (hB : b.val < 2 ^ 2 ^ 0) (hb : towerOf 0 b = 0) :
    gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div a b = .fail .panic := by
  unfold gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div
  rw [gf2_inverse_zero b hB hb]
  simp

theorem gf2_mul_assign_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a * towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (gf2_mul_spec a b) fun r hr => towerOf_mul hr

theorem gf2_add_assign_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (gf2_add_spec a b) fun r hr => towerOf_add hr

theorem gf2_sub_assign_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a - towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (gf2_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem gf2_div_assign_spec (a b : gf2.Gf2) (hB : b.val < 2 ^ 2 ^ 0) (hb : towerOf 0 b ≠ 0) :
    gf2.Gf2.Insts.CoreOpsArithDivAssignGf2.div_assign a b ⦃ r =>
      towerOf 0 r = towerOf 0 a / towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithDivAssignGf2.div_assign
  refine WP.spec_bind (gf2_inverse_spec b hB hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (gf2_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem gf2_eq_spec (a b : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0)
    (hB : b.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.CoreCmpPartialEqGf2.eq a b ⦃ r =>
      (r = true ↔ towerOf 0 a = towerOf 0 b) ⦄ := by
  unfold gf2.Gf2.Insts.CoreCmpPartialEqGf2.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem gf2_bits_spec : gf2.Gf2.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 0 ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldField.bits
  rw [WP.spec_ok]; rfl

theorem gf2_from_bool_spec (b : Bool) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r => r.val = b.toNat ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [lift]

theorem gf2_new_spec (bit : Std.U8) : gf2.Gf2.new bit ⦃ r => r.val = bit.val % 2 ⦄ := by
  unfold gf2.Gf2.new
  simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_and]
  exact Nat.and_one_is_mod _

theorem gf2_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2) :
    gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node
  step*
  refine WP.spec_mono (gf2_new_spec i1) fun r hr => ?_
  rw [hr, i1_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
    Nat.mod_eq_of_lt (show i.val < 2 ^ 8 by omega), Nat.mod_eq_of_lt hi]

theorem gf2_interpolation_node_fail (i : Std.Usize) (hi : 2 ≤ i.val) :
    gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  unfold gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node
  have h : ¬ i < 2#usize := fun h' => by have : i.val < 2 := h'; omega
  simp [massert, h]

theorem gf2_halve_fail (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a = .fail .panic := rfl

theorem gf2_div_2exp_u64_fail (a : gf2.Gf2) (e : Std.U64) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e = .fail .panic := rfl

theorem gf2_double_spec (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.double a ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 a ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.double
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  rw [WP.spec_ok, CharTwo.add_self_eq_zero]
  rfl

theorem gf2_mul_2exp_u64_spec (a : gf2.Gf2) (e : Std.U64) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e ⦃ r =>
      towerOf 0 r = towerOf 0 a * 2 ^ e.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  split
  · rename_i h
    rw [WP.spec_ok, show e.val = 0 by rw [h]; rfl, pow_zero, mul_one]
  · rename_i h
    have he : e.val ≠ 0 := fun h' => h (UScalar.eq_of_val_eq (by rw [h']; rfl))
    rw [WP.spec_ok, CharTwo.two_eq_zero, zero_pow he, mul_zero]
    rfl

theorem gf2_xor_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.xor a b ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 b ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.xor
  exact WP.spec_mono (gf2_add_spec a b) fun r hr => towerOf_add hr

theorem gf2_from_int_u8_spec (n : Std.U8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_int n ⦃ r => r.val = n.val % 2 ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_int
  exact gf2_new_spec n

theorem gf2_from_int_i8_spec (n : Std.I8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_int n ⦃ r => (r.val : ℤ) = n.val % 2 ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_int
  step*
  refine WP.spec_mono (gf2_new_spec i1) fun r hr => ?_
  have key : ∀ x : BitVec 8, ((((x &&& 1#8).signExtend 8).toNat % 2 : ℕ) : ℤ) = x.toInt % 2 := by
    decide
  rw [hr, i1_post]
  show ((((i.bv).signExtend 8).toNat % 2 : ℕ) : ℤ) = n.bv.toInt % 2
  have h := key n.bv
  rw [show (1#8 : BitVec 8) = (1#i8 : Std.I8).bv from rfl, ← i_post1] at h
  exact h

theorem gf2_as_canonical_u64_spec (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 a ⦃ r => r.val = a.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeField64.as_canonical_u64
  rw [WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.hBounds (by simp))

theorem gf2_as_canonical_u32_spec (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeField32.as_canonical_u32 a ⦃ r => r.val = a.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeField32.as_canonical_u32
  rw [WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.hBounds (by simp))


theorem gf2_from_canonical_checked_u8_spec (n : Std.U8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_canonical_checked n ⦃ r =>
      (n.val < 2 → ∃ c, r = .Some c ∧ c.val = n.val) ∧ (2 ≤ n.val → r = .None) ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_canonical_checked CoreModels.core.bool.Bool.then
  by_cases h : n.val < 2
  · have h' : n < 2#u8 := h
    simp only [h', decide_true, ↓reduceIte,
      gf2.QuotientMapGf2U8.from_canonical_checked.closure.Insts.CoreOpsFunctionFnOnceTupleGf2.call_once]
    refine WP.spec_bind (gf2_new_spec n) fun c hc => ?_
    rw [WP.spec_ok]
    exact ⟨fun _ => ⟨c, rfl, by rw [hc, Nat.mod_eq_of_lt h]⟩, fun h2 => absurd h (by omega)⟩
  · have h' : ¬ n < 2#u8 := h
    simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h2 => absurd h2 h, fun _ => trivial⟩

theorem gf2_from_canonical_checked_i8_spec (n : Std.I8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_canonical_checked n ⦃ r =>
      ((0 ≤ n.val ∧ n.val < 2) → ∃ c, r = .Some c ∧ (c.val : ℤ) = n.val) ∧
        (¬ (0 ≤ n.val ∧ n.val < 2) → r = .None) ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_canonical_checked
  simp only [CoreModels.core.ops.range.Range.contains,
    CoreModels.core.ops.range.RangeBounds.contains.default,
    CoreModels.core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.start_bound,
    CoreModels.core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.end_bound,
    CoreModels.core.ops.range.after_start, CoreModels.core.ops.range.before_end,
    CoreModels.core.ops.range.bound_le, CoreModels.core.ops.range.bound_lt,
    CoreModels.core.I8.Insts.CoreCmpPartialOrdI8, CoreModels.core.mkIPartialOrd,
    Aeneas.Std.bind_ok, CoreModels.core.bool.Bool.then,
    gf2.QuotientMapGf2I8.from_canonical_checked.closure.Insts.CoreOpsFunctionFnOnceTupleGf2.call_once]
  generalize hc1 : compare (0#i8 : Std.I8).val n.val = c1
  generalize hc2 : compare n.val (2#i8 : Std.I8).val = c2
  rw [show (0#i8 : Std.I8).val = 0 from rfl] at hc1
  rw [show (2#i8 : Std.I8).val = 2 from rfl] at hc2
  have hin : 0 ≤ n.val ∧ n.val < 2 → gf2.Gf2.new (IScalar.hcast UScalarTy.U8 n) ⦃ c =>
      (c.val : ℤ) = n.val ⦄ := fun ⟨h0, h2⟩ => by
    refine WP.spec_mono (gf2_new_spec _) fun c hc => ?_
    have key : ∀ x : BitVec 8, 0 ≤ x.toInt → x.toInt < 2 →
        (((x.signExtend 8).toNat % 2 : ℕ) : ℤ) = x.toInt := by decide
    rw [hc]
    exact key n.bv h0 h2
  have f1 := hc1
  have f2 := hc2
  cases c1 <;> cases c2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, lift, compare_lt_iff_lt,
      compare_eq_iff_eq, compare_gt_iff_gt] at f1 f2 ⊢
  all_goals first
    | (rw [WP.spec_ok]; exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩)
    | (refine WP.spec_bind (hin (by omega)) fun c hc => ?_
       rw [WP.spec_ok]
       exact ⟨fun _ => ⟨c, rfl, hc⟩, fun h => absurd (by omega) h⟩)

/-! ## `GF(2^2)` -/

theorem bf2_inverse_spec (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (ha : towerOf 1 a ≠ 0) :
    field_defaults.BinaryField2.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 1 ∧ towerOf 1 c = (towerOf 1 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField2.inverse field_defaults.BinaryField2.raw_inverse
  refine WP.spec_bind (bf2_try_inverse_spec a hA) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf2_inverse_zero (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (ha : towerOf 1 a = 0) :
    field_defaults.BinaryField2.inverse a = .fail .panic := by
  have h0 : a = 0#u8 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField2.inverse field_defaults.BinaryField2.raw_inverse
    tower.BinaryField2.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField2.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf2_div_spec (a b : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1)
    (hB : b.val < 2 ^ 2 ^ 1) (hb : towerOf 1 b ≠ 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 a / towerOf 1 b ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div
  refine WP.spec_bind (bf2_inverse_spec b hB hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf2_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf2_div_zero (a b : tower.BinaryField2) (hB : b.val < 2 ^ 2 ^ 1) (hb : towerOf 1 b = 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div a b = .fail .panic := by
  unfold tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div
  rw [bf2_inverse_zero b hB hb]
  simp

theorem bf2_mul_assign_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a * towerOf 1 b ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf2_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf2_add_assign_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a + towerOf 1 b ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf2_add_spec a b) fun r hr => towerOf_add hr

theorem bf2_sub_assign_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a - towerOf 1 b ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf2_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf2_div_assign_spec (a b : tower.BinaryField2) (hB : b.val < 2 ^ 2 ^ 1) (hb : towerOf 1 b ≠ 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivAssignBinaryField2.div_assign a b ⦃ r =>
      towerOf 1 r = towerOf 1 a / towerOf 1 b ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithDivAssignBinaryField2.div_assign
  refine WP.spec_bind (bf2_inverse_spec b hB hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf2_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf2_eq_spec (a b : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1)
    (hB : b.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.CoreCmpPartialEqBinaryField2.eq a b ⦃ r =>
      (r = true ↔ towerOf 1 a = towerOf 1 b) ⦄ := by
  unfold tower.BinaryField2.Insts.CoreCmpPartialEqBinaryField2.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf2_bool_check_spec (a : tower.BinaryField2) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 1 r = towerOf 1 a * towerOf 1 a + towerOf 1 a ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf2_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf2_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf2_bits_spec :
    tower.BinaryField2.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 1 ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldField.bits tower.BinaryField2.BITS
  rw [WP.spec_ok]; rfl

theorem bf2_from_bool_spec (b : Bool) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U8.Insts.CoreConvertFromBool.from]

theorem bf2_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  have hnb' := System.Platform.numBits_eq
  rw [ite_eq_right (by
    unfold tower.BinaryField2.BITS
    intro h
    have h' : i1.val ≤ 2 := h
    omega)]
  step*
  · simp only [tower.BinaryField2.BITS]
    show 2 < _
    omega
  · have hx : x.val = 2 ^ 2 := by
      rw [x_post]
      simp only [tower.BinaryField2.BITS, Usize.size, Usize.numBits]
      rcases hnb' with e | e <;> simp [e]
    intro h
    exact h (by scalar_tac)

/-- An index that does not fit panics: `interpolation_node` stays injective. -/
theorem bf2_interpolation_node_fail (i : Std.Usize) (hi : 2 ^ 2 ^ 1 ≤ i.val) :
    tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node
  have h16 : (2#usize : Std.Usize).val < UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; rcases hnb' with e | e <;> simp [e]
  obtain ⟨x, hsh, hx⟩ : ∃ x : Std.Usize, (1#usize <<< (2#usize : Std.Usize) : RustM Std.Usize) =
      .ok x ∧ x.val = 2 ^ 2 := by
    refine ⟨⟨(1#usize : Std.Usize).bv.shiftLeft 2⟩, ?_, ?_⟩
    · show UScalar.shiftLeft_UScalar _ _ = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [ite_eq_left h16]
      rfl
    · have h1 : (1#usize : Std.Usize).bv.toNat = 1 := rfl
      have e : ((1#usize : Std.Usize).bv.shiftLeft 2).toNat =
          (1#usize : Std.Usize).bv.toNat <<< 2 % 2 ^ UScalarTy.Usize.numBits :=
        BitVec.toNat_shiftLeft
      refine e.trans ?_
      rw [h1]
      simp only [UScalarTy.numBits] at h16 ⊢
      rcases hnb' with e | e <;> simp [e]
  have hi1 : ¬ (UScalar.cast UScalarTy.Usize core.num.Usize.BITS : Std.Usize).val ≤ 2 := by
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
    omega
  have hlt : ¬ i < x := by
    intro h
    have h' : i.val < x.val := h
    omega
  simp only [tower.BinaryField2.BITS, lift, Aeneas.Std.bind_ok, massert]
  rw [ite_eq_right (show ¬ UScalar.cast UScalarTy.Usize core.num.Usize.BITS ≤ 2#usize from hi1),
    hsh, Aeneas.Std.bind_ok, ite_eq_right hlt]
  simp

/-! ## `GF(2^4)` -/

theorem bf4_inverse_spec (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (ha : towerOf 2 a ≠ 0) :
    field_defaults.BinaryField4.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 2 ∧ towerOf 2 c = (towerOf 2 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField4.inverse field_defaults.BinaryField4.raw_inverse
  refine WP.spec_bind (bf4_try_inverse_spec a hA) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf4_inverse_zero (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (ha : towerOf 2 a = 0) :
    field_defaults.BinaryField4.inverse a = .fail .panic := by
  have h0 : a = 0#u8 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField4.inverse field_defaults.BinaryField4.raw_inverse
    tower.BinaryField4.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField4.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf4_div_spec (a b : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2)
    (hB : b.val < 2 ^ 2 ^ 2) (hb : towerOf 2 b ≠ 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 a / towerOf 2 b ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div
  refine WP.spec_bind (bf4_inverse_spec b hB hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf4_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf4_div_zero (a b : tower.BinaryField4) (hB : b.val < 2 ^ 2 ^ 2) (hb : towerOf 2 b = 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div a b = .fail .panic := by
  unfold tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div
  rw [bf4_inverse_zero b hB hb]
  simp

theorem bf4_mul_assign_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a * towerOf 2 b ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf4_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf4_add_assign_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a + towerOf 2 b ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf4_add_spec a b) fun r hr => towerOf_add hr

theorem bf4_sub_assign_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a - towerOf 2 b ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf4_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf4_div_assign_spec (a b : tower.BinaryField4) (hB : b.val < 2 ^ 2 ^ 2) (hb : towerOf 2 b ≠ 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivAssignBinaryField4.div_assign a b ⦃ r =>
      towerOf 2 r = towerOf 2 a / towerOf 2 b ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithDivAssignBinaryField4.div_assign
  refine WP.spec_bind (bf4_inverse_spec b hB hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf4_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf4_eq_spec (a b : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2)
    (hB : b.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.CoreCmpPartialEqBinaryField4.eq a b ⦃ r =>
      (r = true ↔ towerOf 2 a = towerOf 2 b) ⦄ := by
  unfold tower.BinaryField4.Insts.CoreCmpPartialEqBinaryField4.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf4_bool_check_spec (a : tower.BinaryField4) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 2 r = towerOf 2 a * towerOf 2 a + towerOf 2 a ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf4_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf4_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf4_bits_spec :
    tower.BinaryField4.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 2 ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldField.bits tower.BinaryField4.BITS
  rw [WP.spec_ok]; rfl

theorem bf4_from_bool_spec (b : Bool) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U8.Insts.CoreConvertFromBool.from]

theorem bf4_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  have hnb' := System.Platform.numBits_eq
  rw [ite_eq_right (by
    unfold tower.BinaryField4.BITS
    intro h
    have h' : i1.val ≤ 4 := h
    omega)]
  step*
  · simp only [tower.BinaryField4.BITS]
    show 4 < _
    omega
  · have hx : x.val = 2 ^ 4 := by
      rw [x_post]
      simp only [tower.BinaryField4.BITS, Usize.size, Usize.numBits]
      rcases hnb' with e | e <;> simp [e]
    intro h
    exact h (by scalar_tac)

/-- An index that does not fit panics: `interpolation_node` stays injective. -/
theorem bf4_interpolation_node_fail (i : Std.Usize) (hi : 2 ^ 2 ^ 2 ≤ i.val) :
    tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node
  have h16 : (4#usize : Std.Usize).val < UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; rcases hnb' with e | e <;> simp [e]
  obtain ⟨x, hsh, hx⟩ : ∃ x : Std.Usize, (1#usize <<< (4#usize : Std.Usize) : RustM Std.Usize) =
      .ok x ∧ x.val = 2 ^ 4 := by
    refine ⟨⟨(1#usize : Std.Usize).bv.shiftLeft 4⟩, ?_, ?_⟩
    · show UScalar.shiftLeft_UScalar _ _ = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [ite_eq_left h16]
      rfl
    · have h1 : (1#usize : Std.Usize).bv.toNat = 1 := rfl
      have e : ((1#usize : Std.Usize).bv.shiftLeft 4).toNat =
          (1#usize : Std.Usize).bv.toNat <<< 4 % 2 ^ UScalarTy.Usize.numBits :=
        BitVec.toNat_shiftLeft
      refine e.trans ?_
      rw [h1]
      simp only [UScalarTy.numBits] at h16 ⊢
      rcases hnb' with e | e <;> simp [e]
  have hi1 : ¬ (UScalar.cast UScalarTy.Usize core.num.Usize.BITS : Std.Usize).val ≤ 4 := by
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
    omega
  have hlt : ¬ i < x := by
    intro h
    have h' : i.val < x.val := h
    omega
  simp only [tower.BinaryField4.BITS, lift, Aeneas.Std.bind_ok, massert]
  rw [ite_eq_right (show ¬ UScalar.cast UScalarTy.Usize core.num.Usize.BITS ≤ 4#usize from hi1),
    hsh, Aeneas.Std.bind_ok, ite_eq_right hlt]
  simp

/-! ## `GF(2^8)` -/

theorem bf8_inverse_spec (a : tower.BinaryField8) (ha : towerOf 3 a ≠ 0) :
    field_defaults.BinaryField8.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 3 ∧ towerOf 3 c = (towerOf 3 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField8.inverse field_defaults.BinaryField8.raw_inverse
  refine WP.spec_bind (bf8_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf8_inverse_zero (a : tower.BinaryField8) (ha : towerOf 3 a = 0) :
    field_defaults.BinaryField8.inverse a = .fail .panic := by
  have hA : a.val < 2 ^ 2 ^ 3 := by have := a.hBounds; simpa using this
  have h0 : a = 0#u8 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField8.inverse field_defaults.BinaryField8.raw_inverse
    tower.BinaryField8.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField8.table_try_inverse tables.try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf8_div_spec (a b : tower.BinaryField8) (hb : towerOf 3 b ≠ 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 a / towerOf 3 b ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 3 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div
  refine WP.spec_bind (bf8_inverse_spec b hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf8_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf8_div_zero (a b : tower.BinaryField8) (hb : towerOf 3 b = 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div a b = .fail .panic := by
  unfold tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div
  rw [bf8_inverse_zero b hb]
  simp

theorem bf8_mul_assign_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a * towerOf 3 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf8_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf8_add_assign_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a + towerOf 3 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf8_add_spec a b) fun r hr => towerOf_add hr

theorem bf8_sub_assign_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a - towerOf 3 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf8_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf8_div_assign_spec (a b : tower.BinaryField8) (hb : towerOf 3 b ≠ 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivAssignBinaryField8.div_assign a b ⦃ r =>
      towerOf 3 r = towerOf 3 a / towerOf 3 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithDivAssignBinaryField8.div_assign
  refine WP.spec_bind (bf8_inverse_spec b hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf8_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf8_eq_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreCmpPartialEqBinaryField8.eq a b ⦃ r =>
      (r = true ↔ towerOf 3 a = towerOf 3 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 3 := by have := a.hBounds; simpa using this
  have hB : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField8.Insts.CoreCmpPartialEqBinaryField8.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf8_bool_check_spec (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 3 r = towerOf 3 a * towerOf 3 a + towerOf 3 a ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf8_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf8_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf8_bits_spec :
    tower.BinaryField8.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 3 ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldField.bits tower.BinaryField8.BITS
  rw [WP.spec_ok]; rfl

theorem bf8_from_bool_spec (b : Bool) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U8.Insts.CoreConvertFromBool.from]

theorem bf8_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 3) :
    tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  have hnb' := System.Platform.numBits_eq
  rw [ite_eq_right (by
    unfold tower.BinaryField8.BITS
    intro h
    have h' : i1.val ≤ 8 := h
    omega)]
  step*
  · simp only [tower.BinaryField8.BITS]
    show 8 < _
    omega
  · have hx : x.val = 2 ^ 8 := by
      rw [x_post]
      simp only [tower.BinaryField8.BITS, Usize.size, Usize.numBits]
      rcases hnb' with e | e <;> simp [e]
    intro h
    exact h (by scalar_tac)

/-- An index that does not fit panics: `interpolation_node` stays injective. -/
theorem bf8_interpolation_node_fail (i : Std.Usize) (hi : 2 ^ 2 ^ 3 ≤ i.val) :
    tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node
  have h16 : (8#usize : Std.Usize).val < UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; rcases hnb' with e | e <;> simp [e]
  obtain ⟨x, hsh, hx⟩ : ∃ x : Std.Usize, (1#usize <<< (8#usize : Std.Usize) : RustM Std.Usize) =
      .ok x ∧ x.val = 2 ^ 8 := by
    refine ⟨⟨(1#usize : Std.Usize).bv.shiftLeft 8⟩, ?_, ?_⟩
    · show UScalar.shiftLeft_UScalar _ _ = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [ite_eq_left h16]
      rfl
    · have h1 : (1#usize : Std.Usize).bv.toNat = 1 := rfl
      have e : ((1#usize : Std.Usize).bv.shiftLeft 8).toNat =
          (1#usize : Std.Usize).bv.toNat <<< 8 % 2 ^ UScalarTy.Usize.numBits :=
        BitVec.toNat_shiftLeft
      refine e.trans ?_
      rw [h1]
      simp only [UScalarTy.numBits] at h16 ⊢
      rcases hnb' with e | e <;> simp [e]
  have hi1 : ¬ (UScalar.cast UScalarTy.Usize core.num.Usize.BITS : Std.Usize).val ≤ 8 := by
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
    omega
  have hlt : ¬ i < x := by
    intro h
    have h' : i.val < x.val := h
    omega
  simp only [tower.BinaryField8.BITS, lift, Aeneas.Std.bind_ok, massert]
  rw [ite_eq_right (show ¬ UScalar.cast UScalarTy.Usize core.num.Usize.BITS ≤ 8#usize from hi1),
    hsh, Aeneas.Std.bind_ok, ite_eq_right hlt]
  simp

/-! ## `GF(2^32)` -/

theorem bf32_inverse_spec (a : tower.BinaryField32) (ha : towerOf 5 a ≠ 0) :
    field_defaults.BinaryField32.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 5 ∧ towerOf 5 c = (towerOf 5 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField32.inverse field_defaults.BinaryField32.raw_inverse
  refine WP.spec_bind (bf32_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf32_inverse_zero (a : tower.BinaryField32) (ha : towerOf 5 a = 0) :
    field_defaults.BinaryField32.inverse a = .fail .panic := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  have h0 : a = 0#u32 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField32.inverse field_defaults.BinaryField32.raw_inverse
    tower.BinaryField32.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField32.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf32_div_spec (a b : tower.BinaryField32) (hb : towerOf 5 b ≠ 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a / towerOf 5 b ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div
  refine WP.spec_bind (bf32_inverse_spec b hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf32_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf32_div_zero (a b : tower.BinaryField32) (hb : towerOf 5 b = 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div a b = .fail .panic := by
  unfold tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div
  rw [bf32_inverse_zero b hb]
  simp

theorem bf32_mul_assign_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a * towerOf 5 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf32_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf32_add_assign_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a + towerOf 5 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf32_add_spec a b) fun r hr => towerOf_add hr

theorem bf32_sub_assign_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a - towerOf 5 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf32_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf32_div_assign_spec (a b : tower.BinaryField32) (hb : towerOf 5 b ≠ 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivAssignBinaryField32.div_assign a b ⦃ r =>
      towerOf 5 r = towerOf 5 a / towerOf 5 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithDivAssignBinaryField32.div_assign
  refine WP.spec_bind (bf32_inverse_spec b hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf32_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf32_eq_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreCmpPartialEqBinaryField32.eq a b ⦃ r =>
      (r = true ↔ towerOf 5 a = towerOf 5 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  have hB : b.val < 2 ^ 2 ^ 5 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreCmpPartialEqBinaryField32.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf32_bool_check_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 5 r = towerOf 5 a * towerOf 5 a + towerOf 5 a ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf32_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf32_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf32_bits_spec :
    tower.BinaryField32.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 5 ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldField.bits tower.BinaryField32.BITS
  rw [WP.spec_ok]; rfl

theorem bf32_from_bool_spec (b : Bool) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U32.Insts.CoreConvertFromBool.from]

/-! ## `GF(2^64)` -/

theorem bf64_inverse_spec (a : tower.BinaryField64) (ha : towerOf 6 a ≠ 0) :
    field_defaults.BinaryField64.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 6 ∧ towerOf 6 c = (towerOf 6 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField64.inverse field_defaults.BinaryField64.raw_inverse
  refine WP.spec_bind (bf64_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf64_inverse_zero (a : tower.BinaryField64) (ha : towerOf 6 a = 0) :
    field_defaults.BinaryField64.inverse a = .fail .panic := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  have h0 : a = 0#u64 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField64.inverse field_defaults.BinaryField64.raw_inverse
    tower.BinaryField64.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField64.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf64_div_spec (a b : tower.BinaryField64) (hb : towerOf 6 b ≠ 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a / towerOf 6 b ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div
  refine WP.spec_bind (bf64_inverse_spec b hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf64_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf64_div_zero (a b : tower.BinaryField64) (hb : towerOf 6 b = 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div a b = .fail .panic := by
  unfold tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div
  rw [bf64_inverse_zero b hb]
  simp

theorem bf64_mul_assign_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a * towerOf 6 b ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf64_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf64_add_assign_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a + towerOf 6 b ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf64_add_spec a b) fun r hr => towerOf_add hr

theorem bf64_sub_assign_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a - towerOf 6 b ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf64_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf64_div_assign_spec (a b : tower.BinaryField64) (hb : towerOf 6 b ≠ 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivAssignBinaryField64.div_assign a b ⦃ r =>
      towerOf 6 r = towerOf 6 a / towerOf 6 b ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithDivAssignBinaryField64.div_assign
  refine WP.spec_bind (bf64_inverse_spec b hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf64_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf64_eq_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreCmpPartialEqBinaryField64.eq a b ⦃ r =>
      (r = true ↔ towerOf 6 a = towerOf 6 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  have hB : b.val < 2 ^ 2 ^ 6 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreCmpPartialEqBinaryField64.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf64_bool_check_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 6 r = towerOf 6 a * towerOf 6 a + towerOf 6 a ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf64_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf64_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf64_bits_spec :
    tower.BinaryField64.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 6 ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldField.bits tower.BinaryField64.BITS
  rw [WP.spec_ok]; rfl

theorem bf64_from_bool_spec (b : Bool) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U64.Insts.CoreConvertFromBool.from]

/-! ## `GF(2^128)` -/

theorem bf128_inverse_spec (a : tower.BinaryField128) (ha : towerOf 7 a ≠ 0) :
    field_defaults.BinaryField128.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 7 ∧ towerOf 7 c = (towerOf 7 a)⁻¹ ⦄ := by
  unfold field_defaults.BinaryField128.inverse field_defaults.BinaryField128.raw_inverse
  refine WP.spec_bind (bf128_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hcl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact ⟨hcl, hc⟩

theorem bf128_inverse_zero (a : tower.BinaryField128) (ha : towerOf 7 a = 0) :
    field_defaults.BinaryField128.inverse a = .fail .panic := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have h0 : a = 0#u128 := UScalar.eq_of_val_eq ((towerOf_eq_zero_iff hA).mp ha)
  subst h0
  unfold field_defaults.BinaryField128.inverse field_defaults.BinaryField128.raw_inverse
    tower.BinaryField128.Insts.P3_fieldFieldField.try_inverse
    tower.BinaryField128.reference_try_inverse
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem bf128_div_spec (a b : tower.BinaryField128) (hb : towerOf 7 b ≠ 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a / towerOf 7 b ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div
  refine WP.spec_bind (bf128_inverse_spec b hb) fun c ⟨hcl, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf128_mul_spec a c) fun r hr => ⟨hr ▸ towerMul_lt _ hA hcl, ?_⟩
  rw [towerOf_mul hr, hc, div_eq_mul_inv]

theorem bf128_div_zero (a b : tower.BinaryField128) (hb : towerOf 7 b = 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div a b = .fail .panic := by
  unfold tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div
  rw [bf128_inverse_zero b hb]
  simp

theorem bf128_mul_assign_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * towerOf 7 b ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf128_mul_spec a b) fun r hr => towerOf_mul hr

theorem bf128_add_assign_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a + towerOf 7 b ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact WP.spec_mono (bf128_add_spec a b) fun r hr => towerOf_add hr

theorem bf128_sub_assign_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a - towerOf 7 b ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf128_sub_spec a b) fun r hr => ?_
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact towerOf_add hr

theorem bf128_div_assign_spec (a b : tower.BinaryField128) (hb : towerOf 7 b ≠ 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivAssignBinaryField128.div_assign a b ⦃ r =>
      towerOf 7 r = towerOf 7 a / towerOf 7 b ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithDivAssignBinaryField128.div_assign
  refine WP.spec_bind (bf128_inverse_spec b hb) fun c ⟨_, hc⟩ => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (bf128_mul_assign_spec a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem bf128_eq_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreCmpPartialEqBinaryField128.eq a b ⦃ r =>
      (r = true ↔ towerOf 7 a = towerOf 7 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have hB : b.val < 2 ^ 2 ^ 7 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreCmpPartialEqBinaryField128.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, eq_of_towerOf_eq hA hB⟩

theorem bf128_bool_check_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 7 r = towerOf 7 a * towerOf 7 a + towerOf 7 a ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (bf128_square_spec a) fun s hs => ?_
  refine WP.spec_mono (bf128_add_spec s a) fun r hr => ?_
  rw [towerOf_add hr, towerOf_mul hs]

theorem bf128_bits_spec :
    tower.BinaryField128.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 7 ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldField.bits tower.BinaryField128.BITS
  rw [WP.spec_ok]; rfl

theorem bf128_from_bool_spec (b : Bool) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U128.Insts.CoreConvertFromBool.from]

/-- Every `usize` fits: `interpolation_node i` is `i`. -/
theorem bf64_interpolation_node_spec (i : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField64.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  rw [ite_eq_left (show i1 ≤ tower.BinaryField64.BITS by
    unfold tower.BinaryField64.BITS
    show i1.val ≤ 64
    omega)]
  step*
  have hi : i.val < 2 ^ 64 := by
    have h := i.hBounds
    simp only [UScalarTy.numBits] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by norm_num)),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by norm_num))]

/-- Every `usize` fits: `interpolation_node i` is `i`. -/
theorem bf128_interpolation_node_spec (i : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField128.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  rw [ite_eq_left (show i1 ≤ tower.BinaryField128.BITS by
    unfold tower.BinaryField128.BITS
    show i1.val ≤ 128
    omega)]
  step*
  have hi : i.val < 2 ^ 64 := by
    have h := i.hBounds
    simp only [UScalarTy.numBits] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq,
    Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by norm_num)),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by norm_num))]

theorem bf32_interpolation_node_spec (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 5) :
    tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  have hnb' := System.Platform.numBits_eq
  unfold tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node
  step*
  have hnb : i1.val = System.Platform.numBits := by
    rw [i1_post]
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
  split
  · step*
  · step*
    have h32 : (32 : ℕ) < System.Platform.numBits := by
      simpa [tower.BinaryField32.BITS] using «System.Platform.numBits_post»
    have hx : x.val = 2 ^ 32 := by
      rw [x_post]
      simp only [tower.BinaryField32.BITS, Usize.size, Usize.numBits]
      rcases hnb' with e | e <;> simp [e] at h32 ⊢
    intro h
    exact h (by scalar_tac)

/-- An index that does not fit panics: `interpolation_node` stays injective. -/
theorem bf32_interpolation_node_fail (i : Std.Usize) (hi : 2 ^ 2 ^ 5 ≤ i.val) :
    tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic := by
  have h64 : System.Platform.numBits = 64 := by
    have h := i.hBounds
    simp only [UScalarTy.numBits] at h
    rcases System.Platform.numBits_eq with e | e
    · rw [e] at h; norm_num at hi h; omega
    · exact e
  have hnb' : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := Or.inr h64
  unfold tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node
  have h16 : (32#usize : Std.Usize).val < UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; simp [h64]
  obtain ⟨x, hsh, hx⟩ : ∃ x : Std.Usize, (1#usize <<< (32#usize : Std.Usize) : RustM Std.Usize) =
      .ok x ∧ x.val = 2 ^ 32 := by
    refine ⟨⟨(1#usize : Std.Usize).bv.shiftLeft 32⟩, ?_, ?_⟩
    · show UScalar.shiftLeft_UScalar _ _ = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [ite_eq_left h16]
      rfl
    · have h1 : (1#usize : Std.Usize).bv.toNat = 1 := rfl
      have e : ((1#usize : Std.Usize).bv.shiftLeft 32).toNat =
          (1#usize : Std.Usize).bv.toNat <<< 32 % 2 ^ UScalarTy.Usize.numBits :=
        BitVec.toNat_shiftLeft
      refine e.trans ?_
      rw [h1]
      simp only [UScalarTy.numBits] at h16 ⊢
      simp [h64]
  have hi1 : ¬ (UScalar.cast UScalarTy.Usize core.num.Usize.BITS : Std.Usize).val ≤ 32 := by
    simp [core.num.Usize.BITS, UScalar.cast_val_eq]
    omega
  have hlt : ¬ i < x := by
    intro h
    have h' : i.val < x.val := h
    omega
  simp only [tower.BinaryField32.BITS, lift, Aeneas.Std.bind_ok, massert]
  rw [ite_eq_right (show ¬ UScalar.cast UScalarTy.Usize core.num.Usize.BITS ≤ 32#usize from hi1),
    hsh, Aeneas.Std.bind_ok, ite_eq_right hlt]
  simp

end Plonky3Lean.Proofs.Binary
