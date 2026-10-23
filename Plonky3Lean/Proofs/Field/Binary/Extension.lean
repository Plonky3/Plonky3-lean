module

public import Plonky3Lean.Proofs.Field.Binary.TowerExp

@[expose] public section

/-!
# The tower as an extension of its lower levels

`frobenius` over level `l` is `x ↦ x^(2^(2^l))`, raising to the size of level `l`. For a
quadratic step it is the conjugation `(lo + hi Z) + hi X`; otherwise `exp_power_of_2`.
`repeated_frobenius` raises to that power `count` times; it reduces `count` modulo the degree,
which `x^(2^BITS) = x` allows.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- `x^(2^(2^l count))` only depends on `count` modulo the degree `2^(u - l)`. -/
theorem pow_repeated_mod {u l : ℕ} (hlu : l ≤ u) (x : ConcreteBTField u) (count : ℕ) :
    x ^ 2 ^ (2 ^ l * count) = x ^ 2 ^ (2 ^ l * (count % 2 ^ (u - l))) := by
  rw [pow_two_pow_mod x (2 ^ l * count), show 2 ^ u = 2 ^ l * 2 ^ (u - l) by
    rw [← pow_add, Nat.add_sub_cancel' hlu], Nat.mul_mod_mul_left]

/-! ## The embedding -/

/-- CompPoly's embedding of level `l` into level `u`. -/
abbrev embedTo (l u : ℕ) (h : l ≤ u) := concreteTowerAlgebraMap l u h

/-- A value is in the image of level `l` exactly when it fits in `2^l` bits, and its preimage
has the same bits. -/
theorem towerOf_eq_embed_iff {l u : ℕ} (h : l ≤ u) {ty : UScalarTy} {a : UScalar ty}
    (ha : a.val < 2 ^ 2 ^ u) (y : ConcreteBTField l) :
    towerOf u a = embedTo l u h y ↔ a.val = y.toNat := by
  constructor
  · intro e
    have e' := congrArg ConcreteBTField.toNat e
    rwa [towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt ha, toNat_concreteTowerAlgebraMap]
      at e'
  · intro e
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt ha, toNat_concreteTowerAlgebraMap, e]

theorem in_image_iff {l u : ℕ} (h : l ≤ u) {ty : UScalarTy} {a : UScalar ty}
    (ha : a.val < 2 ^ 2 ^ u) :
    (∃ y : ConcreteBTField l, towerOf u a = embedTo l u h y) ↔ a.val < 2 ^ 2 ^ l := by
  constructor
  · rintro ⟨y, e⟩
    rw [(towerOf_eq_embed_iff h ha y).mp e]
    exact y.toNat_lt
  · intro hl
    refine ⟨fromNat a.val, (towerOf_eq_embed_iff h ha _).mpr ?_⟩
    rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hl]

theorem shiftRight_eq_zero_iff_lt (x n : ℕ) : x >>> n = 0 ↔ x < 2 ^ n := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by positivity)]

@[step]
theorem bf128_to_repr_spec (x : tower.BinaryField128) :
    tower.BinaryField128.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField128.to_repr tower.BinaryField128.raw_to_repr; simp only [WP.spec_ok]

/-! ## `GF(2^16)` over `GF(2^8)` -/

theorem bf16_bf8_frobenius_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ 2 ^ 3 ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius
    tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField16.BITS, tower.BinaryField8.BITS]
  step*
  have hg1 : bf1.val < 2 ^ 2 ^ 3 := by scalar_tac
  exact ⟨by rw [r_post]; exact join_lt hg1 (by scalar_tac),
    towerOf_conj a0_post a0_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1 r_post⟩

theorem bf16_bf8_from_spec (x : tower.BinaryField8) :
    tower.BinaryField16.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 4 r = embedTo 3 4 (by omega) (towerOf 3 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 3 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.CoreConvertFromBinaryField8.from
    CoreModels.core.U16.Insts.CoreConvertFromU8.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf16_bf8_is_in_basefield_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 4 a = embedTo 3 4 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield
  simp only [tower.BinaryField8.BITS]
  step*
  have hz : i1 = 0#u16 ↔ a.val >>> 8 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf16_bf8_as_base_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 4 a = embedTo 3 4 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 3 4 (by omega) (towerOf 3 c) = towerOf 4 a) ∧
      ((¬∃ y, towerOf 4 a = embedTo 3 4 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base
  refine WP.spec_bind (bf16_bf8_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField16BinaryField8.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField8.call_once]
    have hl : a.val < 2 ^ 2 ^ 3 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U8 i)
        tower.BinaryField8.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf16_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf8_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]

theorem bf16_bf8_repeated_frobenius_spec (a : tower.BinaryField16) (count : Std.Usize) :
    tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  rw [pow_repeated_mod (show 3 ≤ 4 by omega)]
  unfold tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius
    tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField16.BITS, tower.BinaryField8.BITS]
  step*
  case h1 =>
    have hc : count.val % 2 = 0 := by
      have := congrArg UScalar.val ‹count1 = 0#usize›
      simp only [count1_post, i_post] at this; simpa using this
    refine ⟨hA, ?_⟩
    rw [show 4 - 3 = 1 from rfl, pow_one, hc, mul_zero, pow_zero, pow_one]
  case h2 =>
    have hc : count.val % 2 = 1 := by
      have h0 : count1.val ≠ 0 := fun h => ‹¬count1 = 0#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [count1_post, i_post] at h0; omega
    refine WP.spec_mono (bf16_bf8_frobenius_spec a) fun r h => ⟨h.1, ?_⟩
    rw [h.2, show 4 - 3 = 1 from rfl, pow_one, hc, mul_one]

/-! ## `GF(2^32)` over `GF(2^8)` -/

theorem bf32_bf8_from_spec (x : tower.BinaryField8) :
    tower.BinaryField32.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 5 r = embedTo 3 5 (by omega) (towerOf 3 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 3 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreConvertFromBinaryField8.from
    CoreModels.core.U32.Insts.CoreConvertFromU8.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf32_bf8_is_in_basefield_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 5 a = embedTo 3 5 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield
  simp only [tower.BinaryField8.BITS]
  step*
  have hz : i1 = 0#u32 ↔ a.val >>> 8 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf32_bf8_as_base_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 5 a = embedTo 3 5 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 3 5 (by omega) (towerOf 3 c) = towerOf 5 a) ∧
      ((¬∃ y, towerOf 5 a = embedTo 3 5 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base
  refine WP.spec_bind (bf32_bf8_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField32BinaryField8.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField8.call_once]
    have hl : a.val < 2 ^ 2 ^ 3 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U8 i)
        tower.BinaryField8.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf32_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf8_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf32_bf8_frobenius_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField32.BITS, tower.BinaryField8.BITS]
  step*
  exact WP.spec_mono (bf32_exp_power_of_2_spec a 8#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf32_bf8_repeated_frobenius_spec (a : tower.BinaryField32) (count : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 3 ≤ 5 by omega)]
  unfold tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField32.BITS, tower.BinaryField8.BITS]
  step*
  refine WP.spec_mono (bf32_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num

/-! ## `GF(2^32)` over `GF(2^16)` -/

theorem bf32_bf16_from_spec (x : tower.BinaryField16) :
    tower.BinaryField32.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 5 r = embedTo 4 5 (by omega) (towerOf 4 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 4 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreConvertFromBinaryField16.from
    CoreModels.core.U32.Insts.CoreConvertFromU16.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf32_bf16_is_in_basefield_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 5 a = embedTo 4 5 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield
  simp only [tower.BinaryField16.BITS]
  step*
  have hz : i1 = 0#u32 ↔ a.val >>> 16 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf32_bf16_as_base_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 5 a = embedTo 4 5 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 4 5 (by omega) (towerOf 4 c) = towerOf 5 a) ∧
      ((¬∃ y, towerOf 5 a = embedTo 4 5 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base
  refine WP.spec_bind (bf32_bf16_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField32BinaryField16.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField16.call_once]
    have hl : a.val < 2 ^ 2 ^ 4 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U16 i)
        tower.BinaryField16.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf32_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf16_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf32_bf16_frobenius_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ 2 ^ 4 ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField32.BITS, tower.BinaryField16.BITS]
  step*
  have hg1 : bf1.val < 2 ^ 2 ^ 4 := by scalar_tac
  exact ⟨by rw [r_post]; exact join_lt hg1 (by scalar_tac),
    towerOf_conj a0_post a0_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1 r_post⟩

theorem bf32_bf16_repeated_frobenius_spec (a : tower.BinaryField32) (count : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  rw [pow_repeated_mod (show 4 ≤ 5 by omega)]
  unfold tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField32.BITS, tower.BinaryField16.BITS]
  step*
  case h1 =>
    have hc : count.val % 2 = 0 := by
      have := congrArg UScalar.val ‹count1 = 0#usize›
      simp only [count1_post, i_post] at this; simpa using this
    refine ⟨hA, ?_⟩
    rw [show 5 - 4 = 1 from rfl, pow_one, hc, mul_zero, pow_zero, pow_one]
  case h2 =>
    have hc : count.val % 2 = 1 := by
      have h0 : count1.val ≠ 0 := fun h => ‹¬count1 = 0#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [count1_post, i_post] at h0; omega
    refine WP.spec_mono (bf32_bf16_frobenius_spec a) fun r h => ⟨h.1, ?_⟩
    rw [h.2, show 5 - 4 = 1 from rfl, pow_one, hc, mul_one]

/-! ## `GF(2^64)` over `GF(2^32)` -/

theorem bf64_bf32_from_spec (x : tower.BinaryField32) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField32.from x ⦃ r =>
      towerOf 6 r = embedTo 5 6 (by omega) (towerOf 5 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 5 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreConvertFromBinaryField32.from
    CoreModels.core.U64.Insts.CoreConvertFromU32.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf64_bf32_is_in_basefield_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = embedTo 5 6 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield
  simp only [tower.BinaryField32.BITS]
  step*
  have hz : i1 = 0#u64 ↔ a.val >>> 32 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf64_bf32_as_base_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = embedTo 5 6 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 5 6 (by omega) (towerOf 5 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = embedTo 5 6 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base
  refine WP.spec_bind (bf64_bf32_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField64BinaryField32.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField32.call_once]
    have hl : a.val < 2 ^ 2 ^ 5 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U32 i)
        tower.BinaryField32.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf64_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf32_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf64_bf32_frobenius_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 5 ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField32.BITS]
  step*
  have hg1 : bf1.val < 2 ^ 2 ^ 5 := by scalar_tac
  exact ⟨by rw [r_post]; exact join_lt hg1 (by scalar_tac),
    towerOf_conj a0_post a0_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1 r_post⟩

theorem bf64_bf32_repeated_frobenius_spec (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 5 * count.val) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  rw [pow_repeated_mod (show 5 ≤ 6 by omega)]
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField32.BITS]
  step*
  case h1 =>
    have hc : count.val % 2 = 0 := by
      have := congrArg UScalar.val ‹count1 = 0#usize›
      simp only [count1_post, i_post] at this; simpa using this
    refine ⟨hA, ?_⟩
    rw [show 6 - 5 = 1 from rfl, pow_one, hc, mul_zero, pow_zero, pow_one]
  case h2 =>
    have hc : count.val % 2 = 1 := by
      have h0 : count1.val ≠ 0 := fun h => ‹¬count1 = 0#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [count1_post, i_post] at h0; omega
    refine WP.spec_mono (bf64_bf32_frobenius_spec a) fun r h => ⟨h.1, ?_⟩
    rw [h.2, show 6 - 5 = 1 from rfl, pow_one, hc, mul_one]

/-! ## `GF(2^128)` over `GF(2^64)` -/

theorem bf128_bf64_from_spec (x : tower.BinaryField64) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField64.from x ⦃ r =>
      towerOf 7 r = embedTo 6 7 (by omega) (towerOf 6 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 6 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreConvertFromBinaryField64.from
    CoreModels.core.U128.Insts.CoreConvertFromU64.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf128_bf64_is_in_basefield_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = embedTo 6 7 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.is_in_basefield
  simp only [tower.BinaryField64.BITS]
  step*
  have hz : i1 = 0#u128 ↔ a.val >>> 64 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf128_bf64_as_base_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = embedTo 6 7 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 6 7 (by omega) (towerOf 6 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = embedTo 6 7 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.as_base
  refine WP.spec_bind (bf128_bf64_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField128BinaryField64.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField64.call_once]
    have hl : a.val < 2 ^ 2 ^ 6 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U64 i)
        tower.BinaryField64.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf128_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf64_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf128_bf64_frobenius_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 6 ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField64.BITS]
  step*
  have hg1 : bf1.val < 2 ^ 2 ^ 6 := by scalar_tac
  exact ⟨by rw [r_post]; exact join_lt hg1 (by scalar_tac),
    towerOf_conj a0_post a0_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1 r_post⟩

theorem bf128_bf64_repeated_frobenius_spec (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 6 * count.val) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  rw [pow_repeated_mod (show 6 ≤ 7 by omega)]
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.repeated_frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField64.BITS]
  step*
  case h1 =>
    have hc : count.val % 2 = 0 := by
      have := congrArg UScalar.val ‹count1 = 0#usize›
      simp only [count1_post, i_post] at this; simpa using this
    refine ⟨hA, ?_⟩
    rw [show 7 - 6 = 1 from rfl, pow_one, hc, mul_zero, pow_zero, pow_one]
  case h2 =>
    have hc : count.val % 2 = 1 := by
      have h0 : count1.val ≠ 0 := fun h => ‹¬count1 = 0#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [count1_post, i_post] at h0; omega
    refine WP.spec_mono (bf128_bf64_frobenius_spec a) fun r h => ⟨h.1, ?_⟩
    rw [h.2, show 7 - 6 = 1 from rfl, pow_one, hc, mul_one]

/-! ## `GF(2^64)` over `GF(2^8)` -/

theorem bf64_bf8_from_spec (x : tower.BinaryField8) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 6 r = embedTo 3 6 (by omega) (towerOf 3 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 3 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreConvertFromBinaryField8.from
    CoreModels.core.U64.Insts.CoreConvertFromU8.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf64_bf8_is_in_basefield_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = embedTo 3 6 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield
  simp only [tower.BinaryField8.BITS]
  step*
  have hz : i1 = 0#u64 ↔ a.val >>> 8 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf64_bf8_as_base_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = embedTo 3 6 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 3 6 (by omega) (towerOf 3 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = embedTo 3 6 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base
  refine WP.spec_bind (bf64_bf8_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField64BinaryField8.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField8.call_once]
    have hl : a.val < 2 ^ 2 ^ 3 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U8 i)
        tower.BinaryField8.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf64_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf8_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf64_bf8_frobenius_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField8.BITS]
  step*
  exact WP.spec_mono (bf64_exp_power_of_2_spec a 8#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf64_bf8_repeated_frobenius_spec (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 3 ≤ 6 by omega)]
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField8.BITS]
  step*
  refine WP.spec_mono (bf64_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num
/-! ## `GF(2^128)` over `GF(2^8)` -/

theorem bf128_bf8_from_spec (x : tower.BinaryField8) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 7 r = embedTo 3 7 (by omega) (towerOf 3 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 3 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreConvertFromBinaryField8.from
    CoreModels.core.U128.Insts.CoreConvertFromU8.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf128_bf8_is_in_basefield_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = embedTo 3 7 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield
  simp only [tower.BinaryField8.BITS]
  step*
  have hz : i1 = 0#u128 ↔ a.val >>> 8 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf128_bf8_as_base_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = embedTo 3 7 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 3 7 (by omega) (towerOf 3 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = embedTo 3 7 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base
  refine WP.spec_bind (bf128_bf8_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField128BinaryField8.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField8.call_once]
    have hl : a.val < 2 ^ 2 ^ 3 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U8 i)
        tower.BinaryField8.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf128_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf8_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf128_bf8_frobenius_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField8.BITS]
  step*
  exact WP.spec_mono (bf128_exp_power_of_2_spec a 8#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf128_bf8_repeated_frobenius_spec (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 3 ≤ 7 by omega)]
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField8.BITS]
  step*
  refine WP.spec_mono (bf128_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num
/-! ## `GF(2^64)` over `GF(2^16)` -/

theorem bf64_bf16_from_spec (x : tower.BinaryField16) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 6 r = embedTo 4 6 (by omega) (towerOf 4 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 4 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreConvertFromBinaryField16.from
    CoreModels.core.U64.Insts.CoreConvertFromU16.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf64_bf16_is_in_basefield_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = embedTo 4 6 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield
  simp only [tower.BinaryField16.BITS]
  step*
  have hz : i1 = 0#u64 ↔ a.val >>> 16 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf64_bf16_as_base_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = embedTo 4 6 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 4 6 (by omega) (towerOf 4 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = embedTo 4 6 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base
  refine WP.spec_bind (bf64_bf16_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField64BinaryField16.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField16.call_once]
    have hl : a.val < 2 ^ 2 ^ 4 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U16 i)
        tower.BinaryField16.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf64_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf16_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf64_bf16_frobenius_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField16.BITS]
  step*
  exact WP.spec_mono (bf64_exp_power_of_2_spec a 16#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf64_bf16_repeated_frobenius_spec (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 4 ≤ 6 by omega)]
  unfold tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField64.BITS, tower.BinaryField16.BITS]
  step*
  refine WP.spec_mono (bf64_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num
/-! ## `GF(2^128)` over `GF(2^16)` -/

theorem bf128_bf16_from_spec (x : tower.BinaryField16) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 7 r = embedTo 4 7 (by omega) (towerOf 4 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 4 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreConvertFromBinaryField16.from
    CoreModels.core.U128.Insts.CoreConvertFromU16.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf128_bf16_is_in_basefield_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = embedTo 4 7 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield
  simp only [tower.BinaryField16.BITS]
  step*
  have hz : i1 = 0#u128 ↔ a.val >>> 16 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf128_bf16_as_base_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = embedTo 4 7 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 4 7 (by omega) (towerOf 4 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = embedTo 4 7 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base
  refine WP.spec_bind (bf128_bf16_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField128BinaryField16.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField16.call_once]
    have hl : a.val < 2 ^ 2 ^ 4 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U16 i)
        tower.BinaryField16.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf128_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf16_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf128_bf16_frobenius_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField16.BITS]
  step*
  exact WP.spec_mono (bf128_exp_power_of_2_spec a 16#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf128_bf16_repeated_frobenius_spec (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 4 ≤ 7 by omega)]
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField16.BITS]
  step*
  refine WP.spec_mono (bf128_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num
/-! ## `GF(2^128)` over `GF(2^32)` -/

theorem bf128_bf32_from_spec (x : tower.BinaryField32) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField32.from x ⦃ r =>
      towerOf 7 r = embedTo 5 7 (by omega) (towerOf 5 x) ⦄ := by
  have hx : x.val < 2 ^ 2 ^ 5 := by have := x.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreConvertFromBinaryField32.from
    CoreModels.core.U128.Insts.CoreConvertFromU32.from
  step*
  have hr : r.val = x.val := by
    rw [r_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i_post,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num)), Nat.mod_eq_of_lt (lt_of_lt_of_le hx (by norm_num))]
  refine (towerOf_eq_embed_iff _ (hr ▸ lt_of_lt_of_le hx (by norm_num)) _).mpr ?_
  rw [hr, towerOf, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx]

theorem bf128_bf32_is_in_basefield_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = embedTo 5 7 (by omega) y) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield
  simp only [tower.BinaryField32.BITS]
  step*
  have hz : i1 = 0#u128 ↔ a.val >>> 32 = 0 :=
    ⟨fun h => by rw [← i_post, ← i1_post, h]; rfl,
     fun h => UScalar.eq_of_val_eq (by rw [i1_post, i_post, h]; rfl)⟩
  rw [decide_eq_true_iff, in_image_iff _ hA, hz, shiftRight_eq_zero_iff_lt]
  norm_num

theorem bf128_bf32_as_base_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = embedTo 5 7 (by omega) y) →
        ∃ c, r = .Some c ∧ embedTo 5 7 (by omega) (towerOf 5 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = embedTo 5 7 (by omega) y) → r = .None) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base
  refine WP.spec_bind (bf128_bf32_is_in_basefield_spec a) fun b hb => ?_
  unfold CoreModels.core.bool.Bool.then
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun h => absurd (hb.mpr h) (by simp), fun _ => trivial⟩
  · simp only [↓reduceIte,
      extension.ExtensionFieldBinaryField128BinaryField32.as_base.closure.Insts.CoreOpsFunctionFnOnceTupleBinaryField32.call_once]
    have hl : a.val < 2 ^ 2 ^ 5 := (in_image_iff _ hA).mp (hb.mp rfl)
    have hin : (do
        let i ← a.to_repr
        let i1 ← lift (UScalar.cast UScalarTy.U32 i)
        tower.BinaryField32.from_repr i1) ⦃ c => c.val = a.val ⦄ := by
      refine WP.spec_bind (bf128_to_repr_spec a) fun i hi => ?_
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_mono (bf32_from_repr_spec _) fun c hc => ?_
      rw [hc, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, hi,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), Nat.mod_eq_of_lt hl]
    refine WP.spec_bind hin fun c hc => ?_
    rw [WP.spec_ok]
    refine ⟨fun _ => ⟨c, rfl, ?_⟩, fun h => absurd (hb.mp rfl) h⟩
    symm
    refine (towerOf_eq_embed_iff _ hA _).mpr ?_
    rw [towerOf, ConcreteBTField.toNat_fromNat, hc, Nat.mod_eq_of_lt hl]


theorem bf128_bf32_frobenius_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 5 ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField32.BITS]
  step*
  exact WP.spec_mono (bf128_exp_power_of_2_spec a 32#usize) fun r h => ⟨h.1, by rw [h.2]; rfl⟩

theorem bf128_bf32_repeated_frobenius_spec (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 5 * count.val) ⦄ := by
  rw [pow_repeated_mod (show 5 ≤ 7 by omega)]
  unfold tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [tower.BinaryField128.BITS, tower.BinaryField32.BITS]
  step*
  refine WP.spec_mono (bf128_exp_power_of_2_spec a i1) fun r h => ⟨h.1, ?_⟩
  rw [h.2, i1_post, count1_post, i_post]
  norm_num

end Plonky3Lean.Proofs.Binary
