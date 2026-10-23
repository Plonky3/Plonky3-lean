module

public import Plonky3Lean.Proofs.Field.Binary.ApiMisc

@[expose] public section

/-!
# The remaining `Poly192` methods

`frobenius` maps `a_0 + a_1 Y + a_2 Y^2` to `a_0 + a_2 Y + (a_1 + a_2) Y^2`, which is its `2^64`-th
power in `GF(2^192)`: the coefficients lie in `GF(2^64)`, and `Y^(2^64) = Y^2` because `Y^7 = 1`
(`frob_ofVector`).
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem bf64_pow_card (c : BF64) : c ^ 2 ^ 64 = c := by
  let := Fintype.ofFinite BF64
  rw [← BF64.card_bf64]
  exact FiniteField.pow_card c

/-- The Frobenius of `GF(2^192)` over `GF(2^64)`, on coefficients. -/
theorem frob_ofVector (c₀ c₁ c₂ : BF64) :
    (CompPoly.Extension.Ext.ofVector #v[c₀, c₁, c₂] : BF64.Ext3) ^ 2 ^ 64 =
      CompPoly.Extension.Ext.ofVector #v[c₀, c₂, c₁ + c₂] := by
  apply CompPoly.Extension.Ext.toQuot_injective
  rw [CompPoly.Extension.Ext.toQuot_pow, BF64.toQuot_ofVector, BF64.toQuot_ofVector]
  set R := AdjoinRoot.mk BF64.ext3Params.poly X with hR
  have h2 : (2 : AdjoinRoot BF64.ext3Params.poly) = 0 := by
    rw [show (2 : AdjoinRoot BF64.ext3Params.poly) = AdjoinRoot.of _ 2 from (map_ofNat _ 2).symm,
      BF64.two_eq_zero, map_zero]
  have hmk : ∀ c : BF64, AdjoinRoot.mk BF64.ext3Params.poly (C c) ^ 2 ^ 64 =
      AdjoinRoot.mk BF64.ext3Params.poly (C c) := fun c => by
    rw [← map_pow, ← map_pow, bf64_pow_card]
  have h3 : R ^ 3 = R + 1 := by
    have hp : BF64.ext3Params.poly = X ^ 3 + X + 1 := by rw [BF64.ext3Params_poly, BF64.ext3Poly]
    have h0 : AdjoinRoot.mk BF64.ext3Params.poly (X ^ 3 + X + 1) = 0 :=
      AdjoinRoot.mk_eq_zero.mpr (by rw [hp])
    simp only [map_add, map_pow, map_one] at h0
    rw [← hR] at h0
    linear_combination h0 - (R + 1) * h2
  have : CharP (AdjoinRoot BF64.ext3Params.poly) 2 :=
    charP_of_injective_algebraMap (algebraMap BF64 (AdjoinRoot BF64.ext3Params.poly)).injective 2
  have h7 : R ^ 7 = 1 := by linear_combination (R ^ 4 + R ^ 2 + R + 1) * h3 + (R ^ 2 + R) * h2
  have hq : R ^ 2 ^ 64 = R ^ 2 := by
    rw [show 2 ^ 64 = 7 * 2635249153387078802 + 2 by norm_num, pow_add, pow_mul, h7, one_pow,
      one_mul]
  simp only [map_add, map_mul, map_pow, ← hR]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, hmk, hmk, hmk, hq, ← pow_mul,
    mul_comm 2 (2 ^ 64), pow_mul, hq]
  linear_combination (AdjoinRoot.mk BF64.ext3Params.poly (C c₂)) * (R * h3)

attribute [local step] poly64_add_bf64 poly64_mul_bf64

/-- `frobenius` is the `2^64`-th power, the Frobenius of `GF(2^192)` over `GF(2^64)`. -/
theorem poly192_frobenius_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldExtensionHasFrobeniusPoly64.frobenius a ⦃ r =>
      toExt3 r = toExt3 a ^ 2 ^ 64 ⦄ := by
  rw [array3_eq a]
  unfold poly192.Poly192.Insts.P3_fieldExtensionHasFrobeniusPoly64.frobenius
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  step*
  rw [toExt3_make, toExt3_make, frob_ofVector, p_post]

/-- `composed_mul` is multiplication in `GF(2^192)`. -/
theorem poly192_composed_mul_ext (a b : poly192.Poly192) :
    poly192.Poly192.composed_mul a b ⦃ r => toExt3 r = toExt3 a * toExt3 b ⦄ := by
  rw [array3_eq a, array3_eq b]
  unfold poly192.Poly192.composed_mul
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  step*
  rw [toExt3_make, toExt3_make, toExt3_make, BF64.ofVector_mul_ofVector]
  have h3 : (3 : BF64) = 1 := by
    rw [show (3 : BF64) = 2 + 1 by norm_num, BF64.two_eq_zero, zero_add]
  have h4 : (4 : BF64) = 0 := by rw [show (4 : BF64) = 2 * 2 by norm_num, BF64.two_eq_zero, zero_mul]
  refine ofVector3_congr ?_ ?_ ?_ <;>
    simp only [p10_post, p13_post, p14_post, p31_post, p9_post, p12_post, p11_post, p6_post,
      p21_post, p8_post, p7_post, d01_post, d02_post, d12_post, p_post, p1_post, p2_post, p3_post,
      p4_post, p5_post, c0_post, c1_post, c2_post] <;>
    ring_nf <;> simp only [BF64.two_eq_zero, h3, h4, mul_zero, zero_add, add_zero, mul_one]

/-! ## Equality of arrays -/

theorem array_index_eq {T : Type} {N : Std.Usize} (a : Std.Array T N) (k : Std.Usize)
    (hk : k.val < N.val) :
    CoreModels.rust_primitives.slice.array_index a k =
      .ok (a.val[k.val]'(by have := a.property; omega)) := by
  unfold CoreModels.rust_primitives.slice.array_index
  have h : k.val < (Std.Array.to_slice a).length := by simp [Std.Array.val_to_slice]; omega
  simp [Std.Slice.index_usize, Std.Array.val_to_slice]
  rw [List.getElem?_eq_getElem (by have := a.property; omega)]

theorem array_eq_loop_spec {T : Type} [DecidableEq T] {N : Std.Usize}
    (inst : CoreModels.core.cmp.PartialEq T T)
    (heq : ∀ x y, inst.eq x y ⦃ b => b = decide (x = y) ⦄) (a b : Std.Array T N) (i : Std.Usize)
    (hi : i.val ≤ N.val) (hd : ∀ j < i.val, a.val[j]? = b.val[j]?) :
    CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop inst a b i ⦃ r => r = decide (a = b) ⦄ := by
  unfold CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  refine loop.spec_decr_nat (fun k => N.val - k.val)
    (fun k => k.val ≤ N.val ∧ ∀ j < k.val, a.val[j]? = b.val[j]?) _ _ _ ?_ ⟨hi, hd⟩
  rintro k ⟨hk, hkd⟩
  unfold CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
  have hla := a.property
  have hlb := b.property
  split
  · rename_i hkN
    have hk' : k.val < N.val := by scalar_tac
    rw [array_index_eq a k hk', Aeneas.Std.bind_ok, array_index_eq b k hk', Aeneas.Std.bind_ok]
    apply WP.spec_bind (heq _ _)
    intro c hc
    subst hc
    by_cases he : a.val[k.val]'(by omega) = b.val[k.val]'(by omega)
    · simp only [he, decide_true, ↓reduceIte]
      step*
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      by_cases hjk : j = k.val
      · subst hjk
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), he]
      · exact hkd j (by scalar_tac)
    · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      symm
      rw [decide_eq_false_iff_not]
      intro hab
      exact he (by subst hab; rfl)
  · rename_i hkN
    have hk' : k.val = N.val := by scalar_tac
    rw [WP.spec_ok]
    show true = decide (a = b)
    symm
    rw [decide_eq_true_iff]
    apply Std.Array.ext
    apply List.ext_getElem?
    intro j
    by_cases hj : j < N.val
    · exact hkd j (by omega)
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## The methods -/

theorem bf64_injective {x y : Std.U64} (h : bf64 x = bf64 y) : x = y := by
  have h' := congrArg BF64.toBitVec h
  rw [bf64, bf64, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec] at h'
  exact UScalar.eq_of_val_eq (show x.bv.toNat = y.bv.toNat by rw [h'])

theorem toExt3_injective {a b : poly192.Poly192} (h : toExt3 a = toExt3 b) : a = b := by
  rw [array3_eq a, array3_eq b, toExt3_make, toExt3_make] at h
  have hc : (#v[bf64 (a.val.getD 0 default), bf64 (a.val.getD 1 default),
      bf64 (a.val.getD 2 default)] : Vector BF64 3) =
      #v[bf64 (b.val.getD 0 default), bf64 (b.val.getD 1 default), bf64 (b.val.getD 2 default)] :=
    congrArg CompPoly.Extension.Ext.coeffs h
  have h0 := congrArg (fun v : Vector BF64 3 => v[0]) hc
  have h1 := congrArg (fun v : Vector BF64 3 => v[1]) hc
  have h2 := congrArg (fun v : Vector BF64 3 => v[2]) hc
  rw [array3_eq a, array3_eq b]
  have e0 : a.val.getD 0 default = b.val.getD 0 default := bf64_injective h0
  have e1 : a.val.getD 1 default = b.val.getD 1 default := bf64_injective h1
  have e2 : a.val.getD 2 default = b.val.getD 2 default := bf64_injective h2
  rw [e0, e1, e2]

theorem poly192_eq_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreCmpPartialEqPoly192.eq a b ⦃ r => (r = true ↔ toExt3 a = toExt3 b) ⦄ := by
  unfold poly192.Poly192.Insts.CoreCmpPartialEqPoly192.eq
    CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq
  apply WP.spec_mono (array_eq_loop_spec _ (fun x y => by
    show poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq x y ⦃ _ ⦄
    unfold poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq
    rw [WP.spec_ok]) a b 0#usize (by simp) (fun _ h => absurd h (by simp)))
  intro r hr
  subst hr
  rw [decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, toExt3_injective⟩

theorem poly192_bool_check_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      toExt3 r = toExt3 a * toExt3 a + toExt3 a ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (poly192_square_ext a) fun p hp => ?_
  refine WP.spec_mono (poly192_add_ext p a) fun r hr => ?_
  rw [hr, hp]

theorem poly192_embed_ext (v : poly64.Poly64) :
    poly192.Poly192.embed v ⦃ r => toExt3 r = algebraMap BF64 BF64.Ext3 (bf64 v) ⦄ := by
  unfold poly192.Poly192.embed poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  rw [WP.spec_ok, toExt3_make, algebraMap_ext3]
  rfl

theorem poly192_from_poly64_ext (v : poly64.Poly64) :
    poly192.Poly192.Insts.CoreConvertFromPoly64.from v ⦃ r =>
      toExt3 r = algebraMap BF64 BF64.Ext3 (bf64 v) ⦄ := by
  unfold poly192.Poly192.Insts.CoreConvertFromPoly64.from
  exact poly192_embed_ext v

theorem poly192_ZERO_ext :
    poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO ⦃ r => toExt3 r = 0 ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  apply WP.spec_mono (poly192_embed_ext _)
  intro r hr
  rw [hr]
  unfold poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  rw [show bf64 0#u64 = 0 from (bf64_eq_zero_iff _).mpr rfl, map_zero]

theorem poly192_new_spec (c : Std.Array poly64.Poly64 3#usize) :
    poly192.Poly192.new c ⦃ r => r = c ⦄ := by
  unfold poly192.Poly192.new; rw [WP.spec_ok]

theorem poly192_coefficients_spec (a : poly192.Poly192) :
    poly192.Poly192.coefficients a ⦃ r => r = a ⦄ := by
  unfold poly192.Poly192.coefficients; rw [WP.spec_ok]

theorem poly192_invert_or_zero_ext (a : poly192.Poly192) :
    poly192.Poly192.invert_or_zero a ⦃ r => toExt3 r = (toExt3 a)⁻¹ ⦄ := by
  unfold poly192.Poly192.invert_or_zero
  refine WP.spec_bind (poly192_try_inverse_spec a) fun o ho => ?_
  refine WP.spec_bind poly192_ZERO_ext fun z hz => ?_
  by_cases ha : toExt3 a = 0
  · rw [ho.1 ha]
    simp only [CoreModels.core.option.Option.unwrap_or, WP.spec_ok]
    rw [hz, ha, inv_zero]
  · obtain ⟨c, rfl, hc⟩ := ho.2 ha
    simp only [CoreModels.core.option.Option.unwrap_or, WP.spec_ok]
    exact hc

theorem poly192_is_in_basefield_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldExtensionFieldPoly64.is_in_basefield a ⦃ b =>
      (b = true ↔ bf64 (a.val.getD 1 default) = 0 ∧ bf64 (a.val.getD 2 default) = 0) ⦄ := by
  rw [array3_eq a]
  unfold poly192.Poly192.Insts.P3_fieldFieldExtensionFieldPoly64.is_in_basefield
  simp only [index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly64_is_zero_spec _) fun b hb => ?_
  split
  · rename_i h
    refine WP.spec_mono (poly64_is_zero_spec _) fun c hc => ?_
    have hb' := hb.mp h
    simp only [Std.Array.make_val]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨fun e => ⟨hb', hc.mp e⟩, fun e => hc.mpr e.2⟩
  · rename_i h
    refine (WP.spec_ok _).mpr ?_
    simp only [Std.Array.make_val]
    constructor
    · intro e; exact absurd e (by simp)
    · intro ⟨h1, _⟩; exact absurd (hb.mpr (by simpa using h1)) h

theorem poly192_as_base_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldExtensionFieldPoly64.as_base a ⦃ r =>
      ((bf64 (a.val.getD 1 default) = 0 ∧ bf64 (a.val.getD 2 default) = 0) →
        r = .Some (a.val.getD 0 default) ∧
        toExt3 a = algebraMap BF64 BF64.Ext3 (bf64 (a.val.getD 0 default))) ∧
      (¬ (bf64 (a.val.getD 1 default) = 0 ∧ bf64 (a.val.getD 2 default) = 0) → r = .None) ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldExtensionFieldPoly64.as_base
  refine WP.spec_bind (poly192_is_in_basefield_ext a) fun b hb => ?_
  have e0 := index_usize_0 (a.val.getD 0 default) (a.val.getD 1 default) (a.val.getD 2 default)
  rw [← array3_eq a] at e0
  rw [e0, Aeneas.Std.bind_ok]
  unfold core.bool.Bool.then_some
  rw [WP.spec_ok]
  refine ⟨fun h => ⟨by simp [hb.mpr h], ?_⟩, fun h => by simp [show b = false by
    cases b <;> simp_all]⟩
  rw [array3_eq a, toExt3_make, algebraMap_ext3]
  simp only [Std.Array.make_val, List.getD_cons_zero] at h ⊢
  rw [h.1, h.2]

theorem ext3_pow_card (x : BF64.Ext3) : x ^ (2 ^ 64) ^ 3 = x := by
  let := Fintype.ofFinite BF64.Ext3
  have hc : Fintype.card BF64.Ext3 = (2 ^ 64) ^ 3 := by rw [BF64.card_ext3, ← pow_mul]
  rw [← hc]
  exact FiniteField.pow_card x

theorem pow_pow_mod_three {M : Type} [Monoid M] {q : ℕ} (hM : ∀ y : M, y ^ q ^ 3 = y) (x : M)
    (n : ℕ) : x ^ q ^ n = x ^ q ^ (n % 3) := by
  have h : ∀ k, x ^ q ^ (3 * k) = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [show 3 * (k + 1) = 3 * k + 3 by ring, pow_add, pow_mul, ih, hM]
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, mul_comm, pow_mul, h]

/-- `repeated_frobenius(count)` is the `(2^64)^count`-th power. -/
theorem poly192_repeated_frobenius_ext (a : poly192.Poly192) (count : Std.Usize) :
    poly192.Poly192.Insts.P3_fieldExtensionHasFrobeniusPoly64.repeated_frobenius a count ⦃ r =>
      toExt3 r = toExt3 a ^ (2 ^ 64) ^ count.val ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldExtensionHasFrobeniusPoly64.repeated_frobenius
    poly192.DEGREE
  rw [pow_pow_mod_three ext3_pow_card]
  step
  rw [← i_post]
  have hi3 : i.val < 3 := by scalar_tac
  generalize i.val = v at *
  interval_cases v
  · simp only [WP.spec_ok, pow_zero, pow_one]
  · simpa using poly192_frobenius_ext a
  · refine WP.spec_bind (poly192_frobenius_ext a) fun p hp => ?_
    refine WP.spec_mono (poly192_frobenius_ext p) fun r hr => ?_
    rw [hr, hp, ← pow_mul, ← pow_two]

theorem poly192_bits_spec : poly192.Poly192.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 192 ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldField.bits poly192.Poly192.BITS poly192.DEGREE
  step*

theorem poly192_interpolation_node_ext (i : Std.Usize) :
    poly192.Poly192.Insts.P3_fieldFieldField.interpolation_node i ⦃ r =>
      ∃ p : Std.U64, p.val = i.val ∧ toExt3 r = algebraMap BF64 BF64.Ext3 (bf64 p) ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldField.interpolation_node
  refine WP.spec_bind (poly64_interpolation_node_spec i) fun p hp => ?_
  exact WP.spec_mono (poly192_embed_ext p) fun r hr => ⟨p, hp, hr⟩

theorem poly192_from_prime_subfield_ext (f : gf2.Gf2) :
    poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      ∃ p : Std.U64, p.val = (decide (f.val = 1)).toNat ∧
        toExt3 r = algebraMap BF64 BF64.Ext3 (bf64 p) ⦄ := by
  unfold poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  refine WP.spec_bind (poly64_from_prime_subfield_spec f) fun p hp => ?_
  exact WP.spec_mono (poly192_embed_ext p) fun r hr => ⟨p, hp, hr⟩

end Plonky3Lean.Proofs.Binary
