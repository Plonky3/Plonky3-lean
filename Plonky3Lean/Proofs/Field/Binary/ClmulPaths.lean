module

public import Plonky3Lean.Proofs.Field.Binary.GhashTower

@[expose] public section

/-!
# The carry-less multiplication paths

On a core with a carry-less multiply instruction, the tower multiplies by converting both
operands to a polynomial basis, multiplying there and converting back. Since the conversion is
the field isomorphism `N`, the result is the tower product (`mul_128_spec`, `mul_64_spec`).
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem mk_modPoly_128_iff {p q : (ZMod 2)[X]} :
    AdjoinRoot.mk (modPoly 128 135) p = AdjoinRoot.mk (modPoly 128 135) q ↔
      AdjoinRoot.mk ghashPoly p = AdjoinRoot.mk ghashPoly q := by
  rw [AdjoinRoot.mk_eq_mk, AdjoinRoot.mk_eq_mk, modPoly_128_ghash]

/-! ## 128 bits -/

theorem clmul_128x128_spec (a b : Std.U128) :
    clmul.clmul_128x128 a b ⦃ p =>
      natPoly p.1.val + X ^ 128 * natPoly p.2.val = natPoly a.val * natPoly b.val ⦄ := by
  unfold clmul.clmul_128x128
  simp only [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok]
  step*
  have hlo : ∀ x : Std.U128, (UScalar.cast UScalarTy.U64 x).val = x.val % 2 ^ 64 := fun x => by
    rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
  have hhi : ∀ x : ℕ, x < 2 ^ 128 → (x >>> 64) % 2 ^ 64 = x >>> 64 := fun x hx =>
    Nat.mod_eq_of_lt (shiftRight_64_lt_of_lt hx)
  have hshl : ∀ m : ℕ, (m <<< 64) % 2 ^ 128 = (m % 2 ^ 64) <<< 64 := fun m => by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases h1 : 64 ≤ i
    · by_cases h2 : i < 128
      · simp [h1, h2, show i - 64 < 64 by omega]
      · simp [h2, show ¬ i - 64 < 64 by omega]
    · simp [h1]
  have hm := natPoly_split middle.val 64
  have hmid : natPoly middle.val = natPoly a0.val * natPoly b1.val + natPoly a1.val * natPoly b0.val := by
    rw [middle_post, UScalar.val_xor, natPoly_xor, natPoly_clmulVal, natPoly_clmulVal]
  have hi4 : natPoly i4.val = X ^ 64 * natPoly (middle.val % 2 ^ 64) := by
    rw [i4_post, show U128.size = 2 ^ 128 by simp [U128.size, U128.numBits], hshl,
      natPoly_shiftLeft]
  rw [i5_post, i7_post, UScalar.val_xor, UScalar.val_xor, natPoly_xor, natPoly_xor, hi4, i6_post,
    natPoly_clmulVal, natPoly_clmulVal, natPoly_split a.val 64, natPoly_split b.val 64]
  rw [a0_post, a1_post, b0_post, b1_post, hlo, hlo, hlo, hlo, i_post, i1_post,
    hhi _ (u128_val_lt a), hhi _ (u128_val_lt b)] at hmid
  rw [a0_post, a1_post, b0_post, b1_post, hlo, hlo, hlo, hlo, i_post, i1_post,
    hhi _ (u128_val_lt a), hhi _ (u128_val_lt b)]
  linear_combination (X ^ 64 : (ZMod 2)[X]) * (hm.symm.trans hmid)

theorem composed_poly_mul_128_spec (a b : Std.U128) :
    clmul.composed_poly_mul_128 a b ⦃ r =>
      AdjoinRoot.mk (modPoly 128 135) (natPoly r.val) =
        AdjoinRoot.mk (modPoly 128 135) (natPoly a.val * natPoly b.val) ⦄ := by
  unfold clmul.composed_poly_mul_128
  apply WP.spec_bind (clmul_128x128_spec a b)
  rintro ⟨low, high⟩ h
  dsimp only at h ⊢
  apply WP.spec_mono (reduce_128_toQuot low high)
  intro r hr
  rw [toQuot_eq_mk, h] at hr
  exact mk_modPoly_128_iff.mpr hr

/-- The carry-less path of `GF(2^128)` multiplication computes the tower product. -/
theorem mul_128_spec (a b : Std.U128) :
    clmul.mul_128 a b ⦃ r => towerOf 7 r = towerOf 7 a * towerOf 7 b ⦄ := by
  unfold clmul.mul_128
  apply WP.spec_bind (tower_to_poly_128_spec a)
  intro pa ha
  apply WP.spec_bind (tower_to_poly_128_spec b)
  intro pb hb
  apply WP.spec_bind (composed_poly_mul_128_spec pa pb)
  intro p hp
  apply WP.spec_mono (poly_to_tower_128_spec p)
  intro r hr
  apply N128_injective
  rw [map_mul, N128_apply, N128_apply, N128_apply, hr, hp, map_mul, ha, hb]

/-! ## 64 bits -/

/-- `N` at 64 bits, as a ring homomorphism. -/
noncomputable abbrev N64 : ConcreteBTField 6 →+* AdjoinRoot (modPoly 64 27) :=
  @towerHom _ _ (charP_modPoly (by norm_num) (by norm_num)) xi64 6 xi64_rel

theorem N64_apply (x : ConcreteBTField 6) : N64 x = towerMap xi64 6 x := rfl

theorem N64_injective : Function.Injective N64 := by
  have := nontrivial_modPoly (n := 64) (tail := 27) (by norm_num) (by norm_num)
  exact N64.injective

theorem natPoly_27 : natPoly 27 = X ^ 4 + X ^ 3 + X + 1 := by
  rw [show (27 : ℕ) = 2 ^ 4 ^^^ 2 ^ 3 ^^^ 2 ^ 1 ^^^ 2 ^ 0 by decide +kernel]
  simp only [natPoly_xor, natPoly_two_pow, natPoly_two, natPoly_one, pow_one, pow_zero]

theorem modPoly_64_basePoly : modPoly 64 27 = BF64.basePoly := by
  rw [modPoly, natPoly_27, BF64.basePoly]
  ring

theorem mk_modPoly_64_iff {p q : (ZMod 2)[X]} :
    AdjoinRoot.mk (modPoly 64 27) p = AdjoinRoot.mk (modPoly 64 27) q ↔
      AdjoinRoot.mk BF64.basePoly p = AdjoinRoot.mk BF64.basePoly q := by
  rw [AdjoinRoot.mk_eq_mk, AdjoinRoot.mk_eq_mk, modPoly_64_basePoly]

/-- The carry-less path of `GF(2^64)` multiplication computes the tower product. -/
theorem mul_64_spec (a b : Std.U64) :
    clmul.mul_64 a b ⦃ r => towerOf 6 r = towerOf 6 a * towerOf 6 b ⦄ := by
  unfold clmul.mul_64
  apply WP.spec_bind (tower_to_poly_64_spec a)
  intro pa ha
  apply WP.spec_bind (tower_to_poly_64_spec b)
  intro pb hb
  rw [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok, reduce_64_eq, Aeneas.Std.bind_ok]
  apply WP.spec_mono (poly_to_tower_64_spec _)
  intro r hr
  apply N64_injective
  rw [map_mul, N64_apply, N64_apply, N64_apply, hr, val_ofNat_64 (reduce64Nat_lt _), ← ha, ← hb,
    ← map_mul, ← natPoly_clmulVal, mk_modPoly_64_iff]
  exact mk_natPoly_reduce64Nat (u128_val_lt _)

theorem mul_pair_64_call_spec (c : Std.U64) (s : Std.U64)
    (hc : AdjoinRoot.mk (modPoly 64 27) (natPoly c.val) = N64 (towerOf 6 s)) (x : Std.U64) :
    clmul.mul_pair_64.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c x ⦃ r =>
      towerOf 6 r = towerOf 6 x * towerOf 6 s ⦄ := by
  unfold clmul.mul_pair_64.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
  apply WP.spec_bind (tower_to_poly_64_spec x)
  intro px hx
  rw [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok, reduce_64_eq, Aeneas.Std.bind_ok]
  apply WP.spec_mono (poly_to_tower_64_spec _)
  intro r hr
  apply N64_injective
  rw [map_mul, N64_apply, N64_apply, hr, val_ofNat_64 (reduce64Nat_lt _), ← hx, ← hc,
    ← map_mul, ← natPoly_clmulVal, mk_modPoly_64_iff]
  exact mk_natPoly_reduce64Nat (u128_val_lt _)

/-- Both products of the carry-less `mul_pair_64` are tower products by the shared scalar. -/
theorem mul_pair_64_spec (a b s : Std.U64) :
    clmul.mul_pair_64 a b s ⦃ p =>
      towerOf 6 p.1 = towerOf 6 a * towerOf 6 s ∧ towerOf 6 p.2 = towerOf 6 b * towerOf 6 s ⦄ := by
  unfold clmul.mul_pair_64
  apply WP.spec_bind (tower_to_poly_64_spec s)
  intro ps hs
  apply WP.spec_bind (mul_pair_64_call_spec ps s hs a)
  intro r1 h1
  apply WP.spec_bind (mul_pair_64_call_spec ps s hs b)
  intro r2 h2
  rw [WP.spec_ok]
  exact ⟨h1, h2⟩

/-! ## `Poly64` -/

theorem algEquivOfEq_mk {f g : (ZMod 2)[X]} (h : f = g) (p : (ZMod 2)[X]) :
    AdjoinRoot.algEquivOfEq (ZMod 2) f g h (AdjoinRoot.mk f p) = AdjoinRoot.mk g p := by
  simp only [AdjoinRoot.coe_algEquivOfEq, AdjoinRoot.algHomOfDvd, AdjoinRoot.mapAlgHom,
    AlgHom.coe_mk]
  have e : (AdjoinRoot.map (RingHom.id (ZMod 2)) f g (by rw [Polynomial.map_id, h])).comp
      (AdjoinRoot.mk f) = AdjoinRoot.mk g := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [AdjoinRoot.mk_C]
    · simp [AdjoinRoot.mk_X]
  exact congrArg (fun φ => φ p) e

/-- The basis change `N` at 64 bits, as a field embedding of the tower's `GF(2^64)` into
CompPoly's `BF64` quotient. -/
noncomputable def towerToBF64 : ConcreteBTField 6 →+* BF64.BF64Quot :=
  (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ modPoly_64_basePoly).toRingEquiv.toRingHom.comp N64

theorem towerToBF64_apply (x : ConcreteBTField 6) :
    towerToBF64 x = AdjoinRoot.algEquivOfEq (ZMod 2) _ _ modPoly_64_basePoly (N64 x) := rfl

theorem towerToBF64_injective : Function.Injective towerToBF64 :=
  (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ modPoly_64_basePoly).injective.comp N64_injective

/-- `From<BinaryField64> for Poly64` is `towerToBF64`. -/
theorem poly64_from_bf64_spec (t : tower.BinaryField64) :
    poly64.Poly64.Insts.CoreConvertFromBinaryField64.from t ⦃ p =>
      toQuot64 p = towerToBF64 (towerOf 6 t) ⦄ := by
  unfold poly64.Poly64.Insts.CoreConvertFromBinaryField64.from
  apply WP.spec_bind (bf64_to_repr_spec t)
  intro i hi
  apply WP.spec_bind (tower_to_poly_64_spec i)
  intro r hr
  rw [WP.spec_ok, toQuot64_eq, towerToBF64_apply, N64_apply, towerOf, ← hi, ← towerOf, ← hr,
    algEquivOfEq_mk]

/-- `From<Poly64> for BinaryField64` is the inverse of `towerToBF64`. -/
theorem bf64_from_poly64_spec (p : poly64.Poly64) :
    tower.BinaryField64.Insts.CoreConvertFromPoly64.from p ⦃ t =>
      towerToBF64 (towerOf 6 t) = toQuot64 p ⦄ := by
  unfold tower.BinaryField64.Insts.CoreConvertFromPoly64.from
  apply WP.spec_bind (poly_to_tower_64_spec p)
  intro i hi
  apply WP.spec_mono (bf64_from_repr_spec i)
  intro t ht
  rw [towerToBF64_apply, N64_apply, towerOf, ht,
    Nat.mod_eq_of_lt (show i.val < 2 ^ 2 ^ 6 from u64_val_lt i), ← towerOf, hi, algEquivOfEq_mk,
    toQuot64_eq]

end Plonky3Lean.Proofs.Binary
