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

end Plonky3Lean.Proofs.Binary
