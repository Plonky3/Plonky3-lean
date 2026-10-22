module

public import Plonky3Lean.Proofs.Field.Binary.Statements

@[expose] public section

/-!
# The operators of `Poly64`, `Poly192` and `Ghash128`

Addition and subtraction are a limb-wise XOR, negation returns its argument, and multiplication
calls the kernel `Statements` proves.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem bf64_xor (a b : Std.U64) : bf64 (a ^^^ b) = bf64 a + bf64 b := rfl

theorem ghash_xor (a b : Std.U128) : ghash (a ^^^ b) = ghash a + ghash b := rfl

/-! ## `Poly64` -/

theorem poly64_add_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithAddPoly64Poly64.add a b ⦃ r => bf64 r = bf64 a + bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithAddPoly64Poly64.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok]
  exact bf64_xor a b

theorem poly64_sub_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithSubPoly64Poly64.sub a b ⦃ r => bf64 r = bf64 a - bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithSubPoly64Poly64.sub
  rw [CharTwo.sub_eq_add]
  exact poly64_add_bf64 a b

theorem poly64_neg_bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithNegPoly64.neg a ⦃ r => bf64 r = -bf64 a ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithNegPoly64.neg
  rw [WP.spec_ok, CharTwo.neg_eq]

theorem poly64_mul_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithMulPoly64Poly64.mul a b ⦃ r => bf64 r = bf64 a * bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithMulPoly64Poly64.mul
  exact WP.spec_bind (poly_mul_64_bf64 a b) fun _ h => by rw [WP.spec_ok]; exact h

/-! ## `Ghash128` -/

theorem ghash128_add_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithAddGhash128Ghash128.add a b ⦃ r => ghash r = ghash a + ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithAddGhash128Ghash128.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok]
  exact ghash_xor a b

theorem ghash128_sub_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithSubGhash128Ghash128.sub a b ⦃ r => ghash r = ghash a - ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithSubGhash128Ghash128.sub
  rw [CharTwo.sub_eq_add]
  exact ghash128_add_ghash a b

theorem ghash128_neg_ghash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithNegGhash128.neg a ⦃ r => ghash r = -ghash a ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithNegGhash128.neg
  rw [WP.spec_ok, CharTwo.neg_eq]

theorem ghash128_mul_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithMulGhash128Ghash128.mul a b ⦃ r => ghash r = ghash a * ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithMulGhash128Ghash128.mul
  exact WP.spec_bind (poly_mul_128_spec a b) fun _ h => by rw [WP.spec_ok]; exact h

/-! ## `Poly192` -/

theorem poly192_add_eq (a₀ a₁ a₂ b₀ b₁ b₂ : Std.U64) :
    poly192.Poly192.Insts.CoreOpsArithAddPoly192Poly192.add (Std.Array.make 3#usize [a₀, a₁, a₂])
      (Std.Array.make 3#usize [b₀, b₁, b₂]) =
      .ok (Std.Array.make 3#usize [a₀ ^^^ b₀, a₁ ^^^ b₁, a₂ ^^^ b₂]) := by
  unfold poly192.Poly192.Insts.CoreOpsArithAddPoly192Poly192.add core.array.from_fn
    rust_primitives.slice.array_from_fn
  simp [rust_primitives.slice.array_from_fn_go,
    poly192.AddPoly192Poly192Poly192.add.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoly64.call_mut,
    poly64.Poly64.Insts.CoreOpsArithAddPoly64Poly64.add, lift_eq, Std.Array.index_usize]
  simp [UScalar.val, mod_numBits_of_lt]
  rfl

theorem poly192_add_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithAddPoly192Poly192.add a b ⦃ r =>
      toExt3 r = toExt3 a + toExt3 b ⦄ := by
  rw [array3_eq a, array3_eq b, poly192_add_eq, WP.spec_ok, toExt3_make, toExt3_make, toExt3_make]
  ext i
  fin_cases i <;> rfl

theorem poly192_sub_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithSubPoly192Poly192.sub a b ⦃ r =>
      toExt3 r = toExt3 a - toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithSubPoly192Poly192.sub
  rw [CharTwo.sub_eq_add]
  exact poly192_add_ext a b

theorem poly192_neg_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithNegPoly192.neg a ⦃ r => toExt3 r = -toExt3 a ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithNegPoly192.neg
  rw [WP.spec_ok, CharTwo.neg_eq]

theorem poly192_mul_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithMulPoly192Poly192.mul a b ⦃ r =>
      toExt3 r = toExt3 a * toExt3 b ⦄ := by
  rw [array3_eq a, array3_eq b]
  unfold poly192.Poly192.Insts.CoreOpsArithMulPoly192Poly192.mul poly192.Poly192.limbs_owned
    poly64.Poly64.to_bits
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly_mul_192_ext _ _) fun r hr => ?_
  rw [array3_eq r] at hr ⊢
  unfold poly192.Poly192.from_limbs poly64.Poly64.new
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok, WP.spec_ok]
  exact hr

end Plonky3Lean.Proofs.Binary
