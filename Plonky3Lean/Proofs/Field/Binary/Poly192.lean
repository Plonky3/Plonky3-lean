module

public import Plonky3Lean.Proofs.Field.Binary.Poly64Sqrt
public import ToCompPoly.Fields.Binary.BF64Ext3

@[expose] public section

/-!
# `GF(2^192)` as `GF(2^64)[Y] / (Y^3 + Y + 1)`

The portable multiplication, squaring and scaling of p3-binary-field's `Poly192`.

An element is three 64-bit limbs `[a_0, a_1, a_2]`, standing for `a_0 + a_1 Y + a_2 Y^2`.

- The product is Karatsuba's three-term form: six carry-less limb products, combined unreduced.
- Each combined limb is reduced modulo `x^64 + x^4 + x^3 + x + 1` on its own.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## Limbs -/

/-- Every array of three limbs is the literal of its entries. -/
theorem array3_eq {T : Type} [Inhabited T] (a : Std.Array T 3#usize) :
    a = Std.Array.make 3#usize [a.val.getD 0 default, a.val.getD 1 default, a.val.getD 2 default] := by
  apply Std.Array.ext
  rw [Std.Array.make_val]
  have h : a.val.length = 3 := by simp
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  have : i < 3 := by omega
  interval_cases i <;> simp [List.getD_eq_getElem?_getD]

theorem index_usize_0 {T : Type} (x y z : T) :
    Std.Array.index_usize (Std.Array.make 3#usize [x, y, z]) 0#usize = .ok x := by
  simp [Std.Array.index_usize]

theorem index_usize_1 {T : Type} (x y z : T) :
    Std.Array.index_usize (Std.Array.make 3#usize [x, y, z]) 1#usize = .ok y := by
  simp [Std.Array.index_usize]

theorem index_usize_2 {T : Type} (x y z : T) :
    Std.Array.index_usize (Std.Array.make 3#usize [x, y, z]) 2#usize = .ok z := by
  simp [Std.Array.index_usize]

theorem toExt3_make (x y z : Std.U64) :
    toExt3 (Std.Array.make 3#usize [x, y, z]) = CompPoly.Extension.Ext.ofVector #v[bf64 x, bf64 y, bf64 z] := by
  simp [toExt3, Std.Array.make_val]

theorem xor_val {ty : UScalarTy} (x y : UScalar ty) : (x ^^^ y).val = x.val ^^^ y.val := by
  show (x.bv ^^^ y.bv).toNat = _
  rw [BitVec.toNat_xor]
  rfl

/-- One reduced limb, as `reduce_64` returns it. -/
def reduceLimb (x : Std.U128) : Std.U64 := ⟨BitVec.ofNat 64 (reduce64Nat x.val)⟩

theorem toQuot64_reduceLimb (x : Std.U128) :
    toQuot64 (reduceLimb x) = AdjoinRoot.mk BF64.basePoly (natPoly x.val) := by
  rw [reduceLimb, toQuot64_eq, val_ofNat_64 (reduce64Nat_lt _),
    mk_natPoly_reduce64Nat (u128_val_lt x)]

/-- `reduce_64`, mapped over three limbs, reduces each. -/
theorem map_reduce_64_eq (x y z : Std.U128) :
    core.array.Array.map P.Insts.CoreOpsFunctionFnMutTupleU128U64
      (Std.Array.make 3#usize [x, y, z]) clmul.reduce_64 =
      .ok (Std.Array.make 3#usize [reduceLimb x, reduceLimb y, reduceLimb z]) := by
  unfold core.array.Array.map
  rw [array_map_eq _ _ _ reduceLimb (fun v => by
    show (do let i ← clmul.reduce_64 v; RustM.ok (i, clmul.reduce_64)) = _
    rw [reduce_64_eq, bind_tc_ok]
    rfl)]
  congr 1

/-- A reduced limb is the element of `BF64` whose quotient image is its polynomial. -/
theorem bf64_reduceLimb_eq {X : Std.U128} {e : BF64}
    (h : AdjoinRoot.mk BF64.basePoly (natPoly X.val) = BF64.toQuot e) : bf64 (reduceLimb X) = e :=
  BF64.toQuot_injective (by rw [show BF64.toQuot (bf64 (reduceLimb X)) = toQuot64 (reduceLimb X) from rfl,
    toQuot64_reduceLimb, h])

/-- The limb `Σ` that a combination of carry-less products stands for, in `GF(2^64)`. -/
theorem mk_natPoly_xor (u v : Std.U128) :
    AdjoinRoot.mk BF64.basePoly (natPoly (u ^^^ v).val) =
      AdjoinRoot.mk BF64.basePoly (natPoly u.val) + AdjoinRoot.mk BF64.basePoly (natPoly v.val) := by
  rw [xor_val, natPoly_xor, map_add]

theorem mk_natPoly_xor64 (u v : Std.U64) :
    AdjoinRoot.mk BF64.basePoly (natPoly (u ^^^ v).val) =
      AdjoinRoot.mk BF64.basePoly (natPoly u.val) + AdjoinRoot.mk BF64.basePoly (natPoly v.val) := by
  rw [xor_val, natPoly_xor, map_add]

theorem toQuot64_xor (u v : Std.U64) : toQuot64 (u ^^^ v) = toQuot64 u + toQuot64 v := by
  rw [toQuot64_eq, toQuot64_eq, toQuot64_eq, mk_natPoly_xor64]

/-- The carry-less product `clmul_64x64` returns. -/
def clmulVal (a b : Std.U64) : Std.U128 :=
  ⟨BitVec.ofNat 128 (bmulNat a.val b.val ||| highNat a.bv b.bv <<< 64)⟩

theorem clmul_64x64_eq_clmulVal (a b : Std.U64) :
    clmul.portable.clmul_64x64 a b = .ok (clmulVal a b) := clmul_64x64_eq a b

theorem natPoly_clmulVal (a b : Std.U64) :
    natPoly (clmulVal a b).val = natPoly a.val * natPoly b.val := by
  have h := clmul_64x64_spec a b
  rw [clmul_64x64_eq_clmulVal, WP.spec_ok, poly_eq_natPoly, poly_eq_natPoly,
    poly_eq_natPoly] at h
  exact h

/-! ## The extracted functions -/

theorem toQuot_bf64 (a : Std.U64) : BF64.toQuot (bf64 a) = toQuot64 a := rfl

/-- Two elements of `Ext3` given by equal coefficients are equal. -/
theorem ofVector3_congr {x₀ x₁ x₂ y₀ y₁ y₂ : BF64} (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
    (CompPoly.Extension.Ext.ofVector #v[x₀, x₁, x₂] : BF64.Ext3) =
      CompPoly.Extension.Ext.ofVector #v[y₀, y₁, y₂] := by
  rw [h₀, h₁, h₂]

theorem poly_mul_192_ext_mk (a₀ a₁ a₂ b₀ b₁ b₂ : Std.U64) :
    clmul.gf192.poly_mul_192 (Std.Array.make 3#usize [a₀, a₁, a₂]) (Std.Array.make 3#usize [b₀, b₁, b₂])
      ⦃ r => toExt3 r = toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) *
        toExt3 (Std.Array.make 3#usize [b₀, b₁, b₂]) ⦄ := by
  unfold clmul.gf192.poly_mul_192 clmul.gf192.composed_mul_192 clmul.gf192.mul_unreduced
  simp only [index_usize_0, index_usize_1, index_usize_2, lift_eq, Aeneas.Std.bind_ok,
    clmul_64x64_eq_clmulVal, map_reduce_64_eq, WP.spec_ok]
  rw [toExt3_make, toExt3_make, toExt3_make, BF64.ofVector_mul_ofVector]
  refine ofVector3_congr ?_ ?_ ?_ <;> apply bf64_reduceLimb_eq <;>
    simp only [mk_natPoly_xor, natPoly_clmulVal, map_mul, ← toQuot64_eq, toQuot64_xor,
      BF64.toQuot_add, BF64.toQuot_mul, toQuot_bf64] <;>
    generalize toQuot64 a₀ = A₀, toQuot64 a₁ = A₁, toQuot64 a₂ = A₂, toQuot64 b₀ = B₀,
      toQuot64 b₁ = B₁, toQuot64 b₂ = B₂
  · linear_combination (A₁ * B₁ + A₂ * B₂) * two_eq_zero_quot64
  · linear_combination (A₀ * B₀ + A₁ * B₁) * two_eq_zero_quot64
  · linear_combination (A₀ * B₀) * two_eq_zero_quot64

/-- `poly_mul_192` never panics and multiplies in CompPoly's `BF64.Ext3`. -/
theorem poly_mul_192_ext (a b : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_mul_192 a b ⦃ r => toExt3 r = toExt3 a * toExt3 b ⦄ := by
  rw [array3_eq a, array3_eq b]
  exact poly_mul_192_ext_mk _ _ _ _ _ _

theorem poly_square_192_ext_mk (a₀ a₁ a₂ : Std.U64) :
    clmul.gf192.poly_square_192 (Std.Array.make 3#usize [a₀, a₁, a₂])
      ⦃ r => toExt3 r = toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) *
        toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) ⦄ := by
  unfold clmul.gf192.poly_square_192 clmul.gf192.composed_square_192
  simp only [index_usize_0, index_usize_1, index_usize_2, lift_eq, Aeneas.Std.bind_ok,
    clmul_64x64_eq_clmulVal, map_reduce_64_eq, WP.spec_ok]
  rw [toExt3_make, toExt3_make, BF64.ofVector_mul_ofVector]
  refine ofVector3_congr ?_ ?_ ?_ <;> apply bf64_reduceLimb_eq <;>
    simp only [mk_natPoly_xor, natPoly_clmulVal, map_mul, ← toQuot64_eq,
      BF64.toQuot_add, BF64.toQuot_mul, toQuot_bf64] <;>
    generalize toQuot64 a₀ = A₀, toQuot64 a₁ = A₁, toQuot64 a₂ = A₂
  · linear_combination (-(A₁ * A₂)) * two_eq_zero_quot64
  · linear_combination (-(A₀ * A₁ + A₁ * A₂)) * two_eq_zero_quot64
  · linear_combination (-(A₀ * A₂)) * two_eq_zero_quot64

/-- `poly_square_192` never panics and squares in CompPoly's `BF64.Ext3`. -/
theorem poly_square_192_ext (a : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_square_192 a ⦃ r => toExt3 r = toExt3 a * toExt3 a ⦄ := by
  rw [array3_eq a]
  exact poly_square_192_ext_mk _ _ _

theorem poly_mul_192_by_64_ext_mk (a₀ a₁ a₂ k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 (Std.Array.make 3#usize [a₀, a₁, a₂]) k ⦃ r =>
      toExt3 r = toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) * algebraMap BF64 BF64.Ext3 (bf64 k) ⦄ := by
  unfold clmul.gf192.poly_mul_192_by_64 clmul.gf192.composed_mul_192_by_64 core.array.Array.map
  rw [array_map_eq _ _ _ (fun x => reduceLimb (clmulVal x k)) (fun v => by
      show (do
        let i ← clmul.portable.clmul_64x64 v k
        let i1 ← clmul.reduce_64 i
        RustM.ok (i1, k)) = _
      rw [clmul_64x64_eq_clmulVal, bind_tc_ok, reduce_64_eq, bind_tc_ok]
      rfl), WP.spec_ok]
  rw [toExt3_make, BF64.ofVector_mul_algebraMap]
  simp only [toExt3, Std.Array.from_val, Std.Array.make_val, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ]
  refine ofVector3_congr ?_ ?_ ?_ <;> apply bf64_reduceLimb_eq <;>
    simp only [natPoly_clmulVal, map_mul, ← toQuot64_eq, BF64.toQuot_mul, toQuot_bf64]

/-- `poly_mul_192_by_64` never panics and scales by an element of `GF(2^64)` in `BF64.Ext3`. -/
theorem poly_mul_192_by_64_ext (a : Std.Array Std.U64 3#usize) (k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 a k ⦃ r =>
      toExt3 r = toExt3 a * algebraMap BF64 BF64.Ext3 (bf64 k) ⦄ := by
  rw [array3_eq a]
  exact poly_mul_192_by_64_ext_mk _ _ _ _

end Plonky3Lean.Proofs.Binary
