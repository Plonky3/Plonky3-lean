module

public import Plonky3Lean.Proofs.Field.Binary.Poly64Sqrt
public import ToCompPoly.Fields.Binary.Poly192.Basic

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

theorem array3_eq {T : Type} (a : Std.Array T 3#usize) :
    ∃ x y z, a = ⟨[x, y, z], rfl⟩ := by
  obtain ⟨l, hl⟩ := a
  match l, hl with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

theorem index_usize_0 {T : Type} (x y z : T) :
    Std.Array.index_usize (⟨[x, y, z], rfl⟩ : Std.Array T 3#usize) 0#usize = .ok x := rfl

theorem index_usize_1 {T : Type} (x y z : T) :
    Std.Array.index_usize (⟨[x, y, z], rfl⟩ : Std.Array T 3#usize) 1#usize = .ok y := rfl

theorem index_usize_2 {T : Type} (x y z : T) :
    Std.Array.index_usize (⟨[x, y, z], rfl⟩ : Std.Array T 3#usize) 2#usize = .ok z := rfl

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
      .ok ⟨[reduceLimb x, reduceLimb y, reduceLimb z], rfl⟩ := by
  unfold core.array.Array.map
  rw [array_map_eq _ _ _ reduceLimb (fun v => by
    show (do let i ← clmul.reduce_64 v; RustM.ok (i, clmul.reduce_64)) = _
    rw [reduce_64_eq, Aeneas.Std.bind_ok]
    rfl)]
  rfl

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

/-! ## Arithmetic in the extension -/

theorem two_eq_zero_poly192 : (2 : BF64.BF64Quot[X]) = 0 := by
  rw [show (2 : BF64.BF64Quot[X]) = C 2 from (map_ofNat C 2).symm, two_eq_zero_quot64, map_zero]

/-- The schoolbook product of two elements, with `Y^3 = Y + 1` and `Y^4 = Y^2 + Y`. -/
theorem ofCoeffs_mul (a₀ a₁ a₂ b₀ b₁ b₂ : BF64.BF64Quot) :
    Poly192.ofCoeffs a₀ a₁ a₂ * Poly192.ofCoeffs b₀ b₁ b₂ =
      Poly192.ofCoeffs (a₀ * b₀ + a₁ * b₂ + a₂ * b₁)
        (a₀ * b₁ + a₁ * b₀ + a₁ * b₂ + a₂ * b₁ + a₂ * b₂)
        (a₀ * b₂ + a₁ * b₁ + a₂ * b₀ + a₂ * b₂) := by
  unfold Poly192.ofCoeffs
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  refine ⟨C (a₁ * b₂ + a₂ * b₁) + C (a₂ * b₂) * X, ?_⟩
  simp only [map_add, map_mul]
  unfold Poly192.modulus
  linear_combination (-(C a₁ * C b₂ + C a₂ * C b₁ + C a₂ * C b₂ * X) * (X + 1)) * two_eq_zero_poly192

/-! ## The extracted functions -/

theorem toQuot192_mk (x y z : Std.U64) :
    toQuot192 ⟨[x, y, z], rfl⟩ = Poly192.ofCoeffs (toQuot64 x) (toQuot64 y) (toQuot64 z) := rfl

theorem poly_mul_192_toQuot_mk (a₀ a₁ a₂ b₀ b₁ b₂ : Std.U64) :
    clmul.gf192.poly_mul_192 ⟨[a₀, a₁, a₂], rfl⟩ ⟨[b₀, b₁, b₂], rfl⟩ ⦃ r =>
      toQuot192 r = toQuot192 ⟨[a₀, a₁, a₂], rfl⟩ * toQuot192 ⟨[b₀, b₁, b₂], rfl⟩ ⦄ := by
  obtain ⟨c₀, e₀, h₀⟩ := clmul_64x64_ok a₀ b₀
  obtain ⟨c₁, e₁, h₁⟩ := clmul_64x64_ok a₁ b₁
  obtain ⟨c₂, e₂, h₂⟩ := clmul_64x64_ok a₂ b₂
  obtain ⟨d₀₁, f₀₁, k₀₁⟩ := clmul_64x64_ok (a₀ ^^^ a₁) (b₀ ^^^ b₁)
  obtain ⟨d₀₂, f₀₂, k₀₂⟩ := clmul_64x64_ok (a₀ ^^^ a₂) (b₀ ^^^ b₂)
  obtain ⟨d₁₂, f₁₂, k₁₂⟩ := clmul_64x64_ok (a₁ ^^^ a₂) (b₁ ^^^ b₂)
  unfold clmul.gf192.poly_mul_192 clmul.gf192.composed_mul_192 clmul.gf192.mul_unreduced
  simp only [index_usize_0, index_usize_1, index_usize_2, lift_eq, Aeneas.Std.bind_ok, e₀, e₁, e₂, f₀₁,
    f₀₂, f₁₂, map_reduce_64_eq, WP.spec_ok]
  rw [toQuot192_mk, toQuot192_mk, toQuot192_mk, toQuot64_reduceLimb, toQuot64_reduceLimb,
    toQuot64_reduceLimb, ofCoeffs_mul]
  simp only [mk_natPoly_xor, h₀, h₁, h₂, k₀₁, k₀₂, k₁₂, map_mul, ← toQuot64_eq, toQuot64_xor]
  generalize toQuot64 a₀ = A₀, toQuot64 a₁ = A₁, toQuot64 a₂ = A₂, toQuot64 b₀ = B₀,
    toQuot64 b₁ = B₁, toQuot64 b₂ = B₂
  rw [show A₀ * B₀ + A₁ * B₁ + A₂ * B₂ + (A₁ + A₂) * (B₁ + B₂) = A₀ * B₀ + A₁ * B₂ + A₂ * B₁ by
      linear_combination (A₁ * B₁ + A₂ * B₂) * two_eq_zero_quot64,
    show A₀ * B₀ + (A₀ + A₁) * (B₀ + B₁) + (A₁ + A₂) * (B₁ + B₂) =
      A₀ * B₁ + A₁ * B₀ + A₁ * B₂ + A₂ * B₁ + A₂ * B₂ by
      linear_combination (A₀ * B₀ + A₁ * B₁) * two_eq_zero_quot64,
    show A₀ * B₀ + A₁ * B₁ + (A₀ + A₂) * (B₀ + B₂) = A₀ * B₂ + A₁ * B₁ + A₂ * B₀ + A₂ * B₂ by
      linear_combination (A₀ * B₀) * two_eq_zero_quot64]

/-- `poly_mul_192` never panics and multiplies in `GF(2^64)[Y] / (Y^3 + Y + 1)`. -/
theorem poly_mul_192_toQuot (a b : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_mul_192 a b ⦃ r => toQuot192 r = toQuot192 a * toQuot192 b ⦄ := by
  obtain ⟨la, hla⟩ := a
  obtain ⟨lb, hlb⟩ := b
  match la, hla, lb, hlb with
  | [a₀, a₁, a₂], _, [b₀, b₁, b₂], _ => exact poly_mul_192_toQuot_mk a₀ a₁ a₂ b₀ b₁ b₂

theorem poly_square_192_toQuot_mk (a₀ a₁ a₂ : Std.U64) :
    clmul.gf192.poly_square_192 ⟨[a₀, a₁, a₂], rfl⟩ ⦃ r =>
      toQuot192 r = toQuot192 ⟨[a₀, a₁, a₂], rfl⟩ * toQuot192 ⟨[a₀, a₁, a₂], rfl⟩ ⦄ := by
  obtain ⟨s₀, e₀, h₀⟩ := clmul_64x64_ok a₀ a₀
  obtain ⟨s₁, e₁, h₁⟩ := clmul_64x64_ok a₁ a₁
  obtain ⟨s₂, e₂, h₂⟩ := clmul_64x64_ok a₂ a₂
  unfold clmul.gf192.poly_square_192 clmul.gf192.composed_square_192
  simp only [index_usize_0, index_usize_1, index_usize_2, lift_eq, Aeneas.Std.bind_ok, e₀, e₁, e₂,
    map_reduce_64_eq, WP.spec_ok]
  rw [toQuot192_mk, toQuot192_mk, toQuot64_reduceLimb, toQuot64_reduceLimb,
    toQuot64_reduceLimb, ofCoeffs_mul]
  simp only [mk_natPoly_xor, h₀, h₁, h₂, map_mul, ← toQuot64_eq]
  generalize toQuot64 a₀ = A₀, toQuot64 a₁ = A₁, toQuot64 a₂ = A₂
  rw [show A₀ * A₀ + A₁ * A₂ + A₂ * A₁ = A₀ * A₀ by
      linear_combination (A₁ * A₂) * two_eq_zero_quot64,
    show A₀ * A₁ + A₁ * A₀ + A₁ * A₂ + A₂ * A₁ + A₂ * A₂ = A₂ * A₂ by
      linear_combination (A₀ * A₁ + A₁ * A₂) * two_eq_zero_quot64,
    show A₀ * A₂ + A₁ * A₁ + A₂ * A₀ + A₂ * A₂ = A₁ * A₁ + A₂ * A₂ by
      linear_combination (A₀ * A₂) * two_eq_zero_quot64]

/-- `poly_square_192` never panics and squares in `GF(2^64)[Y] / (Y^3 + Y + 1)`. -/
theorem poly_square_192_toQuot (a : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_square_192 a ⦃ r => toQuot192 r = toQuot192 a * toQuot192 a ⦄ := by
  obtain ⟨la, hla⟩ := a
  match la, hla with
  | [a₀, a₁, a₂], _ => exact poly_square_192_toQuot_mk a₀ a₁ a₂

theorem val_ofNat_128 {n : ℕ} (h : n < 2 ^ 128) : (⟨BitVec.ofNat 128 n⟩ : Std.U128).val = n := by
  show (BitVec.ofNat 128 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem poly_mul_192_by_64_toQuot_mk (a₀ a₁ a₂ k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 ⟨[a₀, a₁, a₂], rfl⟩ k ⦃ r =>
      toQuot192 r = toQuot192 ⟨[a₀, a₁, a₂], rfl⟩ * AdjoinRoot.of Poly192.modulus (toQuot64 k) ⦄ := by
  unfold clmul.gf192.poly_mul_192_by_64 clmul.gf192.composed_mul_192_by_64 core.array.Array.map
  rw [array_map_eq _ _ _ (fun x => reduceLimb (clmulVal x k)) (fun v => by
      show (do
        let i ← clmul.portable.clmul_64x64 v k
        let i1 ← clmul.reduce_64 i
        RustM.ok (i1, k)) = _
      rw [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok, reduce_64_eq, Aeneas.Std.bind_ok]
      rfl), WP.spec_ok]
  show toQuot192 ⟨[_, _, _], rfl⟩ = _
  rw [toQuot192_mk, toQuot192_mk, toQuot64_reduceLimb, toQuot64_reduceLimb,
    toQuot64_reduceLimb]
  simp only [natPoly_clmulVal, map_mul, ← toQuot64_eq]
  unfold Poly192.ofCoeffs
  rw [AdjoinRoot.of, RingHom.comp_apply, ← map_mul]
  congr 1
  simp only [map_mul]
  ring

/-- `poly_mul_192_by_64` never panics and scales by an element of `GF(2^64)`. -/
theorem poly_mul_192_by_64_toQuot (a : Std.Array Std.U64 3#usize) (k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 a k ⦃ r =>
      toQuot192 r = toQuot192 a * AdjoinRoot.of Poly192.modulus (toQuot64 k) ⦄ := by
  obtain ⟨la, hla⟩ := a
  match la, hla with
  | [a₀, a₁, a₂], _ => exact poly_mul_192_by_64_toQuot_mk a₀ a₁ a₂ k

end Plonky3Lean.Proofs.Binary
