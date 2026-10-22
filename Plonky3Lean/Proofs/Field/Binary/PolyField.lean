module

public import Plonky3Lean.Proofs.Field.Binary.Operators
public import Plonky3Lean.Proofs.Field.Binary.Statements

@[expose] public section

/-!
# The field API of `Poly64`, `Poly192` and `Ghash128`

Inversion, square roots, squaring and the operators that reduce to them.

`Poly64`'s inverse is `poly_inverse_64`, an addition chain to `x^(2^64 - 2)`.

`Poly192`'s inverse is the adjugate over the norm. Multiplication by `a = a_0 + a_1 Y + a_2 Y^2`
is a 3×3 matrix over `GF(2^64)`; the code computes the cofactors `c` along its top row and the
determinant `N = a_0 c_0 + a_2 c_1 + a_1 c_2`, so that `a c = N` (`ofVector_mul_adjugate`). It
returns `c / N` when `N ≠ 0`.

`N = 0` only for `a = 0` (`adjugate_norm_eq_zero`): otherwise `c = 0`, and for `a_2 ≠ 0` that
makes `a_1 / a_2` a root of `Y^3 + Y + 1` in `GF(2^64)`, which has none.

`Poly192`'s square root inverts the triangular squaring map with three `GF(2^64)` roots.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The adjugate -/

/-- The cofactors along the top row of the multiplication matrix of `a_0 + a_1 Y + a_2 Y^2`. -/
def adj0 (a₀ a₁ a₂ : BF64) : BF64 := (a₀ + a₂) * (a₀ + a₂) + a₁ * a₁ + a₁ * a₂
def adj1 (a₀ a₁ a₂ : BF64) : BF64 := a₁ * (a₀ + a₂) + (a₁ + a₂) * a₂
def adj2 (a₀ a₁ a₂ : BF64) : BF64 := a₁ * a₁ + (a₀ + a₂) * a₂

/-- The determinant of the multiplication matrix: the norm to `GF(2^64)`. -/
def adjNorm (a₀ a₁ a₂ : BF64) : BF64 :=
  a₀ * adj0 a₀ a₁ a₂ + a₂ * adj1 a₀ a₁ a₂ + a₁ * adj2 a₀ a₁ a₂

theorem algebraMap_ext3 (k : BF64) :
    algebraMap BF64 BF64.Ext3 k = CompPoly.Extension.Ext.ofVector #v[k, 0, 0] := by
  have h := BF64.ofVector_mul_algebraMap 1 0 0 k
  rw [one_mul, zero_mul] at h
  rw [← h, show (CompPoly.Extension.Ext.ofVector #v[(1 : BF64), 0, 0] : BF64.Ext3) = 1 from rfl,
    one_mul]

theorem ofVector_mul_adjugate (a₀ a₁ a₂ : BF64) :
    (CompPoly.Extension.Ext.ofVector #v[a₀, a₁, a₂] : BF64.Ext3) *
      CompPoly.Extension.Ext.ofVector #v[adj0 a₀ a₁ a₂, adj1 a₀ a₁ a₂, adj2 a₀ a₁ a₂] =
      algebraMap BF64 BF64.Ext3 (adjNorm a₀ a₁ a₂) := by
  rw [BF64.ofVector_mul_ofVector, algebraMap_ext3]
  refine ofVector3_congr ?_ ?_ ?_ <;> simp only [adjNorm, adj0, adj1, adj2]
  · ring
  · linear_combination (3 * a₀ * a₁ * a₂ + a₀ * a₂ ^ 2 + a₀ ^ 2 * a₁ + 2 * a₁ * a₂ ^ 2 +
      a₁ ^ 2 * a₂ + a₁ ^ 3 + a₂ ^ 3) * BF64.two_eq_zero
  · linear_combination (a₀ * a₁ ^ 2 + 2 * a₀ * a₂ ^ 2 + a₀ ^ 2 * a₂ + a₁ * a₂ ^ 2 +
      2 * a₁ ^ 2 * a₂ + a₂ ^ 3) * BF64.two_eq_zero

/-- The cofactors vanish only at zero. -/
theorem adjugate_eq_zero {a₀ a₁ a₂ : BF64} (h₀ : adj0 a₀ a₁ a₂ = 0) (h₁ : adj1 a₀ a₁ a₂ = 0)
    (h₂ : adj2 a₀ a₁ a₂ = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  unfold adj0 adj1 adj2 at *
  by_cases ha₂ : a₂ = 0
  · subst ha₂
    simp only [mul_zero, add_zero] at h₀ h₂
    have ha₁ : a₁ = 0 := mul_self_eq_zero.mp h₂
    subst ha₁
    simp only [mul_zero, add_zero] at h₀
    exact ⟨mul_self_eq_zero.mp h₀, rfl, rfl⟩
  · -- `a₁ / a₂` would be a root of `Y^3 + Y + 1`.
    exfalso
    apply BF64.ext3Poly_no_root (a₁ * a₂⁻¹)
    have hc : a₁ ^ 3 + a₁ * a₂ ^ 2 + a₂ ^ 3 = 0 := by
      linear_combination a₂ * h₁ + a₁ * h₂ - (a₁ * (a₀ + a₂) * a₂) * BF64.two_eq_zero
    simp only [BF64.ext3Poly, IsRoot, eval_add, eval_pow, eval_X, eval_one]
    have h3 : a₂ ^ 3 ≠ 0 := pow_ne_zero 3 ha₂
    calc (a₁ * a₂⁻¹) ^ 3 + a₁ * a₂⁻¹ + 1 = (a₁ ^ 3 + a₁ * a₂ ^ 2 + a₂ ^ 3) / a₂ ^ 3 := by
          field_simp
      _ = 0 := by rw [hc, zero_div]

theorem ofVector_eq_zero {a₀ a₁ a₂ : BF64}
    (h : (CompPoly.Extension.Ext.ofVector #v[a₀, a₁, a₂] : BF64.Ext3) = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have h' := congrArg CompPoly.Extension.Ext.coeffs h
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun v => v.get ⟨0, by simp⟩) h'
  · exact congrArg (fun v => v.get ⟨1, by simp⟩) h'
  · exact congrArg (fun v => v.get ⟨2, by simp⟩) h'

/-- The norm vanishes only at zero. -/
theorem adjugate_norm_eq_zero {a₀ a₁ a₂ : BF64} (h : adjNorm a₀ a₁ a₂ = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have hm := ofVector_mul_adjugate a₀ a₁ a₂
  rw [h, map_zero] at hm
  rcases mul_eq_zero.mp hm with h' | h'
  · exact ofVector_eq_zero h'
  · obtain ⟨h₀, h₁, h₂⟩ := ofVector_eq_zero h'
    exact adjugate_eq_zero h₀ h₁ h₂

/-! ## `Poly64` -/

theorem bf64_eq_zero_iff (x : Std.U64) : bf64 x = 0 ↔ x = 0#u64 := by
  constructor
  · intro h
    have h' := congrArg BF64.toBitVec h
    rw [bf64, BF64.toBitVec_ofBitVec, BF64.toBitVec_zero] at h'
    exact UScalar.eq_of_val_eq (show x.bv.toNat = 0 by rw [h']; rfl)
  · rintro rfl; rfl

theorem poly64_square_bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      bf64 r = bf64 a * bf64 a ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  exact WP.spec_bind (poly_square_64_bf64 a) fun _ h => by rw [WP.spec_ok]; exact h

theorem poly64_invert_or_zero_bf64 (a : poly64.Poly64) :
    poly64.Poly64.invert_or_zero a ⦃ r => bf64 r = (bf64 a)⁻¹ ⦄ := by
  unfold poly64.Poly64.invert_or_zero
  exact WP.spec_bind (poly_inverse_64_bf64 a) fun _ h => by rw [WP.spec_ok]; exact h

theorem poly64_is_zero_spec (a : poly64.Poly64) :
    field_defaults.Poly64.is_zero a ⦃ b => (b = true ↔ bf64 a = 0) ⦄ := by
  unfold field_defaults.Poly64.is_zero field_defaults.Poly64.raw_is_zero
    poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  rw [WP.spec_ok, decide_eq_true_iff, bf64_eq_zero_iff]

theorem poly64_try_inverse_spec (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (bf64 a = 0 → r = .None) ∧ (bf64 a ≠ 0 → ∃ c, r = .Some c ∧ bf64 c = (bf64 a)⁻¹) ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldField.try_inverse core.bool.Bool.then_some
  refine WP.spec_bind (poly64_invert_or_zero_bf64 a) fun c hc => ?_
  by_cases h : a = 0#u64
  · have h' : ¬ (a != 0#u64) = true := by simp [h]
    simp only [h', WP.spec_ok]
    exact ⟨fun _ => rfl, fun hn => absurd ((bf64_eq_zero_iff a).mpr h) hn⟩
  · have h' : (a != 0#u64) = true := by simp [h]
    simp only [h', WP.spec_ok]
    exact ⟨fun hz => absurd ((bf64_eq_zero_iff a).mp hz) h, fun _ => ⟨c, rfl, hc⟩⟩

/-! ## `Poly192` -/

theorem poly192_mul_poly64_ext (a : poly192.Poly192) (k : poly64.Poly64) :
    poly192.Poly192.Insts.CoreOpsArithMulPoly64Poly192.mul a k ⦃ r =>
      toExt3 r = toExt3 a * algebraMap BF64 BF64.Ext3 (bf64 k) ⦄ := by
  rw [array3_eq a]
  unfold poly192.Poly192.Insts.CoreOpsArithMulPoly64Poly192.mul poly192.Poly192.limbs_owned
    poly64.Poly64.to_bits poly64.Poly64.as_bits
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly_mul_192_by_64_ext _ k) fun r hr => ?_
  rw [array3_eq r]
  unfold poly192.Poly192.from_limbs poly64.Poly64.new
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok, WP.spec_ok]
  rw [← array3_eq r, hr]

theorem poly192_try_inverse_spec (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (toExt3 a = 0 → r = .None) ∧ (toExt3 a ≠ 0 → ∃ c, r = .Some c ∧ toExt3 c = (toExt3 a)⁻¹) ⦄ := by
  obtain ⟨a₀, a₁, a₂, rfl⟩ : ∃ x y z, a = Std.Array.make 3#usize [x, y, z] :=
    ⟨_, _, _, array3_eq a⟩
  unfold poly192.Poly192.Insts.P3_fieldFieldField.try_inverse
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly64_add_bf64 a₀ a₂) fun d hd => ?_
  refine WP.spec_bind (poly64_square_bf64 d) fun p hp => ?_
  refine WP.spec_bind (poly64_square_bf64 a₁) fun p1 hp1 => ?_
  refine WP.spec_bind (poly64_add_bf64 p p1) fun p2 hp2 => ?_
  refine WP.spec_bind (poly64_mul_bf64 a₁ a₂) fun p3 hp3 => ?_
  refine WP.spec_bind (poly64_add_bf64 p2 p3) fun c0 hc0 => ?_
  refine WP.spec_bind (poly64_mul_bf64 a₁ d) fun p4 hp4 => ?_
  refine WP.spec_bind (poly64_add_bf64 a₁ a₂) fun p5 hp5 => ?_
  refine WP.spec_bind (poly64_mul_bf64 p5 a₂) fun p6 hp6 => ?_
  refine WP.spec_bind (poly64_add_bf64 p4 p6) fun c1 hc1 => ?_
  refine WP.spec_bind (poly64_mul_bf64 d a₂) fun p7 hp7 => ?_
  refine WP.spec_bind (poly64_add_bf64 p1 p7) fun c2 hc2 => ?_
  refine WP.spec_bind (poly64_mul_bf64 a₀ c0) fun p8 hp8 => ?_
  refine WP.spec_bind (poly64_mul_bf64 a₂ c1) fun p9 hp9 => ?_
  refine WP.spec_bind (poly64_add_bf64 p8 p9) fun p10 hp10 => ?_
  refine WP.spec_bind (poly64_mul_bf64 a₁ c2) fun p11 hp11 => ?_
  refine WP.spec_bind (poly64_add_bf64 p10 p11) fun n hn => ?_
  refine WP.spec_bind (poly64_invert_or_zero_bf64 n) fun ni hni => ?_
  refine WP.spec_bind (poly192_mul_poly64_ext _ ni) fun cand hcand => ?_
  refine WP.spec_bind (poly64_is_zero_spec n) fun b hb => ?_
  have hC0 : bf64 c0 = adj0 (bf64 a₀) (bf64 a₁) (bf64 a₂) := by
    rw [hc0, hp2, hp, hp1, hp3, hd]; rfl
  have hC1 : bf64 c1 = adj1 (bf64 a₀) (bf64 a₁) (bf64 a₂) := by
    rw [hc1, hp4, hp6, hp5, hd]; rfl
  have hC2 : bf64 c2 = adj2 (bf64 a₀) (bf64 a₁) (bf64 a₂) := by
    rw [hc2, hp1, hp7, hd]; rfl
  have hN : bf64 n = adjNorm (bf64 a₀) (bf64 a₁) (bf64 a₂) := by
    rw [hn, hp10, hp8, hp9, hp11, hC0, hC1, hC2]; rfl
  have hadj : toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) *
      toExt3 (Std.Array.make 3#usize [c0, c1, c2]) = algebraMap BF64 BF64.Ext3 (bf64 n) := by
    rw [toExt3_make, toExt3_make, hC0, hC1, hC2, hN]
    exact ofVector_mul_adjugate _ _ _
  unfold core.bool.Bool.then_some
  by_cases hz : bf64 n = 0
  · have hb' : b = true := hb.mpr hz
    obtain ⟨h₀, h₁, h₂⟩ := adjugate_norm_eq_zero (hN ▸ hz)
    have ha : toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) = 0 := by
      rw [toExt3_make, h₀, h₁, h₂]; rfl
    simp only [hb', not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨fun _ => trivial, fun h => absurd ha h⟩
  · have hb' : b = false := by
      cases b
      · rfl
      · exact absurd (hb.mp rfl) hz
    have ha : toExt3 (Std.Array.make 3#usize [a₀, a₁, a₂]) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hadj
      exact hz ((map_eq_zero_iff _ (algebraMap BF64 BF64.Ext3).injective).mp hadj.symm)
    simp only [hb', Bool.false_eq_true, not_false_eq_true, decide_true, ↓reduceIte, WP.spec_ok]
    refine ⟨fun h => absurd h ha, fun _ => ⟨cand, rfl, ?_⟩⟩
    rw [hcand, hni]
    refine (eq_inv_of_mul_eq_one_right ?_).symm.symm
    rw [← mul_assoc, hadj, ← map_mul, mul_inv_cancel₀ hz, map_one]

/-! ## Square roots -/

theorem poly64_try_sqrt_bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ bf64 c * bf64 c = bf64 a ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldField.try_sqrt
  exact WP.spec_bind (poly_sqrt_64_bf64 a) fun c h => by rw [WP.spec_ok]; exact ⟨c, rfl, h⟩

theorem poly192_root_bf64 (x : poly64.Poly64) :
    poly192.FieldPoly192.try_sqrt.closure.Insts.CoreOpsFunctionFnTuplePoly64Poly64.call () x ⦃ r =>
      bf64 r * bf64 r = bf64 x ⦄ := by
  unfold poly192.FieldPoly192.try_sqrt.closure.Insts.CoreOpsFunctionFnTuplePoly64Poly64.call
  refine WP.spec_bind (poly64_try_sqrt_bf64 x) fun o ⟨c, ho, hc⟩ => ?_
  subst ho
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact hc

/-- Squaring is `(s_0, s_1, s_2) ↦ (s_0^2, s_2^2, s_1^2 + s_2^2)`; `try_sqrt` reads it backwards. -/
theorem poly192_try_sqrt_spec (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ toExt3 c * toExt3 c = toExt3 a ⦄ := by
  obtain ⟨b₀, b₁, b₂, rfl⟩ : ∃ x y z, a = Std.Array.make 3#usize [x, y, z] :=
    ⟨_, _, _, array3_eq a⟩
  unfold poly192.Poly192.Insts.P3_fieldFieldField.try_sqrt
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly192_root_bf64 b₀) fun s₀ h₀ => ?_
  refine WP.spec_bind (poly64_add_bf64 b₁ b₂) fun t ht => ?_
  refine WP.spec_bind (poly192_root_bf64 t) fun s₁ h₁ => ?_
  refine WP.spec_bind (poly192_root_bf64 b₁) fun s₂ h₂ => ?_
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [toExt3_make, toExt3_make, BF64.ofVector_mul_ofVector]
  refine ofVector3_congr ?_ ?_ ?_
  · rw [← h₀]; linear_combination (bf64 s₁ * bf64 s₂) * BF64.two_eq_zero
  · rw [← h₂]; linear_combination (bf64 s₀ * bf64 s₁ + bf64 s₁ * bf64 s₂) * BF64.two_eq_zero
  · linear_combination h₁ + h₂ + ht + (bf64 s₀ * bf64 s₂ + bf64 b₁) * BF64.two_eq_zero

/-! ## The rest of the API -/

theorem poly64_inverse_bf64 (a : poly64.Poly64) (ha : bf64 a ≠ 0) :
    field_defaults.Poly64.inverse a ⦃ c => bf64 c = (bf64 a)⁻¹ ⦄ := by
  unfold field_defaults.Poly64.inverse field_defaults.Poly64.raw_inverse
  refine WP.spec_bind (poly64_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact hc

theorem poly64_inverse_zero (a : poly64.Poly64) (ha : bf64 a = 0) :
    field_defaults.Poly64.inverse a = .fail .panic := by
  have h0 : a = 0#u64 := (bf64_eq_zero_iff a).mp ha
  subst h0
  unfold field_defaults.Poly64.inverse field_defaults.Poly64.raw_inverse
    poly64.Poly64.Insts.P3_fieldFieldField.try_inverse poly64.Poly64.invert_or_zero
    clmul.gf64.poly_inverse_64
  simp [poly_square_64_eq, poly_mul_64_eq, square_times_eq, core.bool.Bool.then_some,
    CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem poly64_div_bf64 (a b : poly64.Poly64) (hb : bf64 b ≠ 0) :
    poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div a b ⦃ r => bf64 r = bf64 a / bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div
  refine WP.spec_bind (poly64_inverse_bf64 b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (poly64_mul_bf64 a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem poly64_div_zero (a b : poly64.Poly64) (hb : bf64 b = 0) :
    poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div a b = .fail .panic := by
  unfold poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div
  rw [poly64_inverse_zero b hb]
  simp

theorem poly64_mul_assign_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a * bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly64_mul_bf64 a b

theorem poly64_add_assign_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a + bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly64_add_bf64 a b

theorem poly64_sub_assign_bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a - bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly64_sub_bf64 a b

theorem poly64_div_assign_bf64 (a b : poly64.Poly64) (hb : bf64 b ≠ 0) :
    poly64.Poly64.Insts.CoreOpsArithDivAssignPoly64.div_assign a b ⦃ r =>
      bf64 r = bf64 a / bf64 b ⦄ := by
  unfold poly64.Poly64.Insts.CoreOpsArithDivAssignPoly64.div_assign
  refine WP.spec_bind (poly64_inverse_bf64 b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (poly64_mul_assign_bf64 a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem poly64_eq_spec (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq a b ⦃ r => (r = true ↔ bf64 a = bf64 b) ⦄ := by
  unfold poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  have h' := congrArg BF64.toBitVec h
  rw [bf64, bf64, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec] at h'
  exact UScalar.eq_of_val_eq (show a.bv.toNat = b.bv.toNat by rw [h'])

theorem poly64_from_bool_spec (b : Bool) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r => r.val = b.toNat ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U64.Insts.CoreConvertFromBool.from]

theorem poly64_interpolation_node_spec (i : Std.Usize) :
    poly64.Poly64.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  have hnb' := System.Platform.numBits_eq
  unfold poly64.Poly64.Insts.P3_fieldFieldField.interpolation_node
  have hi : i.val < 2 ^ 64 := by
    have h := i.hBounds
    simp only [UScalarTy.numBits] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt hi

theorem poly192_square_ext (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      toExt3 r = toExt3 a * toExt3 a ⦄ := by
  rw [array3_eq a]
  unfold poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.square
    poly192.Poly192.limbs_owned poly64.Poly64.to_bits
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok]
  refine WP.spec_bind (poly_square_192_ext _) fun r hr => ?_
  rw [array3_eq r]
  unfold poly192.Poly192.from_limbs poly64.Poly64.new
  simp only [index_usize_0, index_usize_1, index_usize_2, Aeneas.Std.bind_ok, WP.spec_ok]
  rw [← array3_eq r, hr]

theorem ghash128_square_ghash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      ghash r = ghash a * ghash a ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  exact WP.spec_bind (poly_square_128_ghash a) fun _ h => by rw [WP.spec_ok]; exact h

theorem ghash128_try_sqrt_ghash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ ghash c * ghash c = ghash a ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldField.try_sqrt
  exact WP.spec_bind (poly_sqrt_128_ghash a) fun c h => by rw [WP.spec_ok]; exact ⟨c, rfl, h⟩

theorem ghash128_mul_assign_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a * ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact ghash128_mul_ghash a b

theorem ghash128_add_assign_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a + ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact ghash128_add_ghash a b

theorem ghash128_sub_assign_ghash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a - ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact ghash128_sub_ghash a b

theorem ghash128_interpolation_node_spec (i : Std.Usize) :
    ghash.Ghash128.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ := by
  have hnb' := System.Platform.numBits_eq
  unfold ghash.Ghash128.Insts.P3_fieldFieldField.interpolation_node
  have hi : i.val < 2 ^ 128 := by
    have h := i.hBounds
    simp only [UScalarTy.numBits] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq]
  exact Nat.mod_eq_of_lt hi

theorem poly192_inverse_ext (a : poly192.Poly192) (ha : toExt3 a ≠ 0) :
    field_defaults.Poly192.inverse a ⦃ c => toExt3 c = (toExt3 a)⁻¹ ⦄ := by
  unfold field_defaults.Poly192.inverse field_defaults.Poly192.raw_inverse
  refine WP.spec_bind (poly192_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact hc

theorem poly192_div_ext (a b : poly192.Poly192) (hb : toExt3 b ≠ 0) :
    poly192.Poly192.Insts.CoreOpsArithDivPoly192Poly192.div a b ⦃ r =>
      toExt3 r = toExt3 a / toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithDivPoly192Poly192.div
  refine WP.spec_bind (poly192_inverse_ext b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (poly192_mul_ext a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem poly192_mul_assign_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a * toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithMulAssign.mul_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly192_mul_ext a b

theorem poly192_add_assign_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a + toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithAddAssign.add_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly192_add_ext a b

theorem poly192_sub_assign_ext (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a - toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithSubAssign.sub_assign
  simp only [CoreModels.core.convert.Into.Blanket.into, CoreModels.core.convert.From.Blanket.from,
    Aeneas.Std.bind_ok]
  exact poly192_sub_ext a b

theorem poly192_div_assign_ext (a b : poly192.Poly192) (hb : toExt3 b ≠ 0) :
    poly192.Poly192.Insts.CoreOpsArithDivAssignPoly192.div_assign a b ⦃ r =>
      toExt3 r = toExt3 a / toExt3 b ⦄ := by
  unfold poly192.Poly192.Insts.CoreOpsArithDivAssignPoly192.div_assign
  refine WP.spec_bind (poly192_inverse_ext b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (poly192_mul_assign_ext a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

end Plonky3Lean.Proofs.Binary
