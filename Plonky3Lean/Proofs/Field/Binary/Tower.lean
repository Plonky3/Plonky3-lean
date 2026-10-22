module

public import Plonky3Lean.Proofs.Field.Binary.Tables
public import ToCompPoly.Fields.Binary.Tower.NatMul

@[expose] public section

/-!
# The binary tower's arithmetic

p3-binary-field stores an element of `GF(2^(2^k))` in the low `2^k` bits of an unsigned integer.

Each level splits into two halves of the level below, multiplies by Karatsuba, and multiplies by
the level below's generator with `mul_alpha`.

On values below `2^(2^k)` (canonical ones), the extracted functions compute exactly the steps of
`towerMul k`, CompPoly's tower product on natural numbers (`toNat_concrete_mul`).
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## `usize` literals -/

/-- A `usize` holds every value below `2^32`. -/
theorem mod_numBits_of_lt {n : ℕ} (h : n < 2 ^ 32) : n % 2 ^ System.Platform.numBits = n := by
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

/-! ## `GF(2)` -/

@[step]
theorem gf2_raw_from_repr_spec (r : Std.U8) :
    gf2.Gf2.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 0 ⦄ := by
  unfold gf2.Gf2.raw_from_repr
  simp only [Plonky3Lean.Lib.lift_eq, Aeneas.Std.bind_ok, WP.spec_ok]
  rw [UScalar.val_and, show (1#u8).val = 1 from rfl, Nat.and_one_is_mod]; rfl

@[step]
theorem gf2_from_repr_spec (r : Std.U8) : gf2.Gf2.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 0 ⦄ := by
  unfold gf2.Gf2.from_repr
  exact gf2_raw_from_repr_spec r

@[step]
theorem gf2_to_repr_spec (x : gf2.Gf2) (hx : x.val < 2 ^ 2 ^ 0) : gf2.Gf2.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold gf2.Gf2.to_repr gf2.Gf2.raw_to_repr
  rw [WP.spec_ok]
  rcases (by norm_num at hx; omega : x.val = 0 ∨ x.val = 1) with h | h
  · have : x ≠ 1#u8 := fun e => by rw [e] at h; exact absurd h (by decide)
    simp [this, h]
  · have : x = 1#u8 := UScalar.eq_of_val_eq (by rw [h]; rfl)
    simp [this]

@[step]
theorem gf2_add_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithAddGf2Gf2.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithAddGf2Gf2.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem gf2_sub_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithSubGf2Gf2.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithSubGf2Gf2.sub; exact gf2_add_spec a b

@[step]
theorem gf2_neg_spec (a : gf2.Gf2) : gf2.Gf2.Insts.CoreOpsArithNegGf2.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithNegGf2.neg; simp only [WP.spec_ok]

@[step]
theorem gf2_mul_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul a b ⦃ y => y.val = towerMul 0 a.val b.val ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_and, towerMul]

@[step]
theorem gf2_reference_mul_spec (a b : gf2.Gf2) :
    gf2.Gf2.reference_mul a b ⦃ y => y.val = towerMul 0 a.val b.val ⦄ := by
  unfold gf2.Gf2.reference_mul
  exact gf2_mul_spec a b

@[step]
theorem gf2_raw_mul_alpha_spec (x : gf2.Gf2) (hx : x.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.raw_mul_alpha x ⦃ y => y.val = towerMul 0 x.val (zNat 0) ⦄ := by
  unfold gf2.Gf2.raw_mul_alpha
  rw [WP.spec_ok, show zNat 0 = 1 from rfl, towerMul_one 0 hx]

@[step]
theorem gf2_mul_alpha_spec (x : gf2.Gf2) (hx : x.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.mul_alpha x ⦃ y => y.val = towerMul 0 x.val (zNat 0) ⦄ := by
  unfold gf2.Gf2.mul_alpha
  exact gf2_raw_mul_alpha_spec x hx

/-- The constants of a level: `step*`, then the arithmetic of `BITS`, `MAX` and the shifts. -/
macro "tower_const" : tactic => `(tactic| (
  step*
  all_goals (
    simp only [*, UScalar.cast_val_eq, UScalarTy.Usize_numBits_eq, CoreModels.core.num.U8.BITS,
      CoreModels.core.num.U16.BITS, CoreModels.core.num.U32.BITS, CoreModels.core.num.U64.BITS,
      CoreModels.core.num.U128.BITS] at *
    rw [mod_numBits_of_lt (by norm_num)] at *
    simp_all [U8.rMax, U16.rMax, U32.rMax, U64.rMax, U128.rMax])))

/-! ## The table product -/

/-- `tables::mul` computes `towerMul 3`. -/
@[step]
theorem tables_mul_val_spec (a b : Std.U8) :
    tables.mul a b ⦃ r => r.val = towerMul 3 a.val b.val ⦄ := by
  refine WP.spec_mono (tables_mul_spec a b) fun r h => ?_
  have h' := congrArg ConcreteBTField.toNat h
  rw [show tower8 a * tower8 b = concrete_mul (tower8 a) (tower8 b) from rfl,
    toNat_concrete_mul, tower8_eq, tower8_eq, tower8_eq, ConcreteBTField.toNat_fromNat,
    ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat] at h'
  have ha := a.hBounds; have hb := b.hBounds; have hr := r.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha hb hr
  rwa [Nat.mod_eq_of_lt (by simpa using hr), Nat.mod_eq_of_lt (by simpa using ha),
    Nat.mod_eq_of_lt (by simpa using hb)] at h'

/-! ## Splitting and joining halves -/

/-- Joining two halves that fit: the casts and the shift's truncation change nothing, and the
halves do not overlap. -/
theorem join_val {a0 a1 h R : ℕ} (h0 : a0 < 2 ^ h) (h1 : a1 < 2 ^ h) (hR : h + h ≤ R) :
    a0 % 2 ^ R ||| ((a1 % 2 ^ R) <<< h) % 2 ^ R = a1 <<< h ||| a0 := by
  have hR' : 2 ^ h ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : a1 <<< h < 2 ^ R := by
    rw [Nat.shiftLeft_eq]
    calc a1 * 2 ^ h < 2 ^ h * 2 ^ h := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (h + h) := by rw [pow_add]
      _ ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) hR
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le h0 hR'), Nat.mod_eq_of_lt (lt_of_lt_of_le h1 hR'),
    Nat.mod_eq_of_lt hs, Nat.lor_comm]

/-- `join_val` when the halves already have the level's width. -/
theorem join_val' {a0 a1 h R : ℕ} (h0 : a0 < 2 ^ h) (h1 : a1 < 2 ^ h) (hR : h + h ≤ R) :
    a0 ||| (a1 <<< h) % 2 ^ R = a1 <<< h ||| a0 := by
  have hR' : 2 ^ h ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := join_val h0 h1 hR
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le h0 hR'), Nat.mod_eq_of_lt (lt_of_lt_of_le h1 hR')] at this

/-- The sizes of the integer types, as powers of two. -/
theorem size_pow : U8.size = 2 ^ 8 ∧ U16.size = 2 ^ 16 ∧ U32.size = 2 ^ 32 ∧ U64.size = 2 ^ 64 ∧
    U128.size = 2 ^ 128 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [U8.size_def, U16.size_def, U32.size_def, U64.size_def, U128.size_def, U8.numBits_def,
      U16.numBits_def, U32.numBits_def, U64.numBits_def, U128.numBits_def]

macro "tower_join_close" : tactic => `(tactic| all_goals (
  simp only [*, UScalar.val_or, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq,
    UScalarTy.U32_numBits_eq, UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, size_pow.1,
    size_pow.2.1, size_pow.2.2.1, size_pow.2.2.2.1, size_pow.2.2.2.2]
  first
    | exact join_val (by assumption) (by assumption) (by norm_num)
    | exact join_val' (by assumption) (by assumption) (by norm_num)))

/-! ## Karatsuba -/

/-- The value the Karatsuba step assembles, in the order the Rust computes it, is the tower
product. -/
theorem karatsuba_eq (j a b a0 a1 b0 b1 : ℕ) (ha0 : a0 = (a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j)
    (ha1 : a1 = (a >>> 2 ^ j) % 2 ^ 2 ^ j) (hb0 : b0 = (b &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j)
    (hb1 : b1 = (b >>> 2 ^ j) % 2 ^ 2 ^ j) :
    (((towerMul j (a0 ^^^ a1) (b0 ^^^ b1) ^^^ towerMul j a0 b0) ^^^ towerMul j a1 b1) ^^^
        towerMul j (towerMul j a1 b1) (zNat j)) <<< 2 ^ j |||
      (towerMul j a0 b0 ^^^ towerMul j a1 b1) =
    towerMul (j + 1) a b := by
  subst ha0 ha1 hb0 hb1
  rw [towerMul]
  ac_rfl

/-- Intermediate values of a level's arithmetic fit in the level below. -/
macro "tower_bound" : tactic => `(tactic| (
  simp only [*]
  repeat (first
    | exact zNat_lt _
    | exact Nat.mod_lt _ (by positivity)
    | assumption
    | apply Nat.xor_lt_two_pow
    | apply towerMul_lt)))

macro "tower_alpha_close" : tactic => `(tactic| all_goals (first
  | (simp only [*]; exact (towerMul_zNat_succ _).symm)
  | tower_bound))

macro "tower_mul_close" : tactic => `(tactic| all_goals (first
  | (simp only [*]; exact karatsuba_eq _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | tower_bound))

/-! ## `GF(2^2)` -/

@[step]
theorem bf2_MASK : tower.BinaryField2.MASK ⦃ m => m.val = 2 ^ 2 ^ 1 - 1 ⦄ := by
  unfold tower.BinaryField2.MASK; tower_const

@[step]
theorem bf2_HALF_BITS : tower.BinaryField2.HALF_BITS ⦃ m => m.val = 2 ^ 0 ⦄ := by
  unfold tower.BinaryField2.HALF_BITS; step*

@[step]
theorem bf2_HALF_MASK : tower.BinaryField2.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 0 - 1 ⦄ := by
  unfold tower.BinaryField2.HALF_MASK tower.BinaryField2.MASK tower.BinaryField2.HALF_BITS; tower_const

@[step]
theorem bf2_raw_from_repr_spec (r : Std.U8) : tower.BinaryField2.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 1 ⦄ := by
  unfold tower.BinaryField2.raw_from_repr
  step*
  all_goals simp only [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]

@[step]
theorem bf2_from_repr_spec (r : Std.U8) : tower.BinaryField2.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 1 ⦄ := by
  unfold tower.BinaryField2.from_repr; exact bf2_raw_from_repr_spec r

@[step]
theorem bf2_raw_to_repr_spec (x : tower.BinaryField2) : tower.BinaryField2.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField2.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf2_to_repr_spec (x : tower.BinaryField2) : tower.BinaryField2.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField2.to_repr; exact bf2_raw_to_repr_spec x

@[step]
theorem bf2_add_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithAddBinaryField2BinaryField2.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithAddBinaryField2BinaryField2.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf2_sub_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithSubBinaryField2BinaryField2.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithSubBinaryField2BinaryField2.sub; exact bf2_add_spec a b

@[step]
theorem bf2_neg_spec (a : tower.BinaryField2) : tower.BinaryField2.Insts.CoreOpsArithNegBinaryField2.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithNegBinaryField2.neg; simp only [WP.spec_ok]

@[step]
theorem bf2_split_spec (x : tower.BinaryField2) :
    tower.BinaryField2.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 0 - 1)) % 2 ^ 2 ^ 0 ∧
      q.2.val = (x.val >>> 2 ^ 0) % 2 ^ 2 ^ 0 ⦄ := by
  unfold tower.BinaryField2.split
  step*

@[step]
theorem bf2_join_spec (a0 a1 : gf2.Gf2) (h0 : a0.val < 2 ^ 2 ^ 0) (h1 : a1.val < 2 ^ 2 ^ 0) :
    tower.BinaryField2.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 0 ||| a0.val ⦄ := by
  unfold tower.BinaryField2.join
  step*
  tower_join_close

@[step]
theorem bf2_raw_mul_alpha_spec (x : tower.BinaryField2) :
    tower.BinaryField2.raw_mul_alpha x ⦃ y => y.val = towerMul (0 + 1) x.val (zNat (0 + 1)) ⦄ := by
  unfold tower.BinaryField2.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf2_mul_alpha_spec (x : tower.BinaryField2) :
    tower.BinaryField2.mul_alpha x ⦃ y => y.val = towerMul (0 + 1) x.val (zNat (0 + 1)) ⦄ := by
  unfold tower.BinaryField2.mul_alpha; exact bf2_raw_mul_alpha_spec x

@[step]
theorem bf2_core_mul_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.reference_mul a b ⦃ y => y.val = towerMul (0 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField2.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf2_mul_spec (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithMulBinaryField2BinaryField2.mul a b ⦃ y => y.val = towerMul (0 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField2.Insts.CoreOpsArithMulBinaryField2BinaryField2.mul
  step*

/-! ## `GF(2^4)` -/

@[step]
theorem bf4_MASK : tower.BinaryField4.MASK ⦃ m => m.val = 2 ^ 2 ^ 2 - 1 ⦄ := by
  unfold tower.BinaryField4.MASK; tower_const

@[step]
theorem bf4_HALF_BITS : tower.BinaryField4.HALF_BITS ⦃ m => m.val = 2 ^ 1 ⦄ := by
  unfold tower.BinaryField4.HALF_BITS; step*

@[step]
theorem bf4_HALF_MASK : tower.BinaryField4.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 1 - 1 ⦄ := by
  unfold tower.BinaryField4.HALF_MASK tower.BinaryField4.MASK tower.BinaryField4.HALF_BITS; tower_const

@[step]
theorem bf4_raw_from_repr_spec (r : Std.U8) : tower.BinaryField4.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 2 ⦄ := by
  unfold tower.BinaryField4.raw_from_repr
  step*
  all_goals simp only [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]

@[step]
theorem bf4_from_repr_spec (r : Std.U8) : tower.BinaryField4.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 2 ⦄ := by
  unfold tower.BinaryField4.from_repr; exact bf4_raw_from_repr_spec r

@[step]
theorem bf4_raw_to_repr_spec (x : tower.BinaryField4) : tower.BinaryField4.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField4.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf4_to_repr_spec (x : tower.BinaryField4) : tower.BinaryField4.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField4.to_repr; exact bf4_raw_to_repr_spec x

@[step]
theorem bf4_add_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithAddBinaryField4BinaryField4.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithAddBinaryField4BinaryField4.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf4_sub_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithSubBinaryField4BinaryField4.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithSubBinaryField4BinaryField4.sub; exact bf4_add_spec a b

@[step]
theorem bf4_neg_spec (a : tower.BinaryField4) : tower.BinaryField4.Insts.CoreOpsArithNegBinaryField4.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithNegBinaryField4.neg; simp only [WP.spec_ok]

@[step]
theorem bf4_split_spec (x : tower.BinaryField4) :
    tower.BinaryField4.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 1 - 1)) % 2 ^ 2 ^ 1 ∧
      q.2.val = (x.val >>> 2 ^ 1) % 2 ^ 2 ^ 1 ⦄ := by
  unfold tower.BinaryField4.split
  step*

@[step]
theorem bf4_join_spec (a0 a1 : tower.BinaryField2) (h0 : a0.val < 2 ^ 2 ^ 1) (h1 : a1.val < 2 ^ 2 ^ 1) :
    tower.BinaryField4.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 1 ||| a0.val ⦄ := by
  unfold tower.BinaryField4.join
  step*
  tower_join_close

@[step]
theorem bf4_raw_mul_alpha_spec (x : tower.BinaryField4) :
    tower.BinaryField4.raw_mul_alpha x ⦃ y => y.val = towerMul (1 + 1) x.val (zNat (1 + 1)) ⦄ := by
  unfold tower.BinaryField4.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf4_core_mul_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.reference_mul a b ⦃ y => y.val = towerMul (1 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField4.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf4_mul_spec (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithMulBinaryField4BinaryField4.mul a b ⦃ y => y.val = towerMul (1 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField4.Insts.CoreOpsArithMulBinaryField4BinaryField4.mul
  step*

/-! ## `GF(2^8)` -/

@[step]
theorem bf8_MASK : tower.BinaryField8.MASK ⦃ m => m.val = 2 ^ 2 ^ 3 - 1 ⦄ := by
  unfold tower.BinaryField8.MASK; tower_const

@[step]
theorem bf8_HALF_BITS : tower.BinaryField8.HALF_BITS ⦃ m => m.val = 2 ^ 2 ⦄ := by
  unfold tower.BinaryField8.HALF_BITS; step*

@[step]
theorem bf8_HALF_MASK : tower.BinaryField8.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 2 - 1 ⦄ := by
  unfold tower.BinaryField8.HALF_MASK tower.BinaryField8.MASK tower.BinaryField8.HALF_BITS; tower_const

@[step]
theorem bf8_raw_from_repr_spec (r : Std.U8) : tower.BinaryField8.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField8.raw_from_repr
  step*

@[step]
theorem bf8_from_repr_spec (r : Std.U8) : tower.BinaryField8.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField8.from_repr; exact bf8_raw_from_repr_spec r

@[step]
theorem bf8_raw_to_repr_spec (x : tower.BinaryField8) : tower.BinaryField8.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField8.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf8_to_repr_spec (x : tower.BinaryField8) : tower.BinaryField8.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField8.to_repr; exact bf8_raw_to_repr_spec x

@[step]
theorem bf8_add_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithAddBinaryField8BinaryField8.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithAddBinaryField8BinaryField8.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf8_sub_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithSubBinaryField8BinaryField8.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithSubBinaryField8BinaryField8.sub; exact bf8_add_spec a b

@[step]
theorem bf8_neg_spec (a : tower.BinaryField8) : tower.BinaryField8.Insts.CoreOpsArithNegBinaryField8.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithNegBinaryField8.neg; simp only [WP.spec_ok]

@[step]
theorem bf8_split_spec (x : tower.BinaryField8) :
    tower.BinaryField8.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 2 - 1)) % 2 ^ 2 ^ 2 ∧
      q.2.val = (x.val >>> 2 ^ 2) % 2 ^ 2 ^ 2 ⦄ := by
  unfold tower.BinaryField8.split
  step*

@[step]
theorem bf8_join_spec (a0 a1 : tower.BinaryField4) (h0 : a0.val < 2 ^ 2 ^ 2) (h1 : a1.val < 2 ^ 2 ^ 2) :
    tower.BinaryField8.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 2 ||| a0.val ⦄ := by
  unfold tower.BinaryField8.join
  step*
  tower_join_close

@[step]
theorem bf8_raw_mul_alpha_spec (x : tower.BinaryField8) :
    tower.BinaryField8.raw_mul_alpha x ⦃ y => y.val = towerMul (2 + 1) x.val (zNat (2 + 1)) ⦄ := by
  unfold tower.BinaryField8.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf8_mul_alpha_spec (x : tower.BinaryField8) :
    tower.BinaryField8.mul_alpha x ⦃ y => y.val = towerMul (2 + 1) x.val (zNat (2 + 1)) ⦄ := by
  unfold tower.BinaryField8.mul_alpha; exact bf8_raw_mul_alpha_spec x

@[step]
theorem bf8_core_mul_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.table_mul a b ⦃ y => y.val = towerMul (2 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField8.table_mul
  step*

@[step]
theorem bf8_mul_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField8BinaryField8.mul a b ⦃ y => y.val = towerMul (2 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulBinaryField8BinaryField8.mul
  step*

/-! ## `GF(2^16)` -/

@[step]
theorem bf16_MASK : tower.BinaryField16.MASK ⦃ m => m.val = 2 ^ 2 ^ 4 - 1 ⦄ := by
  unfold tower.BinaryField16.MASK; tower_const

@[step]
theorem bf16_HALF_BITS : tower.BinaryField16.HALF_BITS ⦃ m => m.val = 2 ^ 3 ⦄ := by
  unfold tower.BinaryField16.HALF_BITS; step*

@[step]
theorem bf16_HALF_MASK : tower.BinaryField16.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 3 - 1 ⦄ := by
  unfold tower.BinaryField16.HALF_MASK tower.BinaryField16.MASK tower.BinaryField16.HALF_BITS; tower_const

@[step]
theorem bf16_raw_from_repr_spec (r : Std.U16) : tower.BinaryField16.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField16.raw_from_repr
  step*

@[step]
theorem bf16_from_repr_spec (r : Std.U16) : tower.BinaryField16.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField16.from_repr; exact bf16_raw_from_repr_spec r

@[step]
theorem bf16_raw_to_repr_spec (x : tower.BinaryField16) : tower.BinaryField16.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField16.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf16_to_repr_spec (x : tower.BinaryField16) : tower.BinaryField16.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField16.to_repr; exact bf16_raw_to_repr_spec x

@[step]
theorem bf16_add_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithAddBinaryField16BinaryField16.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithAddBinaryField16BinaryField16.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf16_sub_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithSubBinaryField16BinaryField16.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithSubBinaryField16BinaryField16.sub; exact bf16_add_spec a b

@[step]
theorem bf16_neg_spec (a : tower.BinaryField16) : tower.BinaryField16.Insts.CoreOpsArithNegBinaryField16.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithNegBinaryField16.neg; simp only [WP.spec_ok]

@[step]
theorem bf16_split_spec (x : tower.BinaryField16) :
    tower.BinaryField16.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 3 - 1)) % 2 ^ 2 ^ 3 ∧
      q.2.val = (x.val >>> 2 ^ 3) % 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField16.split
  step*

@[step]
theorem bf16_join_spec (a0 a1 : tower.BinaryField8) (h0 : a0.val < 2 ^ 2 ^ 3) (h1 : a1.val < 2 ^ 2 ^ 3) :
    tower.BinaryField16.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 3 ||| a0.val ⦄ := by
  unfold tower.BinaryField16.join
  step*
  tower_join_close

@[step]
theorem bf16_raw_mul_alpha_spec (x : tower.BinaryField16) :
    tower.BinaryField16.raw_mul_alpha x ⦃ y => y.val = towerMul (3 + 1) x.val (zNat (3 + 1)) ⦄ := by
  unfold tower.BinaryField16.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf16_mul_alpha_spec (x : tower.BinaryField16) :
    tower.BinaryField16.mul_alpha x ⦃ y => y.val = towerMul (3 + 1) x.val (zNat (3 + 1)) ⦄ := by
  unfold tower.BinaryField16.mul_alpha; exact bf16_raw_mul_alpha_spec x

@[step]
theorem bf16_core_mul_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.karatsuba_mul a b ⦃ y => y.val = towerMul (3 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField16.karatsuba_mul
  step*
  tower_mul_close

@[step]
theorem bf16_mul_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul a b ⦃ y => y.val = towerMul (3 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul
  step*

/-! ## `GF(2^32)` -/

@[step]
theorem bf32_MASK : tower.BinaryField32.MASK ⦃ m => m.val = 2 ^ 2 ^ 5 - 1 ⦄ := by
  unfold tower.BinaryField32.MASK; tower_const

@[step]
theorem bf32_HALF_BITS : tower.BinaryField32.HALF_BITS ⦃ m => m.val = 2 ^ 4 ⦄ := by
  unfold tower.BinaryField32.HALF_BITS; step*

@[step]
theorem bf32_HALF_MASK : tower.BinaryField32.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 4 - 1 ⦄ := by
  unfold tower.BinaryField32.HALF_MASK tower.BinaryField32.MASK tower.BinaryField32.HALF_BITS; tower_const

@[step]
theorem bf32_raw_from_repr_spec (r : Std.U32) : tower.BinaryField32.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 5 ⦄ := by
  unfold tower.BinaryField32.raw_from_repr
  step*

@[step]
theorem bf32_from_repr_spec (r : Std.U32) : tower.BinaryField32.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 5 ⦄ := by
  unfold tower.BinaryField32.from_repr; exact bf32_raw_from_repr_spec r

@[step]
theorem bf32_raw_to_repr_spec (x : tower.BinaryField32) : tower.BinaryField32.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField32.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf32_to_repr_spec (x : tower.BinaryField32) : tower.BinaryField32.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField32.to_repr; exact bf32_raw_to_repr_spec x

@[step]
theorem bf32_add_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithAddBinaryField32BinaryField32.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithAddBinaryField32BinaryField32.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf32_sub_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithSubBinaryField32BinaryField32.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithSubBinaryField32BinaryField32.sub; exact bf32_add_spec a b

@[step]
theorem bf32_neg_spec (a : tower.BinaryField32) : tower.BinaryField32.Insts.CoreOpsArithNegBinaryField32.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithNegBinaryField32.neg; simp only [WP.spec_ok]

@[step]
theorem bf32_split_spec (x : tower.BinaryField32) :
    tower.BinaryField32.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 4 - 1)) % 2 ^ 2 ^ 4 ∧
      q.2.val = (x.val >>> 2 ^ 4) % 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField32.split
  step*

@[step]
theorem bf32_join_spec (a0 a1 : tower.BinaryField16) (h0 : a0.val < 2 ^ 2 ^ 4) (h1 : a1.val < 2 ^ 2 ^ 4) :
    tower.BinaryField32.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 4 ||| a0.val ⦄ := by
  unfold tower.BinaryField32.join
  step*
  tower_join_close

@[step]
theorem bf32_raw_mul_alpha_spec (x : tower.BinaryField32) :
    tower.BinaryField32.raw_mul_alpha x ⦃ y => y.val = towerMul (4 + 1) x.val (zNat (4 + 1)) ⦄ := by
  unfold tower.BinaryField32.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf32_mul_alpha_spec (x : tower.BinaryField32) :
    tower.BinaryField32.mul_alpha x ⦃ y => y.val = towerMul (4 + 1) x.val (zNat (4 + 1)) ⦄ := by
  unfold tower.BinaryField32.mul_alpha; exact bf32_raw_mul_alpha_spec x

@[step]
theorem bf32_core_mul_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.karatsuba_mul a b ⦃ y => y.val = towerMul (4 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField32.karatsuba_mul
  step*
  tower_mul_close

@[step]
theorem bf32_mul_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ y => y.val = towerMul (4 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul
  step*

/-! ## `GF(2^64)` -/

@[step]
theorem bf64_MASK : tower.BinaryField64.MASK ⦃ m => m.val = 2 ^ 2 ^ 6 - 1 ⦄ := by
  unfold tower.BinaryField64.MASK; tower_const

@[step]
theorem bf64_HALF_BITS : tower.BinaryField64.HALF_BITS ⦃ m => m.val = 2 ^ 5 ⦄ := by
  unfold tower.BinaryField64.HALF_BITS; step*

@[step]
theorem bf64_HALF_MASK : tower.BinaryField64.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 5 - 1 ⦄ := by
  unfold tower.BinaryField64.HALF_MASK tower.BinaryField64.MASK tower.BinaryField64.HALF_BITS; tower_const

@[step]
theorem bf64_raw_from_repr_spec (r : Std.U64) : tower.BinaryField64.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 6 ⦄ := by
  unfold tower.BinaryField64.raw_from_repr
  step*

@[step]
theorem bf64_from_repr_spec (r : Std.U64) : tower.BinaryField64.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 6 ⦄ := by
  unfold tower.BinaryField64.from_repr; exact bf64_raw_from_repr_spec r

@[step]
theorem bf64_raw_to_repr_spec (x : tower.BinaryField64) : tower.BinaryField64.raw_to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField64.raw_to_repr; simp only [WP.spec_ok]

@[step]
theorem bf64_to_repr_spec (x : tower.BinaryField64) : tower.BinaryField64.to_repr x ⦃ y => y.val = x.val ⦄ := by
  unfold tower.BinaryField64.to_repr; exact bf64_raw_to_repr_spec x

@[step]
theorem bf64_add_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithAddBinaryField64BinaryField64.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithAddBinaryField64BinaryField64.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf64_sub_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithSubBinaryField64BinaryField64.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithSubBinaryField64BinaryField64.sub; exact bf64_add_spec a b

@[step]
theorem bf64_neg_spec (a : tower.BinaryField64) : tower.BinaryField64.Insts.CoreOpsArithNegBinaryField64.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithNegBinaryField64.neg; simp only [WP.spec_ok]

@[step]
theorem bf64_split_spec (x : tower.BinaryField64) :
    tower.BinaryField64.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 5 - 1)) % 2 ^ 2 ^ 5 ∧
      q.2.val = (x.val >>> 2 ^ 5) % 2 ^ 2 ^ 5 ⦄ := by
  unfold tower.BinaryField64.split
  step*

@[step]
theorem bf64_join_spec (a0 a1 : tower.BinaryField32) (h0 : a0.val < 2 ^ 2 ^ 5) (h1 : a1.val < 2 ^ 2 ^ 5) :
    tower.BinaryField64.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 5 ||| a0.val ⦄ := by
  unfold tower.BinaryField64.join
  step*
  tower_join_close

@[step]
theorem bf64_raw_mul_alpha_spec (x : tower.BinaryField64) :
    tower.BinaryField64.raw_mul_alpha x ⦃ y => y.val = towerMul (5 + 1) x.val (zNat (5 + 1)) ⦄ := by
  unfold tower.BinaryField64.raw_mul_alpha
  step*
  tower_alpha_close

@[step]
theorem bf64_mul_alpha_spec (x : tower.BinaryField64) :
    tower.BinaryField64.mul_alpha x ⦃ y => y.val = towerMul (5 + 1) x.val (zNat (5 + 1)) ⦄ := by
  unfold tower.BinaryField64.mul_alpha; exact bf64_raw_mul_alpha_spec x

@[step]
theorem bf64_core_mul_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.karatsuba_mul a b ⦃ y => y.val = towerMul (5 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField64.karatsuba_mul
  step*
  tower_mul_close

@[step]
theorem bf64_dispatched_mul_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.dispatched_mul a b ⦃ y => y.val = towerMul (5 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField64.dispatched_mul
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  exact bf64_core_mul_spec a b

@[step]
theorem bf64_mul_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ y => y.val = towerMul (5 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul
  step*

/-! ## `GF(2^128)` -/

@[step]
theorem bf128_MASK : tower.BinaryField128.MASK ⦃ m => m.val = 2 ^ 2 ^ 7 - 1 ⦄ := by
  unfold tower.BinaryField128.MASK; tower_const

@[step]
theorem bf128_HALF_BITS : tower.BinaryField128.HALF_BITS ⦃ m => m.val = 2 ^ 6 ⦄ := by
  unfold tower.BinaryField128.HALF_BITS; step*

@[step]
theorem bf128_HALF_MASK : tower.BinaryField128.HALF_MASK ⦃ m => m.val = 2 ^ 2 ^ 6 - 1 ⦄ := by
  unfold tower.BinaryField128.HALF_MASK tower.BinaryField128.MASK tower.BinaryField128.HALF_BITS; tower_const

@[step]
theorem bf128_add_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithAddBinaryField128BinaryField128.add a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithAddBinaryField128BinaryField128.add
  simp only [lift_eq, Aeneas.Std.bind_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem bf128_sub_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithSubBinaryField128BinaryField128.sub a b ⦃ y => y.val = a.val ^^^ b.val ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithSubBinaryField128BinaryField128.sub; exact bf128_add_spec a b

@[step]
theorem bf128_neg_spec (a : tower.BinaryField128) : tower.BinaryField128.Insts.CoreOpsArithNegBinaryField128.neg a ⦃ y => y.val = a.val ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithNegBinaryField128.neg; simp only [WP.spec_ok]

@[step]
theorem bf128_split_spec (x : tower.BinaryField128) :
    tower.BinaryField128.split x ⦃ q => q.1.val = (x.val &&& (2 ^ 2 ^ 6 - 1)) % 2 ^ 2 ^ 6 ∧
      q.2.val = (x.val >>> 2 ^ 6) % 2 ^ 2 ^ 6 ⦄ := by
  unfold tower.BinaryField128.split
  step*

@[step]
theorem bf128_join_spec (a0 a1 : tower.BinaryField64) (h0 : a0.val < 2 ^ 2 ^ 6) (h1 : a1.val < 2 ^ 2 ^ 6) :
    tower.BinaryField128.join a0 a1 ⦃ y => y.val = a1.val <<< 2 ^ 6 ||| a0.val ⦄ := by
  unfold tower.BinaryField128.join
  step*
  tower_join_close

@[step]
theorem bf128_core_mul_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.karatsuba_mul a b ⦃ y => y.val = towerMul (6 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField128.karatsuba_mul
  step*
  tower_mul_close

@[step]
theorem bf128_dispatched_mul_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.dispatched_mul a b ⦃ y => y.val = towerMul (6 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField128.dispatched_mul
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  exact bf128_core_mul_spec a b

@[step]
theorem bf128_mul_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ y => y.val = towerMul (6 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField128.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul
  step*


end Plonky3Lean.Proofs.Binary
