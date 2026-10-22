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
open Plonky3Lean.Lib

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
  simp only [Plonky3Lean.Lib.lift_eq, bind_tc_ok, WP.spec_ok]
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
  simp only [lift_eq, bind_tc_ok, WP.spec_ok, UScalar.val_xor]

@[step]
theorem gf2_mul_spec (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul a b ⦃ y => y.val = towerMul 0 a.val b.val ⦄ := by
  unfold gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul
  simp only [lift_eq, bind_tc_ok, WP.spec_ok, UScalar.val_and, towerMul]

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

macro "tower_split_close" : tactic => `(tactic| all_goals (
  simp only [*, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq,
    UScalarTy.U32_numBits_eq, UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, UScalar.val_and]
  omega))

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
  simp only
  rw [Nat.xor_comm ((a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j),
    Nat.xor_comm ((b &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j), Nat.xor_assoc _ (towerMul j _ _)]

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

end Plonky3Lean.Proofs.Binary
