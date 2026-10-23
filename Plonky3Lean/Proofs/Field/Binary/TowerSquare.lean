module

public import Plonky3Lean.Proofs.Field.Binary.LinearTable

@[expose] public section

/-!
# Squaring at every level of the tower

`square` takes a different route at each level:

- `GF(2)` returns its argument;
- `GF(2^2)` and `GF(2^4)` square the two halves at the level below (`reference_square`);
- `GF(2^8)` looks the square up in `tables`;
- `GF(2^16)`, `GF(2^64)` and `GF(2^128)` apply `linear.rs`'s byte tables;
- `GF(2^32)` squares its halves at `GF(2^16)` with `reference_square` (`byte_square`).

Every route computes `towerMul k a a`, CompPoly's square at level `k`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The square at level `j + 1`, from the squares of its halves:
`(a0 + a1 X)^2 = (a0^2 + a1^2) + Z (a1^2) X`. It holds for any `a`: the halves are masked. -/
theorem towerMul_succ_self (j a : ℕ) :
    towerMul (j + 1) a a =
      towerMul j (towerMul j ((a >>> 2 ^ j) % 2 ^ 2 ^ j) ((a >>> 2 ^ j) % 2 ^ 2 ^ j)) (zNat j)
          <<< 2 ^ j |||
        (towerMul j ((a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j) ((a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j) ^^^
          towerMul j ((a >>> 2 ^ j) % 2 ^ 2 ^ j) ((a >>> 2 ^ j) % 2 ^ 2 ^ j)) := by
  have h1 : (a >>> 2 ^ j) % 2 ^ 2 ^ j < 2 ^ 2 ^ j := Nat.mod_lt _ (by positivity)
  have h0 : (a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j < 2 ^ 2 ^ j := Nat.mod_lt _ (by positivity)
  rw [towerMul, towerMul_sq_xor j h1 h0]
  congr 2
  generalize towerMul j ((a >>> 2 ^ j) % 2 ^ 2 ^ j) ((a >>> 2 ^ j) % 2 ^ 2 ^ j) = s1
  generalize towerMul j ((a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j)
    ((a &&& (2 ^ 2 ^ j - 1)) % 2 ^ 2 ^ j) = s0
  rw [Nat.xor_comm s0 s1, Nat.xor_self, Nat.zero_xor]

/-! ## `GF(2)` -/

@[step]
theorem gf2_square_spec (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 0 a.val a.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  rw [WP.spec_ok, towerMul, Nat.and_self]

/-! ## `GF(2^2)` -/

@[step]
theorem bf2_reference_square_spec (a : tower.BinaryField2) :
    tower.BinaryField2.reference_square a ⦃ y => y.val = towerMul 1 a.val a.val ⦄ := by
  unfold tower.BinaryField2.reference_square
  step*
  all_goals first
    | (rw [y_post, g1_post, g_post, a1_sq_post, a0_sq_post, a0_post, a0_post1]
       exact (towerMul_succ_self 0 a.val).symm)
    | tower_bound

@[step]
theorem bf2_square_spec (a : tower.BinaryField2) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 1 a.val a.val ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  rw [ite_eq_right (by unfold tower.BinaryField2.BITS; decide)]
  exact bf2_reference_square_spec a

/-! ## `GF(2^4)` -/

@[step]
theorem bf4_reference_square_spec (a : tower.BinaryField4) :
    tower.BinaryField4.reference_square a ⦃ y => y.val = towerMul 2 a.val a.val ⦄ := by
  unfold tower.BinaryField4.reference_square
  step*
  all_goals first
    | (rw [y_post, bf1_post, bf_post, a1_sq_post, a0_sq_post, a0_post, a0_post1]
       exact (towerMul_succ_self 1 a.val).symm)
    | tower_bound

@[step]
theorem bf4_square_spec (a : tower.BinaryField4) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 2 a.val a.val ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  rw [ite_eq_right (by unfold tower.BinaryField4.BITS; decide)]
  exact bf4_reference_square_spec a

/-! ## `GF(2^8)` -/

/-- `tables::square` computes `towerMul 3 a a`. -/
@[step]
theorem tables_square_val_spec (a : Std.U8) :
    tables.square a ⦃ r => r.val = towerMul 3 a.val a.val ⦄ := by
  refine WP.spec_mono (tables_square_spec a) fun r h => ?_
  have h' := congrArg ConcreteBTField.toNat h
  rw [show tower8 a * tower8 a = concrete_mul (tower8 a) (tower8 a) from rfl,
    toNat_concrete_mul, tower8_eq, tower8_eq, ConcreteBTField.toNat_fromNat,
    ConcreteBTField.toNat_fromNat] at h'
  have ha := a.hBounds; have hr := r.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha hr
  rwa [Nat.mod_eq_of_lt (by simpa using hr), Nat.mod_eq_of_lt (by simpa using ha)] at h'

@[step]
theorem bf8_square_spec (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 3 a.val a.val ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  rw [ite_eq_right (by unfold tower.BinaryField8.BITS; decide)]
  unfold tower.BinaryField8.table_square
  step*

/-! ## `GF(2^16)` -/

@[step]
theorem bf16_reference_square_spec (a : tower.BinaryField16) :
    tower.BinaryField16.reference_square a ⦃ y => y.val = towerMul 4 a.val a.val ⦄ := by
  unfold tower.BinaryField16.reference_square
  step*
  rw [y_post, bf1_post, bf_post, a1_sq_post, a0_sq_post, a0_post, a0_post1]
  exact (towerMul_succ_self 3 a.val).symm

@[step]
theorem bf16_square_spec (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 4 a.val a.val ⦄ := by
  have ha : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  simp only [tower.BinaryField16.BITS]
  rw [ite_eq_left (by decide), show (16#usize : Std.Usize).val = 16 from rfl]
  refine WP.spec_bind (square_16_spec a) fun i hi => ?_
  step*

/-! ## `GF(2^32)` -/

@[step]
theorem bf32_byte_square_spec (a : tower.BinaryField32) :
    tower.BinaryField32.byte_square a ⦃ y => y.val = towerMul 5 a.val a.val ⦄ := by
  unfold tower.BinaryField32.byte_square
  step*
  rw [y_post, bf1_post, bf_post, a1_sq_post, a0_sq_post, a0_post, a0_post1]
  exact (towerMul_succ_self 4 a.val).symm

@[step]
theorem bf32_square_spec (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 5 a.val a.val ⦄ := by
  have ha : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  simp only [tower.BinaryField32.BITS]
  rw [ite_eq_left (by decide), show (32#usize : Std.Usize).val = 32 from rfl]
  step*

/-! ## `GF(2^64)` -/

@[step]
theorem bf64_square_spec (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 6 a.val a.val ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  simp only [tower.BinaryField64.BITS]
  rw [ite_eq_left (by decide), show (64#usize : Std.Usize).val = 64 from rfl]
  refine WP.spec_bind (square_64_spec a) fun i hi => ?_
  step*

/-! ## `GF(2^128)` -/

@[step]
theorem bf128_raw_from_repr_spec (r : Std.U128) :
    tower.BinaryField128.raw_from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 7 ⦄ := by
  unfold tower.BinaryField128.raw_from_repr
  step*

@[step]
theorem bf128_from_repr_spec (r : Std.U128) :
    tower.BinaryField128.from_repr r ⦃ x => x.val = r.val % 2 ^ 2 ^ 7 ⦄ := by
  unfold tower.BinaryField128.from_repr; exact bf128_raw_from_repr_spec r

@[step]
theorem bf128_square_spec (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ y =>
      y.val = towerMul 7 a.val a.val ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.square
  simp only [tower.BinaryField128.BITS]
  rw [ite_eq_left (by decide), show (128#usize : Std.Usize).val = 128 from rfl]
  refine WP.spec_bind (square_128_spec a) fun i hi => ?_
  step*

end Plonky3Lean.Proofs.Binary
