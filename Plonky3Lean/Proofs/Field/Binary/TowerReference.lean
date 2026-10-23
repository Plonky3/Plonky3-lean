module

public import Plonky3Lean.Proofs.Field.Binary.TowerFrobenius

@[expose] public section

/-!
# The reference multiplication

`reference_mul` is the Karatsuba product of the tower spelled out at every level, without the
table at `GF(2^8)`. It computes the same product as `towerMul`.
-/

open Aeneas Aeneas.Std CoreModels
open ConcreteBinaryTower
open p3_binary_field

namespace Plonky3Lean.Proofs.Binary

@[step]
theorem bf8_reference_mul_spec (a b : tower.BinaryField8) :
    tower.BinaryField8.reference_mul a b ⦃ y => y.val = towerMul (2 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField8.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf16_reference_mul_spec (a b : tower.BinaryField16) :
    tower.BinaryField16.reference_mul a b ⦃ y => y.val = towerMul (3 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField16.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf32_reference_mul_spec (a b : tower.BinaryField32) :
    tower.BinaryField32.reference_mul a b ⦃ y => y.val = towerMul (4 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField32.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf64_reference_mul_spec (a b : tower.BinaryField64) :
    tower.BinaryField64.reference_mul a b ⦃ y => y.val = towerMul (5 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField64.reference_mul
  step*
  tower_mul_close

@[step]
theorem bf128_reference_mul_spec (a b : tower.BinaryField128) :
    tower.BinaryField128.reference_mul a b ⦃ y => y.val = towerMul (6 + 1) a.val b.val ⦄ := by
  unfold tower.BinaryField128.reference_mul
  step*
  tower_mul_close

end Plonky3Lean.Proofs.Binary
