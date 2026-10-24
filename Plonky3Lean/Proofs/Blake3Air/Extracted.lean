module

public import P3Blake3Air
public import Plonky3Lean.Lib.Scalar.Words
public import Plonky3Lean.Lib.Scalar.Bits

@[expose] public section

/-!
# The extracted code of p3-blake3-air

The extracted constants are the transcribed ones.

The extracted half quarter round computes the transcribed one, and never panics.

So do the extracted IV word and carry word of the characteristic-2 generator.
-/

namespace Plonky3Lean.Proofs.Blake3Air

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib

/-- The extracted IV halves are the transcribed ones. -/
theorem IV_eq : p3_blake3_air.constants.IV.val.map (fun w => w.val.map (·.val)) = p3_blake3_air.mirror.IV := by
  unfold p3_blake3_air.constants.IV
  decide +kernel

/-- The extracted message permutation is the transcribed one. -/
theorem MSG_PERMUTATION_eq :
    p3_blake3_air.constants.MSG_PERMUTATION.val.map (·.val) = p3_blake3_air.mirror.MSG_PERMUTATION := by
  unfold p3_blake3_air.constants.MSG_PERMUTATION
  decide +kernel

/-- The extracted half quarter round never panics, and computes the transcribed one. -/
theorem verifiable_half_round_eq (a b c d m : Std.U32) (flag : Bool) :
    p3_blake3_air.generation.verifiable_half_round a b c d m flag =
      let r := p3_blake3_air.mirror.verifiable_half_round a.bv b.bv c.bv d.bv m.bv flag
      .ok (⟨r.1⟩, ⟨r.2.1⟩, ⟨r.2.2.1⟩, ⟨r.2.2.2⟩) := by
  cases flag <;>
    simp only [p3_blake3_air.generation.verifiable_half_round, p3_blake3_air.mirror.verifiable_half_round,
      u32_wrapping_add_eq, u32_rotate_right_eq, lift_eq, bind_ok, ite_true, ite_false,
      Bool.false_eq_true] <;> rfl

/-- The extracted carry word is the transcribed one. -/
theorem carries_word_eq (x y s : Std.U32) :
    p3_blake3_air.binary.generation.carries_word x y s =
      .ok ⟨p3_blake3_air.mirror.binary.carries_word x.bv y.bv s.bv⟩ := by
  simp only [p3_blake3_air.binary.generation.carries_word, p3_blake3_air.mirror.binary.carries_word, lift_eq,
    bind_ok]
  rw [u32_shiftRight_i32_eq _ _ (by decide) (by decide)]
  rfl

end Plonky3Lean.Proofs.Blake3Air
