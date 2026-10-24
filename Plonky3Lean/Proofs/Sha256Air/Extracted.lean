module

public import P3Sha256Air
public import Plonky3Lean.Lib.Scalar.Words
public import Plonky3Lean.Spec.Sha256

@[expose] public section

/-!
# The extracted integer code of p3-sha256-air

- The extracted round constants and initial hash value are the transcribed lists, and those of FIPS 180-4.
- The extracted limb split returns the low and the high 16 bits.
- The extracted sigma functions of the characteristic-2 generator never panic, and are those of FIPS 180-4.
-/

namespace Plonky3Lean.Proofs.Sha256Air

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib Plonky3Lean.Spec.Sha256

/-- The extracted round constants are the transcribed ones. -/
theorem SHA256_K_eq : p3_sha256_air.constants.SHA256_K.val.map (·.val) = p3_sha256_air.mirror.SHA256_K := by
  unfold p3_sha256_air.constants.SHA256_K
  decide +kernel

/-- The extracted round constants are those of FIPS 180-4, section 4.2.2. -/
theorem SHA256_K_bv : p3_sha256_air.constants.SHA256_K.val.map UScalar.bv = K := by
  unfold p3_sha256_air.constants.SHA256_K
  decide +kernel

/-- The extracted initial hash value is the transcribed one. -/
theorem SHA256_IV_eq : p3_sha256_air.constants.SHA256_IV.val.map (·.val) = p3_sha256_air.mirror.SHA256_IV := by
  unfold p3_sha256_air.constants.SHA256_IV
  decide +kernel

/-- The extracted initial hash value is that of FIPS 180-4, section 5.3.3. -/
theorem SHA256_IV_bv : p3_sha256_air.constants.SHA256_IV.val.map UScalar.bv = H0 := by
  unfold p3_sha256_air.constants.SHA256_IV
  decide +kernel

/-- The transcribed round constants are FIPS 180-4's. -/
theorem kOf_bv : ∀ t < 64, BitVec.ofNat 32 (p3_sha256_air.mirror.kOf t) = K.getD t 0 := by decide

/-- The extracted big sigma 0 never panics, and is that of FIPS 180-4. -/
theorem big_sigma0_eq (x : Std.U32) :
    p3_sha256_air.binary.generation.big_sigma0 x = .ok ⟨bigSigma0 x.bv⟩ := by
  simp only [p3_sha256_air.binary.generation.big_sigma0, u32_rotate_right_eq, bind_ok, lift]
  rfl

/-- The extracted big sigma 1 never panics, and is that of FIPS 180-4. -/
theorem big_sigma1_eq (x : Std.U32) :
    p3_sha256_air.binary.generation.big_sigma1 x = .ok ⟨bigSigma1 x.bv⟩ := by
  simp only [p3_sha256_air.binary.generation.big_sigma1, u32_rotate_right_eq, bind_ok, lift]
  rfl

/-- The extracted small sigma 0 never panics, and is that of FIPS 180-4. -/
theorem small_sigma0_eq (x : Std.U32) :
    p3_sha256_air.binary.generation.small_sigma0 x = .ok ⟨smallSigma0 x.bv⟩ := by
  simp only [p3_sha256_air.binary.generation.small_sigma0, u32_rotate_right_eq, bind_ok, lift,
    u32_shiftRight_i32_eq x 3#i32 (by decide) (by decide)]
  rfl

/-- The extracted small sigma 1 never panics, and is that of FIPS 180-4. -/
theorem small_sigma1_eq (x : Std.U32) :
    p3_sha256_air.binary.generation.small_sigma1 x = .ok ⟨smallSigma1 x.bv⟩ := by
  simp only [p3_sha256_air.binary.generation.small_sigma1, u32_rotate_right_eq, bind_ok, lift,
    u32_shiftRight_i32_eq x 10#i32 (by decide) (by decide)]
  rfl

/-- The extracted limb split never panics, and returns the low and the high 16 bits. -/
theorem u32_to_limbs_eq (value : Std.U32) :
    ∃ out, p3_sha256_air.constants.u32_to_limbs value = .ok out ∧
      out.val.map (·.val) = [value.val % 2 ^ 16, value.val / 2 ^ 16] := by
  unfold p3_sha256_air.constants.u32_to_limbs p3_sha256_air.constants.BITS_PER_LIMB
  simp only [lift, bind_ok]
  have hs : (value >>> 16#usize : RustM Std.U32) = .ok ⟨value.bv >>> 16⟩ := by
    simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
    rfl
  rw [hs, bind_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [Array.make, Std.Array.from_val, List.map_cons, List.map_nil, UScalar.cast_val_eq,
    List.cons.injEq, and_true]
  refine ⟨rfl, ?_⟩
  show (value.bv >>> 16).toNat % 2 ^ 16 = _
  have := value.bv.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, UScalar.bv_toNat]
  rw [UScalar.bv_toNat] at this
  exact Nat.mod_eq_of_lt (by change value.val < 2 ^ 32 at this; omega)

end Plonky3Lean.Proofs.Sha256Air
