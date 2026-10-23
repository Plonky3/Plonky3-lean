module

public import Plonky3Lean.Proofs.KeccakAir.Tables
public import Plonky3Lean.Proofs.Hash.Keccak.Permutation

@[expose] public section

/-!
# The extracted tables of p3-keccak-air

The extracted rho offsets, round constants and round-constant bits are the transcribed lists.

So they are also those of FIPS 202: the rho rotations of Algorithm 2 and the round constants of Algorithm 6.
-/

namespace Plonky3Lean.Proofs.KeccakAir

open Aeneas Aeneas.Std p3_keccak_air.mirror Plonky3Lean.Proofs.Keccak

/-- The extracted rho table is the transcribed one. -/
theorem R_eq : p3_keccak_air.constants.R.val.map (fun row => row.val.map (·.val)) = R := by
  unfold p3_keccak_air.constants.R
  decide +kernel

/-- The extracted round constants are the transcribed ones. -/
theorem RC_eq : p3_keccak_air.constants.RC.val.map (·.val) = RC := by
  unfold p3_keccak_air.constants.RC
  decide +kernel

/-- The extracted round-constant bits are the transcribed ones. -/
theorem RC_BITS_eq : p3_keccak_air.constants.RC_BITS.val.map (fun row => row.val.map (·.val)) = RC_BITS := by
  unfold p3_keccak_air.constants.RC_BITS
  decide +kernel

/-- The extracted round constants are those of Algorithm 6 of FIPS 202. -/
theorem RC_eq_lfsr : p3_keccak_air.constants.RC.val.map UScalar.bv = (List.range 24).map rcWord := by
  unfold p3_keccak_air.constants.RC
  decide +kernel

end Plonky3Lean.Proofs.KeccakAir
