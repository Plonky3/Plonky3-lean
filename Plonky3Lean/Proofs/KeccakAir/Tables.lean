module

public import P3KeccakAir
public import Plonky3Lean.Proofs.Hash.Keccak.Lanes

@[expose] public section

/-!
# The tables of the Keccak-f AIR are those of FIPS 202

The rho offsets are the rotations Algorithm 2 computes.

The bits of the round constants are those Algorithm 5 and Algorithm 6 compute.
-/

namespace Plonky3Lean.Proofs.KeccakAir

open p3_keccak_air.mirror Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Keccak

/-- Entry [x][y] of the rho table is the rotation of lane (x, y). -/
theorem rOf_eq : ∀ x < 5, ∀ y < 5, rOf x y = rhoOffsets.getD (x + 5 * y) 0 := by
  decide +kernel

theorem rOf_lt : ∀ x < 5, ∀ y < 5, rOf x y < 64 := by decide

/-- The round-constant bits of rounds 0 to 7. -/
theorem rcBit_eq_0 : ∀ r < 8, ∀ z < 64, (rcBit r z ≠ 0) = roundConstant r (Fin.ofNat 64 z) := by
  decide +kernel

/-- The round-constant bits of rounds 8 to 15. -/
theorem rcBit_eq_8 : ∀ r < 8, ∀ z < 64,
    (rcBit (r + 8) z ≠ 0) = roundConstant (r + 8) (Fin.ofNat 64 z) := by
  decide +kernel

/-- The round-constant bits of rounds 16 to 23. -/
theorem rcBit_eq_16 : ∀ r < 8, ∀ z < 64,
    (rcBit (r + 16) z ≠ 0) = roundConstant (r + 16) (Fin.ofNat 64 z) := by
  decide +kernel

/-- Bit z of the table's round constant r is bit z of the round constant of round r. -/
theorem rcBit_eq {r z : ℕ} (hr : r < 24) (hz : z < 64) :
    (rcBit r z ≠ 0) = roundConstant r (Fin.ofNat 64 z) := by
  rcases (by omega : r < 8 ∨ 8 ≤ r ∧ r < 16 ∨ 16 ≤ r) with h | ⟨h, h'⟩ | h
  · exact rcBit_eq_0 r h z hz
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm]; exact rcBit_eq_8 k (by omega) z hz
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm]; exact rcBit_eq_16 k (by omega) z hz

end Plonky3Lean.Proofs.KeccakAir
