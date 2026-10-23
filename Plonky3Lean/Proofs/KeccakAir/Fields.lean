module

public import Plonky3Lean.Proofs.KeccakAir.Degree
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Mersenne31.Basic

@[expose] public section

/-!
# The Keccak-f AIR at BabyBear, KoalaBear, Goldilocks and Mersenne31

Each of the four fields has characteristic at least 2^16, which soundness needs.

Over each, the bounding builder accepts the AIR, so its constraint degrees are at most 3.
-/

namespace Plonky3Lean.Proofs.KeccakAir

open p3_keccak_air.mirror p3_air.air.mirror

/-- Unfold the bounding builder's run to a closed computation and evaluate it. -/
macro "top_tac" : tactic => `(tactic| (
  simp only [TopOk, keccakAir, eval, eval_round_flags, topBuilder, getD_map_const, AirLayout.from_air]
  decide +kernel))

theorem top_babyBear : TopOk BabyBear.Field := by top_tac
theorem top_koalaBear : TopOk KoalaBear.Field := by top_tac
theorem top_goldilocks : TopOk Goldilocks.Field := by top_tac
theorem top_mersenne31 : TopOk Mersenne31.Field := by top_tac

theorem ringChar_babyBear : 2 ^ 16 ≤ ringChar BabyBear.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_koalaBear : 2 ^ 16 ≤ ringChar KoalaBear.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_goldilocks : 2 ^ 16 ≤ ringChar Goldilocks.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_mersenne31 : 2 ^ 16 ≤ ringChar Mersenne31.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

end Plonky3Lean.Proofs.KeccakAir
