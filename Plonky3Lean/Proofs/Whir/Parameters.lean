module

public import Plonky3Lean.Proofs.Whir.Complete

@[expose] public section

/-!
# The parameter schedule

The configuration checks the first folded domain against the encoder's capacity, and no later one.
-/

namespace Plonky3Lean.Proofs.Whir

open p3_whir.mirror p3_whir.parameters.mirror

/-- BabyBear, 28 variables, rate 1/4, schedule [8, 2, 18], rates [10, 10]: accepted, and round 1 queries a folded domain of 2^28 points. -/
theorem later_fold_exceeds (cs : Counts) :
    ∃ c, schedule cs 28 2 [8, 2, 18] [10, 10] 27 = .ok c ∧
      (c.round_parameters.map (·.log_folded_domain_size)) = [22, 28] := by
  have h30 : Nat.log 2 1073741824 = 30 := by
    rw [show (1073741824 : ℕ) = 2 ^ 30 by norm_num, Nat.log_pow (by norm_num)]
  refine ⟨_, rfl, ?_⟩
  simp [h30]

end Plonky3Lean.Proofs.Whir
