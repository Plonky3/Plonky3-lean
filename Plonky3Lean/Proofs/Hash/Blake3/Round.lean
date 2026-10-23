module

public import Plonky3Lean.Proofs.Hash.Blake3.Schedule

@[expose] public section

/-!
# p3-blake3: the rounds

Round `r` reads the message through row `r` of the schedule, which is the message permuted `r`
times.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem permPow_succ' (r i : ℕ) : permPow (r + 1) i = MSG_PERMUTATION.getD (permPow r i) 0 := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih => exact ih (MSG_PERMUTATION.getD i 0)

theorem length_permute (m : List Word) : (permute m).length = 16 := by simp [permute, MSG_PERMUTATION]

/-- The message after `r` permutations, read at `i`, is the message read at `permPow r i`. -/
theorem permute_iter_getD (m : List Word) (r i : ℕ) (hi : i < 16) :
    (permute^[r] m).getD i 0 = m.getD (permPow r i) 0 := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hP : (permute (permute^[r] m)).getD i 0 =
        (permute^[r] m).getD (MSG_PERMUTATION.getD i 0) 0 := by
      simp only [permute, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by simp [MSG_PERMUTATION]; omega)]
      simp
    rw [hP, ih _ (MSG_PERMUTATION_lt i hi)]
    rfl

theorem index_schedule_row (r : ℕ) (hr : r < 7) :
    Std.Array.index_usize (schedOf permPow) (usz r) = .ok (rowArr (permPow r)) :=
  index_sched _ r hr

theorem length_g (s : List Word) (a b c d : ℕ) (mx my : Word) : (g s a b c d mx my).length = s.length := by
  simp [g]

/-- Round `r` is the specification's round, on the message permuted `r` times. -/
theorem round_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (r : ℕ) (hr : r < 7) :
    p3_blake3.batch.compress.round (usz r) WI (grp 16#usize s) (grp 16#usize m) =
      .ok (grp 16#usize (round s (permute^[r] m))) := by
  unfold p3_blake3.batch.compress.round
  have hp := fun i (hi : i < 16) => permPow_lt r i hi
  rw [SCHEDULE_eq, bind_ok, index_sched _ r hr, bind_ok]
  simp (disch := norm_num) only [ofNatCore_eq_usz]
  simp only [index_row _ _ (show 0 < 16 by norm_num), index_row _ _ (show 1 < 16 by norm_num),
    index_row _ _ (show 2 < 16 by norm_num), index_row _ _ (show 3 < 16 by norm_num),
    index_row _ _ (show 4 < 16 by norm_num), index_row _ _ (show 5 < 16 by norm_num),
    index_row _ _ (show 6 < 16 by norm_num), index_row _ _ (show 7 < 16 by norm_num),
    index_row _ _ (show 8 < 16 by norm_num), index_row _ _ (show 9 < 16 by norm_num),
    index_row _ _ (show 10 < 16 by norm_num), index_row _ _ (show 11 < 16 by norm_num),
    index_row _ _ (show 12 < 16 by norm_num), index_row _ _ (show 13 < 16 by norm_num),
    index_row _ _ (show 14 < 16 by norm_num), index_row _ _ (show 15 < 16 by norm_num), bind_ok]
  simp (disch := first | exact hp _ (by norm_num) | simp [length_g, hs, hm]) only [mix_eq, bind_ok]
  simp (disch := norm_num) only [round, permute_iter_getD m r]

end Plonky3Lean.Proofs.Blake3
