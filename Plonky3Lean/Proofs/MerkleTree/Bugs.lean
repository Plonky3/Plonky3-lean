module

public import Plonky3Lean.Proofs.MerkleTree.Schedule
public import Plonky3Lean.Proofs.MerkleTree.Bind
public import Plonky3Lean.Proofs.MerkleTree.Forward

@[expose] public section

/-!
# Two defects of the pinned verifier

Both are fixed on Plonky3 main by Plonky3/Plonky3#2471, after the commit this model is pinned to.

- With arity 8, heights 4 and 2 make the schedule loop run forever.
- With arity 2 and a cap two layers below the root, a height-1 matrix beside a height-8 one is never read.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

theorem npt_two_pow (k : ℕ) : npt (2 ^ k) = 2 ^ k :=
  Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k)

/-- Two matrices of the given heights. -/
def dims2 (w0 h0 w1 h1 : Std.Usize) : Slice p3_matrix.Dimensions :=
  Slice.from [{ width := w0, height := h0 }, { width := w1, height := h1 }] (by simp; scalar_tac)

theorem dims2_height (w0 h0 w1 h1 : Std.Usize) :
    heightOf (dims2 w0 h0 w1 h1) 0 = h0.val ∧ heightOf (dims2 w0 h0 w1 h1) 1 = h1.val := by
  simp [heightOf, dims2]

theorem dims2_length (w0 h0 w1 h1 : Std.Usize) : (dims2 w0 h0 w1 h1).val.length = 2 := by
  simp [dims2]

theorem npt_one : npt 1 = 1 := by simpa using npt_two_pow 0
theorem npt_two : npt 2 = 2 := by simpa using npt_two_pow 1
theorem npt_four : npt 4 = 4 := by simpa using npt_two_pow 2
theorem npt_eight : npt 8 = 8 := by simpa using npt_two_pow 3

/-! ## Arity 8, heights 4 and 2: the schedule loop never ends -/

/-- From the state the schedule loop reaches, every step returns to that same state. -/
theorem sched_loops (height : ℕ → ℕ) (h1 : height 1 = 2) :
    ∀ f acc, schedRun 8 4 height [0, 1] f 8 1 acc = none := by
  intro f
  induction f with
  | zero => intro acc; rfl
  | succ f ih =>
    intro acc
    have hsel : selectSpec 8 8 4 height [0, 1] 1 = 2 := by
      simp [selectSpec, h1, npt_two, npt_one]
    simp only [schedRun, hsel]
    rw [ite_eq_left (by norm_num)]
    have hpos : (if 1 < [0, 1].length ∧ npt (height ([0, 1].getD 1 0)) = npt (8 / 2)
        then advance height [0, 1] (height ([0, 1].getD 1 0)) 1 else 1) = 1 := by
      simp [h1, npt_two, npt_four]
    rw [hpos, show padded (8 / 2) 8 = 8 by simp [padded]]
    exact ih _

/-- With arity 8, the pinned verifier's schedule for heights 4 and 2 never returns. -/
theorem schedule_never_returns (w0 w1 cap : Std.Usize) (x : alloc.vec.Vec Std.Usize × Std.Usize) :
    mmcs.hax_reshaped.arity_schedule_and_proof_levels 8#usize cap (dims2 w0 4#usize w1 2#usize) ≠
      RustM.ok (core.result.Result.Ok x) := by
  intro h
  obtain ⟨sched, pl⟩ := x
  obtain ⟨val, order, curr, lnpt, pos0, f, hval, horder, hcurr, hlnpt, hpos0, hrun, -⟩ := arity_eq h
  obtain ⟨hh0, hh1⟩ := dims2_height w0 4#usize w1 2#usize
  have hv : val.val = 4 := by
    rw [(validate_ok_val hval).1]; simp [maxHeight, dims2]
  have ho : ordL order = [0, 1] := by
    rw [tallest_first_eq horder, dims2_length]
    simp [sortTallest, insertPos, hh0, hh1]
  have hc : curr.val = 8 := by rw [padded_len_ok hcurr, hv]; simp [padded]
  have hl : lnpt.val = 4 := by rw [(npt_ok hlnpt).1, hv, npt_four]
  have hp : pos0.val = 1 := by
    rw [hpos0, ho, hl]
    rw [leafEnd]; simp only [List.length_cons, List.getD_cons_zero, hh0]
    rw [ite_eq_left (by simp [npt_four])]
    rw [leafEnd]
    rw [ite_eq_right (by simp [hh1, npt_two])]
  have hN8 : (8#usize : Std.Usize).val = 8 := by simp
  rw [ho, hl, hc, hp, hN8, sched_loops _ hh1] at hrun
  cases hrun

/-! ## Arity 2, cap height 2, heights 8 and 1: the short matrix is never read -/

set_option linter.unusedSimpArgs false in
theorem sched_8_1 (height : ℕ → ℕ) (h1 : height 1 = 1) (f : ℕ) (v : List ℕ)
    (h : schedRun 2 8 height [0, 1] f 8 1 [] = some v) : v = [2, 2, 2] := by
  have a1 : advance height [0, 1] 1 1 = 2 := by
    rw [advance, ite_eq_left (by simp [h1])]
    rw [advance, ite_eq_right (by simp)]
  rcases f with _ | _ | _ | _ | f
  · cases h
  all_goals
    simp only [schedRun, selectSpec] at h
    simp [h1, npt_one, npt_two, npt_four, npt_eight, padded, a1, schedRun] at h
  exact h.symm

/-- Take arity 2 and the cap two layers below the root.

The pinned verifier never reads a matrix of height 1 next to one of height 8.

Its rows are bound by no check: any row of the right width verifies. -/
theorem short_matrix_unread (w0 w1 : Std.Usize) :
    ¬ Reads 2#usize 2#usize (dims2 w0 8#usize w1 1#usize) 1 := by
  rintro ⟨val, sched, pl, sched1, order, curr, lnpt, pos, hval, hsched, hsched1, horder, hcurr,
    hlnpt, hpos, k, hk, hm, hread⟩
  obtain ⟨hh0, hh1⟩ := dims2_height w0 8#usize w1 1#usize
  have hv : val.val = 8 := by rw [(validate_ok_val hval).1]; simp [maxHeight, dims2]
  have ho : ordL order = [0, 1] := by
    rw [tallest_first_eq horder, dims2_length]
    simp [sortTallest, insertPos, hh0, hh1]
  have hN2 : (2#usize : Std.Usize).val = 2 := by simp
  have hc : curr.val = 8 := by rw [padded_len_ok hcurr, hv, hN2]; simp [padded]
  have hl : lnpt.val = 8 := by rw [(npt_ok hlnpt).1, hv, npt_eight]
  have hp : pos.val = 1 := by
    rw [leaf_loop_ok _ order lnpt _ 0#usize pos rfl hpos, ho, hl]
    rw [leafEnd, ite_eq_left (by simp [hh0, npt_eight])]
    rw [leafEnd, ite_eq_right (by simp [hh1, npt_one])]
    simp
  obtain ⟨val', order', curr', lnpt', pos0, f, hval', horder', hcurr', hlnpt', hpos0', hrun, hpl⟩ :=
    arity_eq hsched
  rw [hval] at hval'; have := result_ok_inj (ok_inj hval'); subst this
  rw [horder] at horder'; cases ok_inj horder'
  rw [hcurr] at hcurr'; cases ok_inj hcurr'
  rw [hlnpt] at hlnpt'; cases ok_inj hlnpt'
  have hpos0 : pos0.val = 1 := by
    rw [hpos0', ho, hl]
    rw [leafEnd, ite_eq_left (by simp [hh0, npt_eight])]
    rw [leafEnd, ite_eq_right (by simp [hh1, npt_one])]
  rw [ho, hl, hc, hN2, hpos0] at hrun
  have hs := sched_8_1 _ hh1 f _ hrun
  have hslen : sched.val.length = 3 := by
    have := congrArg List.length hs; simpa using this
  have hplv : pl.val = 1 := by rw [hpl, hslen, hN2]; rfl
  have hs1 : schedFrom sched1 0 = [2] := by
    simp only [schedFrom, List.drop_zero]
    rw [vec_truncate_ok hsched1, hplv, List.map_take, hs]
    rfl
  rw [hs1, ho, hc, hp, hN2] at hread
  have hk2 : k < 2 := by rw [← ordL_length, ho] at hk; simpa using hk
  have hk1 : k = 1 := by
    rw [ho] at hm
    rcases k with _ | _ | k
    · simp at hm
    · rfl
    · omega
  subst hk1
  rcases hread with h1 | ⟨g, hg, -⟩
  · omega
  · simp [plan, injected, hh1, npt_one, npt_four] at hg

end Plonky3Lean.Proofs.MerkleTree

