module

public import Plonky3Lean.Spec.Sha256

@[expose] public section

/-!
# SHA-256: the message schedule and the rounds, one step at a time

The specification builds the schedule by appending words and runs the rounds as a fold.

Here they are stated as recurrences: word `t` from the four words it depends on, and round `k + 1` from round `k`.
-/

namespace Plonky3Lean.Proofs.Sha256

open Plonky3Lean.Spec.Sha256

theorem length_extend (W : List Word) : (extend W).length = W.length + 1 := by
  simp [extend]

theorem length_extend_iterate (W : List Word) (n : ℕ) : (extend^[n] W).length = W.length + n := by
  induction n generalizing W with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, length_extend]; omega

/-- Extending keeps every word already there. -/
theorem getD_extend (W : List Word) (t : ℕ) (ht : t < W.length) :
    (extend W).getD t 0 = W.getD t 0 := by
  simp [extend, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem getD_extend_iterate (W : List Word) (n t : ℕ) (ht : t < W.length) :
    (extend^[n] W).getD t 0 = W.getD t 0 := by
  induction n generalizing W with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih _ (by rw [length_extend]; omega), getD_extend _ _ ht]

/-- The word an extension appends. -/
theorem getD_extend_last (W : List Word) :
    (extend W).getD W.length 0 = smallSigma1 (W.getD (W.length - 2) 0) + W.getD (W.length - 7) 0 +
      smallSigma0 (W.getD (W.length - 15) 0) + W.getD (W.length - 16) 0 := by
  simp [extend, List.getD_eq_getElem?_getD]

/-- Words below 16 are the block's. -/
theorem schedule_lt (M : List Word) (t : ℕ) (hM : M.length = 16) (ht : t < 16) :
    (schedule M).getD t 0 = M.getD t 0 :=
  getD_extend_iterate M 48 t (by omega)

/-- Word `t` from words `t - 2`, `t - 7`, `t - 15` and `t - 16`. -/
theorem schedule_ge (M : List Word) (t : ℕ) (hM : M.length = 16) (h16 : 16 ≤ t) (h64 : t < 64) :
    (schedule M).getD t 0 =
      smallSigma1 ((schedule M).getD (t - 2) 0) + (schedule M).getD (t - 7) 0 +
        smallSigma0 ((schedule M).getD (t - 15) 0) + (schedule M).getD (t - 16) 0 := by
  -- The schedule is the first `t - 15` extensions, extended further.
  have split : schedule M = extend^[48 - (t - 15)] (extend (extend^[t - 16] M)) := by
    rw [schedule, ← Function.iterate_succ_apply' extend, ← Function.iterate_add_apply]
    congr 1; omega
  have hlen : (extend^[t - 16] M).length = t := by rw [length_extend_iterate]; omega
  have keep : ∀ s < t, (schedule M).getD s 0 = (extend^[t - 16] M).getD s 0 := by
    intro s hs
    rw [split, getD_extend_iterate _ _ _ (by rw [length_extend]; omega), getD_extend _ _ (by omega)]
  rw [keep (t - 2) (by omega), keep (t - 7) (by omega), keep (t - 15) (by omega),
    keep (t - 16) (by omega), split, getD_extend_iterate _ _ _ (by rw [length_extend]; omega)]
  have last := getD_extend_last (extend^[t - 16] M)
  rw [hlen] at last
  exact last

/-- Round `k + 1` from round `k`. -/
theorem rounds_succ (W : List Word) (v : Vars) (k : ℕ) :
    rounds W v (k + 1) = round (rounds W v k) (K.getD k 0) (W.getD k 0) := by
  simp [rounds, List.range_succ, List.foldl_append]

/-- The words of `4 n` bytes, by index. -/
theorem wordsOfBytes_eq (n : ℕ) (l : List Byte) (hl : l.length = 4 * n) :
    wordsOfBytes l = (List.range n).map fun k =>
      wordOfBytes (l.getD (4 * k) 0) (l.getD (4 * k + 1) 0) (l.getD (4 * k + 2) 0)
        (l.getD (4 * k + 3) 0) := by
  induction n generalizing l with
  | zero => simp at hl; subst hl; rfl
  | succ n ih =>
    match l, hl with
    | a :: b :: c :: d :: rest, hl =>
      simp only [List.length_cons] at hl
      rw [wordsOfBytes, ih rest (by omega), List.range_succ_eq_map]
      simp [Nat.mul_succ, Nat.add_assoc]

end Plonky3Lean.Proofs.Sha256
