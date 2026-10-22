module

public import Plonky3Lean.Proofs.Hash.Blake3.Hash

@[expose] public section

/-!
# p3-blake3: the lane digest is the BLAKE3 digest

The model's chunk windows are the specification's chunks, its plain-block chaining value is the
specification's fold over a chunk's blocks, and its split of the tree is the specification's.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem cvBytes_eq (cv : List Word) (h : cv.length = 8) :
    cvBytes cv = ((cv.take 8).map bytesOfWord).flatten := by
  match cv, h with
  | [a, b, c, d, e, f, g, k], _ => rfl

theorem pow2Below_eq (f n : ℕ) (hn : 2 ≤ n) : pow2Below f n = 2 ^ min f (Nat.log 2 (n - 1)) := by
  induction f with
  | zero => simp [pow2Below]
  | succ f ih =>
    rw [pow2Below, ih]
    by_cases hf : f < Nat.log 2 (n - 1)
    · have h1 : 2 * 2 ^ f < n := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show f + 1 ≤ Nat.log 2 (n - 1) by omega)
        have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
        rw [pow_succ] at *; omega
      rw [Nat.min_eq_left hf.le, ite_eq_left_of_eq_true _ _ (eq_true h1), Nat.min_eq_left (by omega), pow_succ]
      ring
    · have hm : min f (Nat.log 2 (n - 1)) = Nat.log 2 (n - 1) := Nat.min_eq_right (by omega)
      have h1 : ¬ 2 * 2 ^ Nat.log 2 (n - 1) < n := by
        have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n - 1)
        rw [pow_succ] at this; omega
      rw [hm, ite_eq_right_of_eq_false _ _ (eq_false h1), Nat.min_eq_right (by omega)]

theorem leftChunks_eq (c : ℕ) (hc : 2 ≤ c) : leftChunks c = pow2Below c c := by
  rw [pow2Below_eq c c hc, Nat.min_eq_right]
  · rfl
  · have := Nat.log_le_self 2 (c - 1); omega

end Plonky3Lean.Proofs.Blake3
