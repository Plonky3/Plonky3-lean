module

public import P3Fri.Transcript
public import Mathlib.Data.List.Count
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The described transcripts

Each grinding step sits where its parameter says, with that parameter's difficulty, and only when the difficulty is positive.

The query indices are the last step, drawn with the index bits of the shape.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.transcript.mirror

theorem count_commitPow (s : FriShape) (b : ℕ) :
    s.pattern.count (Step.commitPow b) =
      if 0 < s.commit_pow_bits ∧ b = s.commit_pow_bits then s.log_arities.length else 0 := by
  simp only [FriShape.pattern, List.count_append, List.count_flatMap]
  by_cases hb : s.commit_pow_bits = b
  · subst hb
    by_cases hq : 0 < s.query_pow_bits <;> by_cases hc : 0 < s.commit_pow_bits <;>
      simp [hq, hc, Function.comp_def, List.map_const']
  · by_cases hq : 0 < s.query_pow_bits <;> by_cases hc : 0 < s.commit_pow_bits <;>
      simp [hq, hc, hb, Ne.symm hb, Function.comp_def, List.map_const']

theorem queryPow_mem (s : FriShape) (b : ℕ) :
    Step.queryPow b ∈ s.pattern ↔ 0 < s.query_pow_bits ∧ b = s.query_pow_bits := by
  by_cases hq : 0 < s.query_pow_bits <;> by_cases hc : 0 < s.commit_pow_bits <;>
    simp [FriShape.pattern, hq, hc, eq_comm]

theorem pattern_getLast (s : FriShape) :
    s.pattern.getLast? = some (Step.queryIndices s.index_bits s.num_queries) := by
  rw [FriShape.pattern, List.getLast?_append]
  simp

theorem batchPow_mem (s : PcsShape) (b : ℕ) :
    Step.batchPow b ∈ s.pattern ↔ 0 < s.batch_pow_bits ∧ b = s.batch_pow_bits := by
  by_cases hb : 0 < s.batch_pow_bits <;> simp [PcsShape.pattern, hb, eq_comm]

/-- An index of the tallest codeword, shifted to a height h, indexes the codeword of height h. -/
theorem shifted_index_lt {H h idx : ℕ} (hh : h ≤ H) (hidx : idx < 2 ^ H) : idx / 2 ^ (H - h) < 2 ^ h := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show h + (H - h) = H by omega]; exact hidx

end Plonky3Lean.Proofs.Fri
