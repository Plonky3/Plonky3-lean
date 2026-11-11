module

public import Plonky3Lean.Proofs.Whir.Fold
public import Plonky3Lean.Proofs.MultilinearUtil.Fold
public import Plonky3Lean.Proofs.Sumcheck.Kernel

@[expose] public section

/-!
# Folding a table

Folding at r and then at s is folding at r ++ s.

The extension of the folded table at s is the extension of the table at r ++ s.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil

variable {K : Type _} [CommRing K]

/-- The vertex j 2^m + c of the (k + m)-cube is the vertex j of the k-cube followed by the vertex c of the m-cube. -/
theorem vertex_add {m c : ℕ} (hc : c < 2 ^ m) :
    ∀ {k j : ℕ}, j < 2 ^ k → (vertex (k + m) (j * 2 ^ m + c) : List K) = vertex k j ++ vertex m c
  | 0, j, hj => by simp [show j = 0 by simpa using hj, vertex]
  | k + 1, j, hj => by
    rw [show k + 1 + m = k + m + 1 by omega]
    by_cases hlo : j < 2 ^ k
    · have : j * 2 ^ m + c < 2 ^ (k + m) := by
        rw [pow_add]; nlinarith
      rw [vertex_low this, vertex_low hlo, vertex_add hc hlo, List.cons_append]
    · obtain ⟨j', rfl⟩ : ∃ j', j = 2 ^ k + j' := ⟨j - 2 ^ k, by omega⟩
      have hj' : j' < 2 ^ k := by rw [pow_succ] at hj; omega
      have : j' * 2 ^ m + c < 2 ^ (k + m) := by rw [pow_add]; nlinarith
      rw [show (2 ^ k + j') * 2 ^ m + c = 2 ^ (k + m) + (j' * 2 ^ m + c) by rw [pow_add]; ring,
        vertex_high this, vertex_high hj', vertex_add hc hj', List.cons_append]

/-- The extension of the fold at s is the extension at r ++ s. -/
theorem mle_foldTable (P : List K) (r s : List K) :
    mle (foldTable P (r.length + s.length) r) s = mle P (r ++ s) := by
  simp only [mle, foldTable, List.length_append, Nat.add_sub_cancel_left]
  rw [pow_add, ← Plonky3Lean.Proofs.Sumcheck.sum_tiles _ (2 ^ s.length) (2 ^ r.length), sum_comm]
  refine sum_congr rfl fun c hc => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hc),
    Option.map_some, Option.getD_some, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [vertex_add (mem_range.mp hc) (mem_range.mp hj), eq_append (by simp)]
  ring

end Plonky3Lean.Proofs.Whir
