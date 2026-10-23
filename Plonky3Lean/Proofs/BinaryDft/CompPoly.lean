module

public import Plonky3Lean.Proofs.BinaryDft.Basic
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis

@[expose] public section

/-!
# The subspace polynomial of CompPoly

CompPoly's additive NTT defines W_i as the product of X - u over the subspace U_i spanned by beta_0, ..., beta_(i-1).

For a linearly independent basis over a field of two elements, the points 0, ..., 2^i - 1 run over U_i once each.

So CompPoly's W_i evaluates to the subspace polynomial of this specification.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft Polynomial

universe u

variable {r : ℕ} [NeZero r] {L : Type u} [Field L] [Fintype L] [DecidableEq L]
  (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q] [hF₂ : Fact (Fintype.card 𝔽q = 2)] [Algebra 𝔽q L]
  (β : Fin r → L) [hβ : Fact (LinearIndependent 𝔽q β)]

/-- The basis on all indices: beta below r, zero from r on. -/
def extendBasis (β : Fin r → L) (k : ℕ) : L := if h : k < r then β ⟨k, h⟩ else 0

/-- Point m, for m below 2^i, as a combination of the basis with coefficients 0 and 1. -/
theorem point_eq_combination {i : ℕ} (hi : i ≤ r) {m : ℕ} (hm : m < 2 ^ i) :
    point (extendBasis β) m =
      ∑ k : Fin r, (if k.val < i ∧ m.testBit k then (1 : 𝔽q) else 0) • β k := by
  rw [point_eq_sum _ (lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos hi)),
    ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : k.val < i
  · by_cases hb : m.testBit k <;> simp [hk, hb, extendBasis]
  · simp [hk, testBit_of_lt hm (not_lt.mp hk)]

theorem point_mem_U (i : Fin r) {m : ℕ} (hm : m < 2 ^ i.val) :
    point (extendBasis β) m ∈ AdditiveNTT.U 𝔽q β i := by
  rw [point_eq_combination 𝔽q β i.isLt.le hm]
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, by simpa using h.1, rfl⟩)
  · simp

include hβ in
theorem point_injective {i : ℕ} (hi : i ≤ r) {a b : ℕ} (ha : a < 2 ^ i) (hb : b < 2 ^ i)
    (h : point (extendBasis β) a = point (extendBasis β) b) : a = b := by
  rw [point_eq_combination 𝔽q β hi ha, point_eq_combination 𝔽q β hi hb, ← sub_eq_zero,
    ← sum_sub_distrib] at h
  simp_rw [← sub_smul] at h
  have hc := Fintype.linearIndependent_iff.mp hβ.out _ h
  have h01 : (1 : 𝔽q) ≠ 0 := one_ne_zero
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < i
  · have := hc ⟨k, by omega⟩
    by_cases h1 : a.testBit k <;> by_cases h2 : b.testBit k <;> simp_all
  · rw [testBit_of_lt ha (not_lt.mp hk), testBit_of_lt hb (not_lt.mp hk)]

/-- CompPoly's W_i, evaluated at x, is the subspace polynomial of the extended basis. -/
theorem compPoly_W_eval (i : Fin r) (x : L) :
    (AdditiveNTT.W 𝔽q β i).eval x = vanishing (extendBasis β) i x := by
  let g : Fin (2 ^ i.val) → AdditiveNTT.U 𝔽q β i := fun m =>
    ⟨point (extendBasis β) m, point_mem_U 𝔽q β i m.isLt⟩
  have hg : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => Fin.ext (point_injective 𝔽q β i.isLt.le a.isLt b.isLt
      (congrArg Subtype.val h)), ?_⟩
    rw [Fintype.card_fin, AdditiveNTT.U_card, hF₂.out]
  rw [AdditiveNTT.W, eval_prod, vanishing, ← Fin.prod_univ_eq_prod_range]
  simp only [eval_sub, eval_X, eval_C]
  exact (Function.Bijective.prod_comp hg (fun u => x - u.val)).symm

end Plonky3Lean.Proofs.BinaryDft
