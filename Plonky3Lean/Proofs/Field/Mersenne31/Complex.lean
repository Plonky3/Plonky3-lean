import Plonky3Lean.Proofs.Field.Mersenne31.Constants

/-!
# Mersenne31: multiplication by `W = 2 + i` in QM31
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-- `mul_by_w(z)` is `z · (2 + i)`, for `z` with valid coordinates. -/
theorem mul_by_w.toComplex (z : Array Element 2#usize)
    (hz : ∀ x ∈ z.val, Valid x) :
    extension.Mersenne31.mul_by_w z ⦃ r =>
      (∀ x ∈ r.val, Valid x) ∧
        Spec.Mersenne31.toComplex r = Spec.Mersenne31.toComplex z * Mersenne31.Complex.mk 2 1 ⦄ := by
  obtain ⟨l, hl⟩ := z
  match l, hl with
  | [re, im], _ =>
    have hre : Valid re := hz re (by simp)
    have him : Valid im := hz im (by simp)
    unfold extension.Mersenne31.mul_by_w
    have h0 : Array.index_usize ⟨[re, im], ‹_›⟩ 0#usize = .ok re := rfl
    have h1 : Array.index_usize ⟨[re, im], ‹_›⟩ 1#usize = .ok im := rfl
    rw [h0, h1]
    simp only [bind_tc_ok]
    step with add.toField re re hre hre as ⟨a, ha1, ha2⟩
    step with sub.toField a im ha1 him as ⟨a1, ha3, ha4⟩
    step with add.toField re im hre him as ⟨b, hb1, hb2⟩
    step with add.toField b im hb1 him as ⟨b1, hb3, hb4⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Array.make, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption
    · show Mersenne31.Complex.mk (toField a1) (toField b1) =
        Mersenne31.Complex.mk (toField re) (toField im) * Mersenne31.Complex.mk 2 1
      rw [Mersenne31.Complex.mk_mul, ha4, ha2, hb4, hb2]
      congr 1 <;> ring

end Plonky3Lean.Proofs.Mersenne31
