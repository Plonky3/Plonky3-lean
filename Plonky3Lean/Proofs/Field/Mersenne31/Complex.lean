module

public import Plonky3Lean.Proofs.Field.Mersenne31.Constants

@[expose] public section

/-!
# Mersenne31: multiplication by `W = 2 + i` in QM31
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.P3Mersenne31

/-- `mul_by_w(z)` is `z · (2 + i)`, for `z` with valid coordinates. -/
theorem mul_by_w.toComplex (z : Array Element 2#usize)
    (hz : ∀ x ∈ z.val, Valid x) :
    extension.Mersenne31.mul_by_w z ⦃ r =>
      (∀ x ∈ r.val, Valid x) ∧
        Spec.Mersenne31.toComplex r = Spec.Mersenne31.toComplex z * Mersenne31.Complex.mk 2 1 ⦄ := by
  have hlen : z.val.length = 2 := z.property
  have hre : Valid (z.val[0]'(by omega)) := hz _ (List.getElem_mem _)
  have him : Valid (z.val[1]'(by omega)) := hz _ (List.getElem_mem _)
  have h0 : Array.index_usize z 0#usize = .ok (z.val[0]'(by omega)) := eq_ok_of_spec (by step*)
  have h1 : Array.index_usize z 1#usize = .ok (z.val[1]'(by omega)) := eq_ok_of_spec (by step*)
  unfold extension.Mersenne31.mul_by_w
  rw [h0, h1]
  simp only [bind_ok]
  step with add.toField _ _ hre hre as ⟨a, ha1, ha2⟩
  step with sub.toField a _ ha1 him as ⟨a1, ha3, ha4⟩
  step with add.toField _ _ hre him as ⟨b, hb1, hb2⟩
  step with add.toField b _ hb1 him as ⟨b1, hb3, hb4⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Array.make_val, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · unfold Spec.Mersenne31.toComplex
    simp only [Array.make_val, List.getD_cons_zero, List.getD_cons_succ,
      List.getD_eq_getElem _ _ (show 0 < z.val.length by omega),
      List.getD_eq_getElem _ _ (show 1 < z.val.length by omega)]
    rw [Mersenne31.Complex.mk_mul, ha4, ha2, hb4, hb2]
    congr 1 <;> ring

end Plonky3Lean.Proofs.P3Mersenne31
