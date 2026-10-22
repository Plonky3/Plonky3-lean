module

public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Proofs.Field.Mersenne31.Field

@[expose] public section

/-!
# Mersenne31: `new_array`
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.P3Mersenne31

/-- After `i` iterations, the first `i` entries are reduced inputs. -/
def ArrInv {N : Std.Usize} (input : Array Std.U32 N) (output : Array Element N) (i : ℕ) : Prop :=
  i ≤ N.val ∧ ∀ j (_ : j < i) (h1 : j < output.val.length) (h2 : j < input.val.length),
    (output.val[j]'h1).value.val = (input.val[j]'h2).val % 2147483647

theorem new_array_loop.spec {N : Std.Usize} (input : Array Std.U32 N) (output : Array Element N)
    (i : Std.Usize) (h : ArrInv input output i.val) :
    mersenne_31.Mersenne31.new_array_loop input output i ⦃ r => ArrInv input r N.val ⦄ := by
  unfold mersenne_31.Mersenne31.new_array_loop
  refine loop.spec_decr_nat (fun p => N.val - p.2.val) (fun p => ArrInv input p.1 p.2.val) _ _ _ ?_ h
  rintro ⟨out, k⟩ ⟨hk, hinv⟩
  unfold mersenne_31.Mersenne31.new_array_loop.body
  rw [mersenne_31.P.eq]
  simp only at hk hinv
  step*
  · subst_vars
    have hkN : k.val < N.val := by scalar_tac
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    intro j hj h1 h2
    simp only [Array.set_val_eq] at h1 ⊢
    by_cases hjk : j = k.val
    · subst hjk; simp [List.getElem_set_self, i3_post]
    · rw [List.getElem_set_ne (Ne.symm hjk)]
      exact hinv j (by omega) (by simpa using h1) h2
  · have hkN : k.val = N.val := by scalar_tac
    refine ⟨le_rfl, fun j hj h1 h2 => hinv j (by omega) h1 h2⟩

/-- `new_array(input)` reduces each entry. -/
theorem new_array.spec {N : Std.Usize} (input : Array Std.U32 N) :
    mersenne_31.Mersenne31.new_array input ⦃ r =>
      ∀ j (h1 : j < r.val.length) (h2 : j < input.val.length),
        Canonical (r.val[j]'h1) ∧
          Spec.Mersenne31.toField (r.val[j]'h1) = ((input.val[j]'h2).val : Mersenne31.Field) ⦄ := by
  unfold mersenne_31.Mersenne31.new_array
  obtain ⟨out, hout⟩ := array_repeat_ok N mersenne_31.Mersenne31.Insts.CoreCloneClone
    (fun x => ⟨x, rfl⟩) _
  rw [hout, bind_ok]
  refine WP.spec_mono (new_array_loop.spec input _ 0#usize ⟨Nat.zero_le _, fun j hj => by
    simp at hj⟩) ?_
  rintro r ⟨-, hr⟩ j h1 h2
  have hj : j < N.val := by have := r.property; omega
  have := hr j hj h1 h2
  refine ⟨by unfold Canonical; rw [this]; exact Nat.mod_lt _ (by norm_num), ?_⟩
  unfold Spec.Mersenne31.toField
  rw [this, natCast_eq_iff]; omega

end Plonky3Lean.Proofs.P3Mersenne31
