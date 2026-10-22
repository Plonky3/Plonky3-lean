import Plonky3Lean.Lib.RustM
import Plonky3Lean.Proofs.Field.Monty31.Element

/-!
# Monty31: multiplication by powers of two, for any valid parameters
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {FP : Type} {inst : data_traits.FieldParameters FP} {p mu : Std.U32}

/-- Entry `i` of `MONTY_POWERS_OF_TWO`, for `1 <= i < 64`, stores `2^i` in Montgomery form. -/
theorem monty_31.MontyField31.MONTY_POWERS_OF_TWO.spec (hv : FieldValid inst p mu)
    (hd : FieldDefaults inst) :
    monty_31.MontyField31.MONTY_POWERS_OF_TWO inst ⦃ t => ∀ i (h1 : 1 ≤ i) (h2 : i < 64),
      (t.val[i]'(by rw [t.property]; exact h2)).value.val = 2 ^ i * 2 ^ 32 % p.val ⦄ := by
  unfold monty_31.MontyField31.MONTY_POWERS_OF_TWO
  rw [hd.one]
  have hm := hv.monty
  obtain ⟨rest, hrest, hfa⟩ := mapM_forall₂
    (fun i => do
      let v ← utils.to_monty_64 inst.PackedMontyParametersInst.MontyParametersInst
        ⟨BitVec.ofNat 64 (2 ^ i)⟩
      monty_31.MontyField31.new_monty inst.PackedMontyParametersInst.MontyParametersInst v)
    (fun i r => i < 64 → r.value.val = 2 ^ i * 2 ^ 32 % p.val)
    (fun i => by
      have hv64 : ∀ hi : i < 64, (⟨BitVec.ofNat 64 (2 ^ i)⟩ : Std.U64).val = 2 ^ i := by
        intro hi
        show (BitVec.ofNat 64 (2 ^ i)).toNat = 2 ^ i
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)
      step*)
    (List.range' 1 63)
  step*
  rw [hrest]
  have hlen : rest.length = 63 := by rw [← hfa.length_eq]; simp
  have hlen' : (one :: rest).length = 64 := by simp [hlen]
  simp only [bind_tc_ok, hlen', _root_.dite_true, WP.spec_ok]
  intro i h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [List.getElem_cons_succ]
  have := (List.forall₂_iff_get.mp hfa).2 j (by simp; omega) (by omega)
  simp only [List.get_eq_getElem, List.getElem_range'] at this
  have h := this (by omega)
  rwa [show 1 + 1 * j = j + 1 by omega] at h

end Plonky3Lean.Proofs.Monty31

namespace Plonky3Lean.Proofs.Monty31

variable {FP : Type} {inst : data_traits.FieldParameters FP} {p mu : Std.U32}

/-- `2^32` is invertible modulo an odd `p`: a Montgomery product can be cancelled. -/
theorem cancel_monty {p a b : ℕ} (hodd : p % 2 = 1) (h : a * 2 ^ 32 ≡ b * 2 ^ 32 [MOD p]) :
    a ≡ b [MOD p] :=
  Nat.ModEq.cancel_right_of_coprime (c := 2 ^ 32)
    (Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.coprime_two_left).mpr
      (Nat.odd_iff.mpr hodd)))) h

/-- `mul_2exp_u64(a, exp)` for `2 <= exp < 64` multiplies a canonical `a` by `2^exp`:
`c ≡ a · 2^exp (mod p)` on the stored values, and `c` is canonical. -/
theorem monty_31.MontyField31.mul_2exp_u64.spec_lt (hv : FieldValid inst p mu)
    (hd : FieldDefaults inst) (a : monty_31.MontyField31 FP) (ha : a.value.val < p.val)
    (exp : Std.U64) (h2 : 2 ≤ exp.val) (h64 : exp.val < 64) :
    monty_31.MontyField31.mul_2exp_u64 inst a exp ⦃ c => c.value.val < p.val ∧
      c.value.val ≡ a.value.val * 2 ^ exp.val [MOD p.val] ⦄ := by
  unfold monty_31.MontyField31.mul_2exp_u64
  have hm := hv.monty
  have hp0 : 0 < p.val := by have := hm.odd; omega
  have h0 : exp ≠ 0#u64 := fun h => by subst h; simp at h2
  have h1 : exp ≠ 1#u64 := fun h => by subst h; simp at h2
  have hlt : exp < 64#u64 := by scalar_tac
  simp only [h0, h1, hlt, if_false, if_true]
  have ht := monty_31.MontyField31.MONTY_POWERS_OF_TWO.spec hv hd
  have hcast : (UScalar.cast .Usize exp).val = exp.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by
      cases System.Platform.numBits_eq <;> simp [*] <;> omega)
  step*
  rename_i x
  refine ⟨c_post1, cancel_monty hm.odd ?_⟩
  have hxv : x.value.val = 2 ^ exp.val * 2 ^ 32 % p.val := by
    rw [e_post2]; simp only [hcast]; exact table_post _ (by omega) h64
  show c.value.val * 2 ^ 32 % p.val = a.value.val * 2 ^ exp.val * 2 ^ 32 % p.val
  rw [c_post2, hxv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]

end Plonky3Lean.Proofs.Monty31
