module

public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Lib.RustM
public import Plonky3Lean.Proofs.Field.Monty31.Arith
public import Plonky3Lean.Proofs.Field.Monty31.Convert

@[expose] public section

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
  have hp0 : 0 < p.val := by have := hm.odd; omega
  step*
  obtain ⟨arr, harr⟩ := array_repeat_ok 64#usize _
    (fun x => ⟨x, monty_31.MontyField31.clone.eq _ x⟩) mf
  rw [harr, bind_ok]
  unfold monty_31.MontyField31.MONTY_POWERS_OF_TWO_loop
  apply loop.spec_decr_nat (fun (x : _ × Std.Usize) => 64 - x.2.val)
    (fun x => 1 ≤ x.2.val ∧ x.2.val ≤ 64 ∧ ∀ j (h1 : 1 ≤ j) (h2 : j < x.2.val) (h3 : j < 64),
      (x.1.val[j]'(by rw [x.1.property]; exact h3)).value.val = 2 ^ j * 2 ^ 32 % p.val)
  · rintro ⟨t, k⟩ ⟨hk1, hk64, hk⟩
    unfold monty_31.MontyField31.MONTY_POWERS_OF_TWO_loop.body
    simp only at hk1 hk64 hk ⊢
    split
    · rename_i hlt
      have hk64' : k.val < 64 := by scalar_tac
      step*
      rename mf.value = i2 => hmf
      have hi1 : i1.val = 2 ^ k.val := by
        rw [i1_post, Nat.one_shiftLeft, show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits]]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk64')
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j h1 h2 h3
      subst a_post
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rename_i hjk
        subst hjk
        rw [hmf, i2_post, hi1]
      · exact hk j h1 (by omega) h3
    · rename_i hge
      have hk' : k.val = 64 := by scalar_tac
      refine (WP.spec_ok _).mpr fun j h1 h3 => hk j h1 (by omega) h3
  · exact ⟨by simp, by simp, fun j h1 h2 => by simp at h2; omega⟩

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
  simp only [h0, h1, hlt, ite_false, ite_true]
  have ht := monty_31.MontyField31.MONTY_POWERS_OF_TWO.spec hv hd
  have hcast : (UScalar.cast .Usize exp).val = exp.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by
      cases System.Platform.numBits_eq <;> simp [*] <;> omega)
  step*
  refine ⟨c_post, cancel_monty hm.odd ?_⟩
  have hxv : e.value.val = 2 ^ exp.val * 2 ^ 32 % p.val := by
    rw [e_post1]; simp only [hcast]; exact table_post _ (by omega) h64
  show c.value.val * 2 ^ 32 % p.val = a.value.val * 2 ^ exp.val * 2 ^ 32 % p.val
  rw [c_post1, hxv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]

end Plonky3Lean.Proofs.Monty31
