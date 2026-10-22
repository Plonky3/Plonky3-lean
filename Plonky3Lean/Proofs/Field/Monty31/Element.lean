module

public import Plonky3Lean.Proofs.Field.Monty31.Reduce

@[expose] public section

/-!
# Monty31: field elements, for any valid parameters

The constructor and the multiplication of `MontyField31`, read through `toField`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-- `MontyField31::new(x)` passes its four parameter checks.

It stores `x · 2^32 mod p`, for every `u32` input. -/
@[step]
theorem monty_31.MontyField31.new.spec (hv : Valid inst p mu) (x : Std.U32) :
    monty_31.MontyField31.new inst x ⦃ r => r.value.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold monty_31.MontyField31.new
  rw [hv.prime, hv.bits, hv.monty_mu]
  have hp := hv.lt
  have hodd := hv.odd
  have hinv := hv.inv
  step*

end Plonky3Lean.Proofs.Monty31

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-- `new_monty` stores its argument unchanged. -/
@[step]
theorem monty_31.MontyField31.new_monty.spec (x : Std.U32) :
    monty_31.MontyField31.new_monty inst x ⦃ r => r.value = x ⦄ := by
  simp [monty_31.MontyField31.new_monty]

/-- `a * b` of canonical elements is canonical, and is the Montgomery product:
`c · 2^32 ≡ a · b (mod p)` on the stored values.

The `u64` product cannot overflow, and is below `2^32 · p` as `monty_reduce` requires. -/
@[step]
theorem monty_31.MontyField31.mul.spec (hv : Valid inst p mu) (a b : monty_31.MontyField31 MP)
    (ha : a.value.val < p.val) (hb : b.value.val < p.val) :
    monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul inst a b ⦃ c => c.value.val < p.val ∧
      c.value.val * 2 ^ 32 % p.val = a.value.val * b.value.val % p.val ⦄ := by
  unfold monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
  have hp := hv.lt
  have hab : a.value.val * b.value.val < 2 ^ 32 * p.val := by
    calc a.value.val * b.value.val < p.val * p.val := Nat.mul_lt_mul'' ha hb
      _ ≤ 2 ^ 32 * p.val := Nat.mul_le_mul_right _ (by omega)
  step*

end Plonky3Lean.Proofs.Monty31
