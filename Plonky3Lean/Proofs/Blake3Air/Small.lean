module

public import Plonky3Lean.Proofs.Blake3Air.Row
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# The addition constraints over small fields

Soundness needs a characteristic above 3 * 2^16.

Below it, the addition constraints accept wrong sums.

```text
    p = 65537 = 2^16 + 1:      two operands,   0x00010001 = 0 + 0
    p = 131071 = 2^17 - 1:     three operands, 0 = 0xffff + 0xffff + 1
```

Both fields have more than 16 bits, which the AIR's own documentation allows.
-/

namespace Plonky3Lean.Proofs.Blake3Air

instance fact_prime_65537 : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

instance fact_prime_131071 : Fact (Nat.Prime 131071) := ⟨by norm_num⟩

/-- Over a field of 65537 elements, the two-operand constraints accept 2^16 + 1 = 0 + 0. -/
theorem add2C_accepts_wrong_sum :
    Add2C (F := ZMod 65537) (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧
      (1 + 2 ^ 16 * 1) % 2 ^ 32 ≠ (0 + 0 : ℕ) := by
  refine ⟨?_, by norm_num⟩
  simp only [Add2C]
  decide

/-- Over a field of 131071 elements, the three-operand constraints accept 0 = 65535 + 65535 + 1. -/
theorem add3C_accepts_wrong_sum :
    Add3C (F := ZMod 131071) (fun _ => 0) (fun l => if l = 0 then 65535 else 0)
        (fun l => if l = 0 then 65535 else 0) (fun l => if l = 0 then 1 else 0) ∧
      (0 : ℕ) ≠ (65535 + 65535 + 1) % 2 ^ 32 := by
  refine ⟨?_, by norm_num⟩
  simp only [Add3C, ite_true, one_ne_zero, ite_false]
  decide

end Plonky3Lean.Proofs.Blake3Air
