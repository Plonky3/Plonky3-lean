module

public import Plonky3Lean.Proofs.Field.Binary.Tower

@[expose] public section

/-!
# The binary tower's arithmetic, as field arithmetic

`Tower` computes each level's operations on natural numbers. Here those values become elements
of CompPoly's `ConcreteBTField k`, read through `towerOf k`, which keeps the low `2^k` bits.

Every statement holds for every input: the operations only read the low `2^k` bits.
-/

open Aeneas Aeneas.Std
open ConcreteBinaryTower
open Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The high half of the low `2^(k+1)` bits is the high half. -/
theorem high_half_mod (a k : ℕ) :
    ((a % 2 ^ 2 ^ (k + 1)) >>> 2 ^ k) % 2 ^ 2 ^ k = (a >>> 2 ^ k) % 2 ^ 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 2 ^ k
  · have : 2 ^ k + i < 2 ^ (k + 1) := by rw [pow_succ]; omega
    simp [hi, this]
  · simp [hi]

/-- The low half of the low `2^(k+1)` bits is the low half. -/
theorem low_half_mod (a k : ℕ) :
    (a % 2 ^ 2 ^ (k + 1) &&& (2 ^ 2 ^ k - 1)) % 2 ^ 2 ^ k = (a &&& (2 ^ 2 ^ k - 1)) % 2 ^ 2 ^ k := by
  rw [and_sub_one_mod, and_sub_one_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- Above level `0`, the product reads only the low `2^k` bits of its operands. -/
theorem towerMul_succ_mod (k a b : ℕ) :
    towerMul (k + 1) a b = towerMul (k + 1) (a % 2 ^ 2 ^ (k + 1)) (b % 2 ^ 2 ^ (k + 1)) := by
  simp only [towerMul, high_half_mod, low_half_mod]

/-- The product, reduced to the level's width, is the product of the reduced operands. -/
theorem towerMul_mod (k a b : ℕ) :
    towerMul k a b % 2 ^ 2 ^ k = towerMul k (a % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k) := by
  cases k with
  | zero =>
    simp only [towerMul]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_and]
    cases decide (i < 2 ^ 0) <;> simp
  | succ k =>
    rw [towerMul_succ_mod]
    exact Nat.mod_eq_of_lt
      (towerMul_lt _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)))

/-- A value computed as `towerMul k a b` stands for the product of what `a` and `b` stand for. -/
theorem towerOf_mul {k : ℕ} {ty₁ ty₂ ty₃ : UScalarTy} {y : UScalar ty₁} {a : UScalar ty₂}
    {b : UScalar ty₃} (h : y.val = towerMul k a.val b.val) :
    towerOf k y = towerOf k a * towerOf k b := by
  apply ConcreteBTField.toNat_injective
  rw [show towerOf k a * towerOf k b = concrete_mul (towerOf k a) (towerOf k b) from rfl,
    toNat_concrete_mul]
  simp only [towerOf, ConcreteBTField.toNat_fromNat, h, towerMul_mod]

/-- A value computed as `towerMul k x (zNat k)` stands for `x` times the level's generator
`Z k`. -/
theorem towerOf_mul_Z {k : ℕ} {ty₁ ty₂ : UScalarTy} {y : UScalar ty₁} {x : UScalar ty₂}
    (h : y.val = towerMul k x.val (zNat k)) : towerOf k y = towerOf k x * Z k := by
  apply ConcreteBTField.toNat_injective
  rw [show towerOf k x * Z k = concrete_mul (towerOf k x) (Z k) from rfl, toNat_concrete_mul,
    toNat_Z]
  simp only [towerOf, ConcreteBTField.toNat_fromNat, h, towerMul_mod,
    Nat.mod_eq_of_lt (zNat_lt k)]

/-- A value computed as `a ^^^ b` stands for the sum of what `a` and `b` stand for. -/
theorem towerOf_add {k : ℕ} {ty₁ ty₂ ty₃ : UScalarTy} {y : UScalar ty₁} {a : UScalar ty₂}
    {b : UScalar ty₃} (h : y.val = a.val ^^^ b.val) :
    towerOf k y = towerOf k a + towerOf k b := by
  apply ConcreteBTField.toNat_injective
  simp only [toNat_add, towerOf, ConcreteBTField.toNat_fromNat, h, Nat.xor_mod_two_pow]

/-- A value computed as `a ^^^ b` stands for the difference of what `a` and `b` stand for. -/
theorem towerOf_sub {k : ℕ} {ty₁ ty₂ ty₃ : UScalarTy} {y : UScalar ty₁} {a : UScalar ty₂}
    {b : UScalar ty₃} (h : y.val = a.val ^^^ b.val) :
    towerOf k y = towerOf k a - towerOf k b := by
  rw [CharTwo.sub_eq_add]
  exact towerOf_add h

/-- A value equal to `a` stands for the negation of what `a` stands for. -/
theorem towerOf_neg {k : ℕ} {ty₁ ty₂ : UScalarTy} {y : UScalar ty₁} {a : UScalar ty₂}
    (h : y.val = a.val) : towerOf k y = -towerOf k a := by
  rw [CharTwo.neg_eq]
  simp only [towerOf, h]

/-- A value computed as `r % 2^(2^k)` stands for what `r` stands for. -/
theorem towerOf_mod {k : ℕ} {ty₁ ty₂ : UScalarTy} {y : UScalar ty₁} {r : UScalar ty₂}
    (h : y.val = r.val % 2 ^ 2 ^ k) : towerOf k y = towerOf k r := by
  apply ConcreteBTField.toNat_injective
  simp only [towerOf, ConcreteBTField.toNat_fromNat, h, Nat.mod_mod]

end Plonky3Lean.Proofs.Binary
