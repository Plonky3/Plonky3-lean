import Plonky3Lean.Proofs.Field.Goldilocks.Constants
import Plonky3Lean.Proofs.Field.Goldilocks.Convert
import Plonky3Lean.Proofs.Field.Goldilocks.Field
import Plonky3Lean.Proofs.Field.Goldilocks.Inverse
import Plonky3Lean.Proofs.Field.Goldilocks.Sum
import ToCompPoly.Fields.Goldilocks

/-!
# Goldilocks: claims

What this repository asserts about p3-goldilocks's scalar arithmetic, at the Plonky3 commit pinned in `plonky3/`.

- The model is the scoped extraction in `crates/goldilocks`, with the transcriptions in its `Assumptions/Mirror.lean`.
- `Goldilocks.*` is CompPoly's field `ZMod p`, `p = 2^64 - 2^32 + 1`, extended by `ToCompPoly`.
- A stored `u64` stands for its residue mod `p` (`toField`).

Every claim holds for every stored `u64`, including the non-canonical range `[p, 2^64)`.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Never panicking covers each overflow-checked operation, each `unchecked_*` operation and each `assert_unchecked`.

Not claimed:
- exponentiation, `try_sqrt` and `injective_exp_root_n`;
- serialization and deserialization;
- the packed (SIMD) arithmetic and the extension fields;
- the Poseidon1 and Poseidon2 permutations and the MDS layer.
-/

open Aeneas Aeneas.Std CoreModels
open p3_goldilocks
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Claims.Goldilocks

/-! ## The modulus -/

/-- `ORDER_U64` (`0xFFFF_FFFF_0000_0001`) is CompPoly's `Goldilocks.fieldSize`. -/
theorem goldilocks.Goldilocks.ORDER_U64.eq_fieldSize :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64.val = Goldilocks.fieldSize :=
  Proofs.Goldilocks.ORDER_U64.val_eq

/-! ## Reduction and the operators -/

/-- `reduce128(x)` stands for `x`, for every `u128`. -/
theorem goldilocks.reduce128.toField (x : Std.U128) :
    goldilocks.reduce128 x ⦃ r => toField r = (x.val : Goldilocks.Field) ⦄ :=
  Proofs.Goldilocks.reduce128.field x

/-- `Add` is field addition. -/
theorem goldilocks.Goldilocks.add.toField (a b : Element) :
    goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add a b ⦃ r =>
      toField r = toField a + toField b ⦄ :=
  Proofs.Goldilocks.add.field a b

/-- `Sub` is field subtraction. -/
theorem goldilocks.Goldilocks.sub.toField (a b : Element) :
    goldilocks.Goldilocks.Insts.CoreOpsArithSubGoldilocksGoldilocks.sub a b ⦃ r =>
      toField r = toField a - toField b ⦄ :=
  Proofs.Goldilocks.sub.field a b

/-- `Mul` is field multiplication. -/
theorem goldilocks.Goldilocks.mul.toField (a b : Element) :
    goldilocks.Goldilocks.Insts.CoreOpsArithMulGoldilocksGoldilocks.mul a b ⦃ r =>
      toField r = toField a * toField b ⦄ :=
  Proofs.Goldilocks.mul.field a b

/-- `Neg` is field negation. -/
theorem goldilocks.Goldilocks.neg.toField (a : Element) :
    goldilocks.Goldilocks.Insts.CoreOpsArithNegGoldilocks.neg a ⦃ r => toField r = -toField a ⦄ :=
  Proofs.Goldilocks.neg.field a

/-- `halve` is division by `2`. -/
theorem goldilocks.Goldilocks.halve.toField (a : Element) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a ⦃ r =>
      toField r * 2 = toField a ⦄ :=
  Proofs.Goldilocks.halve.field a

/-- `mul_2exp_u64(a, e)` is `a * 2^e`, for every `u64` exponent. -/
theorem goldilocks.Goldilocks.mul_2exp_u64.toField (a : Element) (e : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e ⦃ r =>
      toField r = toField a * 2 ^ e.val ⦄ :=
  Proofs.Goldilocks.mul_2exp_u64.spec a e

/-- `div_2exp_u64(a, e)` is `a / 2^e`, for every `u64` exponent. -/
theorem goldilocks.Goldilocks.div_2exp_u64.toField (a : Element) (e : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e ⦃ r =>
      toField r * 2 ^ e.val = toField a ⦄ :=
  Proofs.Goldilocks.div_2exp_u64.spec a e

/-- `POWERS_OF_TWO[j] = 2^j mod p`, for every `j < 96`. -/
theorem goldilocks.Goldilocks.POWERS_OF_TWO.eq :
    goldilocks.Goldilocks.POWERS_OF_TWO ⦃ r => ∀ j < 96,
      ∃ x, r.val[j]? = some x ∧ x.value.val = 2 ^ j % Goldilocks.fieldSize ⦄ :=
  Proofs.Goldilocks.POWERS_OF_TWO.spec

/-- `try_inverse` returns `None` exactly on zero, and the inverse otherwise. -/
theorem goldilocks.Goldilocks.try_inverse.toField (a : Element) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      match r with
      | .None => toField a = 0
      | .Some y => toField y * toField a = 1 ⦄ :=
  Proofs.Goldilocks.try_inverse.spec a

/-! ## Comparisons -/

/-- `as_canonical_u64` returns the canonical representative of the field element. -/
theorem goldilocks.Goldilocks.as_canonical_u64.toField (a : Element) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 a ⦃ r =>
      (r.val : Goldilocks.Field) = toField a ∧ r.val < Goldilocks.fieldSize ⦄ :=
  Proofs.Goldilocks.as_canonical_u64.field a

/-- `PartialEq::eq` compares field elements, so `x` and `x + p` are equal. -/
theorem goldilocks.Goldilocks.eq.toField (a b : Element) :
    goldilocks.Goldilocks.Insts.CoreCmpPartialEqGoldilocks.eq a b ⦃ r =>
      r = decide (toField a = toField b) ⦄ :=
  Proofs.Goldilocks.eq.field a b

/-- `Ord::cmp` compares canonical representatives. -/
theorem goldilocks.Goldilocks.cmp.canonical (a b : Element) :
    goldilocks.Goldilocks.Insts.CoreCmpOrd.cmp a b ⦃ r =>
      r = (match compare (a.value.val % Goldilocks.fieldSize) (b.value.val % Goldilocks.fieldSize) with
        | .lt => core.cmp.Ordering.Less
        | .eq => core.cmp.Ordering.Equal
        | .gt => core.cmp.Ordering.Greater) ⦄ :=
  Proofs.Goldilocks.cmp.spec a b

/-- `is_zero` tests the field element, so it accepts both stored zeros, `0` and `p`. -/
theorem goldilocks.Goldilocks.is_zero.toField (a : Element) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.is_zero a ⦃ r => r = decide (toField a = 0) ⦄ :=
  Proofs.Goldilocks.is_zero.field a

/-! ## Integer conversions -/

/-- `from_int` on a `u64` stores the integer. -/
theorem goldilocks.Goldilocks.from_int_u64.value (int : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_int int ⦃ r => r.value = int ⦄ :=
  Proofs.Goldilocks.U64.from_int.spec int

/-- `from_int` on a `u128` stands for the integer, and is canonical. -/
theorem goldilocks.Goldilocks.from_int_u128.toField (int : Std.U128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int int ⦃ r =>
      toField r = int.val ∧ Canonical r ⦄ :=
  Proofs.Goldilocks.U128.from_int.field int

/-- `from_int` on an `i64` stands for the integer, and is canonical. -/
theorem goldilocks.Goldilocks.from_int_i64.toField (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_int int ⦃ r =>
      toField r = (int.val : Goldilocks.Field) ∧ Canonical r ⦄ :=
  Proofs.Goldilocks.I64.from_int.spec int

/-- `from_int` on an `i128` stands for the integer. -/
theorem goldilocks.Goldilocks.from_int_i128.toField (int : Std.I128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_int int ⦃ r =>
      toField r = (int.val : Goldilocks.Field) ⦄ :=
  Proofs.Goldilocks.I128.from_int.spec int

/-- `from_canonical_checked` on a `u64` accepts exactly the integers below `p`. -/
theorem goldilocks.Goldilocks.from_canonical_checked_u64.eq (int : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked int ⦃ r =>
      r = if int.val < Goldilocks.fieldSize then .Some ⟨int⟩ else .None ⦄ :=
  Proofs.Goldilocks.U64.from_canonical_checked.spec int

/-- `from_canonical_checked` on a `u128` accepts exactly the integers below `p`. -/
theorem goldilocks.Goldilocks.from_canonical_checked_u128.eq (int : Std.U128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked int ⦃ r =>
      r = if int.val < Goldilocks.fieldSize then .Some ⟨UScalar.cast .U64 int⟩ else .None ⦄ :=
  Proofs.Goldilocks.U128.from_canonical_checked.spec int

/-- `from_canonical_checked` on an `i64` accepts exactly `[-(p - 1)/2, (p - 1)/2]`. -/
theorem goldilocks.Goldilocks.from_canonical_checked_i64.toField (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked int ⦃ r =>
      match r with
      | .Some x => -9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160 ∧
          toField x = (int.val : Goldilocks.Field)
      | .None => ¬ (-9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160) ⦄ :=
  Proofs.Goldilocks.I64.from_canonical_checked.spec int

/-- `from_canonical_checked` on an `i128` accepts exactly `[-(p - 1)/2, (p - 1)/2]`. -/
theorem goldilocks.Goldilocks.from_canonical_checked_i128.toField (int : Std.I128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked int ⦃ r =>
      match r with
      | .Some x => -9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160 ∧
          toField x = (int.val : Goldilocks.Field)
      | .None => ¬ (-9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160) ⦄ :=
  Proofs.Goldilocks.I128.from_canonical_checked.spec int

/-- `from_canonical_unchecked` on a `u128` stands for the integer, on its documented range `[0, 2^64)`. -/
theorem goldilocks.Goldilocks.from_canonical_unchecked_u128.toField (int : Std.U128)
    (h : int.val < 2 ^ 64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_unchecked int ⦃ r =>
      toField r = int.val ⦄ :=
  Proofs.Goldilocks.U128.from_canonical_unchecked.spec int h

/-- `from_canonical_unchecked` on an `i64` stands for the integer, on every input. -/
theorem goldilocks.Goldilocks.from_canonical_unchecked_i64.toField (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked int ⦃ r =>
      toField r = (int.val : Goldilocks.Field) ⦄ :=
  Proofs.Goldilocks.I64.from_canonical_unchecked.spec int

/-- `from_canonical_unchecked` on an `i128` stands for the integer on `[-2^63, 2^63)`. -/
theorem goldilocks.Goldilocks.from_canonical_unchecked_i128.toField (int : Std.I128)
    (h0 : -2 ^ 63 ≤ int.val) (h1 : int.val < 2 ^ 63) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked int ⦃ r =>
      toField r = (int.val : Goldilocks.Field) ⦄ :=
  Proofs.Goldilocks.I128.from_canonical_unchecked.spec int h0 h1

/-- Its documented range `[1 + 2^32 - 2^64, 2^64 - 1]` is too wide.

At `2^64 - 1` the result stands for `-1`, not for `2^64 - 1`. -/
theorem goldilocks.Goldilocks.from_canonical_unchecked_i128.doc_range_counterexample :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked
      18446744073709551615#i128 ⦃ r =>
      Spec.Goldilocks.toField r = -1 ∧
        Spec.Goldilocks.toField r ≠ ((18446744073709551615 : ℤ) : Goldilocks.Field) ⦄ :=
  Proofs.Goldilocks.I128.from_canonical_unchecked.doc_range_counterexample

/-! ## Constants -/

/-- `TWO_ADIC_GENERATORS[i]` has order `2^i` and squares to the entry before it. -/
theorem goldilocks.Goldilocks.TWO_ADIC_GENERATORS.order :
    goldilocks.Goldilocks.TWO_ADIC_GENERATORS ⦃ r => r.val.length = 33 ∧
      (∀ i (h : i < r.val.length), orderOf (toField r.val[i]) = 2 ^ i) ∧
      (∀ i (h : i + 1 < r.val.length), toField r.val[i + 1] ^ 2 = toField r.val[i]) ⦄ :=
  Proofs.Goldilocks.TWO_ADIC_GENERATORS.order

/-- `two_adic_generator(bits)` has order `2^bits`, for `bits <= TWO_ADICITY = 32`. -/
theorem goldilocks.Goldilocks.two_adic_generator.order (bits : Std.Usize) (h : bits.val ≤ 32) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator bits ⦃ r =>
      orderOf (toField r) = 2 ^ bits.val ⦄ :=
  Proofs.Goldilocks.two_adic_generator.spec bits h

/-- `two_adic_generator(bits)` panics for `bits > 32`. -/
theorem goldilocks.Goldilocks.two_adic_generator.panics (bits : Std.Usize) (h : 32 < bits.val) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator bits = .fail .panic :=
  Proofs.Goldilocks.two_adic_generator.panics bits h

/-- `GENERATOR` is `7`, which generates the multiplicative group. -/
theorem goldilocks.Goldilocks.GENERATOR.generates :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.GENERATOR ⦃ r =>
      orderOf (toField r) = Goldilocks.fieldSize - 1 ⦄ :=
  WP.spec_mono Proofs.Goldilocks.GENERATOR.spec
    (fun _ hr => by rw [hr]; exact Goldilocks.orderOf_generator)

/-- `NEG_ONE` is `-1`, stored canonically. -/
theorem goldilocks.Goldilocks.NEG_ONE.toField :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE ⦃ r =>
      toField r = -1 ∧ Canonical r ⦄ :=
  Proofs.Goldilocks.NEG_ONE.spec

/-! ## Sums and dot products -/

/-- `Sum::sum` over fewer than `2^64` items returns their field sum. -/
theorem goldilocks.Goldilocks.sum.toField (xs : List Element) (h : xs.length < 2 ^ 64) :
    goldilocks.Goldilocks.Insts.CoreIterTraitsAccumSumGoldilocks.sum xs ⦃ r =>
      toField r = (xs.map toField).sum ⦄ :=
  Proofs.Goldilocks.sum.spec xs (Proofs.Goldilocks.sum_lt_of_length xs h)

/-- `sum_array::<N>` returns the field sum of its `N` inputs. -/
theorem goldilocks.Goldilocks.sum_array.toField (N : Std.Usize) (input : Slice Element)
    (hN : N.val = input.val.length) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.sum_array N input ⦃ r =>
      toField r = (input.val.map toField).sum ⦄ :=
  Proofs.Goldilocks.sum_array.spec N input hN

/-- `dot_product::<N>` returns the field dot product, for `N <= 2^31`. -/
theorem goldilocks.Goldilocks.dot_product.toField {N : Std.Usize} (lhs rhs : Array Element N)
    (hN : N.val ≤ 2 ^ 31) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product lhs rhs ⦃ r =>
      toField r = ((List.zip lhs.val rhs.val).map (fun xy => toField xy.1 * toField xy.2)).sum ⦄ :=
  Proofs.Goldilocks.dot_product.spec lhs rhs hN

/-- The `const` check of `dot_product` does not enforce `N <= 2^31`.

It compares `N as u32`, which passes at `N = 2^32 + 3`.

There the top-bit accumulator can reach `2^64`, where its `unchecked_add` overflows. -/
theorem goldilocks.Goldilocks.dot_product.const_check_truncates (N : Std.Usize)
    (h : N.val = 2 ^ 32 + 3) :
    (UScalar.cast .U32 N).val ≤ 2 ^ 31 ∧ 2 ^ 64 ≤ N.val * (2 ^ 32 - 1) :=
  Proofs.Goldilocks.dot_product.const_check_truncates N h

end Plonky3Lean.Claims.Goldilocks
