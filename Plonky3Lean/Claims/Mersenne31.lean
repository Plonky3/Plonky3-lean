import Plonky3Lean.Proofs.Field.Mersenne31.Complex
import Plonky3Lean.Proofs.Field.Mersenne31.DotProductLoop
import Plonky3Lean.Proofs.Field.Mersenne31.Sum

/-!
# Mersenne31: claims

What this repository asserts about p3-mersenne-31, at the Plonky3 commit pinned in `plonky3/`.

- The model is the scoped extraction in `crates/mersenne-31`, rooted at the module that pre-patch `010-extraction-roots` adds.
- The `Complex<Mersenne31>` constants, `mul_by_w` and `Sum::sum` are transcriptions, in its `Assumptions/Mirror.lean`.
- `Mersenne31.*` is CompPoly's field `ZMod p`, `p = 2^31 - 1`, extended by `ToCompPoly`.
- A stored `u32` stands for its residue mod `p` (`toField`).
- `Valid` is the invariant the Rust maintains: the stored value fits in 31 bits.

So `p` itself is a valid stored value, a second representation of zero.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Never panicking covers each overflow-checked operation and each `debug_assert!`.

Not claimed:
- exponentiation, `try_sqrt`, `injective_exp_root_n`, `sum_array` and `new_array`;
- serialization, hashing and sampling;
- the packed (SIMD) arithmetic;
- the generic extension-field arithmetic of p3-field, and the `EXT_GENERATOR`s of QM31 and of the cubic extension of `F[i]`;
- the Poseidon1 and Poseidon2 permutations, the MDS layer and the DFTs.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31
open Polynomial

namespace Plonky3Lean.Claims.Mersenne31

/-! ## The modulus -/

/-- `P` (`(1 << 31) - 1`) is CompPoly's `Mersenne31.fieldSize`. -/
theorem mersenne_31.P.eq_fieldSize :
    mersenne_31.P = .ok 2147483647#u32 ∧ (2147483647#u32).val = Mersenne31.fieldSize :=
  ⟨Proofs.Mersenne31.mersenne_31.P.eq, rfl⟩

/-! ## Constructors and readers -/

/-- `new(x)` reduces every `u32` to its canonical residue. -/
theorem mersenne_31.Mersenne31.new.toField (x : Std.U32) :
    mersenne_31.Mersenne31.new x ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.new.toField x

/-- `new_checked(x)` accepts exactly the `x < 2^31`, and stores `x` unreduced.

So `new_checked(p)` stores `p`, the second representation of zero. -/
theorem mersenne_31.Mersenne31.new_checked.toField (x : Std.U32) :
    mersenne_31.Mersenne31.new_checked x ⦃ r =>
      match r with
      | .Some y => x.val < 2 ^ 31 ∧ y.value = x ∧ Valid y ∧ toField y = (x.val : Mersenne31.Field)
      | .None => 2 ^ 31 ≤ x.val ⦄ :=
  Proofs.Mersenne31.new_checked.toField x

/-- `as_canonical_u32` returns the canonical residue, also for the stored value `p`. -/
theorem mersenne_31.Mersenne31.as_canonical_u32.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.as_canonical_u32 a
      ⦃ r => r.val < Mersenne31.fieldSize ∧ (r.val : Mersenne31.Field) = toField a ⦄ :=
  Proofs.Mersenne31.as_canonical_u32.toField a ha

/-- `PartialEq` is field equality, so `0` and `p` are equal. -/
theorem mersenne_31.Mersenne31.eq.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreCmpPartialEqMersenne31.eq a b
      ⦃ r => r = decide (toField a = toField b) ⦄ :=
  Proofs.Mersenne31.eq.toField a b ha hb

/-- `is_zero` recognises both representations of zero. -/
theorem mersenne_31.Mersenne31.is_zero.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.is_zero a ⦃ r => r = decide (toField a = 0) ⦄ :=
  Proofs.Mersenne31.is_zero.toField a ha

/-- `from_bool(b)` is `1` or `0`. -/
theorem mersenne_31.Mersenne31.from_bool.toField (b : Bool) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b
      ⦃ r => Canonical r ∧ toField r = if b then 1 else 0 ⦄ :=
  Proofs.Mersenne31.from_bool.toField b

/-! ## Arithmetic

Each operation keeps the invariant and is the field operation. -/

/-- `Add` is field addition. -/
theorem mersenne_31.Mersenne31.add.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add a b
      ⦃ r => Valid r ∧ toField r = toField a + toField b ⦄ :=
  Proofs.Mersenne31.add.toField a b ha hb

/-- `Sub` is field subtraction. -/
theorem mersenne_31.Mersenne31.sub.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithSubMersenne31Mersenne31.sub a b
      ⦃ r => Valid r ∧ toField r = toField a - toField b ⦄ :=
  Proofs.Mersenne31.sub.toField a b ha hb

/-- `Neg` is field negation. -/
theorem mersenne_31.Mersenne31.neg.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithNegMersenne31.neg a
      ⦃ r => Valid r ∧ toField r = -toField a ⦄ :=
  Proofs.Mersenne31.neg.toField a ha

/-- `Mul` is field multiplication. -/
theorem mersenne_31.Mersenne31.mul.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul a b
      ⦃ r => Valid r ∧ toField r = toField a * toField b ⦄ :=
  Proofs.Mersenne31.mul.toField a b ha hb

/-- `halve` is division by `2`. -/
theorem mersenne_31.Mersenne31.halve.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a
      ⦃ r => Valid r ∧ toField r * 2 = toField a ⦄ :=
  Proofs.Mersenne31.halve.toField a ha

/-- `mul_2exp_u64(a, e)`, a 31-bit left rotation, is `a · 2^e` for every `u64` exponent. -/
theorem mersenne_31.Mersenne31.mul_2exp_u64.toField (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e
      ⦃ r => Valid r ∧ toField r = toField a * 2 ^ e.val ⦄ :=
  Proofs.Mersenne31.mul_2exp_u64.toField a ha e

/-- `div_2exp_u64(a, e)`, a 31-bit right rotation, is `a / 2^e` for every `u64` exponent. -/
theorem mersenne_31.Mersenne31.div_2exp_u64.toField (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e
      ⦃ r => Valid r ∧ toField r * 2 ^ e.val = toField a ⦄ :=
  Proofs.Mersenne31.div_2exp_u64.toField a ha e

/-- `try_inverse` returns `None` exactly on zero, and the inverse otherwise. -/
theorem mersenne_31.Mersenne31.try_inverse.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      match r with
      | .None => toField a = 0
      | .Some y => Valid y ∧ toField y = (toField a)⁻¹ ⦄ :=
  Proofs.Mersenne31.try_inverse.toField Proofs.Mersenne31.gcdInversionContract a ha

/-! ## Reduction and accumulation -/

/-- `reduce_64(x)` is the canonical residue of every `u64`, stricter than its doc's `[0, P]`. -/
theorem mersenne_31.reduce_64.spec (x : Std.U64) :
    mersenne_31.reduce_64 x ⦃ r => r.val = x.val % Mersenne31.fieldSize ⦄ :=
  Proofs.Mersenne31.reduce_64.spec x

/-- `partial_reduce(x)` is congruent to `x` and below `2^34`, for every `u64`. -/
theorem mersenne_31.partial_reduce.spec (x : Std.U64) :
    mersenne_31.partial_reduce x ⦃ r =>
      r.val = x.val % 2 ^ 31 + x.val / 2 ^ 31 ∧ r.val % Mersenne31.fieldSize = x.val % Mersenne31.fieldSize ⦄ :=
  Proofs.Mersenne31.partial_reduce.spec x

/-- `from_u62(x)` is valid and congruent to `x` for `x < 2^62`. -/
theorem mersenne_31.from_u62.spec (x : Std.U64) (hx : x.val < 2 ^ 62) :
    mersenne_31.from_u62 x ⦃ r => Valid r ∧ r.value.val % Mersenne31.fieldSize = x.val % Mersenne31.fieldSize ⦄ :=
  Proofs.Mersenne31.from_u62.spec x hx

/-- `Sum::sum` is the field sum while the stored values add up to less than `2^62`. -/
theorem mersenne_31.Mersenne31.sum.toField (l : List Element)
    (hs : (l.map fun x => x.value.val).sum < 2 ^ 62) :
    mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum l ⦃ r =>
      Valid r ∧ toField r = (l.map toField).sum ⦄ :=
  Proofs.Mersenne31.sum.toField l hs

/-- At most `2^31 + 1` valid items add up to less than `2^62`. -/
theorem mersenne_31.Mersenne31.sum.length_bound (l : List Element) (hl : ∀ x ∈ l, Valid x)
    (hn : l.length ≤ 2 ^ 31 + 1) : (l.map fun x => x.value.val).sum < 2 ^ 62 :=
  Proofs.Mersenne31.valSum_lt l hl hn

/-- `Sum::sum` panics, in a debug build, once the stored values add up to `2^62`.

`2^31 + 3` copies of `-1` reach it. -/
theorem mersenne_31.Mersenne31.sum.panics (l : List Element)
    (hs : 2 ^ 62 ≤ (l.map fun x => x.value.val).sum) (hs' : (l.map fun x => x.value.val).sum < 2 ^ 64) :
    mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum l = .fail .panic :=
  Proofs.Mersenne31.sum.panics l hs hs'

/-- `dot_product` is the field dot product, for `N < 2^30`. -/
theorem mersenne_31.Mersenne31.dot_product.toField {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (hN : N.val < 2 ^ 30) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product lhs rhs ⦃ r =>
      Valid r ∧ toField r = ((List.range N.val).map fun j =>
        toField (lhs.val.getD j ⟨0#u32⟩) * toField (rhs.val.getD j ⟨0#u32⟩)).sum ⦄ :=
  Proofs.Mersenne31.dot_product.toField lhs rhs hl hr hN

/-! ## Integer conversions -/

/-- `from_int::<u32>` is the residue, for every `u32`. -/
theorem mersenne_31.Mersenne31.from_int_u32.toField (x : Std.U32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_u32.toField x

/-- `from_int::<u64>` is the canonical residue, for every `u64`. -/
theorem mersenne_31.Mersenne31.from_int_u64.toField (x : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_int x
      ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_u64.toField x

/-- `from_int::<u128>` is the canonical residue, for every `u128`. -/
theorem mersenne_31.Mersenne31.from_int_u128.toField (x : Std.U128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_int x
      ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_u128.toField x

/-- `from_int::<i32>` is the residue, for every `i32`, `i32::MIN` included. -/
theorem mersenne_31.Mersenne31.from_int_i32.toField (x : Std.I32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_i32.toField x

/-- `from_int::<i64>` is the residue, for every `i64`, `i64::MIN` included. -/
theorem mersenne_31.Mersenne31.from_int_i64.toField (x : Std.I64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_i64.toField x

/-- `from_int::<i128>` is the residue, for every `i128`, `i128::MIN` included. -/
theorem mersenne_31.Mersenne31.from_int_i128.toField (x : Std.I128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ :=
  Proofs.Mersenne31.from_int_i128.toField x

/-- `from_canonical_checked::<i64>` accepts exactly `(-2^30, 2^30)`.

Its doc comment claims `[-2^30, 2^30]`. -/
theorem mersenne_31.Mersenne31.from_canonical_checked_i64.spec (x : Std.I64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => -1073741824 < x.val ∧ x.val < 1073741824 ∧ Valid y ∧
            (y.value.val : Int) % 2147483647 = x.val % 2147483647
        | .None => ¬ (-1073741824 < x.val ∧ x.val < 1073741824) ⦄ :=
  Proofs.Mersenne31.from_canonical_checked_i64.spec x

/-- `from_canonical_unchecked::<u32>` stores `x` for `x < p`. -/
theorem mersenne_31.Mersenne31.from_canonical_unchecked_u32.spec (x : Std.U32)
    (hx : x.val < Mersenne31.fieldSize) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked x
      ⦃ r => r.value = x ⦄ :=
  Proofs.Mersenne31.from_canonical_unchecked_u32.spec x hx

/-- `from_canonical_unchecked::<u32>(2^31 - 1)` panics in a debug build.

Its doc comment allows `[0, 2^31 - 1]`. -/
theorem mersenne_31.Mersenne31.from_canonical_unchecked_u32.panics_at_p :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked
      2147483647#u32 = .fail .panic :=
  Proofs.Mersenne31.from_canonical_unchecked_u32.panics_at_p

/-! ## Base-field constants -/

/-- `GENERATOR` (`7`) generates the multiplicative group. -/
theorem mersenne_31.Mersenne31.GENERATOR.order :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.GENERATOR ⦃ g =>
      Canonical g ∧ orderOf (toField g) = Mersenne31.fieldSize - 1 ⦄ :=
  Proofs.Mersenne31.GENERATOR.toField

/-- `NEG_ONE` is `-1`. -/
theorem mersenne_31.Mersenne31.NEG_ONE.toField :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE ⦃ g =>
      Canonical g ∧ toField g = -1 ⦄ :=
  Proofs.Mersenne31.NEG_ONE.toField

/-- `x ↦ x^1717986917`, the root that `injective_exp_root_n` computes, inverts `x ↦ x^5`. -/
theorem mersenne_31.Mersenne31.injective_exp_root_n.exponent (x : Mersenne31.Field) :
    (x ^ 1717986917) ^ 5 = x :=
  Mersenne31.pow_1717986917_pow_five x

/-! ## The complex extension `F[i]`, `i^2 = -1` -/

/-- Entry `k` of `EXT_TWO_ADIC_GENERATORS` has order `2^k`. -/
theorem mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS.order :
    mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS ⦃ t =>
      ∀ k (hk : k < 33), orderOf (toComplex (t.val[k]'(by rw [t.property]; exact hk))) = 2 ^ k ⦄ :=
  Proofs.Mersenne31.EXT_TWO_ADIC_GENERATORS.order

/-- `ext_two_adic_generator(bits)` has order `2^bits` for `bits ≤ 32`, and panics otherwise. -/
theorem mersenne_31.Mersenne31.ext_two_adic_generator.order (bits : Std.Usize) :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.ext_two_adic_generator bits
      ⦃ c => bits.val ≤ 32 ∧ orderOf (toComplex c) = 2 ^ bits.val ⦄ ∨
    (32 < bits.val ∧
      mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.ext_two_adic_generator
        bits = .fail .panic) :=
  Proofs.Mersenne31.ext_two_adic_generator.order bits

/-- Entry `k` of `CIRCLE_TWO_ADIC_GENERATORS` has order `2^k` and lies on the circle: its norm `z^(p + 1)` is `1`. -/
theorem complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS.order :
    complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS ⦃ t =>
      ∀ k (hk : k < 32),
        orderOf (toComplex (t.val[k]'(by rw [t.property]; exact hk))) = 2 ^ k ∧
        toComplex (t.val[k]'(by rw [t.property]; exact hk)) ^ (Mersenne31.fieldSize + 1) = 1 ⦄ :=
  Proofs.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS.order

/-- `circle_two_adic_generator(bits)` has order `2^bits` for `bits ≤ 31`, and panics otherwise. -/
theorem complex.Mersenne31.circle_two_adic_generator.order (bits : Std.Usize) :
    complex.Mersenne31.circle_two_adic_generator bits
      ⦃ c => bits.val ≤ 31 ∧ orderOf (toComplex c) = 2 ^ bits.val ⦄ ∨
    (31 < bits.val ∧ complex.Mersenne31.circle_two_adic_generator bits = .fail .panic) :=
  Proofs.Mersenne31.circle_two_adic_generator.order bits

/-- `COMPLEX_GENERATOR` (`12 + i`) generates the multiplicative group of `F[i]`. -/
theorem complex.Mersenne31.COMPLEX_GENERATOR.order :
    complex.Mersenne31.COMPLEX_GENERATOR ⦃ c =>
      orderOf (toComplex c) = Mersenne31.fieldSize ^ 2 - 1 ⦄ :=
  Proofs.Mersenne31.COMPLEX_GENERATOR.order

/-! ## QM31, `F[i][u]` with `u^2 = 2 + i` -/

/-- `W = 2 + i` is not a square in `F[i]`, so QM31 is a field. -/
theorem extension.Mersenne31.QUADRATIC_W.irreducible :
    Irreducible (X ^ 2 - C (toComplex extension.Mersenne31.QUADRATIC_W)) :=
  Proofs.Mersenne31.QUADRATIC_W.irreducible

/-- `DTH_ROOT` is `W^((p^2 - 1) / 2)`. -/
theorem extension.Mersenne31.QUADRATIC_DTH_ROOT.toComplex :
    extension.Mersenne31.QUADRATIC_DTH_ROOT ⦃ c => toComplex c =
      toComplex extension.Mersenne31.QUADRATIC_W ^ ((Mersenne31.fieldSize ^ 2 - 1) / 2) ⦄ :=
  Proofs.Mersenne31.QUADRATIC_DTH_ROOT.toComplex

/-- `mul_by_w(z)` is `z · (2 + i)`. -/
theorem extension.Mersenne31.mul_by_w.toComplex (z : Array Element 2#usize)
    (hz : ∀ x ∈ z.val, Valid x) :
    extension.Mersenne31.mul_by_w z ⦃ r =>
      (∀ x ∈ r.val, Valid x) ∧ toComplex r = toComplex z * Mersenne31.Complex.mk 2 1 ⦄ :=
  Proofs.Mersenne31.mul_by_w.toComplex z hz

/-- `complex_ext_two_adic_generator(33)` has order `2^33`, the two-adicity of `p^4 - 1`. -/
theorem extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33.order :
    extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33 ⦃ c => orderOf (toQM31 c) = 2 ^ 33 ⦄ :=
  Proofs.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33.order

/-! ## The cubic extension of `F[i]`, `v^3 = 5i` -/

/-- `W = 5i` is not a cube in `F[i]`, so `F[i][v] / (v^3 - W)` is a field. -/
theorem extension.Mersenne31.CUBIC_W.irreducible :
    extension.Mersenne31.CUBIC_W ⦃ w => Irreducible (X ^ 3 - C (toComplex w)) ⦄ :=
  Proofs.Mersenne31.CUBIC_W.irreducible

/-- `DTH_ROOT` is `W^((p^2 - 1) / 3)`, not the `W^((p^2 - 1) / 2)` its comment states. -/
theorem extension.Mersenne31.CUBIC_DTH_ROOT.toComplex :
    extension.Mersenne31.CUBIC_DTH_ROOT ⦃ c => toComplex c =
      Mersenne31.Complex.mk 0 5 ^ ((Mersenne31.fieldSize ^ 2 - 1) / 3) ⦄ :=
  Proofs.Mersenne31.CUBIC_DTH_ROOT.toComplex

/-! ## The cubic extension of `F`, `X^3 = 5` -/

/-- `W = 5` is not a cube, so `F[X] / (X^3 - W)` is a field. -/
theorem mersenne_31.Mersenne31.CUBIC_W.irreducible :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.W ⦃ w =>
      Canonical w ∧ toField w = 5 ∧ Irreducible (X ^ 3 - C (toField w)) ⦄ :=
  Proofs.Mersenne31.CUBIC_BASE_W.irreducible

/-- `DTH_ROOT` is `W^((p - 1) / 3)`, a primitive cube root of unity. -/
theorem mersenne_31.Mersenne31.CUBIC_DTH_ROOT.toField :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.DTH_ROOT ⦃ d =>
      Canonical d ∧ toField d = 5 ^ ((Mersenne31.fieldSize - 1) / 3) ∧
        toField d ^ 3 = 1 ∧ toField d ≠ 1 ⦄ :=
  Proofs.Mersenne31.CUBIC_BASE_DTH_ROOT.toField

/-- `EXT_GENERATOR` (`10 + X`) generates the multiplicative group of `F[X] / (X^3 - 5)`. -/
theorem mersenne_31.Mersenne31.CUBIC_EXT_GENERATOR.order :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.EXT_GENERATOR ⦃ g =>
      orderOf (toCubic g) = Mersenne31.fieldSize ^ 3 - 1 ⦄ :=
  Proofs.Mersenne31.CUBIC_BASE_EXT_GENERATOR.order

end Plonky3Lean.Claims.Mersenne31
