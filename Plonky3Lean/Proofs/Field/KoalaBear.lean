import CompPoly.Fields.KoalaBear
import Plonky3Lean.Proofs.Field.Monty31.Arith
import Plonky3Lean.Spec.KoalaBear
import ToCompPoly.Fields.KoalaBear

/-!
# KoalaBear: the parameters

Proofs of the KoalaBear claims in `Plonky3Lean.Claims.KoalaBear` about `KoalaBearParameters`, its constructors and its `u32` arithmetic.

KoalaBear's parameters pass `MontyField31::new`'s checks (`MontyParams.valid`), so every generic Monty31 theorem applies at them.

Theorems are named `<item>.<property>`, after the Rust item they are about.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.KoalaBear

/-! ## Wiring: the instances return these constants -/

theorem koala_bear.KoalaBearParameters.PRIME.from_instance :
    MontyParams.PRIME = .ok PRIME := rfl
theorem koala_bear.KoalaBearParameters.MONTY_MU.from_instance :
    MontyParams.MONTY_MU = .ok MONTY_MU := rfl
theorem koala_bear.KoalaBearParameters.MONTY_BITS.from_instance :
    MontyParams.MONTY_BITS = .ok MONTY_BITS := rfl
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.from_instance :
    TwoAdicParams.TWO_ADICITY = .ok TWO_ADICITY := rfl

/-! ## The constants against the specification -/

/-- `PRIME` is exactly CompPoly's `KoalaBear.fieldSize` (`2^31 - 2^24 + 1 = 2130706433`). -/
theorem koala_bear.KoalaBearParameters.PRIME.eq_fieldSize :
    PRIME.val = KoalaBear.fieldSize := by
  simp [PRIME, KoalaBear.fieldSize,
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME]

/-- The modulus is prime: CompPoly's Pratt certificate `KoalaBear.is_prime`. -/
theorem koala_bear.KoalaBearParameters.PRIME.is_prime : Nat.Prime PRIME.val := by
  rw [koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  exact KoalaBear.is_prime

/-- `gcd(3, p - 1) = 1`, so `x ↦ x^3` permutes the field: the fact behind `RelativelyPrimePower<3>`. -/
theorem koala_bear.KoalaBearParameters.PRIME.coprime_three_pred :
    Nat.Coprime 3 (PRIME.val - 1) := by
  rw [koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  exact KoalaBear.coprime_three_fieldSize_sub_one

/-- Extraction tripwire: `MONTY_BITS` is the literal `32` that `MontyField31::new` asserts. -/
theorem koala_bear.KoalaBearParameters.MONTY_BITS.val_eq_32 : MONTY_BITS.val = 32 := by
  simp [MONTY_BITS,
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS]

/-- `PRIME · MONTY_MU ≡ 1 (mod 2^32)`: the precondition of Montgomery reduction. -/
theorem koala_bear.KoalaBearParameters.MONTY_MU.inverse :
    (PRIME.val * MONTY_MU.val) % (2 ^ 32) = 1 := by
  simp [PRIME, MONTY_MU,
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME,
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU]

/-- `TWO_ADICITY` is CompPoly's `KoalaBear.twoAdicity` (24). -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity :
    TWO_ADICITY.val = KoalaBear.twoAdicity := by
  simp [TWO_ADICITY, KoalaBear.twoAdicity,
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.TWO_ADICITY]

/-- `p - 1 = 2^TWO_ADICITY · 127`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.factorization :
    PRIME.val - 1 = 2 ^ TWO_ADICITY.val * 127 := by
  rw [koala_bear.KoalaBearParameters.PRIME.eq_fieldSize,
    koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
  exact KoalaBear.fieldSize_sub_one_factorization

/-- `TWO_ADICITY` is maximal: `2^(TWO_ADICITY + 1)` does not divide `p - 1`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.maximal :
    ¬ 2 ^ (TWO_ADICITY.val + 1) ∣ PRIME.val - 1 := by
  rw [koala_bear.KoalaBearParameters.TWO_ADICITY.factorization, pow_succ,
    Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)]
  decide

/-! ## The parameters pass `MontyField31::new`'s checks -/

/-- `MONTY_MASK` keeps its default, `(1 << MONTY_BITS) - 1 = 2^32 - 1`. -/
theorem MontyParams.MONTY_MASK.eq : MontyParams.MONTY_MASK = .ok 4294967295#u32 := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS
  rfl

/-- KoalaBear's `MontyParameters` are valid: `PRIME` is odd and below `2^31`, `MONTY_BITS = 32`, and `MONTY_MU` inverts `PRIME` modulo `2^32`. -/
theorem MontyParams.valid : Spec.Monty31.Valid MontyParams PRIME MONTY_MU where
  prime := rfl
  bits := by
    show RustM.ok MONTY_BITS = _
    unfold MONTY_BITS
      koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS
    rfl
  monty_mu := rfl
  mask := MontyParams.MONTY_MASK.eq
  odd := by
    unfold PRIME koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
    decide
  lt := by
    unfold PRIME koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
    decide
  inv := koala_bear.KoalaBearParameters.MONTY_MU.inverse

/-- KoalaBear's `FieldParameters` are valid: its `MontyParameters` are, and `HALF_P_PLUS_1` keeps its default `(p + 1) / 2`. -/
theorem FieldParams.valid : Spec.Monty31.FieldValid FieldParams PRIME MONTY_MU where
  monty := MontyParams.valid
  half := by
    refine ⟨1065353217#u32, ?_, ?_⟩
    · dsimp only
      unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
      rfl
    · unfold PRIME koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
      decide

/-! ## The `u32` helpers at KoalaBear's parameters

The generic theorems of `Plonky3Lean.Proofs.Monty31`, at `MontyParams.valid`. -/

/-- `monty_reduce(x)`, for `x < 2^32 p`, is the canonical `r` with `r · 2^32 ≡ x (mod p)`. -/
theorem utils.monty_reduce.spec (x : Std.U64) (hx : x.val < 2 ^ 32 * KoalaBear.fieldSize) :
    p3_monty_31.utils.monty_reduce MontyParams x ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2 ^ 32) % KoalaBear.fieldSize = x.val % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize] at *
  exact Monty31.utils.monty_reduce.spec MontyParams.valid x hx

/-- `from_monty(x)` is the canonical `r` with `r · 2^32 ≡ x (mod p)`, for every `u32`. -/
theorem utils.from_monty.spec (x : Std.U32) :
    p3_monty_31.utils.from_monty MontyParams x ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2 ^ 32) % KoalaBear.fieldSize = x.val % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  exact Monty31.utils.from_monty.spec MontyParams.valid x

/-- `add(a, b)` of canonical `a`, `b` is `(a + b) mod p`. -/
theorem utils.add.spec (a b : Std.U32) (ha : a.val < KoalaBear.fieldSize)
    (hb : b.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.add MontyParams a b ⦃ r => r.val = (a.val + b.val) % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize] at *
  exact Monty31.utils.add.spec MontyParams.valid a b ha hb

/-- `sub(a, b)` of canonical `a`, `b` is `(a - b) mod p`, as `(a + p - b) mod p`. -/
theorem utils.sub.spec (a b : Std.U32) (ha : a.val < KoalaBear.fieldSize)
    (hb : b.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.sub MontyParams a b
      ⦃ r => r.val = (a.val + KoalaBear.fieldSize - b.val) % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize] at *
  exact Monty31.utils.sub.spec MontyParams.valid a b ha hb

/-- `halve_u32(a)` of a canonical `a` is the canonical `r` with `2r ≡ a (mod p)`. -/
theorem utils.halve_u32.spec (a : Std.U32) (ha : a.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.halve_u32 FieldParams a ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2) % KoalaBear.fieldSize = a.val ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize] at *
  exact Monty31.utils.halve_u32.spec FieldParams.valid a ha

/-- `to_monty(x)` is `x · 2^32 mod p`, for every `u32`. -/
theorem utils.to_monty.spec (x : Std.U32) :
    p3_monty_31.utils.to_monty MontyParams x ⦃ r => r.val = x.val * 2 ^ 32 % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  exact Monty31.utils.to_monty.spec MontyParams.valid x

/-! ## The `KoalaBear` constructors -/

/-- `KoalaBear::new x` never panics and returns the Montgomery form `x · 2^32 mod p`. -/
theorem koala_bear.KoalaBear.new.montgomery_form (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => r.value.val = x.val * 2 ^ 32 % KoalaBear.fieldSize ⦄ := by
  rw [← koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  exact Monty31.monty_31.MontyField31.new.spec MontyParams.valid x

/-- `KoalaBear::new x` stands for `x mod p` and is canonical. -/
theorem koala_bear.KoalaBear.new.toField (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => Canonical r ∧ toField r = (x.val : KoalaBear.Field) ⦄ :=
  Monty31.monty_31.MontyField31.new.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize x

/-- `KoalaBear::new_array` stands for its inputs mod `p`, elementwise, and is canonical. -/
theorem koala_bear.KoalaBear.new_array.toField {N : Std.Usize} (input : Array Std.U32 N) :
    p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      ⦃ r => (∀ y ∈ r.val, Canonical y) ∧
        r.val.map toField = input.val.map (fun x => (x.val : KoalaBear.Field)) ⦄ :=
  Monty31.monty_31.MontyField31.new_array.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize input

/-- `KoalaBear::new_2d_array` stands for its inputs mod `p`, elementwise, and is canonical. -/
theorem koala_bear.KoalaBear.new_2d_array.toField {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input
      ⦃ r => (∀ row ∈ r.val, ∀ y ∈ row.val, Canonical y) ∧
        r.val.map (fun row => row.val.map toField) =
          input.val.map (fun row => row.val.map (fun x => (x.val : KoalaBear.Field))) ⦄ :=
  Monty31.monty_31.MontyField31.new_2d_array.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize input

/-- `KoalaBear::new_array` never panics. -/
theorem koala_bear.KoalaBear.new_array.never_panics {N : Std.Usize} (input : Array Std.U32 N) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_array MontyParams input = .ok r :=
  Monty31.monty_31.MontyField31.new_array.ok MontyParams.valid input

/-- `KoalaBear::new_2d_array` never panics. -/
theorem koala_bear.KoalaBear.new_2d_array.never_panics {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input = .ok r :=
  Monty31.monty_31.MontyField31.new_2d_array.ok MontyParams.valid input

end Plonky3Lean.Proofs.KoalaBear
