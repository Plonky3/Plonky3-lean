import Plonky3Lean.Proofs.Field.Monty31.Findings
import Plonky3Lean.Proofs.Field.Monty31.Inverse
import Plonky3Lean.Proofs.Field.Monty31.QuotientMap

/-!
# p3-monty-31: claims, for every prime

What this repository asserts about `MontyField31` and its `u32` helpers.

Each claim holds for every `MontyParameters` impl that passes `MontyField31::new`'s checks.

`Valid inst p mu` is exactly those checks:

- `p` is odd,
- `p < 2^31`,
- `MONTY_BITS = 32`,
- `p · mu ≡ 1 (mod 2^32)`.

A claim that needs more says so, and why.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Stored values are in Montgomery form: an element `a` is stored as `a · 2^32 mod p`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31

namespace Plonky3Lean.Claims.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-! ## Montgomery reductions -/

/-- `monty_reduce(x)`, for `x < 2^32 · p`, is the canonical `r` with `r · 2^32 ≡ x (mod p)`. -/
theorem utils.monty_reduce.spec (hv : Valid inst p mu) (x : Std.U64)
    (hx : x.val < 2 ^ 32 * p.val) :
    utils.monty_reduce inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ :=
  Proofs.Monty31.utils.monty_reduce.spec hv x hx

/-- `large_monty_reduce(x)`, for `x < 2 · 2^32 · p`, gives the canonical `r` with `r · 2^32 ≡ x`. -/
theorem utils.large_monty_reduce.spec (hv : Valid inst p mu) (x : Std.U64)
    (hx : x.val < 2 * 2 ^ 32 * p.val) :
    utils.large_monty_reduce inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ :=
  Proofs.Monty31.utils.large_monty_reduce.spec hv x hx

/-- `monty_reduce_u128(x)`, for `x < 2^96`, is the canonical `r` with `r · 2^32 ≡ x (mod p)`.

It needs `p >= 2^30`, which `MontyField31::new` does not check.

Below it, one subtraction does not bring the low limb into range.

The last claim of this file shows a prime where that happens. -/
theorem utils.monty_reduce_u128.spec (hv : Valid inst p mu) (hp30 : 2 ^ 30 ≤ p.val)
    (x : Std.U128) (hx : x.val < 2 ^ 96) :
    utils.monty_reduce_u128 inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ :=
  Proofs.Monty31.utils.monty_reduce_u128.spec hv hp30 x hx

/-- `from_monty(x)` takes any `u32` out of Montgomery form.

It gives the canonical `r` with `r · 2^32 ≡ x`. -/
theorem utils.from_monty.spec (hv : Valid inst p mu) (x : Std.U32) :
    utils.from_monty inst x ⦃ r => r.val < p.val ∧
      r.val * 2 ^ 32 % p.val = x.val % p.val ⦄ :=
  Proofs.Monty31.utils.from_monty.spec hv x

/-! ## Addition, subtraction, halving -/

/-- `add(a, b)` of canonical `a`, `b` is `(a + b) mod p`, and the `u32` sum does not overflow. -/
theorem utils.add.spec (hv : Valid inst p mu) (a b : Std.U32) (ha : a.val < p.val)
    (hb : b.val < p.val) :
    utils.add inst a b ⦃ r => r.val = (a.val + b.val) % p.val ⦄ :=
  Proofs.Monty31.utils.add.spec hv a b ha hb

/-- `sub(a, b)` of canonical `a`, `b` is `(a - b) mod p`, computed as `(a + p - b) mod p`. -/
theorem utils.sub.spec (hv : Valid inst p mu) (a b : Std.U32) (ha : a.val < p.val)
    (hb : b.val < p.val) :
    utils.sub inst a b ⦃ r => r.val = (a.val + p.val - b.val) % p.val ⦄ :=
  Proofs.Monty31.utils.sub.spec hv a b ha hb

/-- `halve_u32(a)` of a canonical `a` is the canonical `r` with `2r ≡ a (mod p)`.

It needs `HALF_P_PLUS_1` at its default `(p + 1) / 2` (`FieldValid`). -/
theorem utils.halve_u32.spec {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (a : Std.U32) (ha : a.val < p.val) :
    utils.halve_u32 inst a ⦃ r => r.val < p.val ∧ r.val * 2 % p.val = a.val ⦄ :=
  Proofs.Monty31.utils.halve_u32.spec hv a ha

/-! ## Integers into Montgomery form -/

/-- `to_monty(x)` stores any `u32` in Montgomery form: `x · 2^32 mod p`. -/
theorem utils.to_monty.spec (hv : Valid inst p mu) (x : Std.U32) :
    utils.to_monty inst x ⦃ r => r.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.utils.to_monty.spec hv x

/-- `to_monty_64(x)` stores any `u64` in Montgomery form: `x · 2^32 mod p`. -/
theorem utils.to_monty_64.spec (hv : Valid inst p mu) (x : Std.U64) :
    utils.to_monty_64 inst x ⦃ r => r.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.utils.to_monty_64.spec hv x

/-- `to_monty_signed(x)` stores any `i32` in Montgomery form, canonically. -/
theorem utils.to_monty_signed.spec (hv : Valid inst p mu) (x : Std.I32) :
    utils.to_monty_signed inst x ⦃ r => r.val < p.val ∧
      (r.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.utils.to_monty_signed.spec hv x

/-- `to_monty_64_signed(x)` stores any `i64` in Montgomery form, canonically. -/
theorem utils.to_monty_64_signed.spec (hv : Valid inst p mu) (x : Std.I64) :
    utils.to_monty_64_signed inst x ⦃ r => r.val < p.val ∧
      (r.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.utils.to_monty_64_signed.spec hv x

/-! ## Integers into the field -/

open monty_31.MontyField31.Insts in
/-- `from_int` on an `i32` gives the element `x mod p`, stored canonically. -/
theorem QuotientMap.from_int_i32 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I32) :
    P3_fieldIntegersQuotientMapI32.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.from_int_i32.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_int` on a `u64` gives the element `x mod p`. -/
theorem QuotientMap.from_int_u64 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.U64) :
    P3_fieldIntegersQuotientMapU64.from_int inst x ⦃ r =>
      r.value.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.from_int_u64.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_int` on an `i64` gives the element `x mod p`, stored canonically. -/
theorem QuotientMap.from_int_i64 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I64) :
    P3_fieldIntegersQuotientMapI64.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.from_int_i64.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_int` on a `u128` gives the element `x mod p`. -/
theorem QuotientMap.from_int_u128 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.U128) :
    P3_fieldIntegersQuotientMapU128.from_int inst x ⦃ r =>
      r.value.val = x.val % p.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.from_int_u128.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_int` on an `i128` gives the element `x mod p`, stored canonically. -/
theorem QuotientMap.from_int_i128 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I128) :
    P3_fieldIntegersQuotientMapI128.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.from_int_i128.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on a `u32` is `Some(x mod p)` for `x < p`, and `None` otherwise. -/
theorem QuotientMap.from_canonical_checked_u32 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.U32) :
    P3_fieldIntegersQuotientMapU32.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_u32.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on an `i32` is `Some(x mod p)` for `|x| <= (p - 1)/2`.

Outside that range it is `None`. -/
theorem QuotientMap.from_canonical_checked_i32 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I32) :
    P3_fieldIntegersQuotientMapI32.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_i32.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on a `u64` is `Some(x mod p)` for `x < p`, and `None` otherwise. -/
theorem QuotientMap.from_canonical_checked_u64 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.U64) :
    P3_fieldIntegersQuotientMapU64.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_u64.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on a `u128` is `Some(x mod p)` for `x < p`, and `None` otherwise. -/
theorem QuotientMap.from_canonical_checked_u128 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.U128) :
    P3_fieldIntegersQuotientMapU128.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_u128.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on an `i64` is `Some(x mod p)` for `|x| <= (p - 1)/2`.

Outside that range it is `None`. -/
theorem QuotientMap.from_canonical_checked_i64 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I64) :
    P3_fieldIntegersQuotientMapI64.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_i64.spec hv x

open monty_31.MontyField31.Insts in
/-- `from_canonical_checked` on an `i128` is `Some(x mod p)` for `|x| <= (p - 1)/2`.

Outside that range it is `None`. -/
theorem QuotientMap.from_canonical_checked_i128 {FP : Type} {inst : data_traits.FieldParameters FP}
    (hv : FieldValid inst p mu) (x : Std.I128) :
    P3_fieldIntegersQuotientMapI128.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ :=
  Proofs.Monty31.from_canonical_checked_i128.spec hv x

/-! ## Field elements -/

/-- `MontyField31::new(x)` passes its parameter checks.

It stores `x · 2^32 mod p`, for every `u32`. -/
theorem monty_31.MontyField31.new.spec (hv : Valid inst p mu) (x : Std.U32) :
    monty_31.MontyField31.new inst x ⦃ r => r.value.val = x.val * 2 ^ 32 % p.val ⦄ :=
  Proofs.Monty31.monty_31.MontyField31.new.spec hv x

/-- `a * b` of canonical elements is canonical, with `c · 2^32 ≡ a · b (mod p)` on stored values.

That is the product of the field elements they stand for. -/
theorem monty_31.MontyField31.mul.spec (hv : Valid inst p mu) (a b : monty_31.MontyField31 MP)
    (ha : a.value.val < p.val) (hb : b.value.val < p.val) :
    monty_31.MontyField31.mul inst a b ⦃ c => c.value.val < p.val ∧
      c.value.val * 2 ^ 32 % p.val = a.value.val * b.value.val % p.val ⦄ :=
  Proofs.Monty31.monty_31.MontyField31.mul.spec hv a b ha hb

/-- `mul_2exp_u64(a, e)` for `2 <= e < 64` multiplies a canonical `a` by `2^e`.

It reads the table of powers of two, which needs `MONTY_ONE` at its default (`FieldDefaults`). -/
theorem monty_31.MontyField31.mul_2exp_u64.spec_lt {FP : Type}
    {inst : data_traits.FieldParameters FP} (hv : FieldValid inst p mu) (hd : FieldDefaults inst)
    (a : monty_31.MontyField31 FP) (ha : a.value.val < p.val) (exp : Std.U64)
    (h2 : 2 ≤ exp.val) (h64 : exp.val < 64) :
    monty_31.MontyField31.mul_2exp_u64 inst a exp ⦃ c => c.value.val < p.val ∧
      c.value.val ≡ a.value.val * 2 ^ exp.val [MOD p.val] ⦄ :=
  Proofs.Monty31.monty_31.MontyField31.mul_2exp_u64.spec_lt hv hd a ha exp h2 h64

/-- `try_inverse(a)` of a canonical `a`, for a prime `p >= 2^30`.

- Zero gives `None`.
- Otherwise `Some(c)`, with `c` canonical and `c · a ≡ 2^64 (mod p)` on stored values.

The second congruence says the field elements multiply to `1`.

`MontyField31::new` does not check `p >= 2^30`.

The bound is needed: the GCD claims show a smaller prime where inversion goes wrong. -/
theorem monty_31.MontyField31.try_inverse.spec {FP : Type}
    {inst : data_traits.FieldParameters FP} (hv : FieldValid inst p mu) (hd : FieldDefaults inst)
    (hprime : Nat.Prime p.val) (hp30 : 2 ^ 30 ≤ p.val) (a : monty_31.MontyField31 FP)
    (ha : a.value.val < p.val) :
    monty_31.MontyField31.try_inverse inst a ⦃ r =>
      (a.value.val = 0 → r = none) ∧
      (a.value.val ≠ 0 → ∃ c, r = some c ∧ c.value.val < p.val ∧
        c.value.val * a.value.val ≡ 2 ^ 64 [MOD p.val]) ⦄ :=
  Proofs.Monty31.monty_31.MontyField31.try_inverse.spec hv hd hprime hp30 a ha

/-! ## A valid prime below `2^30` -/

/-- The prime `2^29 - 3` passes every check `MontyField31::new` makes.

Its `MONTY_MU` is `894784853`. -/
theorem thirty_bit_prime.valid :
    Valid Proofs.Monty31.Findings.thirtyBit 536870909#u32 894784853#u32 :=
  Proofs.Monty31.Findings.thirtyBit_valid

/-- For that prime and `x = 2^64 - 1`, one subtraction leaves the low limb too large.

```text
  lo                  = 2^64 - 1
  lo - 2 · 2^32 · p  >= 2 · 2^32 · p    (outside the inner reduction's domain)
```
-/
theorem thirty_bit_prime.low_limb_out_of_range :
    2 * 2 ^ 32 * 536870909 ≤ 2 ^ 64 - 1 ∧
      2 * 2 ^ 32 * 536870909 ≤ (2 ^ 64 - 1) - 2 * 2 ^ 32 * 536870909 :=
  Proofs.Monty31.Findings.thirtyBit_low_limb_out_of_range

end Plonky3Lean.Claims.Monty31
