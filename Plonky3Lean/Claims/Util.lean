module

public import Plonky3Lean.Proofs.Util.GcdInversion

@[expose] public section

/-!
# p3-util: claims

What this repository asserts about `p3_util::gcd_inversion_prime_field_32`, at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/util`.

`m ⦃ v => P v ⦄` states that `m` returns a value `v`, so it does not panic, and that `P v` holds.

`F` is `FIELD_BITS`, `a` the value to invert and `b` the modulus `P`.

The Rust documents `b` as an odd prime with at most `F` bits, and `a < b`.
-/

open Aeneas Aeneas.Std
open p3_util

namespace Plonky3Lean.Claims.Util

/-! ## Any `FIELD_BITS` -/

/-- For `2 ≤ F ≤ 32` and `b < 2^F` (the `debug_assert`), `gcd_inversion_prime_field_32` never panics, for every `a`.

No `i64` operation overflows.

The result lies in `[-(2^{2F-2} - 2), 2^{2F-2}]`. -/
theorem gcd_inversion_prime_field_32.never_panics (F a b : Std.U32) (hF2 : 2 ≤ F.val)
    (hF : F.val ≤ 32) (hb : b.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F a b ⦃ v =>
      -(2 ^ (2 * F.val - 2) - 2) ≤ v.val ∧ v.val ≤ 2 ^ (2 * F.val - 2) ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.bounds F a b hF2 hF hb

/-- For `1 ≤ F ≤ 32`, an odd `b < 2^F` and `a < 2^F`, the result `v` satisfies `v a ≡ 2^{2F-2} gcd(a, b) (mod b)`.

Primality of `b` is not needed, and `a ≥ b` is allowed as long as `a < 2^F`. -/
theorem gcd_inversion_prime_field_32.cong (F a b : Std.U32) (hF1 : 1 ≤ F.val)
    (hF : F.val ≤ 32) (hb : b.val < 2 ^ F.val) (hodd : b.val % 2 = 1) (ha : a.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F a b ⦃ v =>
      v.val * a.val ≡ 2 ^ (2 * F.val - 2) * (Nat.gcd a.val b.val : ℤ) [ZMOD b.val] ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.cong F a b hF1 hF hb hodd ha

/-- With `b ≥ 2^F` the `debug_assert` fails, and the function panics. -/
theorem gcd_inversion_prime_field_32.panics (F a b : Std.U32) (hF : F.val ≤ 32)
    (hb : 2 ^ F.val ≤ b.val) :
    gcd_inversion_prime_field_32 F a b = .fail .panic :=
  Proofs.Util.gcd_inversion_prime_field_32.panics F a b hF hb

/-- `a = 0` returns `0`, without panicking. -/
theorem gcd_inversion_prime_field_32.zero (F b : Std.U32) (hF1 : 1 ≤ F.val) (hF : F.val ≤ 32)
    (hb : b.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F 0#u32 b ⦃ v => v.val = 0 ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.zero F b hF1 hF hb

/-- `a = 1` returns exactly `2^{2F-2}`, for every `b > 1`.

So the documented strict bound `|v| < 2^{2F-2}` does not hold: the true bound is `|v| ≤ 2^{2F-2}`. -/
theorem gcd_inversion_prime_field_32.one (F b : Std.U32) (hF2 : 2 ≤ F.val) (hF : F.val ≤ 32)
    (hb : b.val < 2 ^ F.val) (hb1 : 1 < b.val) :
    gcd_inversion_prime_field_32 F 1#u32 b ⦃ v => v.val = 2 ^ (2 * F.val - 2) ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.one F b hF2 hF hb hb1

/-! ## `FIELD_BITS = 31`, as `MontyField31::try_inverse` calls it -/

/-- For an odd prime `b < 2^31` and `0 < a < b`, the result is `2^60 a^{-1} mod b`, with `|v| ≤ 2^60`. -/
theorem gcd_inversion_prime_field_32.inverse (a b : Std.U32) (hp : Nat.Prime b.val)
    (hodd : b.val % 2 = 1) (hb : b.val < 2 ^ 31) (ha0 : 0 < a.val) (hab : a.val < b.val) :
    gcd_inversion_prime_field_32 31#u32 a b ⦃ v =>
      |v.val| ≤ 2 ^ 60 ∧ v.val * a.val ≡ 2 ^ 60 [ZMOD b.val] ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.spec_prime a b hp hodd hb ha0 hab

/-- For `2^30 ≤ b < 2^31` and any `a`, `b · 2^30 + v` lies in `(0, 2^32 b)`.

This is the value `try_inverse` passes to `monty_reduce`, whose precondition is `x < 2^32 P`. -/
theorem gcd_inversion_prime_field_32.pos_inverse (a b : Std.U32) (hb1 : 2 ^ 30 ≤ b.val)
    (hb : b.val < 2 ^ 31) :
    gcd_inversion_prime_field_32 31#u32 a b ⦃ v =>
      0 < (b.val : ℤ) * 2 ^ 30 + v.val ∧ (b.val : ℤ) * 2 ^ 30 + v.val < 2 ^ 32 * b.val ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.pos_inverse a b hb1 hb

/-- For the prime `P = 536870909 < 2^30` and `a = 194997`, `P · 2^30 + v` is negative.

So `try_inverse` needs `P ≥ 2^30`, which `MontyField31::new` does not check. -/
theorem gcd_inversion_prime_field_32.pos_inverse_small_prime :
    Nat.Prime 536870909 ∧
    gcd_inversion_prime_field_32 31#u32 194997#u32 536870909#u32 ⦃ v =>
      v.val = -580141285873025024 ∧ (536870909 : ℤ) * 2 ^ 30 + v.val < 0 ⦄ :=
  ⟨Proofs.Util.small_prime_is_prime, Proofs.Util.gcd_inversion_prime_field_32.small_prime⟩

/-- For BabyBear's prime and `a = 3 · 2^30`, which is at least `2^31`, the result is not `2^60 a^{-1}`.

So the congruence needs `a < 2^F`, which the documented `a < b` implies. -/
theorem gcd_inversion_prime_field_32.wrong_of_large_a :
    gcd_inversion_prime_field_32 31#u32 3221225472#u32 2013265921#u32 ⦃ v =>
      v.val = 2 ^ 30 ∧ ¬ v.val * 3221225472 ≡ 2 ^ 60 [ZMOD 2013265921] ⦄ :=
  Proofs.Util.gcd_inversion_prime_field_32.large_a

end Plonky3Lean.Claims.Util
