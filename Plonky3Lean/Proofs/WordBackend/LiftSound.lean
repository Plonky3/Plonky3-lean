module

public import Plonky3Lean.Proofs.WordBackend.Lift
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Size

@[expose] public section

/-!
# When equal lifts mean equal integers

Equal lifts mean exponents congruent modulo the order $N$ of the generator.

With $N \ge 2^{2w} - 1$ both exponents lie in $[0, N]$, so they are equal, with one exception.

When $N = 2^{2w} - 1$, the all-ones limbs lift to one, exactly as a zero product does.

The low-bit relation $lo_0 = a_0 b_0$ closes that gap: an odd claim needs two odd factors.
-/

open Finset p3_word_backend.integer_mul.mirror

namespace Plonky3Lean.Proofs.WordBackend

theorem prod_lt {w a b : ℕ} (hw : 1 ≤ w) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    a * b < 2 ^ (2 * w) - 1 := by
  have hX : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  rw [two_mul, pow_add]
  have h1 : a ≤ 2 ^ w - 1 := by omega
  have h2 : b ≤ 2 ^ w - 1 := by omega
  have h3 : a * b ≤ (2 ^ w - 1) * (2 ^ w - 1) := Nat.mul_le_mul h1 h2
  have h4 : (2 ^ w - 1) * (2 ^ w - 1) + 2 < 2 ^ w * 2 ^ w := by
    zify [show 1 ≤ 2 ^ w by omega]
    nlinarith
  omega

/-- The exact collisions of the lift: a congruent but false product.

They occur only when the order is $2^{2w} - 1$, the product is zero and the claim is all ones. -/
theorem lift_collision {N w a b c : ℕ} (hw : 1 ≤ w) (hN : 2 ^ (2 * w) - 1 ≤ N)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ (2 * w)) :
    (a * b ≡ c [MOD N] ∧ a * b ≠ c) ↔ N = 2 ^ (2 * w) - 1 ∧ a * b = 0 ∧ c = N := by
  have hab := prod_lt hw ha hb
  constructor
  · rintro ⟨hm, hne⟩
    by_cases hcN : c < N
    · exact absurd (Nat.ModEq.eq_of_lt_of_lt hm (by omega) hcN) hne
    · have hcN' : c = N := by omega
      have h0 : a * b ≡ 0 [MOD N] := hm.trans (by rw [hcN']; exact Nat.modEq_zero_iff_dvd.2 dvd_rfl)
      have : a * b = 0 := Nat.ModEq.eq_of_lt_of_lt h0 (by omega) (by omega)
      exact ⟨by omega, this, hcN'⟩
  · rintro ⟨hN', h0, hcN⟩
    refine ⟨?_, by omega⟩
    rw [h0, hcN]
    exact (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm

/-- Congruent lifts and the low-bit relation together give the integer identity. -/
theorem lift_sound {N w a b c : ℕ} (hw : 1 ≤ w) (hN : 2 ^ (2 * w) - 1 ≤ N)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ (2 * w)) :
    (a * b ≡ c [MOD N] ∧ a % 2 * (b % 2) = c % 2) ↔ a * b = c := by
  constructor
  · rintro ⟨hm, hlow⟩
    by_contra hne
    obtain ⟨hN', h0, hcN⟩ := (lift_collision hw hN ha hb hc).1 ⟨hm, hne⟩
    have hodd : c % 2 = 1 := by
      have : 2 ≤ 2 ^ (2 * w) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ∣ 2 ^ (2 * w) := dvd_pow_self 2 (by omega)
      omega
    have : a % 2 * (b % 2) = 0 := by
      rcases Nat.mul_eq_zero.1 h0 with h | h <;> simp [h]
    omega
  · rintro rfl
    refine ⟨rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp [Nat.mul_mod, h, h']

theorem limbs_all_ones {X lo hi : ℕ} (hX : 1 ≤ X) (hl : lo < X) :
    lo + X * hi = X * X - 1 ↔ lo = X - 1 ∧ hi = X - 1 := by
  have e : X * X - 1 = (X - 1) + X * (X - 1) := by
    zify [hX, show 1 ≤ X * X by nlinarith]; ring
  rw [e]
  constructor
  · intro h
    have hmod := congrArg (· % X) h
    have hdiv := congrArg (· / X) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_of_lt (show X - 1 < X by omega)] at hmod
    simp only [Nat.add_mul_div_left _ _ (show 0 < X by omega), Nat.div_eq_of_lt hl,
      Nat.div_eq_of_lt (show X - 1 < X by omega), zero_add] at hdiv
    exact ⟨hmod, hdiv⟩
  · rintro ⟨rfl, rfl⟩; rfl

variable {F : Type _} [Field F]

theorem ne_zero_of_orderOf {g : F} (h : 0 < orderOf g) : g ≠ 0 := by
  rintro rfl
  rw [orderOf_eq_zero_iff'.2] at h
  · exact lt_irrefl _ h
  · intro n hn; simp [zero_pow hn.ne']

theorem pow_eq_pow_iff {g : F} (h : 0 < orderOf g) (x y : ℕ) :
    g ^ x = g ^ y ↔ x ≡ y [MOD orderOf g] := by
  have hg := ne_zero_of_orderOf h
  have := pow_eq_pow_iff_modEq (x := Units.mk0 g hg) (n := x) (m := y)
  rw [← orderOf_units, Units.val_mk0] at this
  rw [← this, Units.ext_iff]
  simp

/-- The field check accepts a field of $2^n$ elements exactly when $n \ge 2w$. -/
theorem check_field_two_pow (n w : ℕ) : check_field (2 ^ n) w = .ok () ↔ 2 * w ≤ n := by
  unfold check_field
  rw [Nat.size_pow]
  split <;> simp_all

/-- One row of the reduction accepts exactly the true full-width products.

- The field has $2^n$ elements and passes the field check.
- The generator has order $2^n - 1$.
- The factors and limbs are words of $w \ge 1$ bits.

Then the rows multiply to the same value and the low bits agree exactly when $a b = lo + 2^w hi$. -/
theorem row_sound {n w a b lo hi : ℕ} (g : F) (hg : orderOf g = 2 ^ n - 1)
    (hcheck : check_field (2 ^ n) w = .ok ()) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hl : lo < 2 ^ w) (hh : hi < 2 ^ w) :
    ((factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod =
        (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod ∧
      a % 2 * (b % 2) = lo % 2) ↔ a * b = lo + 2 ^ w * hi := by
  rw [check_field_two_pow] at hcheck
  have hN : 2 ^ (2 * w) - 1 ≤ 2 ^ n - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hcheck) 1
  have hpos : 0 < orderOf g := by
    rw [hg]
    have : 2 ≤ 2 ^ (2 * w) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hc : lo + 2 ^ w * hi < 2 ^ (2 * w) := by
    rw [two_mul, pow_add]; nlinarith
  have hlow : (lo + 2 ^ w * hi) % 2 = lo % 2 := by
    have : 2 ∣ 2 ^ w := dvd_pow_self 2 (by omega)
    obtain ⟨k, hk⟩ := this
    rw [hk, mul_assoc, Nat.add_mul_mod_self_left]
  rw [factor_row_prod g hb, result_row_prod g hl hh, Nat.mod_eq_of_lt ha, mul_comm b a,
    pow_eq_pow_iff hpos, hg, ← hlow]
  exact lift_sound hw hN ha hb hc

/-- Without the low-bit relation, the two rows agree on a false product exactly in one case.

The field has exactly $2^{2w}$ elements, the product is zero and both limbs are all ones. -/
theorem row_collision {n w a b lo hi : ℕ} (g : F) (hg : orderOf g = 2 ^ n - 1)
    (hcheck : check_field (2 ^ n) w = .ok ()) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hl : lo < 2 ^ w) (hh : hi < 2 ^ w) :
    ((factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod =
        (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod ∧
      a * b ≠ lo + 2 ^ w * hi) ↔
      n = 2 * w ∧ a * b = 0 ∧ lo = 2 ^ w - 1 ∧ hi = 2 ^ w - 1 := by
  rw [check_field_two_pow] at hcheck
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hN : 2 ^ (2 * w) - 1 ≤ 2 ^ n - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hcheck) 1
  have hpos : 0 < orderOf g := by
    rw [hg]
    have : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hc : lo + 2 ^ w * hi < 2 ^ (2 * w) := by
    rw [two_mul, pow_add]; nlinarith
  rw [factor_row_prod g hb, result_row_prod g hl hh, Nat.mod_eq_of_lt ha, mul_comm b a,
    pow_eq_pow_iff hpos, hg, lift_collision hw hN ha hb hc]
  have hsq : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  constructor
  · rintro ⟨hn, h0, hc'⟩
    have hn' : n = 2 * w := by
      by_contra hne
      have : 2 ^ (2 * w) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    refine ⟨hn', h0, ?_⟩
    rw [hn', hsq] at hc'
    exact (limbs_all_ones (by omega) hl).1 hc'
  · rintro ⟨rfl, h0, rfl, rfl⟩
    refine ⟨rfl, h0, ?_⟩
    rw [hsq]
    exact (limbs_all_ones (by omega) (by omega)).2 ⟨rfl, rfl⟩

/-- The reduction exists exactly when the statement declares a product. -/
theorem reduction_new_none (r k : ℕ) : IntegerMulReduction.new r k = none ↔ r = 0 := by
  unfold IntegerMulReduction.new; split <;> simp_all

end Plonky3Lean.Proofs.WordBackend
