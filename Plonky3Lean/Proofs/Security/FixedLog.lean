module

public import Mathlib

@[expose] public section

/-!
# The bit-by-bit binary logarithm, on naturals

# Overview

The Rust computes `log_2 x` in fixed point, with 16 fractional bits.

It works in three steps:

- scale `x` to a mantissa in `[1, 2)`, with 32 fractional bits;
- square the mantissa 16 times, truncating each square to 32 fractional bits;
- read one result bit off each square.

This file states that algorithm on the naturals and proves it never exceeds the true logarithm:

```text
    2^(result) <= x^(2^16),   that is   result <= 2^16 * log_2 x
```

# Why it can fall short

Truncation can only lower the mantissa, so it can only lose result bits.

Each truncation loses at most a factor `(2^32 - 1) / 2^32`, and together they lose less than two units:

```text
    2^16 * log_2 x - 2  <  result  <=  2^16 * log_2 x
```

At one input the loss is one unit:

```text
    x = 14917

    computed:                     908634
    floor(2^16 * log_2 14917):    908635
```
-/

namespace Plonky3Lean.Proofs.Security.FixedLog

/-- The state `(result, mantissa, bit)` after scaling. -/
def init (x : ℕ) : ℕ × ℕ × ℕ :=
  let ip := Nat.log2 x
  (ip * 2 ^ 16, if 32 ≤ ip then x / 2 ^ (ip - 32) else x * 2 ^ (32 - ip), 0)

/-- One loop iteration.

It squares the mantissa and truncates it to 32 fractional bits.

When the square reaches `2`, it takes a result bit and halves the mantissa. -/
def step (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let m := s.2.1 * s.2.1 / 2 ^ 32
  if 2 ^ 33 ≤ m then (s.1 + 2 ^ (15 - s.2.2), m / 2, s.2.2 + 1) else (s.1, m, s.2.2 + 1)

/-- The state after `n` iterations. -/
def iter (x : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => init x
  | n + 1 => step (iter x n)

/-- The fixed-point floor logarithm, on naturals. -/
def flog (x : ℕ) : ℕ := (iter x 16).1

theorem iter_bit (x n : ℕ) : (iter x n).2.2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, step]; split <;> simp [ih]

/-- The loop invariant after `b` iterations, with `ip = log_2 x`.

- The mantissa `m` stays in `[2^32, 2^33)`.
- The result is `ip * 2^16 + F * 2^(16 - b)`, for the `b` bits `F` read so far.
- The truncated mantissa never exceeds the true one: `(m / 2^32) * 2^F <= (x / 2^ip)^(2^b)`.

The last inequality is raised to the power `2^(16 - b)` to stay in the naturals. -/
def Inv (x b : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  s.2.2 = b ∧ 2 ^ 32 ≤ s.2.1 ∧ s.2.1 < 2 ^ 33 ∧ ∃ F, F < 2 ^ b ∧
    s.1 = Nat.log2 x * 2 ^ 16 + F * 2 ^ (16 - b) ∧
    (s.2.1 * 2 ^ F) ^ 2 ^ (16 - b) * 2 ^ (Nat.log2 x * 2 ^ 16) ≤
      x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b)

theorem init_inv (x : ℕ) (hx : 0 < x) : Inv x 0 (init x) := by
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le (by omega)
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  set ip := Nat.log2 x
  -- The mantissa satisfies m * 2^ip <= x * 2^32 and 2^32 <= m < 2^33.
  have key : 2 ^ 32 ≤ (init x).2.1 ∧ (init x).2.1 < 2 ^ 33 ∧
      (init x).2.1 * 2 ^ ip ≤ x * 2 ^ 32 := by
    simp only [init]
    split_ifs with h
    · have e : 2 ^ ip = 2 ^ (ip - 32) * 2 ^ 32 := by rw [← pow_add]; congr 1; omega
      have e1 : 2 ^ (ip + 1) = 2 ^ (ip - 32) * 2 ^ 33 := by rw [← pow_add]; congr 1; omega
      have hp : 0 < 2 ^ (ip - 32) := by positivity
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.le_div_iff_mul_le hp]; rw [e] at hlo; linarith
      · rw [Nat.div_lt_iff_lt_mul hp]; rw [e1] at hhi; linarith
      · rw [e, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    · have e : 2 ^ 32 = 2 ^ (32 - ip) * 2 ^ ip := by rw [← pow_add]; congr 1; omega
      have e1 : 2 ^ 33 = 2 ^ (32 - ip) * 2 ^ (ip + 1) := by rw [← pow_add]; congr 1; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [e, mul_comm x]; exact Nat.mul_le_mul_left _ hlo
      · rw [e1, mul_comm x]; exact Nat.mul_lt_mul_of_pos_left hhi (by positivity)
      · rw [e, mul_assoc]
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨rfl, h1, h2, 0, by simp, by simp [init], ?_⟩
  simp only [pow_zero, mul_one, Nat.sub_zero]
  rw [← mul_pow]
  calc (init x).2.1 ^ 2 ^ 16 * 2 ^ (ip * 2 ^ 16)
      = ((init x).2.1 * 2 ^ ip) ^ 2 ^ 16 := by rw [mul_pow, ← pow_mul]
    _ ≤ (x * 2 ^ 32) ^ 2 ^ 16 := Nat.pow_le_pow_left h3 _

theorem step_inv (x b : ℕ) (hb : b < 16) (s : ℕ × ℕ × ℕ) (h : Inv x b s) :
    Inv x (b + 1) (step s) := by
  obtain ⟨hb', h1, h2, F, hF, hr, hle⟩ := h
  set m := s.2.1
  set m' := m * m / 2 ^ 32
  set e := 2 ^ (16 - (b + 1))
  have he : 2 ^ (16 - b) = 2 * e := by
    simp only [e]; rw [← pow_succ']; congr 1; omega
  have hm'le : m' * 2 ^ 32 ≤ m * m := Nat.div_mul_le_self _ _
  have hm'lo : 2 ^ 32 ≤ m' := by
    rw [Nat.le_div_iff_mul_le (by positivity)]; nlinarith
  have hm'hi : m' < 2 ^ 34 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; nlinarith
  -- The invariant after squaring, before the bit is decided.
  have hsq : (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) ≤
      x ^ 2 ^ 16 * (2 ^ 32) ^ e := by
    have hA : (m' * 2 ^ (2 * F)) ^ e * (2 ^ 32) ^ e ≤ (m * 2 ^ F) ^ (2 ^ (16 - b)) := by
      rw [he, pow_mul (m * 2 ^ F) 2 e, ← mul_pow]
      apply Nat.pow_le_pow_left
      calc m' * 2 ^ (2 * F) * 2 ^ 32 = m' * 2 ^ 32 * 2 ^ (2 * F) := by ring
        _ ≤ m * m * 2 ^ (2 * F) := Nat.mul_le_mul_right _ hm'le
        _ = (m * 2 ^ F) ^ 2 := by
          rw [show 2 ^ (2 * F) = 2 ^ F * 2 ^ F by rw [two_mul, pow_add]]; ring
    have hpos : 0 < (2 ^ 32) ^ e := by positivity
    have := calc (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) * (2 ^ 32) ^ e
        = (m' * 2 ^ (2 * F)) ^ e * (2 ^ 32) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) := by ring
      _ ≤ (m * 2 ^ F) ^ (2 ^ (16 - b)) * 2 ^ (Nat.log2 x * 2 ^ 16) := Nat.mul_le_mul_right _ hA
      _ ≤ x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b) := hle
      _ = x ^ 2 ^ 16 * (2 ^ 32) ^ e * (2 ^ 32) ^ e := by rw [he, pow_mul']; ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hrb : 2 ^ (16 - b) = 2 * 2 ^ (15 - b) := by rw [← pow_succ']; congr 1; omega
  have h15 : 16 - (b + 1) = 15 - b := by omega
  simp only [step]
  split_ifs with hc
  · have hc' : 2 ^ 33 ≤ m' := hc
    refine ⟨by simp [hb'], ?_, ?_, 2 * F + 1, ?_, ?_, ?_⟩
    · show 2 ^ 32 ≤ m' / 2; omega
    · show m' / 2 < 2 ^ 33; omega
    · rw [pow_succ]; omega
    · simp only [hb', hr, hrb, h15]; ring
    · simp only
      calc (m' / 2 * 2 ^ (2 * F + 1)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16)
          ≤ (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) := by
            apply Nat.mul_le_mul_right; apply Nat.pow_le_pow_left
            rw [pow_succ, ← mul_assoc, mul_comm _ 2, ← mul_assoc]
            exact Nat.mul_le_mul_right _ (by rw [mul_comm]; exact Nat.div_mul_le_self _ _)
        _ ≤ _ := hsq
  · have hc' : ¬ 2 ^ 33 ≤ m' := hc
    refine ⟨by simp [hb'], hm'lo, by show m' < 2 ^ 33; omega, 2 * F, ?_, ?_, hsq⟩
    · rw [pow_succ]; omega
    · simp only [hr, hrb, h15]; ring

theorem iter_inv (x : ℕ) (hx : 0 < x) : ∀ n, n ≤ 16 → Inv x n (iter x n)
  | 0, _ => init_inv x hx
  | n + 1, h => step_inv x n (by omega) _ (iter_inv x hx n (by omega))

/-- **The fixed-point logarithm is sound.**

The result never exceeds `2^16 * log_2 x`, that is `2^(result) <= x^(2^16)`. -/
theorem flog_le (x : ℕ) (hx : 0 < x) : 2 ^ flog x ≤ x ^ 2 ^ 16 := by
  obtain ⟨-, h1, -, F, -, hr, hle⟩ := iter_inv x hx 16 le_rfl
  simp only [Nat.sub_self, pow_zero, pow_one, mul_one] at hr hle
  rw [flog, hr, pow_add]
  have : 2 ^ 32 * (2 ^ F * 2 ^ (Nat.log2 x * 2 ^ 16)) ≤ 2 ^ 32 * x ^ 2 ^ 16 := by
    calc 2 ^ 32 * (2 ^ F * 2 ^ (Nat.log2 x * 2 ^ 16))
        ≤ (iter x 16).2.1 * 2 ^ F * 2 ^ (Nat.log2 x * 2 ^ 16) := by
          rw [← mul_assoc]; gcongr
      _ ≤ x ^ 2 ^ 16 * 2 ^ 32 := hle
      _ = 2 ^ 32 * x ^ 2 ^ 16 := mul_comm _ _
  rw [mul_comm (2 ^ _) (2 ^ F)]
  exact Nat.le_of_mul_le_mul_left this (by positivity)

/-! ## Monotonicity -/

/-- Two runs of the loop after `b` iterations, the first not ahead of the second.

Either the first result is behind by at least one unit at the current bit.

Or the results agree and the first mantissa is not larger. -/
def Mono (b : ℕ) (s t : ℕ × ℕ × ℕ) : Prop :=
  s.2.2 = b ∧ t.2.2 = b ∧ (s.1 + 2 ^ (16 - b) ≤ t.1 ∨ (s.1 = t.1 ∧ s.2.1 ≤ t.2.1))

theorem step_mono (b : ℕ) (hb : b < 16) (s t : ℕ × ℕ × ℕ) (h : Mono b s t) :
    Mono (b + 1) (step s) (step t) := by
  obtain ⟨hs, ht, h⟩ := h
  have he : 2 ^ (16 - b) = 2 * 2 ^ (16 - (b + 1)) := by rw [← pow_succ']; congr 1; omega
  have h15 : 15 - b = 16 - (b + 1) := by omega
  simp only [step, hs, ht, h15]
  rcases h with h | ⟨hr, hm⟩
  · refine ⟨by split_ifs <;> rfl, by split_ifs <;> rfl, Or.inl ?_⟩
    split_ifs <;> simp only <;> omega
  · have hm' : s.2.1 * s.2.1 / 2 ^ 32 ≤ t.2.1 * t.2.1 / 2 ^ 32 :=
      Nat.div_le_div_right (Nat.mul_le_mul hm hm)
    refine ⟨by split_ifs <;> rfl, by split_ifs <;> rfl, ?_⟩
    split_ifs with h1 h2 h2
    · exact Or.inr ⟨by simp [hr], Nat.div_le_div_right hm'⟩
    · omega
    · exact Or.inl (by simp only; omega)
    · exact Or.inr ⟨hr, hm'⟩

theorem init_mono (x y : ℕ) (hxy : x ≤ y) : Mono 0 (init x) (init y) := by
  have hl : Nat.log2 x ≤ Nat.log2 y := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right hxy
  refine ⟨rfl, rfl, ?_⟩
  rcases Nat.lt_or_eq_of_le hl with hlt | heq
  · left; simp only [init, Nat.sub_zero]
    have : (Nat.log2 x + 1) * 2 ^ 16 ≤ Nat.log2 y * 2 ^ 16 := Nat.mul_le_mul_right _ hlt
    linarith
  · right; simp only [init, heq, true_and]
    split_ifs
    · exact Nat.div_le_div_right hxy
    · exact Nat.mul_le_mul_right _ hxy

theorem iter_mono (x y : ℕ) (hxy : x ≤ y) :
    ∀ n, n ≤ 16 → Mono n (iter x n) (iter y n)
  | 0, _ => init_mono x y hxy
  | n + 1, h => step_mono n (by omega) _ _ (iter_mono x y hxy n (by omega))

/-- The fixed-point floor logarithm is monotone. -/
theorem flog_mono (x y : ℕ) (hxy : x ≤ y) : flog x ≤ flog y := by
  obtain ⟨-, -, h⟩ := iter_mono x y hxy 16 le_rfl
  simp only [flog]; omega

/-- The result is at least `2^16 * floor(log_2 x)`, because the fractional bits only add. -/
theorem log2_le_flog (x : ℕ) (hx : 0 < x) : Nat.log2 x * 2 ^ 16 ≤ flog x := by
  obtain ⟨-, -, -, F, -, hr, -⟩ := iter_inv x hx 16 le_rfl
  simp only [flog, hr]; omega

/-! ## The ceiling logarithm and the bits per query -/

/-- A nonzero `x` with `x &&& (x - 1) = 0` is a power of two, `2^(log_2 x)`. -/
theorem eq_two_pow_of_and (x : ℕ) (hx : x ≠ 0) (h : x &&& (x - 1) = 0) : x = 2 ^ Nat.log2 x := by
  by_contra hne
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le hx
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  have hl : Nat.log2 (x - 1) = Nat.log2 x := by
    rw [Nat.log2_eq_iff (by omega)]; omega
  have h1 : (x - 1).testBit (Nat.log2 x) = true := by
    rw [← hl]; exact Nat.testBit_log2 (by omega)
  have h2 : (x &&& (x - 1)).testBit (Nat.log2 x) = true := by
    rw [Nat.testBit_and, Nat.testBit_log2 hx, h1]; rfl
  rw [h] at h2; simp at h2

/-- The fixed-point ceiling logarithm, on naturals.

It is exact on a power of two, and the floor logarithm plus one unit elsewhere. -/
def clog (x : ℕ) : ℕ := if x &&& (x - 1) = 0 then Nat.log2 x * 2 ^ 16 else flog x + 1

theorem flog_le_clog (x : ℕ) (hx : 0 < x) : flog x ≤ clog x := by
  unfold clog
  split_ifs with h
  · have h2 := eq_two_pow_of_and x (by omega) h
    have := flog_le x hx
    rw [h2, ← pow_mul] at this
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    rwa [← h2] at h3
  · omega

/-- The bits of security per query, on naturals.

Here `b` is the log of the blowup and `f` the field size in bits, in fixed point. -/
def bpq (b f : ℕ) : ℕ :=
  if b = 0 ∨ f = 0 ∨ (2 ^ 32 - 1) * 2 ^ 16 < f then 0
  else b * 2 ^ 16 - (clog (f + 94549 + b * 2 ^ 16) - flog f)

/-- At `x = 14917` the model loses a unit: it returns `908634`. -/
theorem flog_14917 : flog 14917 = 908634 := by decide +kernel

/-- The true value `floor(2^16 * log_2 14917)` is `908635`, one unit above the model. -/
theorem log2_14917_bounds : 2 ^ 908635 < 14917 ^ 2 ^ 16 ∧ 14917 ^ 2 ^ 16 < 2 ^ 908636 := by
  decide +kernel

/-! ## A lower bound: the truncation loses less than two units -/

/-- Truncating the square of a mantissa `m >= P` loses at most a factor `(P - 1) / P`. -/
theorem sq_div_mul (p m : ℕ) (hm : p + 1 ≤ m) : m * m * p ≤ m * m / (p + 1) * (p + 1) * (p + 1) := by
  have h1 := Nat.div_add_mod (m * m) (p + 1)
  have h2 := Nat.mod_lt (m * m) (show 0 < p + 1 by omega)
  set q := m * m / (p + 1)
  set r := m * m % (p + 1)
  have hq : p + 1 ≤ q := by
    rw [Nat.le_div_iff_mul_le (by omega)]; nlinarith
  nlinarith

/-- Halving a mantissa `m >= P`, rounded down, loses at most a factor `(P - 1) / P`. -/
theorem half_mul (p m : ℕ) (hm : p + 1 ≤ m) : m * p ≤ 2 * (m / 2) * (p + 1) := by
  have := Nat.div_add_mod m 2
  have := Nat.mod_lt m (show 0 < 2 by omega)
  nlinarith

/-- A step that reads a zero bit keeps `m^2 (P - 1)^2 <= floor(m^2 / P) P^3`, for `m >= P`. -/
theorem key_nobit (p m : ℕ) (hm : p + 1 ≤ m) :
    m * m * (p * p) ≤ m * m / (p + 1) * ((p + 1) * (p + 1) * (p + 1)) := by
  have hsq := sq_div_mul p m hm
  calc m * m * (p * p) = m * m * p * p := by ring
    _ ≤ m * m / (p + 1) * (p + 1) * (p + 1) * p := Nat.mul_le_mul_right _ hsq
    _ ≤ m * m / (p + 1) * (p + 1) * (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

/-- A step that reads a one bit keeps `m^2 (P - 1)^2 <= 2 floor(floor(m^2 / P) / 2) P^3`, for `m >= P`. -/
theorem key_bit (p m : ℕ) (hm : p + 1 ≤ m) :
    m * m * (p * p) ≤ 2 * (m * m / (p + 1) / 2) * ((p + 1) * (p + 1) * (p + 1)) := by
  have hsq := sq_div_mul p m hm
  have hq : p + 1 ≤ m * m / (p + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; nlinarith
  have hh := half_mul p (m * m / (p + 1)) hq
  calc m * m * (p * p) = m * m * p * p := by ring
    _ ≤ m * m / (p + 1) * (p + 1) * (p + 1) * p := Nat.mul_le_mul_right _ hsq
    _ = m * m / (p + 1) * p * ((p + 1) * (p + 1)) := by ring
    _ ≤ 2 * (m * m / (p + 1) / 2) * (p + 1) * ((p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hh
    _ = _ := by ring

/-- Every step keeps `(m 2^F)^2 (P - 1)^2 <= m' 2^F' P^3`, with `P = 2^32`. -/
theorem step_key (s : ℕ × ℕ × ℕ) (F : ℕ) (h1 : 2 ^ 32 ≤ s.2.1) :
    ∃ F', (step s).1 = s.1 + (F' - 2 * F) * 2 ^ (15 - s.2.2) ∧ 2 * F ≤ F' ∧ F' ≤ 2 * F + 1 ∧
      (s.2.1 * 2 ^ F) ^ 2 * (2 ^ 32 - 1) ^ 2 ≤ (step s).2.1 * 2 ^ F' * (2 ^ 32) ^ 3 := by
  have hP : (2 : ℕ) ^ 32 = (2 ^ 32 - 1) + 1 := by norm_num
  set m := s.2.1
  have hpow : (m * 2 ^ F) ^ 2 = m * m * 2 ^ (2 * F) := by
    rw [show 2 ^ (2 * F) = 2 ^ F * 2 ^ F by rw [two_mul, pow_add]]; ring
  simp only [step]
  generalize (2 : ℕ) ^ 32 - 1 = p at hP
  rw [hP] at h1 ⊢
  have hm : p + 1 ≤ m := h1
  split_ifs with hc
  · refine ⟨2 * F + 1, by simp, by omega, le_rfl, ?_⟩
    simp only
    rw [hpow]
    have := key_bit p m hm
    calc m * m * 2 ^ (2 * F) * p ^ 2 = m * m * (p * p) * 2 ^ (2 * F) := by ring
      _ ≤ 2 * (m * m / (p + 1) / 2) * ((p + 1) * (p + 1) * (p + 1)) * 2 ^ (2 * F) :=
        Nat.mul_le_mul_right _ this
      _ = _ := by ring
  · refine ⟨2 * F, by simp, le_rfl, by omega, ?_⟩
    simp only
    rw [hpow]
    have := key_nobit p m hm
    calc m * m * 2 ^ (2 * F) * p ^ 2 = m * m * (p * p) * 2 ^ (2 * F) := by ring
      _ ≤ m * m / (p + 1) * ((p + 1) * (p + 1) * (p + 1)) * 2 ^ (2 * F) :=
        Nat.mul_le_mul_right _ this
      _ = _ := by ring

/-- The lower invariant after `b` iterations.

Each truncation loses at most a factor `(P - 1) / P`, with `P = 2^32`.

Each square doubles the losses so far, so `N` of them pile up:

```text
    x^(2^16) * P^e * (P - 1)^N  <=  (m * 2^F)^e * 2^(log_2 x * 2^16) * P^N

    e = 2^(16 - b),   N = 3 * 2^16 - 2e
```
-/
def LoInv (x b : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  ∃ F, s.1 = Nat.log2 x * 2 ^ 16 + F * 2 ^ (16 - b) ∧
    x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b) * (2 ^ 32 - 1) ^ (3 * 2 ^ 16 - 2 * 2 ^ (16 - b)) ≤
      (s.2.1 * 2 ^ F) ^ 2 ^ (16 - b) * 2 ^ (Nat.log2 x * 2 ^ 16) *
        (2 ^ 32) ^ (3 * 2 ^ 16 - 2 * 2 ^ (16 - b))

theorem init_lo (x : ℕ) (hx : 0 < x) : LoInv x 0 (init x) := by
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le (by omega)
  set ip := Nat.log2 x
  -- `x (P - 1) <= m 2^ip`: scaling truncates at most one unit of a mantissa of size `P`.
  have key : x * (2 ^ 32 - 1) ≤ (init x).2.1 * 2 ^ ip := by
    simp only [init]
    split_ifs with h
    · have e : 2 ^ ip = 2 ^ (ip - 32) * 2 ^ 32 := by rw [← pow_add]; congr 1; omega
      set d := 2 ^ (ip - 32)
      have hd : 0 < d := by positivity
      have h3 := Nat.div_add_mod x d
      have h4 := Nat.mod_lt x hd
      rw [e] at hlo ⊢
      have h5 : x % d * 2 ^ 32 ≤ x := by nlinarith
      have h6 : x / d * (d * 2 ^ 32) = (x - x % d) * 2 ^ 32 := by
        rw [show x - x % d = d * (x / d) by omega]; ring
      rw [h6, Nat.sub_mul, Nat.mul_sub]
      omega
    · have e : 2 ^ 32 = 2 ^ (32 - ip) * 2 ^ ip := by rw [← pow_add]; congr 1; omega
      calc x * (2 ^ 32 - 1) ≤ x * 2 ^ 32 := Nat.mul_le_mul_left _ (by omega)
        _ = x * 2 ^ (32 - ip) * 2 ^ ip := by rw [e, mul_assoc]
  refine ⟨0, by simp [init], ?_⟩
  simp only [pow_zero, mul_one, Nat.sub_zero]
  have hN : 3 * 2 ^ 16 - 2 * 2 ^ 16 = 2 ^ 16 := by norm_num
  rw [hN]
  generalize (2 : ℕ) ^ 32 - 1 = R at key ⊢
  generalize (2 : ℕ) ^ 32 = P
  generalize (2 : ℕ) ^ 16 = E
  calc x ^ E * P ^ E * R ^ E = (x * R) ^ E * P ^ E := by rw [mul_pow]; ring
    _ ≤ ((init x).2.1 * 2 ^ ip) ^ E * P ^ E := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left key _)
    _ = (init x).2.1 ^ E * 2 ^ (ip * E) * P ^ E := by rw [mul_pow, ← pow_mul]

theorem iter_lo (x : ℕ) (hx : 0 < x) : ∀ n, n ≤ 16 → LoInv x n (iter x n)
  | 0, _ => init_lo x hx
  | n + 1, hn => by
    obtain ⟨F, hr, hle⟩ := iter_lo x hx n (by omega)
    obtain ⟨hb, h1, h2, -⟩ := iter_inv x hx n (by omega)
    obtain ⟨F', hr', hF1, hF2, hkey⟩ := step_key (iter x n) F h1
    rw [hb] at hr'
    set e' := 2 ^ (16 - (n + 1))
    have he : 2 ^ (16 - n) = 2 * e' := by
      simp only [e']; rw [← pow_succ']; congr 1; omega
    have h15 : 16 - (n + 1) = 15 - n := by omega
    set N := 3 * 2 ^ 16 - 2 * 2 ^ (16 - n)
    have hN : 3 * 2 ^ 16 - 2 * e' = N + 2 * e' := by
      simp only [N, he]
      have : e' ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have he2 : e' = 2 ^ (15 - n) := by simp only [e', h15]
    refine ⟨F', ?_, ?_⟩
    · show (step (iter x n)).1 = _
      rw [hr', hr, he, he2, h15]
      have : F' = 2 * F + (F' - 2 * F) := by omega
      conv_rhs => rw [this]
      ring
    · show x ^ 2 ^ 16 * (2 ^ 32) ^ e' * (2 ^ 32 - 1) ^ (3 * 2 ^ 16 - 2 * e') ≤
        ((step (iter x n)).2.1 * 2 ^ F') ^ e' * 2 ^ (Nat.log2 x * 2 ^ 16) *
          (2 ^ 32) ^ (3 * 2 ^ 16 - 2 * e')
      rw [hN]
      rw [he] at hle
      have hP0 : (0 : ℕ) < 2 ^ 32 := by positivity
      generalize (2 : ℕ) ^ 32 - 1 = R at hle hkey ⊢
      generalize (2 : ℕ) ^ 32 = P at hle hkey hP0 ⊢
      generalize x ^ 2 ^ 16 = X at hle ⊢
      generalize 2 ^ (Nat.log2 x * 2 ^ 16) = Q at hle ⊢
      generalize (iter x n).2.1 * 2 ^ F = a at hle hkey
      generalize (step (iter x n)).2.1 * 2 ^ F' = b at hkey ⊢
      have hpos : 0 < P ^ e' := by positivity
      apply Nat.le_of_mul_le_mul_right _ hpos
      calc X * P ^ e' * R ^ (N + 2 * e') * P ^ e'
          = X * P ^ (2 * e') * R ^ N * (R ^ 2) ^ e' := by
            rw [pow_add, two_mul, pow_add, ← pow_mul, mul_comm 2 e']; ring
        _ ≤ a ^ (2 * e') * Q * P ^ N * (R ^ 2) ^ e' := Nat.mul_le_mul_right _ hle
        _ = (a ^ 2 * R ^ 2) ^ e' * (Q * P ^ N) := by
            rw [mul_pow, ← pow_mul, mul_comm 2 e']; ring
        _ ≤ (b * P ^ 3) ^ e' * (Q * P ^ N) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hkey _)
        _ = b ^ e' * Q * P ^ (N + 2 * e') * P ^ e' := by
            rw [mul_pow, ← pow_mul]; ring

/-- All the truncation losses together cost less than a factor two.

```text
    (2^32)^N <= 2 * (2^32 - 1)^N,   N = 3 * 2^16 - 2
```
-/
theorem loss_lt_two : (2 ^ 32) ^ (3 * 2 ^ 16 - 2) ≤ 2 * (2 ^ 32 - 1) ^ (3 * 2 ^ 16 - 2) := by
  decide +kernel

/-- **The fixed-point logarithm loses less than two units.**

The result `r` satisfies `x^(2^16) < 2^(r + 2)`, that is `2^16 * log_2 x < r + 2`, for every `x > 0`. -/
theorem lt_flog_add_two (x : ℕ) (hx : 0 < x) : x ^ 2 ^ 16 < 2 ^ (flog x + 2) := by
  obtain ⟨F, hr, hle⟩ := iter_lo x hx 16 le_rfl
  obtain ⟨-, -, h2, -⟩ := iter_inv x hx 16 le_rfl
  simp only [Nat.sub_self, pow_zero, pow_one, mul_one] at hr hle
  rw [flog, hr, pow_add, pow_add]
  have hL := loss_lt_two
  have h2' : (iter x 16).2.1 < 2 * 2 ^ 32 := by rw [← pow_succ']; exact h2
  have hP0 : (0 : ℕ) < 2 ^ 32 - 1 := by norm_num
  generalize 3 * 2 ^ 16 - 2 = N at hle hL
  generalize (2 : ℕ) ^ 32 - 1 = R at hle hL hP0
  generalize (2 : ℕ) ^ 32 = P at hle hL h2'
  have hQ0 : 0 < 2 ^ (Nat.log2 x * 2 ^ 16) := by positivity
  generalize x ^ 2 ^ 16 = X at hle ⊢
  generalize 2 ^ (Nat.log2 x * 2 ^ 16) = Q at hle hQ0 ⊢
  generalize (iter x 16).2.1 = m at hle h2'
  have hR : 0 < R ^ N := by positivity
  have hP : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h | h
    · subst h; omega
    · exact h
  have hpos : 0 < P * R ^ N := by positivity
  apply lt_of_mul_lt_mul_right _ hpos.le
  calc X * (P * R ^ N) = X * P * R ^ N := by ring
    _ ≤ m * 2 ^ F * Q * P ^ N := hle
    _ < 2 * P * 2 ^ F * Q * P ^ N := by
        have hQ : 0 < 2 ^ F * Q * P ^ N := by positivity
        nlinarith
    _ ≤ 2 * P * 2 ^ F * Q * (2 * R ^ N) := Nat.mul_le_mul_left _ hL
    _ = Q * 2 ^ F * 2 ^ 2 * (P * R ^ N) := by ring

/-! ## The ceiling logarithm on Plonky3 main

Plonky3 main replaces the pinned ceiling logarithm by the minimum of two upper bounds.

That function is not in the pinned commit, so it is not extracted.

The definition below transcribes it by hand, on top of the extracted floor logarithm:

```text
    guarded = floor_log2(x) + 2
    whole   = from_bits(64 - (x - 1).leading_zeros())
    result  = min(guarded, whole)
```

For a 64-bit word `v`, the second line reads the bit length of `v`.
-/

/-- The bit length of `v`: 0 for `v = 0`, and `log_2 v + 1` otherwise. -/
def bitLength (v : ℕ) : ℕ := if v = 0 then 0 else Nat.log2 v + 1

/-- The ceiling logarithm of Plonky3 main, in fixed point, transcribed by hand. -/
def ceilLog2Main (x : ℕ) : ℕ := min (flog x + 2) (bitLength (x - 1) * 2 ^ 16)

/-- The whole-bit ceiling is an upper bound: `x <= 2^b`, with `b` the bit length of `x - 1`. -/
theorem le_two_pow_bitLength (x : ℕ) (hx : 0 < x) : x ≤ 2 ^ bitLength (x - 1) := by
  unfold bitLength
  split_ifs with h
  · omega
  · have := Nat.lt_log2_self (n := x - 1); omega

/-- **The ceiling logarithm of Plonky3 main rounds up.**

The result `r` satisfies `x^(2^16) <= 2^r`, that is `r >= 2^16 * log_2 x`, for every `x > 0`. -/
theorem le_ceilLog2Main (x : ℕ) (hx : 0 < x) : x ^ 2 ^ 16 ≤ 2 ^ ceilLog2Main x := by
  unfold ceilLog2Main
  rcases le_total (flog x + 2) (bitLength (x - 1) * 2 ^ 16) with h | h
  · rw [min_eq_left h]; exact (lt_flog_add_two x hx).le
  · rw [min_eq_right h, pow_mul]
    exact Nat.pow_le_pow_left (le_two_pow_bitLength x hx) _

/-- At `x = 14917` it returns `908636`, two units above the floor. -/
theorem ceilLog2Main_14917 : ceilLog2Main 14917 = 908636 := by decide +kernel

end Plonky3Lean.Proofs.Security.FixedLog
