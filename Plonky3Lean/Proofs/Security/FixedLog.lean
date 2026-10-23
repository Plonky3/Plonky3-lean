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

The loss is at most one unit:

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

/-! ## Rounding every truncation up -/

theorem le_ceil_div_mul (a d : ℕ) (hd : 0 < d) : a ≤ (a + d - 1) / d * d := by
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  rw [mul_comm]; omega

/-- Scaling, rounded up. -/
def initU (x : ℕ) : ℕ × ℕ × ℕ :=
  let ip := Nat.log2 x
  (ip * 2 ^ 16,
    if 32 ≤ ip then (x + 2 ^ (ip - 32) - 1) / 2 ^ (ip - 32) else x * 2 ^ (32 - ip), 0)

/-- One iteration with the square and the halving rounded up. -/
def stepU (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let m := (s.2.1 * s.2.1 + 2 ^ 32 - 1) / 2 ^ 32
  if 2 ^ 33 ≤ m then (s.1 + 2 ^ (15 - s.2.2), (m + 1) / 2, s.2.2 + 1) else (s.1, m, s.2.2 + 1)

def iterU (x : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => initU x
  | n + 1 => stepU (iterU x n)

/-- The rounded-up ceiling logarithm.

It is exact on a power of two.

Elsewhere it is the rounded-up loop's result plus one unit. -/
def cflog (x : ℕ) : ℕ := if x &&& (x - 1) = 0 then Nat.log2 x * 2 ^ 16 else (iterU x 16).1 + 1

/-- The invariant of the rounded-up loop: the mantissa never falls below the true one. -/
def InvU (x b : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  s.2.2 = b ∧ 2 ^ 32 ≤ s.2.1 ∧ s.2.1 ≤ 2 ^ 33 ∧ ∃ F, F < 2 ^ b ∧
    s.1 = Nat.log2 x * 2 ^ 16 + F * 2 ^ (16 - b) ∧
    x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b) ≤
      (s.2.1 * 2 ^ F) ^ 2 ^ (16 - b) * 2 ^ (Nat.log2 x * 2 ^ 16)

theorem initU_inv (x : ℕ) (hx : 0 < x) : InvU x 0 (initU x) := by
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le (by omega)
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  set ip := Nat.log2 x
  have key : 2 ^ 32 ≤ (initU x).2.1 ∧ (initU x).2.1 ≤ 2 ^ 33 ∧
      x * 2 ^ 32 ≤ (initU x).2.1 * 2 ^ ip := by
    simp only [initU]
    split_ifs with h
    · have e : 2 ^ ip = 2 ^ (ip - 32) * 2 ^ 32 := by rw [← pow_add]; congr 1; omega
      have e1 : 2 ^ (ip + 1) = 2 ^ (ip - 32) * 2 ^ 33 := by rw [← pow_add]; congr 1; omega
      have hp : 0 < 2 ^ (ip - 32) := by positivity
      set d := 2 ^ (ip - 32)
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.le_div_iff_mul_le hp]; rw [e] at hlo; omega
      · rw [Nat.div_le_iff_le_mul_add_pred hp]; rw [e1] at hhi; omega
      · rw [e, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (le_ceil_div_mul x d hp)
    · have e : 2 ^ 32 = 2 ^ (32 - ip) * 2 ^ ip := by rw [← pow_add]; congr 1; omega
      have e1 : 2 ^ 33 = 2 ^ (32 - ip) * 2 ^ (ip + 1) := by rw [← pow_add]; congr 1; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [e, mul_comm x]; exact Nat.mul_le_mul_left _ hlo
      · rw [e1, mul_comm x]; exact Nat.mul_le_mul_left _ hhi.le
      · rw [e, mul_assoc]
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨rfl, h1, h2, 0, by simp, by simp [initU], ?_⟩
  simp only [pow_zero, mul_one, Nat.sub_zero]
  rw [← mul_pow]
  calc (x * 2 ^ 32) ^ 2 ^ 16 ≤ ((initU x).2.1 * 2 ^ ip) ^ 2 ^ 16 := Nat.pow_le_pow_left h3 _
    _ = (initU x).2.1 ^ 2 ^ 16 * 2 ^ (ip * 2 ^ 16) := by rw [mul_pow, ← pow_mul]

theorem stepU_inv (x b : ℕ) (hb : b < 16) (s : ℕ × ℕ × ℕ) (h : InvU x b s) :
    InvU x (b + 1) (stepU s) := by
  obtain ⟨hb', h1, h2, F, hF, hr, hle⟩ := h
  set m := s.2.1
  set m' := (m * m + 2 ^ 32 - 1) / 2 ^ 32
  set e := 2 ^ (16 - (b + 1))
  have he : 2 ^ (16 - b) = 2 * e := by
    simp only [e]; rw [← pow_succ']; congr 1; omega
  have hm'ge : m * m ≤ m' * 2 ^ 32 := le_ceil_div_mul _ _ (by positivity)
  have hmm1 := Nat.mul_le_mul h1 h1
  have hmm2 := Nat.mul_le_mul h2 h2
  have hm'lo : 2 ^ 32 ≤ m' := by
    simp only [m']; rw [Nat.le_div_iff_mul_le (by positivity)]; omega
  have hm'hi : m' ≤ 2 ^ 34 := by
    simp only [m']; rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]; omega
  have hsq : x ^ 2 ^ 16 * (2 ^ 32) ^ e ≤
      (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) := by
    have hA : (m * 2 ^ F) ^ (2 ^ (16 - b)) ≤ (m' * 2 ^ (2 * F)) ^ e * (2 ^ 32) ^ e := by
      rw [he, pow_mul (m * 2 ^ F) 2 e, ← mul_pow]
      apply Nat.pow_le_pow_left
      calc (m * 2 ^ F) ^ 2 = m * m * 2 ^ (2 * F) := by
            rw [show 2 ^ (2 * F) = 2 ^ F * 2 ^ F by rw [two_mul, pow_add]]; ring
        _ ≤ m' * 2 ^ 32 * 2 ^ (2 * F) := Nat.mul_le_mul_right _ hm'ge
        _ = m' * 2 ^ (2 * F) * 2 ^ 32 := by ring
    have hpos : 0 < (2 ^ 32) ^ e := by positivity
    have := calc x ^ 2 ^ 16 * (2 ^ 32) ^ e * (2 ^ 32) ^ e
        = x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b) := by rw [he, pow_mul']; ring
      _ ≤ (m * 2 ^ F) ^ 2 ^ (16 - b) * 2 ^ (Nat.log2 x * 2 ^ 16) := hle
      _ ≤ (m' * 2 ^ (2 * F)) ^ e * (2 ^ 32) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) :=
          Nat.mul_le_mul_right _ hA
      _ = (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) * (2 ^ 32) ^ e := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hrb : 2 ^ (16 - b) = 2 * 2 ^ (15 - b) := by rw [← pow_succ']; congr 1; omega
  have h15 : 16 - (b + 1) = 15 - b := by omega
  simp only [stepU]
  split_ifs with hc
  · have hc' : 2 ^ 33 ≤ m' := hc
    refine ⟨by simp [hb'], ?_, ?_, 2 * F + 1, ?_, ?_, ?_⟩
    · show 2 ^ 32 ≤ (m' + 1) / 2; omega
    · show (m' + 1) / 2 ≤ 2 ^ 33; omega
    · rw [pow_succ]; omega
    · simp only [hb', hr, hrb, h15]; ring
    · simp only
      calc x ^ 2 ^ 16 * (2 ^ 32) ^ e ≤ (m' * 2 ^ (2 * F)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) := hsq
        _ ≤ ((m' + 1) / 2 * 2 ^ (2 * F + 1)) ^ e * 2 ^ (Nat.log2 x * 2 ^ 16) := by
          apply Nat.mul_le_mul_right; apply Nat.pow_le_pow_left
          rw [pow_succ, ← mul_assoc, mul_comm _ 2, ← mul_assoc]
          apply Nat.mul_le_mul_right; omega
  · have hc' : ¬ 2 ^ 33 ≤ m' := hc
    refine ⟨by simp [hb'], hm'lo, by show m' ≤ 2 ^ 33; omega, 2 * F, ?_, ?_, hsq⟩
    · rw [pow_succ]; omega
    · simp only [hr, hrb, h15]; ring

theorem iterU_inv (x : ℕ) (hx : 0 < x) : ∀ n, n ≤ 16 → InvU x n (iterU x n)
  | 0, _ => initU_inv x hx
  | n + 1, h => stepU_inv x n (by omega) _ (iterU_inv x hx n (by omega))

/-- **The rounded-up ceiling logarithm rounds up.**

For every `x > 0` the result is at least `2^16 * log_2 x`, that is `x^(2^16) <= 2^(result)`. -/
theorem le_cflog (x : ℕ) (hx : 0 < x) : x ^ 2 ^ 16 ≤ 2 ^ cflog x := by
  unfold cflog
  split_ifs with hp
  · have h2 := eq_two_pow_of_and x (by omega) hp
    conv_lhs => rw [h2]
    rw [← pow_mul]
  · obtain ⟨-, -, h2, F, -, hr, hle⟩ := iterU_inv x hx 16 le_rfl
    simp only [Nat.sub_self, pow_zero, pow_one, mul_one] at hr hle
    rw [hr]
    have : x ^ 2 ^ 16 * 2 ^ 32 ≤ 2 ^ (Nat.log2 x * 2 ^ 16 + F + 1) * 2 ^ 32 := by
      calc x ^ 2 ^ 16 * 2 ^ 32 ≤ (iterU x 16).2.1 * 2 ^ F * 2 ^ (Nat.log2 x * 2 ^ 16) := hle
        _ ≤ 2 ^ 33 * 2 ^ F * 2 ^ (Nat.log2 x * 2 ^ 16) := by gcongr
        _ = 2 ^ (Nat.log2 x * 2 ^ 16 + F + 1) * 2 ^ 32 := by
          simp only [pow_add, pow_one]; ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)

/-- Rounding up moves `x = 14917` up one unit, to `908636`. -/
theorem cflog_14917 : cflog 14917 = 908636 := by decide +kernel

end Plonky3Lean.Proofs.Security.FixedLog
