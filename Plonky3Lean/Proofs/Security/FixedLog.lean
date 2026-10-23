module

public import Mathlib

@[expose] public section

/-!
# The bit-by-bit binary logarithm, on naturals

`p3_security::fixed::floor_log2` computes `log2 x` in fixed point with 16 fractional bits: it
normalizes `x` to a Q32 mantissa in `[1, 2)` and squares it 16 times, truncating each square to
32 fractional bits, and reads one result bit off each square. This file states that algorithm on
naturals (`flog`) and proves that it never exceeds the true logarithm:

  `2 ^ flog x ≤ x ^ 2 ^ 16`,  that is  `flog x ≤ 2^16 · log2 x`.

Truncation can only lower the mantissa, so it can only lose result bits. The converse fails by up
to one unit: `flog 14917 = 908634`, while `⌊2^16 · log2 14917⌋ = 908635`.
-/

namespace Plonky3Lean.Proofs.Security.FixedLog

/-- The state `(result, mantissa, bit)` after normalization. -/
def init (x : ℕ) : ℕ × ℕ × ℕ :=
  let ip := Nat.log2 x
  (ip * 2 ^ 16, if 32 ≤ ip then x / 2 ^ (ip - 32) else x * 2 ^ (32 - ip), 0)

/-- One loop iteration: square the mantissa, truncate to 32 fractional bits, and take a result bit
when the square reaches `2`. -/
def step (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let m := s.2.1 * s.2.1 / 2 ^ 32
  if 2 ^ 33 ≤ m then (s.1 + 2 ^ (15 - s.2.2), m / 2, s.2.2 + 1) else (s.1, m, s.2.2 + 1)

/-- The state after `n` iterations. -/
def iter (x : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => init x
  | n + 1 => step (iter x n)

/-- `floor_log2 x`, on naturals. -/
def flog (x : ℕ) : ℕ := (iter x 16).1

theorem iter_bit (x n : ℕ) : (iter x n).2.2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, step]; split <;> simp [ih]

/-- The loop invariant after `b` iterations, with `ip = log2 x`: the mantissa stays in
`[2^32, 2^33)`, the result is `ip · 2^16 + F · 2^(16-b)` for the `b` bits `F` read so far, and the
truncated mantissa never exceeds the true one, `(m / 2^32) · 2^F ≤ (x / 2^ip)^(2^b)`, raised to
the power `2^(16-b)` to stay in naturals. -/
def Inv (x b : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  s.2.2 = b ∧ 2 ^ 32 ≤ s.2.1 ∧ s.2.1 < 2 ^ 33 ∧ ∃ F, F < 2 ^ b ∧
    s.1 = Nat.log2 x * 2 ^ 16 + F * 2 ^ (16 - b) ∧
    (s.2.1 * 2 ^ F) ^ 2 ^ (16 - b) * 2 ^ (Nat.log2 x * 2 ^ 16) ≤
      x ^ 2 ^ 16 * (2 ^ 32) ^ 2 ^ (16 - b)

theorem init_inv (x : ℕ) (hx : 0 < x) : Inv x 0 (init x) := by
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le (by omega)
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  set ip := Nat.log2 x
  -- `m · 2^ip ≤ x · 2^32` and `2^32 ≤ m < 2^33`.
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
  -- the squared invariant, before deciding the bit
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

/-- **Soundness of the fixed-point logarithm.** `flog x` never exceeds `2^16 · log2 x`:
`2 ^ flog x ≤ x ^ 2^16`. -/
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

/-- Two runs of the loop after `b` iterations, the first not ahead of the second: either the
first result is behind by at least one unit at the current bit, or the results agree and the
first mantissa is not larger. -/
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

/-- `flog` is monotone. -/
theorem flog_mono (x y : ℕ) (hxy : x ≤ y) : flog x ≤ flog y := by
  obtain ⟨-, -, h⟩ := iter_mono x y hxy 16 le_rfl
  simp only [flog]; omega

/-- `flog x ≥ 2^16 · ⌊log2 x⌋`: the fractional bits only add. -/
theorem log2_le_flog (x : ℕ) (hx : 0 < x) : Nat.log2 x * 2 ^ 16 ≤ flog x := by
  obtain ⟨-, -, -, F, -, hr, -⟩ := iter_inv x hx 16 le_rfl
  simp only [flog, hr]; omega

/-! ## `ceil_log2` and `bits_per_query` -/

/-- A nonzero `x` with `x &&& (x - 1) = 0` is `2 ^ log2 x`. -/
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

/-- `ceil_log2 x`, on naturals: exact on powers of two, `flog x + 1` elsewhere. -/
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

/-- `bits_per_query b f`, on naturals (`f` the field size in bits, in fixed point). -/
def bpq (b f : ℕ) : ℕ :=
  if b = 0 ∨ f = 0 ∨ (2 ^ 32 - 1) * 2 ^ 16 < f then 0
  else b * 2 ^ 16 - (clog (f + 94549 + b * 2 ^ 16) - flog f)

/-- The model on the input where it loses a unit: `flog 14917 = 908634`. -/
theorem flog_14917 : flog 14917 = 908634 := by decide +kernel

/-- `⌊2^16 · log2 14917⌋ = 908635`: one unit above `flog 14917`. -/
theorem log2_14917_bounds : 2 ^ 908635 < 14917 ^ 2 ^ 16 ∧ 14917 ^ 2 ^ 16 < 2 ^ 908636 := by
  decide +kernel

end Plonky3Lean.Proofs.Security.FixedLog
