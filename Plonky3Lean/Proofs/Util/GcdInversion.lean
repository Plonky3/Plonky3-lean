import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum.Prime
import P3Util
import Plonky3Lean.Lib.Scalar

/-!
# p3-util: the 32-bit GCD inversion

`gcd_inversion_prime_field_32::<F>(a, P)` runs `2F - 2` iterations of a binary GCD on `(a, b, u, v)`.

- `step` is one iteration on the mathematical values, and `run` the value of `v` after `n` of them.
- The extracted function never panics for `1 ≤ F ≤ 32` and `P < 2^F`, and returns `run (2F - 2) a P`.
- `Bound` bounds `(u, v)` by the iteration count alone, which rules out `i64` overflow.
- `Inv` is the invariant that makes `b = gcd(a, P)` at the end, so that `v a ≡ 2^{2F-2} gcd(a, P)`.
-/

open Aeneas Aeneas.Std Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Util

/-! ## The loop, on integers -/

/-- One iteration of the loop, on the values of `(a, b, u, v)`. -/
def step (s : ℕ × ℕ × ℤ × ℤ) : ℕ × ℕ × ℤ × ℤ :=
  if s.1 % 2 = 1 then
    if s.1 < s.2.1 then ((s.2.1 - s.1) / 2, s.1, s.2.2.2 - s.2.2.1, 2 * s.2.2.1)
    else ((s.1 - s.2.1) / 2, s.2.1, s.2.2.1 - s.2.2.2, 2 * s.2.2.2)
  else (s.1 / 2, s.2.1, s.2.2.1, 2 * s.2.2.2)

/-- The state after `n` iterations from `(a, b, 1, 0)`. -/
def iter (n a b : ℕ) : ℕ × ℕ × ℤ × ℤ := step^[n] (a, b, 1, 0)

/-- The value the function returns after `n` iterations. -/
def run (n a b : ℕ) : ℤ := (iter n a b).2.2.2

theorem iter_succ (n a b : ℕ) : iter (n + 1) a b = step (iter n a b) := by
  simp only [iter, Function.iterate_succ_apply']

/-! ## The size of the coefficients

The bound on `(u, v)` after `i` iterations depends on `i` only. -/

/-- The size of `(u, v)` after `i` iterations.

At `i = 0` the pair is `(1, 0)`.

From `i = 1` on:
- `u` and `v` have opposite signs,
- `|u| ≤ 2^i - 1` and `|u| + |v| ≤ 2^{i+1} - 1`,
- `-(2^i - 2) ≤ v ≤ 2^i`.
-/
def Bound (i : ℕ) (u v : ℤ) : Prop :=
  (i = 0 ∧ u = 1 ∧ v = 0) ∨
  (1 ≤ i ∧
    ((0 ≤ u ∧ v ≤ 0 ∧ u ≤ 2 ^ i - 1 ∧ u - v ≤ 2 ^ (i + 1) - 1 ∧ -v ≤ 2 ^ i - 2) ∨
     (u ≤ 0 ∧ 0 ≤ v ∧ -u ≤ 2 ^ i - 1 ∧ v - u ≤ 2 ^ (i + 1) - 1 ∧ v ≤ 2 ^ i)))

theorem bound_step (i : ℕ) (s : ℕ × ℕ × ℤ × ℤ) (h : Bound i s.2.2.1 s.2.2.2) :
    Bound (i + 1) (step s).2.2.1 (step s).2.2.2 := by
  obtain ⟨a, b, u, v⟩ := s
  have hK : (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i := by ring
  have hK2 : (2 : ℤ) ^ (i + 1 + 1) = 4 * 2 ^ i := by ring
  have hK0 : (1 : ℤ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  unfold Bound at h ⊢
  rw [hK, hK2]
  generalize (2 : ℤ) ^ i = K at *
  dsimp only at h
  dsimp only [step]
  split_ifs <;> dsimp only <;> omega

theorem bound_iter (n a b : ℕ) : Bound n (iter n a b).2.2.1 (iter n a b).2.2.2 := by
  induction n with
  | zero => left; simp [iter]
  | succ n ih => rw [iter_succ]; exact bound_step n _ ih

/-- The returned value lies in `[-(2^n - 2), 2^n]` for `n ≥ 1`. -/
theorem run_bounds (n a b : ℕ) (hn : 1 ≤ n) :
    -(2 ^ n - 2) ≤ run n a b ∧ run n a b ≤ 2 ^ n := by
  have h := bound_iter n a b
  have hK0 : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hK : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  unfold Bound at h
  unfold run
  rw [hK] at h
  generalize (2 : ℤ) ^ n = K at *
  omega

/-! ## What the loop computes -/

/-- The loop invariant after `i` iterations from `(a_0, P, 1, 0)`, with `g = gcd(a_0, P)`.

- `b` is odd.
- `gcd(a, b) = g`.
- `2^i a ≡ u a_0` and `2^i b ≡ v a_0` modulo `P`.
- Either `a = 0` and `b = g`, or the bit lengths of `a` and `b` add up to at most `2F - i`.
-/
def Inv (F P a₀ i : ℕ) (a b : ℕ) (u v : ℤ) : Prop :=
  b % 2 = 1 ∧ Nat.gcd a b = Nat.gcd a₀ P ∧
  (2 ^ i * a : ℤ) ≡ u * a₀ [ZMOD P] ∧ (2 ^ i * b : ℤ) ≡ v * a₀ [ZMOD P] ∧
  ((a = 0 ∧ b = Nat.gcd a₀ P) ∨ ∃ x y, a < 2 ^ x ∧ b < 2 ^ y ∧ x + y + i ≤ 2 * F)

theorem half_lt {c x : ℕ} (h : c < 2 ^ x) (hc : 0 < c) : 1 ≤ x ∧ c / 2 < 2 ^ (x - 1) := by
  cases x with
  | zero => simp at h; omega
  | succ k => rw [Nat.pow_succ] at h; simp only [Nat.add_sub_cancel]; omega

/-- Halving the even entry keeps the gcd with an odd number. -/
theorem gcd_half {c b : ℕ} (hc : c % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd (c / 2) b = Nat.gcd c b := by
  obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k := ⟨c / 2, by omega⟩
  rw [Nat.mul_div_cancel_left _ (by norm_num), Nat.Coprime.gcd_mul_left_cancel]
  rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hb

/-- Halving the even entry divides `2^i c` by `2` while `i` grows by one. -/
theorem pow_half {c : ℕ} (i : ℕ) (hc : c % 2 = 0) :
    (2 ^ (i + 1) * ((c / 2 : ℕ) : ℤ)) = 2 ^ i * (c : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k := ⟨c / 2, by omega⟩
  rw [Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring

theorem inv_step {F P a₀ i a b : ℕ} {u v : ℤ} (h : Inv F P a₀ i a b u v) :
    Inv F P a₀ (i + 1) (step (a, b, u, v)).1 (step (a, b, u, v)).2.1
      (step (a, b, u, v)).2.2.1 (step (a, b, u, v)).2.2.2 := by
  obtain ⟨hb, hg, hu, hv, hlen⟩ := h
  -- The gcd, parity and congruence parts, and the length part when the new `a` is positive.
  suffices H : (step (a, b, u, v)).2.1 % 2 = 1 ∧
      Nat.gcd (step (a, b, u, v)).1 (step (a, b, u, v)).2.1 = Nat.gcd a₀ P ∧
      (2 ^ (i + 1) * (step (a, b, u, v)).1 : ℤ) ≡ (step (a, b, u, v)).2.2.1 * a₀ [ZMOD P] ∧
      (2 ^ (i + 1) * (step (a, b, u, v)).2.1 : ℤ) ≡ (step (a, b, u, v)).2.2.2 * a₀ [ZMOD P] ∧
      (0 < (step (a, b, u, v)).1 → ∃ x y, (step (a, b, u, v)).1 < 2 ^ x ∧
        (step (a, b, u, v)).2.1 < 2 ^ y ∧ x + y + (i + 1) ≤ 2 * F) by
    obtain ⟨h1, h2, h3, h4, h5⟩ := H
    refine ⟨h1, h2, h3, h4, ?_⟩
    rcases Nat.eq_zero_or_pos (step (a, b, u, v)).1 with h0 | h0
    · left; rw [h0, Nat.gcd_zero_left] at h2; exact ⟨h0, h2⟩
    · right; exact h5 h0
  have hpow : (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i := by ring
  simp only [step]
  split_ifs with hodd hlt
  · -- `a` odd, `a < b`: swap, subtract, halve.
    have hc : (b - a) % 2 = 0 := by omega
    refine ⟨hodd, ?_, ?_, ?_, ?_⟩
    · rw [gcd_half hc hodd, Nat.gcd_sub_self_left hlt.le, Nat.gcd_comm, hg]
    · rw [pow_half i hc, Nat.cast_sub hlt.le, mul_sub, sub_mul]
      exact hv.sub hu
    · rw [hpow, mul_assoc, mul_assoc]; exact hu.mul_left 2
    · intro _
      rcases hlen with ⟨ha0, -⟩ | ⟨x, y, hx, hy, hxy⟩
      · omega
      · obtain ⟨hy1, hy'⟩ := half_lt (c := b - a) (x := y) (by omega) (by omega)
        exact ⟨y - 1, x, hy', hx, by omega⟩
  · -- `a` odd, `b ≤ a`: subtract, halve.
    have hle : b ≤ a := Nat.le_of_not_lt hlt
    have hc : (a - b) % 2 = 0 := by omega
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · rw [gcd_half hc hb, Nat.gcd_sub_self_left hle, hg]
    · rw [pow_half i hc, Nat.cast_sub hle, mul_sub, sub_mul]
      exact hu.sub hv
    · rw [hpow, mul_assoc, mul_assoc]; exact hv.mul_left 2
    · intro hpos
      rcases hlen with ⟨ha0, -⟩ | ⟨x, y, hx, hy, hxy⟩
      · omega
      · obtain ⟨hx1, hx'⟩ := half_lt (c := a - b) (x := x) (by omega) (by omega)
        exact ⟨x - 1, y, hx', hy, by omega⟩
  · -- `a` even: halve.
    have hc : a % 2 = 0 := by omega
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · rw [gcd_half hc hb, hg]
    · rw [pow_half i hc]; exact hu
    · rw [hpow, mul_assoc, mul_assoc]; exact hv.mul_left 2
    · intro hpos
      rcases hlen with ⟨ha0, -⟩ | ⟨x, y, hx, hy, hxy⟩
      · subst ha0; simp at hpos
      · obtain ⟨hx1, hx'⟩ := half_lt (c := a) (x := x) hx (by omega)
        exact ⟨x - 1, y, hx', hy, by omega⟩

theorem inv_iter {F P a₀ : ℕ} (hP : P % 2 = 1) (ha : a₀ < 2 ^ F) (hPF : P < 2 ^ F) (n : ℕ) :
    Inv F P a₀ n (iter n a₀ P).1 (iter n a₀ P).2.1 (iter n a₀ P).2.2.1 (iter n a₀ P).2.2.2 := by
  induction n with
  | zero =>
    refine ⟨hP, rfl, ?_, ?_, Or.inr ⟨F, F, ha, hPF, by omega⟩⟩
    · simp [iter]
    · simp only [iter, Function.iterate_zero, id, pow_zero, one_mul, zero_mul]
      simp [Int.ModEq]
  | succ n ih => rw [iter_succ]; exact inv_step ih

/-- At the end of the loop `b = gcd(a_0, P)`. -/
theorem inv_end {F P a₀ a b : ℕ} {u v : ℤ} (h : Inv F P a₀ (2 * F - 2) a b u v) (hF : 1 ≤ F) :
    b = Nat.gcd a₀ P := by
  obtain ⟨hb, hg, -, -, hlen⟩ := h
  rcases hlen with ⟨-, h⟩ | ⟨x, y, hx, hy, hxy⟩
  · exact h
  · rw [← hg]
    have hy1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with rfl | h
      · simp at hy; omega
      · exact h
    rcases Nat.eq_zero_or_pos x with rfl | hx1
    · simp at hx; subst hx; simp
    · have hx' : x = 1 := by omega
      have hy' : y = 1 := by omega
      subst hx' hy'
      have : b = 1 := by simp at hy; omega
      subst this; simp

/-- After `2F - 2` iterations, `v a_0 ≡ 2^{2F-2} gcd(a_0, P) (mod P)`. -/
theorem run_cong {F P a₀ : ℕ} (hF : 1 ≤ F) (hP : P % 2 = 1) (ha : a₀ < 2 ^ F)
    (hPF : P < 2 ^ F) :
    run (2 * F - 2) a₀ P * a₀ ≡ 2 ^ (2 * F - 2) * (Nat.gcd a₀ P : ℤ) [ZMOD P] := by
  have h := inv_iter hP ha hPF (2 * F - 2)
  have hb := inv_end h hF
  obtain ⟨-, -, -, hv, -⟩ := h
  rw [hb] at hv
  exact hv.symm

/-! ## The extracted loop body -/

/-- `x << 1` on an `i64` doubles `x` when `|x| < 2^62`. -/
theorem shl_one_bmod {x : ℤ} (h1 : -2 ^ 62 < x) (h2 : x < 2 ^ 62) :
    (x <<< 1).bmod I64.size = 2 * x := by
  rw [Int.shiftLeft_eq, I64.size, I64.numBits, IScalarTy.I64_numBits_eq]
  rw [Int.bmod_eq_of_le] <;> push_cast <;> omega

open p3_util in
/-- One iteration of the extracted body is `step`, and the loop exits exactly at `i = 2F - 2`. -/
theorem body_spec (F a b : Std.U32) (u v : Std.I64) (i : Std.U32) (hF1 : 1 ≤ F.val)
    (hF : F.val ≤ 32)
    (huv : i.val < 2 * F.val - 2 →
      -2 ^ 62 < u.val ∧ u.val < 2 ^ 62 ∧ -2 ^ 62 < v.val ∧ v.val < 2 ^ 62) :
    gcd_inversion_prime_field_32_loop.body F a b u v i ⦃ r => match r with
      | .done y => 2 * F.val - 2 ≤ i.val ∧ y = v
      | .cont (a', b', u', v', i') => i.val < 2 * F.val - 2 ∧ i'.val = i.val + 1 ∧
          (a'.val, b'.val, u'.val, v'.val) = step (a.val, b.val, u.val, v.val) ⦄ := by
  unfold gcd_inversion_prime_field_32_loop.body
  step*
  have hi3 : i3.val = a.val % 2 := by
    rw [i3_post1, UScalar.val_and]; exact Nat.and_one_is_mod _
  have hiN : i.val < 2 * F.val - 2 := by scalar_tac
  obtain ⟨hu1, hu2, hv1, hv2⟩ := huv hiN
  by_cases hodd : a.val % 2 = 1
  · have hne : (i3 != 0#u32) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; rw [h] at hi3; simp at hi3; omega
    simp only [hne, if_true]
    by_cases hlt : a < b
    · simp only [hlt, if_true]
      step*
      have hlt' : a.val < b.val := by scalar_tac
      refine ⟨hiN, i4_post, ?_⟩
      simp only [step, hodd, if_true, hlt', a2_post1, x_post1, Nat.shiftRight_eq_div_pow,
        pow_one, x_post, v2_post1, shl_one_bmod hu1 hu2]
    · simp only [hlt, if_false]
      step*
      have hlt' : ¬ a.val < b.val := by scalar_tac
      refine ⟨hiN, i4_post, ?_⟩
      simp only [step, hodd, if_true, hlt', if_false, a2_post1, x_post1,
        Nat.shiftRight_eq_div_pow, pow_one, x_post, v2_post1, shl_one_bmod hv1 hv2]
  · have hne : (i3 != 0#u32) = false := by
      simp only [bne_eq_false_iff_eq]; scalar_tac
    simp only [hne, Bool.false_eq_true, if_false]
    step*
    refine ⟨hiN, i4_post, ?_⟩
    simp only [step, hodd, if_false, a2_post1, Nat.shiftRight_eq_div_pow, pow_one, v2_post1,
      shl_one_bmod hv1 hv2]

/-- Up to `i = 61`, `|u|, |v| < 2^62`, so the next iteration fits in an `i64`. -/
theorem bound_small {i : ℕ} {u v : ℤ} (hi : i ≤ 61) (h : Bound i u v) :
    -2 ^ 62 < u ∧ u < 2 ^ 62 ∧ -2 ^ 62 < v ∧ v < 2 ^ 62 := by
  have hK : (2 : ℤ) ^ i ≤ 2 ^ 61 := pow_le_pow_right₀ (by norm_num) hi
  have hK1 : (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i := by ring
  unfold Bound at h
  rw [hK1] at h
  generalize (2 : ℤ) ^ i = K at *
  omega

/-! ## The extracted function -/

open p3_util in
/-- The loop returns the value of `v` after `2F - 2` iterations, without panicking. -/
theorem loop_spec (F a b : Std.U32) (hF1 : 1 ≤ F.val) (hF : F.val ≤ 32) :
    gcd_inversion_prime_field_32_loop F a b 1#i64 0#i64 0#u32 ⦃ y =>
      y.val = run (2 * F.val - 2) a.val b.val ⦄ := by
  unfold gcd_inversion_prime_field_32_loop
  apply loop.spec_decr_nat (fun s => 2 * F.val - 2 - s.2.2.2.2.val)
    (fun s => s.2.2.2.2.val ≤ 2 * F.val - 2 ∧
      (s.1.val, s.2.1.val, s.2.2.1.val, s.2.2.2.1.val) = iter s.2.2.2.2.val a.val b.val)
  · rintro ⟨a', b', u', v', i'⟩ ⟨hi, hs⟩
    simp only at hi hs
    refine WP.spec_mono (body_spec F a' b' u' v' i' hF1 hF ?_) ?_
    · intro hlt
      have hB := bound_iter i'.val a.val b.val
      rw [← hs] at hB
      exact bound_small (by omega) hB
    · rintro (⟨a'', b'', u'', v'', i''⟩ | y) h
      · obtain ⟨hlt, hi', hs'⟩ := h
        refine ⟨⟨by simp only; omega, ?_⟩, by simp only; omega⟩
        simp only
        rw [hs', hi', iter_succ, hs]
      · obtain ⟨hge, rfl⟩ := h
        have hN : i'.val = 2 * F.val - 2 := by omega
        simp only [run]
        rw [← hN, ← hs]
  · simp [iter]

open p3_util in
/-- For `1 ≤ F ≤ 32` and `b < 2^F`, the function never panics, whatever `a`.

It returns the value of `v` after `2F - 2` iterations. -/
theorem gcd_inversion_prime_field_32.spec (F a b : Std.U32) (hF1 : 1 ≤ F.val) (hF : F.val ≤ 32)
    (hb : b.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F a b ⦃ y => y.val = run (2 * F.val - 2) a.val b.val ⦄ := by
  unfold gcd_inversion_prime_field_32
  have hpow : (2 : ℕ) ^ F.val < U64.size := by
    rw [U64.size, U64.numBits, UScalarTy.U64_numBits_eq]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpow1 : 1 ≤ (2 : ℕ) ^ F.val := Nat.one_le_two_pow
  step*
  exact loop_spec F a b hF1 hF

/-! ## Boundary inputs -/

/-- From `a = 0` nothing moves except `v = 0`, which doubles. -/
theorem iter_zero_left (n b : ℕ) : iter n 0 b = (0, b, 1, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih]; simp [step]

/-- From `a = 1` and `b > 1`, the first iteration swaps to `b = 1`.

From then on `b` stays `1` and `v = 2^i`. -/
theorem iter_one_left {b : ℕ} (hb : 1 < b) (n : ℕ) (hn : 1 ≤ n) :
    (iter n 1 b).2.1 = 1 ∧ (iter n 1 b).2.2.2 = 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [iter_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [iter, step, hb]
    · obtain ⟨h1, h2⟩ := ih hn'
      generalize iter n 1 b = s at h1 h2 ⊢
      obtain ⟨a, b', u, v⟩ := s
      simp only at h1 h2
      subst h1 h2
      simp only [step]
      split_ifs
      · omega
      · exact ⟨rfl, by ring⟩
      · exact ⟨rfl, by ring⟩

/-! ## `FIELD_BITS = 31` -/

open p3_util in
/-- The result for `FIELD_BITS = 31`, an odd `b < 2^31` and `a < 2^31`. -/
theorem gcd_inversion_prime_field_32.spec_31 (a b : Std.U32) (hb : b.val < 2 ^ 31)
    (hodd : b.val % 2 = 1) (ha : a.val < 2 ^ 31) :
    gcd_inversion_prime_field_32 31#u32 a b ⦃ v => -(2 ^ 60 - 2) ≤ v.val ∧ v.val ≤ 2 ^ 60 ∧
      v.val * a.val ≡ 2 ^ 60 * (Nat.gcd a.val b.val : ℤ) [ZMOD b.val] ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec 31#u32 a b (by decide) (by decide) hb) ?_
  intro v hv
  have hN : 2 * (31#u32 : Std.U32).val - 2 = 60 := by decide
  rw [hN] at hv
  rw [hv]
  obtain ⟨h1, h2⟩ := run_bounds 60 a.val b.val (by norm_num)
  have h3 := run_cong (F := 31) (by norm_num) hodd ha hb
  exact ⟨h1, h2, h3⟩


/-! ## Any `FIELD_BITS` -/

open p3_util in
/-- With `b ≥ 2^F` the `debug_assert` fails. -/
theorem gcd_inversion_prime_field_32.panics (F a b : Std.U32) (hF : F.val ≤ 32)
    (hb : 2 ^ F.val ≤ b.val) :
    gcd_inversion_prime_field_32 F a b = .fail .panic := by
  unfold gcd_inversion_prime_field_32
  have h1 : F ≤ 32#u32 := by scalar_tac
  simp only [massert, h1, if_true, bind_tc_ok]
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
  have h2 : F.val < UScalarTy.U64.numBits := by simp; omega
  simp only [h2, if_true, bind_tc_ok]
  set x : Std.U64 := UScalar.mk (1#u64.bv.shiftLeft F.val) with hxdef
  have hx : x.val = 2 ^ F.val := by
    have : F.val < 64 := by omega
    change (BitVec.shiftLeft (1#u64 : Std.U64).bv F.val).toNat = _
    refine (BitVec.toNat_shiftLeft (x := (1#u64 : Std.U64).bv) (n := F.val)).trans ?_
    rw [UScalar.bv_toNat, show (1#u64 : Std.U64).val = 1 from rfl, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) this)
  have hs := UScalar.sub_equiv x 1#u64
  split at hs
  · rename_i z hz
    rw [hz]
    have hcast : (UScalar.cast UScalarTy.U64 b).val = b.val := cast_u32_u64_val b
    have hn : ¬ z ≥ UScalar.cast UScalarTy.U64 b := by scalar_tac
    simp only [bind_tc_ok, lift, hn, if_false, bind_tc_fail]
  · obtain ⟨-, hlt⟩ := hs
    rw [hx] at hlt
    have : 1 ≤ 2 ^ F.val := Nat.one_le_two_pow
    scalar_tac
  · simp at hs

open p3_util in
/-- For `2 ≤ F ≤ 32` and `b < 2^F`, whatever `a`, the function never panics.

Its result lies in `[-(2^{2F-2} - 2), 2^{2F-2}]`. -/
theorem gcd_inversion_prime_field_32.bounds (F a b : Std.U32) (hF2 : 2 ≤ F.val)
    (hF : F.val ≤ 32) (hb : b.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F a b ⦃ v =>
      -(2 ^ (2 * F.val - 2) - 2) ≤ v.val ∧ v.val ≤ 2 ^ (2 * F.val - 2) ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec F a b (by omega) hF hb) ?_
  intro v hv
  rw [hv]
  exact run_bounds _ _ _ (by omega)

open p3_util in
/-- For `1 ≤ F ≤ 32`, an odd `b < 2^F` and `a < 2^F`, the result is `2^{2F-2} gcd(a, b) / a`.

That is, `v a ≡ 2^{2F-2} gcd(a, b) (mod b)`. -/
theorem gcd_inversion_prime_field_32.cong (F a b : Std.U32) (hF1 : 1 ≤ F.val)
    (hF : F.val ≤ 32) (hb : b.val < 2 ^ F.val) (hodd : b.val % 2 = 1) (ha : a.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F a b ⦃ v =>
      v.val * a.val ≡ 2 ^ (2 * F.val - 2) * (Nat.gcd a.val b.val : ℤ) [ZMOD b.val] ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec F a b hF1 hF hb) ?_
  intro v hv
  rw [hv]
  exact run_cong hF1 hodd ha hb

open p3_util in
/-- `a = 0` returns `0`. -/
theorem gcd_inversion_prime_field_32.zero (F b : Std.U32) (hF1 : 1 ≤ F.val) (hF : F.val ≤ 32)
    (hb : b.val < 2 ^ F.val) :
    gcd_inversion_prime_field_32 F 0#u32 b ⦃ v => v.val = 0 ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec F 0#u32 b hF1 hF hb) ?_
  intro v hv
  rw [hv, run, show (0#u32 : Std.U32).val = 0 from rfl, iter_zero_left]

open p3_util in
/-- `a = 1` returns exactly `2^{2F-2}`, for every `b > 1`. -/
theorem gcd_inversion_prime_field_32.one (F b : Std.U32) (hF2 : 2 ≤ F.val) (hF : F.val ≤ 32)
    (hb : b.val < 2 ^ F.val) (hb1 : 1 < b.val) :
    gcd_inversion_prime_field_32 F 1#u32 b ⦃ v => v.val = 2 ^ (2 * F.val - 2) ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec F 1#u32 b (by omega) hF hb) ?_
  intro v hv
  rw [hv, run, show (1#u32 : Std.U32).val = 1 from rfl]
  exact (iter_one_left hb1 _ (by omega)).2

/-! ## `FIELD_BITS = 31`, prime `b` -/

open p3_util in
/-- For an odd prime `b < 2^31` and `0 < a < b`, the result is `2^60 a^{-1} mod b`.

It lies in `[-2^60, 2^60]`. -/
theorem gcd_inversion_prime_field_32.spec_prime (a b : Std.U32) (hp : Nat.Prime b.val)
    (hodd : b.val % 2 = 1) (hb : b.val < 2 ^ 31) (ha0 : 0 < a.val) (hab : a.val < b.val) :
    gcd_inversion_prime_field_32 31#u32 a b ⦃ v =>
      |v.val| ≤ 2 ^ 60 ∧ v.val * a.val ≡ 2 ^ 60 [ZMOD b.val] ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec_31 a b hb hodd (by omega)) ?_
  rintro v ⟨h1, h2, h3⟩
  have hg : Nat.gcd a.val b.val = 1 := (Nat.coprime_of_lt_prime (by omega) hab hp).symm
  rw [hg, Nat.cast_one, mul_one] at h3
  exact ⟨abs_le.mpr ⟨by linarith, h2⟩, h3⟩

/-- For `P ≥ 2^30` and `v` in the result range, `P 2^30 + v` lies in `(0, 2^32 P)`. -/
theorem pos_inverse_range {P v : ℤ} (hP : 2 ^ 30 ≤ P) (hv1 : -(2 ^ 60 - 2) ≤ v)
    (hv2 : v ≤ 2 ^ 60) : 0 < P * 2 ^ 30 + v ∧ P * 2 ^ 30 + v < 2 ^ 32 * P := by
  constructor <;> nlinarith

open p3_util in
/-- For `2^30 ≤ b < 2^31` and any `a`, `b 2^30 + v` lies in `(0, 2^32 b)`. -/
theorem gcd_inversion_prime_field_32.pos_inverse (a b : Std.U32) (hb1 : 2 ^ 30 ≤ b.val)
    (hb : b.val < 2 ^ 31) :
    gcd_inversion_prime_field_32 31#u32 a b ⦃ v =>
      0 < (b.val : ℤ) * 2 ^ 30 + v.val ∧ (b.val : ℤ) * 2 ^ 30 + v.val < 2 ^ 32 * b.val ⦄ := by
  refine WP.spec_mono
    (gcd_inversion_prime_field_32.bounds 31#u32 a b (by decide) (by decide) hb) ?_
  rintro v ⟨h1, h2⟩
  exact pos_inverse_range (by exact_mod_cast hb1) h1 h2

/-! ## Concrete inputs, evaluated by the kernel -/

/-- `536870909 = 2^29 - 3` is prime. -/
theorem small_prime_is_prime : Nat.Prime 536870909 := by norm_num

set_option maxRecDepth 10000 in
open p3_util in
/-- For the prime `P = 536870909 < 2^30` and `a = 194997`, `P 2^30 + v` is negative. -/
theorem gcd_inversion_prime_field_32.small_prime :
    gcd_inversion_prime_field_32 31#u32 194997#u32 536870909#u32 ⦃ v =>
      v.val = -580141285873025024 ∧ (536870909 : ℤ) * 2 ^ 30 + v.val < 0 ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec _ _ _ (by decide) (by decide)
    (by decide)) ?_
  intro v hv
  have h : run 60 194997 536870909 = -580141285873025024 := by decide
  have hN : 2 * (31#u32 : Std.U32).val - 2 = 60 := by decide
  rw [hN, show (194997#u32 : Std.U32).val = 194997 from rfl,
    show (536870909#u32 : Std.U32).val = 536870909 from rfl, h] at hv
  rw [hv]
  exact ⟨rfl, by norm_num⟩

set_option maxRecDepth 10000 in
open p3_util in
/-- For BabyBear's prime and `a = 3 · 2^30 ≥ 2^31`, the result is not `2^60 a^{-1}`. -/
theorem gcd_inversion_prime_field_32.large_a :
    gcd_inversion_prime_field_32 31#u32 3221225472#u32 2013265921#u32 ⦃ v =>
      v.val = 2 ^ 30 ∧ ¬ v.val * 3221225472 ≡ 2 ^ 60 [ZMOD 2013265921] ⦄ := by
  refine WP.spec_mono (gcd_inversion_prime_field_32.spec _ _ _ (by decide) (by decide)
    (by decide)) ?_
  intro v hv
  have h : run 60 3221225472 2013265921 = 2 ^ 30 := by decide
  have hN : 2 * (31#u32 : Std.U32).val - 2 = 60 := by decide
  rw [hN, show (3221225472#u32 : Std.U32).val = 3221225472 from rfl,
    show (2013265921#u32 : Std.U32).val = 2013265921 from rfl, h] at hv
  rw [hv]
  exact ⟨rfl, by decide⟩

end Plonky3Lean.Proofs.Util
