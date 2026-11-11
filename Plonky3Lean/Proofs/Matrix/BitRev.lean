module

public import Plonky3Lean.Spec.Matrix

@[expose] public section

/-!
# Bit reversal

The bits, range and involution of k-bit reversal, and the identity behind bit-reversed zero padding.
-/

namespace Plonky3Lean.Proofs.Matrix

open Plonky3Lean.Spec.Matrix

theorem bitRev_lt (k i : ℕ) : bitRev k i < 2 ^ k := by
  induction k generalizing i with
  | zero => simp [bitRev]
  | succ k ih =>
    simp only [bitRev, pow_succ]
    have := ih (i / 2)
    have : i % 2 ≤ 1 := by omega
    nlinarith

theorem testBit_bitRev (k i j : ℕ) :
    (bitRev k i).testBit j = (decide (j < k) && i.testBit (k - 1 - j)) := by
  induction k generalizing i j with
  | zero => simp [bitRev]
  | succ k ih =>
    simp only [bitRev]
    have hlt := bitRev_lt k (i / 2)
    rw [show i % 2 * 2 ^ k + bitRev k (i / 2) = 2 ^ k * (i % 2) + bitRev k (i / 2) by ring,
      Nat.testBit_two_pow_mul_add _ hlt, ih]
    rcases Nat.lt_trichotomy j k with h | h | h
    · simp only [h, ite_true, decide_true, Bool.true_and, show j < k + 1 by omega]
      rw [Nat.testBit_div_two]; congr 1; omega
    · subst h
      simp only [lt_irrefl, ite_false, Nat.sub_self, show j < j + 1 by omega, decide_true,
        Bool.true_and, Nat.add_sub_cancel, Nat.sub_self]
      rw [Nat.testBit_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one i with h2 | h2 <;> simp [h2]
    · simp only [show ¬ j < k by omega, ite_false, show ¬ j < k + 1 by omega, decide_false,
        Bool.false_and]
      rw [Nat.testBit_eq_false_of_lt]
      calc i % 2 < 2 := Nat.mod_lt _ (by omega)
        _ = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j - k) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Reversing k bits twice is the identity on [0, 2^k). -/
theorem bitRev_bitRev {k i : ℕ} (hi : i < 2 ^ k) : bitRev k (bitRev k i) = i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitRev, testBit_bitRev]
  by_cases hj : j < k
  · simp [hj, show k - 1 - j < k by omega, show k - 1 - (k - 1 - j) = j by omega]
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega)
      (by omega)))).symm

/-- Reversing n + k bits of j 2^k reverses the n bits of j. -/
theorem bitRev_mul_two_pow (n k j : ℕ) : bitRev (n + k) (j * 2 ^ k) = bitRev n j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_bitRev, testBit_bitRev, Nat.testBit_mul_two_pow]
  by_cases ht : t < n
  · simp [ht, show t < n + k by omega, show k ≤ n + k - 1 - t by omega,
      show n + k - 1 - t - k = n - 1 - t by omega]
  · simp only [ht, decide_false, Bool.false_and]
    by_cases ht' : t < n + k
    · simp [ht', show ¬ k ≤ n + k - 1 - t by omega]
    · simp [ht']

/-- Reversing n + k bits of m < 2^n reverses its n bits and shifts them up by k. -/
theorem bitRev_add_of_lt {n k m : ℕ} (hm : m < 2 ^ n) : bitRev (n + k) m = bitRev n m * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_bitRev, Nat.testBit_mul_two_pow, testBit_bitRev]
  by_cases hkt : k ≤ t
  · by_cases htn : t - k < n
    · simp [hkt, htn, show t < n + k by omega, show n + k - 1 - t = n - 1 - (t - k) by omega]
    · simp only [hkt, htn, decide_false, Bool.false_and, decide_true, Bool.true_and,
        Bool.and_eq_false_imp, decide_eq_true_eq]
      intro _
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
  · simp only [hkt, decide_false, Bool.false_and, Bool.and_eq_false_imp, decide_eq_true_eq]
    intro _
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))

/-- An index below 2^(n + k) reverses into the first 2^n exactly when 2^k divides it. -/
theorem bitRev_lt_iff_dvd {n k i : ℕ} (hi : i < 2 ^ (n + k)) :
    bitRev (n + k) i < 2 ^ n ↔ 2 ^ k ∣ i := by
  constructor
  · intro h
    rw [← bitRev_bitRev hi, bitRev_add_of_lt h]
    exact Dvd.intro_left _ rfl
  · rintro ⟨j, rfl⟩
    rw [mul_comm, bitRev_mul_two_pow]
    exact bitRev_lt n j

variable {T : Type _}

theorem bitRevRows_apply {k w : ℕ} (M : Mat (2 ^ k) w T) (r : Fin (2 ^ k)) (c : Fin w) :
    bitRevRows M r c = M ⟨bitRev k r.val, bitRev_lt k r.val⟩ c := by
  simp [bitRevRows, Nat.mod_eq_of_lt (bitRev_lt k r.val)]

/-- Viewing the rows in bit-reversed order twice gives the matrix back. -/
theorem bitRevRows_bitRevRows {k w : ℕ} (M : Mat (2 ^ k) w T) : bitRevRows (bitRevRows M) = M := by
  ext r c
  simp only [bitRevRows_apply]
  congr 1
  exact Fin.ext (bitRev_bitRev r.isLt)

/-- Bit-reverse 2^n rows, append zero rows up to 2^(n + k), and bit-reverse again.

Row i of the result is row i / 2^k of the input when 2^k divides i, and zero otherwise. -/
theorem bitRevRows_padRows_bitRevRows [Zero T] {n k w : ℕ} (M : Mat (2 ^ n) w T) :
    bitRevRows (k := n + k) (padRows (bitRevRows M) (2 ^ (n + k)) 0) =
      Matrix.of fun i c => if _ : 2 ^ k ∣ i.val then M ⟨i.val / 2 ^ k, by
        have h1 : i.val < 2 ^ n * 2 ^ k := by rw [← pow_add]; exact i.isLt
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)⟩ c else 0 := by
  ext i c
  rw [bitRevRows_apply]
  simp only [padRows, Matrix.of_apply]
  by_cases h : 2 ^ k ∣ i.val
  · have hl := (bitRev_lt_iff_dvd i.isLt).mpr h
    simp only [hl, dite_true, h, bitRevRows_apply]
    congr 1
    apply Fin.ext
    obtain ⟨j, hj⟩ := h
    simp only [hj]
    have h1 : 2 ^ k * j < 2 ^ k * 2 ^ n := by
      rw [← hj, mul_comm, ← pow_add]; exact i.isLt
    rw [mul_comm, bitRev_mul_two_pow, bitRev_bitRev (Nat.lt_of_mul_lt_mul_left h1)]
    rw [Nat.mul_div_cancel _ (by positivity)]
  · have hl : ¬ bitRev (n + k) i.val < 2 ^ n := fun hl => h ((bitRev_lt_iff_dvd i.isLt).mp hl)
    simp [hl, h]

end Plonky3Lean.Proofs.Matrix
