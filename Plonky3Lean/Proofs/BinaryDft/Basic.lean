module

public import Plonky3Lean.Spec.BinaryDft
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Points of a span and subspace polynomials

Point m of the span of a basis sums the basis vectors at the set bits of m.

So it is additive over disjoint bits, and it shifts with the basis.

The subspace polynomial W_i is additive in characteristic 2, which is Lemma 1 of Lin, Chung and Han.

The proof runs the recursion W_(i+1)(x) = W_i(x) W_i(x - beta_i).
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft

variable {F : Type _} [Field F]

/-! ## Points -/

theorem testBit_of_lt {m r n : ℕ} (hm : m < 2 ^ n) (hr : n ≤ r) : m.testBit r = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos hr))

/-- The sum over the bits of m below a bound stops changing once the bound covers m. -/
theorem sum_bits_eq {M : Type _} [AddCommMonoid M] (f : ℕ → M) {m a b : ℕ} (hab : a ≤ b)
    (ha : m < 2 ^ a) :
    ∑ r ∈ range a, (if m.testBit r then f r else 0) =
      ∑ r ∈ range b, (if m.testBit r then f r else 0) := by
  rw [← sum_range_add_sum_Ico _ hab, sum_eq_zero (s := Ico a b) fun r hr => by
    simp [testBit_of_lt ha (mem_Ico.mp hr).1], add_zero]

/-- Point m as a sum over any range of bits that covers m. -/
theorem point_eq_sum (β : ℕ → F) {m n : ℕ} (hm : m < 2 ^ n) :
    point β m = ∑ r ∈ range n, if m.testBit r then β r else 0 := by
  rcases le_total m n with h | h
  · exact sum_bits_eq β h (Nat.lt_two_pow_self)
  · exact (sum_bits_eq β h hm).symm

@[simp] theorem point_zero (β : ℕ → F) : point β 0 = 0 := by simp [point]

theorem point_two_pow (β : ℕ → F) (j : ℕ) : point β (2 ^ j) = β j := by
  rw [point_eq_sum β (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j))]
  rw [sum_eq_single j (fun r _ hr => by simp [Ne.symm hr]) (by simp)]
  simp

/-- Bits below 2^k and bits above it contribute separately. -/
theorem point_add_mul (β : ℕ → F) (a k : ℕ) {b : ℕ} (hb : b < 2 ^ k) :
    point β (2 ^ k * a + b) = point β (2 ^ k * a) + point β b := by
  have hlt : ∀ c, c ≤ a → 2 ^ k * c + b < 2 ^ (k + a + 1) := fun c hc => by
    have : c < 2 ^ (a + 1) := lt_of_le_of_lt hc (Nat.lt_two_pow_self.trans
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self a)))
    calc 2 ^ k * c + b < 2 ^ k * c + 2 ^ k := by omega
      _ = 2 ^ k * (c + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (a + 1) := Nat.mul_le_mul_left _ this
      _ = 2 ^ (k + a + 1) := by ring
  have h1 := hlt a le_rfl
  have h2 : 2 ^ k * a < 2 ^ (k + a + 1) := by omega
  have h3 : b < 2 ^ (k + a + 1) := by omega
  rw [point_eq_sum β h1, point_eq_sum β h2, point_eq_sum β h3,
    ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.testBit_two_pow_mul_add a hb, Nat.testBit_two_pow_mul]
  by_cases hr : r < k
  · simp [hr, show ¬ k ≤ r by omega]
  · simp [hr, show k ≤ r by omega, testBit_of_lt hb (show k ≤ r by omega)]

theorem point_add_two_pow (β : ℕ → F) {m k : ℕ} (hm : m < 2 ^ k) :
    point β (m + 2 ^ k) = point β m + β k := by
  rw [add_comm, ← mul_one (2 ^ k), point_add_mul β 1 k hm, mul_one, point_two_pow, add_comm]

/-- Point m of a shifted basis is point m 2^s of the basis. -/
theorem point_mul_two_pow (β : ℕ → F) (m s : ℕ) :
    point β (2 ^ s * m) = point (fun r => β (s + r)) m := by
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  have hsm : 2 ^ s * m < 2 ^ (s + m) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left hm (Nat.two_pow_pos s)
  rw [point_eq_sum _ hm, point_eq_sum β hsm, sum_range_add, sum_eq_zero (s := range s), zero_add]
  · refine sum_congr rfl fun r _ => ?_
    rw [Nat.testBit_two_pow_mul]; simp
  · exact fun r hr => by
      rw [Nat.testBit_two_pow_mul]; simp [show ¬ s ≤ r by simpa using hr]

/-- Point m only reads the basis vectors below the bit length of m. -/
theorem point_congr {β β' : ℕ → F} {m n : ℕ} (hm : m < 2 ^ n) (h : ∀ r < n, β r = β' r) :
    point β m = point β' m := by
  rw [point_eq_sum β hm, point_eq_sum β' hm]
  exact sum_congr rfl fun r hr => by rw [h r (mem_range.mp hr)]

/-- An additive map sends point m of a basis to point m of the image basis. -/
theorem map_point (f : F →+ F) (β : ℕ → F) (m : ℕ) : f (point β m) = point (f ∘ β) m := by
  simp only [point, map_sum, Function.comp]
  exact sum_congr rfl fun r _ => by split_ifs <;> simp

/-- With every bit below t set, point (2^t - 1) is the sum of the first t basis vectors. -/
theorem point_two_pow_sub_one (β : ℕ → F) (t : ℕ) :
    point β (2 ^ t - 1) = ∑ q ∈ range t, β q := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : 2 ^ (t + 1) - 1 = (2 ^ t - 1) + 2 ^ t := by rw [pow_succ]; have := Nat.two_pow_pos t; omega
    rw [h, point_add_two_pow β (by have := Nat.two_pow_pos t; omega), ih, sum_range_succ]

end Plonky3Lean.Proofs.BinaryDft
