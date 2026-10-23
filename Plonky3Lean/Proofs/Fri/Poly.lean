module

public import Plonky3Lean.Spec.Fri
public import Plonky3Lean.Proofs.Matrix.BitRev
public import Plonky3Lean.Proofs.Dft.Network

@[expose] public section

/-!
# The folding operator: pieces, degree, and the fold of a coset word
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri

variable {K : Type _} [Field K]

theorem eval_split (p : K[X]) (a j : ℕ) (y : K) :
    (split p a j).eval y = ∑ i ∈ p.support with i % a = j, p.coeff i * y ^ (i / a) := by
  simp [split, eval_finsetSum]

theorem coeff_split (p : K[X]) {a j : ℕ} (hj : j < a) (m : ℕ) :
    (split p a j).coeff m = p.coeff (m * a + j) := by
  have ha : 0 < a := by omega
  simp only [split, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (m * a + j)]
  · have h1 : (m * a + j) / a = m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ ha, Nat.div_eq_of_lt hj, zero_add]
    simp [h1]
  · intro i hi hne
    simp only [Finset.mem_filter] at hi
    have : m ≠ i / a := fun h => hne (by rw [h, ← hi.2, Nat.div_add_mod' i a])
    simp [this]
  · intro h
    by_cases hz : p.coeff (m * a + j) = 0
    · simp [hz]
    · exact absurd (Finset.mem_filter.2 ⟨mem_support_iff.2 hz, by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]⟩) h

/-- The splitting identity at a point: p(x) = sum_j x^j p_j(x^a). -/
theorem eval_eq_sum_split (p : K[X]) {a : ℕ} (ha : 0 < a) (x : K) :
    p.eval x = ∑ j ∈ range a, x ^ j * (split p a j).eval (x ^ a) := by
  simp only [eval_split, Finset.mul_sum]
  rw [eval_eq_sum, Polynomial.sum_def]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => i % a) (t := range a)
    (fun i _ => Finset.mem_range.2 (Nat.mod_lt _ ha))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2.symm, ← pow_mul, mul_left_comm, ← pow_add, Nat.mod_add_div]

theorem eval_polyFold (p : K[X]) (a : ℕ) (β y : K) :
    (polyFold p a β).eval y = ∑ j ∈ range a, β ^ j * (split p a j).eval y := by
  simp [polyFold, eval_finsetSum]

theorem coeff_polyFold (p : K[X]) (a : ℕ) (β : K) (m : ℕ) :
    (polyFold p a β).coeff m = ∑ j ∈ range a, β ^ j * p.coeff (m * a + j) := by
  simp only [polyFold, finsetSum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun j hj => by rw [coeff_split p (Finset.mem_range.1 hj)]

/-- Exactness: the fold by a of a polynomial of degree below a d has degree below d. -/
theorem degree_polyFold_lt {p : K[X]} {a d : ℕ} (hp : p.degree < ↑(a * d)) (β : K) :
    (polyFold p a β).degree < d := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyFold]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast (by nlinarith))), mul_zero]

/-- The bits of t 2^k + j for j < 2^k: the k low bits reversed on top, the n high bits reversed below. -/
theorem bitRev_split (n k t j : ℕ) (hj : j < 2 ^ k) :
    p3_dft.mirror.bitRev (n + k) (t * 2 ^ k + j) =
      p3_dft.mirror.bitRev k j * 2 ^ n + p3_dft.mirror.bitRev n t := by
  induction k generalizing j with
  | zero =>
    have : j = 0 := by simpa using hj
    simp [this, p3_dft.mirror.bitRev]
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    simp only [p3_dft.mirror.bitRev]
    have e : t * 2 ^ (k + 1) + j = 2 * (t * 2 ^ k) + j := by ring
    rw [e, show (2 * (t * 2 ^ k) + j) % 2 = j % 2 by omega,
      show (2 * (t * 2 ^ k) + j) / 2 = t * 2 ^ k + j / 2 by omega,
      ih (j / 2) (by rw [pow_succ] at hj; omega)]
    ring

variable {s ω : K} {k : ℕ}

theorem revCoset_injective (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) :
    Function.Injective (revCoset s ω k) := by
  intro i j h
  simp only [revCoset, mul_right_inj' hs] at h
  have h1 := hω.pow_inj (by rw [Plonky3Lean.Proofs.Dft.bitRev_eq]; exact Plonky3Lean.Proofs.Matrix.bitRev_lt _ _)
    (by rw [Plonky3Lean.Proofs.Dft.bitRev_eq]; exact Plonky3Lean.Proofs.Matrix.bitRev_lt _ _) h
  rw [Plonky3Lean.Proofs.Dft.bitRev_eq] at h1
  have := congrArg (Plonky3Lean.Spec.Matrix.bitRev k) h1
  rw [Plonky3Lean.Proofs.Matrix.bitRev_bitRev i.2, Plonky3Lean.Proofs.Matrix.bitRev_bitRev j.2] at this
  exact Fin.ext this

theorem revCoset_pow (hω : ω ^ 2 ^ k = 1) (j : Fin (2 ^ k)) : revCoset s ω k j ^ 2 ^ k = s ^ 2 ^ k := by
  rw [revCoset, mul_pow, ← pow_mul, mul_comm (p3_dft.mirror.bitRev k j), pow_mul, hω, one_pow, mul_one]

/-- The fold of the word of p on the coset s H is the fold of p, at s^(2^k). -/
theorem foldValue_eval (p : K[X]) (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) (β : K) :
    foldValue s ω k (fun j => p.eval (revCoset s ω k j)) β = (polyFold p (2 ^ k) β).eval (s ^ 2 ^ k) := by
  have hq : (∑ j ∈ range (2 ^ k), C ((split p (2 ^ k) j).eval (s ^ 2 ^ k)) * X ^ j) =
      Lagrange.interpolate univ (revCoset s ω k) (fun j => p.eval (revCoset s ω k j)) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ (revCoset_injective hω hs).injOn ?_ ?_
    · rw [Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_)
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Finset.mem_range.1 hj)
    · intro j _
      rw [eval_eq_sum_split p (a := 2 ^ k) (by positivity), revCoset_pow hω.pow_eq_one, eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
  rw [foldValue, ← hq, eval_polyFold, eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

theorem sum_range_two_mul {M : Type _} [AddCommMonoid M] (f : ℕ → M) (b : ℕ) :
    ∑ j ∈ range b, ∑ e ∈ range 2, f (2 * j + e) = ∑ i ∈ range (2 * b), f i := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (b + 1) = 2 * b + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, add_zero, add_assoc]

/-- Folding by 2 with beta, then by b with beta^2, is folding by 2 b with beta. -/
theorem polyFold_polyFold (p : K[X]) (b : ℕ) (β : K) :
    polyFold (polyFold p 2 β) b (β ^ 2) = polyFold p (2 * b) β := by
  ext m
  simp only [coeff_polyFold, Finset.mul_sum]
  rw [← sum_range_two_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_assoc, ← pow_mul, ← pow_add, show (m * b + j) * 2 + e = m * (2 * b) + (2 * j + e) by ring]

/-- Folding by 2^k with beta is k folds by 2, with beta, beta^2, ..., beta^(2^(k - 1)). -/
theorem polyFold_two_pow (p : K[X]) (k : ℕ) (β : K) :
    polyFold p (2 ^ (k + 1)) β = polyFold (polyFold p 2 β) (2 ^ k) (β ^ 2) := by
  rw [polyFold_polyFold, pow_succ, mul_comm]

/-- A polynomial of degree below a folds by a to the constant p(beta). -/
theorem polyFold_of_degree_lt {p : K[X]} {a : ℕ} (hp : p.degree < a) (β : K) :
    polyFold p a β = C (p.eval β) := by
  ext m
  rw [coeff_polyFold, coeff_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    rw [eval_eq_sum_range' ((natDegree_lt_iff_degree_lt hp0).2 hp)]
    simp only [↓reduceIte]
    exact Finset.sum_congr rfl fun j _ => by rw [zero_mul, zero_add, mul_comm]
  · simp only [hm.ne', ↓reduceIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast (by nlinarith))), mul_zero]

/-- Folding by a with beta, then by 2 with beta^a, is folding by 2 a with beta. -/
theorem polyFold_two_after (p : K[X]) (a : ℕ) (β : K) :
    polyFold (polyFold p a β) 2 (β ^ a) = polyFold p (2 * a) β := by
  ext m
  simp only [coeff_polyFold, Finset.mul_sum, two_mul, Finset.sum_range_add, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_zero, one_mul, pow_one]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (m * 2 + 0) * a + j = m * (a + a) + j by ring]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← pow_add, show (m * 2 + 1) * a + j = m * (a + a) + (a + j) by ring]

end Plonky3Lean.Proofs.Fri
