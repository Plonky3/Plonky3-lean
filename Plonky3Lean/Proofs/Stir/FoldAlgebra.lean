module

public import Plonky3Lean.Proofs.Stir.Horner
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# One arity-2 pass of a fold

A codeword of length N lives on the powers of omega, a primitive N-th root of unity.

The fold of arity k at index j interpolates the k entries j, j + M, ..., j + (k - 1) M, for N = k M, and evaluates at beta:

```text
    nodes   omega^(j + l M),   l < k
    values  c[j + l M]
```

One pass pairs x with -x, which sit N/2 apart, and keeps

```text
    (c(x) + c(-x)) / 2 + beta (c(x) - c(-x)) / (2 x)  =  E(x^2) + beta O(x^2),     P(X) = E(X^2) + X O(X^2)
```

so the fold of arity 2m at beta is the fold of arity m of the pass, at beta^2.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The fold of arity k at index j: interpolate entries j + l M at omega^(j + l M), l < k, and evaluate at beta. -/
noncomputable def foldIdx (ω : K) (c : List K) (M k j : ℕ) (β : K) : K :=
  (Lagrange.interpolate (range k) (fun l => ω ^ (j + l * M)) (fun l => c.getD (j + l * M) 0)).eval β

theorem sum_range_two_mul (f : ℕ → K) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]; ring

/-- The even part E, with P(X) = E(X^2) + X O(X^2) below degree 2 m. -/
noncomputable def evenPart (P : K[X]) (m : ℕ) : K[X] := ∑ i ∈ range m, C (P.coeff (2 * i)) * X ^ i

/-- The odd part O, with P(X) = E(X^2) + X O(X^2) below degree 2 m. -/
noncomputable def oddPart (P : K[X]) (m : ℕ) : K[X] := ∑ i ∈ range m, C (P.coeff (2 * i + 1)) * X ^ i

theorem degree_part_lt (P : K[X]) (m : ℕ) (e : ℕ) :
    (∑ i ∈ range m, C (P.coeff (2 * i + e)) * X ^ i).degree < (m : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi => ?_)
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast mem_range.1 hi)

theorem eval_even_odd {P : K[X]} {m : ℕ} (hP : P.natDegree < 2 * m) (x : K) :
    P.eval x = (evenPart P m).eval (x ^ 2) + x * (oddPart P m).eval (x ^ 2) := by
  rw [eval_eq_sum_range' hP, sum_range_two_mul]
  simp only [evenPart, oddPart, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => by ring

/-- The fold of arity 2m at beta is the fold of arity m, at beta^2, of one pass. -/
theorem foldIdx_pass {ω : K} {m M : ℕ} (hω : IsPrimitiveRoot ω (2 * m * M)) (hm : 0 < m)
    (h2 : (2 : K) ≠ 0) (c out : List K) (β : K)
    (hout : ∀ i < m * M, out.getD i 0 = (c.getD i 0 + c.getD (i + m * M) 0) / 2 +
      β * (c.getD i 0 - c.getD (i + m * M) 0) / (2 * ω ^ i))
    {j : ℕ} (hj : j < M) :
    foldIdx (ω ^ 2) out M m j (β ^ 2) = foldIdx ω c M (2 * m) j β := by
  have hM : 0 < M := by omega
  have hω0 : ω ≠ 0 := hω.ne_zero (by positivity)
  have hneg : ω ^ (m * M) = -1 := by
    have h := hω.pow_of_dvd (p := m * M) (by positivity) ⟨2, by ring⟩
    rw [show 2 * m * M / (m * M) = 2 by rw [mul_assoc, Nat.mul_div_cancel _ (by positivity)]] at h
    exact h.eq_neg_one_of_two_right
  have hω2 : IsPrimitiveRoot (ω ^ 2) (m * M) := by
    have h := hω.pow_of_dvd (p := 2) two_ne_zero ⟨m * M, by ring⟩
    rwa [show 2 * m * M / 2 = m * M by rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]] at h
  have hidx : ∀ l, l < 2 * m → j + l * M < 2 * m * M := fun l hl => by nlinarith
  have hinj : Set.InjOn (fun l => ω ^ (j + l * M)) (range (2 * m) : Set ℕ) := by
    intro l hl l' hl' h
    have := hω.pow_inj (hidx l (mem_range.1 hl)) (hidx l' (mem_range.1 hl')) h
    exact Nat.eq_of_mul_eq_mul_right hM (by omega)
  have hinj2 : Set.InjOn (fun l => (ω ^ 2) ^ (j + l * M)) (range m : Set ℕ) := by
    intro l hl l' hl' h
    have hl1 := mem_range.1 hl; have hl2 := mem_range.1 hl'
    have := hω2.pow_inj (by nlinarith) (by nlinarith) h
    exact Nat.eq_of_mul_eq_mul_right hM (by omega)
  set P := Lagrange.interpolate (range (2 * m)) (fun l => ω ^ (j + l * M))
    (fun l => c.getD (j + l * M) 0)
  have hPdeg : P.natDegree < 2 * m := by
    have := Lagrange.degree_interpolate_lt (r := fun l => c.getD (j + l * M) 0) hinj
    rw [card_range] at this
    by_cases hP0 : P = 0
    · rw [hP0]; simp; omega
    · exact (natDegree_lt_iff_degree_lt hP0).2 this
  have hPnode : ∀ l < 2 * m, P.eval (ω ^ (j + l * M)) = c.getD (j + l * M) 0 := fun l hl =>
    Lagrange.eval_interpolate_at_node _ hinj (mem_range.2 hl)
  have hQ : Lagrange.interpolate (range m) (fun l => (ω ^ 2) ^ (j + l * M))
      (fun l => out.getD (j + l * M) 0) = evenPart P m + C β * oddPart P m := by
    symm
    refine Lagrange.eq_interpolate_of_eval_eq _ hinj2 ?_ fun l hl => ?_
    · rw [card_range]
      refine (degree_add_le _ _).trans_lt (max_lt (by simpa [evenPart] using degree_part_lt P m 0) ?_)
      rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt (by simpa [oddPart] using degree_part_lt P m 1)
    · have hl1 := mem_range.1 hl
      set x := ω ^ (j + l * M)
      have hx0 : x ≠ 0 := pow_ne_zero _ hω0
      have hpos : P.eval x = c.getD (j + l * M) 0 := hPnode l (by omega)
      have hnegx : P.eval (-x) = c.getD (j + l * M + m * M) 0 := by
        have := hPnode (l + m) (by omega)
        rw [show j + (l + m) * M = j + l * M + m * M by ring, pow_add, hneg, mul_neg_one] at this
        exact this
      rw [show (ω ^ 2) ^ (j + l * M) = x ^ 2 by simp only [x]; ring, hout _ (by nlinarith), ← hpos,
        ← hnegx, eval_even_odd hPdeg x, eval_even_odd hPdeg (-x), neg_sq]
      simp only [eval_add, eval_mul, eval_C]
      field_simp
      ring
  unfold foldIdx
  rw [hQ, eval_even_odd hPdeg]
  simp only [eval_add, eval_mul, eval_C]

/-- A fold of arity one reads the entry. -/
theorem foldIdx_one (ω : K) (c : List K) (M j : ℕ) (β : K) : foldIdx ω c M 1 j β = c.getD j 0 := by
  simp [foldIdx]

end Plonky3Lean.Proofs.Stir
