module

public import Plonky3Lean.Proofs.Commit.Domain

@[expose] public section

/-!
# p3-commit: evaluating periodic columns at a point

A column of length p = 2^l over a trace coset s H of order n = 2^k defines the polynomial P of degree below n with

```text
    P(s omega^i) = col[i mod p]          for 0 <= i < n
```

Write f = k - l.

The code evaluates Q(x^(2^f)) instead, for Q the interpolant of the column over the coset s^(2^f) H^(2^f) of order p.

The two agree because Q(X^(2^f)) has degree below n and takes the same values on s H.
-/

open Polynomial Finset
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The periodic polynomial of a column over s H: the interpolant of col[i mod p]. -/
noncomputable def periodicPoly (s ω : K) (k : ℕ) (col : List K) : K[X] :=
  interpolant s ω k fun i => col.getD (i.val % col.length) 0

/-- Interpolation over the coset of the evaluations' length evaluates their interpolant. -/
theorem evaluate_polynomial_at_eq (hV : GenValid G) (h2 : (2 : K) ≠ 0) (c : Coset G)
    (evals : List K) {k : ℕ} (hlen : evals.length = 2 ^ k) (hk : k ≤ G.adicity) (x : K) :
    Coset.evaluate_polynomial_at G c evals x =
      some ((interpolant c.shift (G.gen k) k fun i => evals.getD i.val 0).eval x) := by
  simp [Coset.evaluate_polynomial_at, hlen, log2Strict_pow, gen_get_of_le G hk,
    Plonky3Lean.Proofs.Matrix.Interp.interpolate_coset_eq (hV k hk) h2, c.shift_ne_zero,
    interpolant, cosetPoints_eq_cosetPt]

/-- Evaluations whose length is not a power of two panic. -/
theorem evaluate_polynomial_at_none (c : Coset G) (evals : List K)
    (hlen : ∀ k, evals.length ≠ 2 ^ k) (x : K) : Coset.evaluate_polynomial_at G c evals x = none := by
  simp [Coset.evaluate_polynomial_at, log2Strict_eq_none hlen]

/-- Q(X^(2^f)), for Q of degree below 2^l through values on s^(2^f) H_l, is the periodic polynomial over s H_k. -/
theorem comp_eq_periodicPoly (hV : GenValid G) (hN : GenNested G) {s : K} (hs : s ≠ 0) {k l : ℕ}
    (hk : k ≤ G.adicity) (hl : l ≤ k) (col : List K) (hcol : col.length = 2 ^ l) :
    (interpolant (s ^ 2 ^ (k - l)) (G.gen l) l fun i => col.getD i.val 0).comp (X ^ 2 ^ (k - l)) =
      periodicPoly s (G.gen k) k col := by
  classical
  have hωl := hV l (by omega)
  have hωk := hV k hk
  have hQ := Lagrange.degree_interpolate_lt (s := univ) (v := cosetPoints (s ^ 2 ^ (k - l)) (G.gen l) l)
    (fun i => col.getD i.val 0)
    ((cosetPoints_injective hωl (pow_ne_zero _ hs)).injOn)
  rw [card_univ, Fintype.card_fin] at hQ
  rw [interpolant]
  refine Lagrange.eq_interpolate_of_eval_eq _
    ((cosetPoints_injective hωk hs).injOn) ?_ ?_
  · rw [card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    rw [natDegree_comp, natDegree_X_pow, Nat.cast_lt]
    have hnat : (Lagrange.interpolate univ (cosetPoints (s ^ 2 ^ (k - l)) (G.gen l) l)
        fun i => col.getD i.val 0).natDegree < 2 ^ l := by
      rcases eq_or_ne (Lagrange.interpolate univ (cosetPoints (s ^ 2 ^ (k - l)) (G.gen l) l)
        fun i => col.getD i.val 0) 0 with h | h
      · rw [h]; simp
      · exact (natDegree_lt_iff_degree_lt h).mpr hQ
    calc (Lagrange.interpolate univ (cosetPoints (s ^ 2 ^ (k - l)) (G.gen l) l)
          fun i => col.getD i.val 0).natDegree * 2 ^ (k - l) ≤ (2 ^ l - 1) * 2 ^ (k - l) := by
          exact Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ k := by
          rw [Nat.sub_mul, one_mul, ← pow_add, Nat.add_sub_cancel' hl]
          exact Nat.sub_lt (by positivity) (by positivity)
  · intro i _
    have hidx : i.val % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
    have hpt : cosetPoints s (G.gen k) k i ^ 2 ^ (k - l) =
        cosetPoints (s ^ 2 ^ (k - l)) (G.gen l) l ⟨i.val % 2 ^ l, hidx⟩ := by
      simp only [cosetPoints]
      rw [mul_pow, ← pow_mul, mul_comm i.val, pow_mul, ← gen_sub G hN hk (show k - l ≤ k by omega),
        show k - (k - l) = l by omega, hωl.eq_orderOf, pow_mod_orderOf]
    rw [eval_comp, eval_pow, eval_X, hpt,
      Lagrange.eval_interpolate_at_node _
        ((cosetPoints_injective hωl (pow_ne_zero _ hs)).injOn)
        (mem_univ _), hcol]

/-- A column of length 2^l <= n evaluates to its periodic polynomial at the point. -/
theorem evaluate_periodic_column_at_eq (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (c : Coset G) (col : List K) {l : ℕ} (hcol : col.length = 2 ^ l) (hl : l ≤ c.log_size) (x : K) :
    Coset.evaluate_periodic_column_at G c col x =
      some ((periodicPoly c.shift c.subgroup_generator c.log_size col).eval x) := by
  have hla : l ≤ G.adicity := hl.trans c.log_size_le
  have hnew : (TwoAdicMultiplicativeCoset.new (c.shift ^ 2 ^ (c.log_size - l)) l : Option (Coset G)) =
      some ⟨c.shift ^ 2 ^ (c.log_size - l), l, pow_ne_zero _ c.shift_ne_zero, hla⟩ := by
    simp [TwoAdicMultiplicativeCoset.new, c.shift_ne_zero, hla]
  simp only [Coset.evaluate_periodic_column_at, hcol, log2Strict_pow, Option.bind_eq_bind,
    Option.bind_some, hl, ite_true, hnew]
  rw [evaluate_polynomial_at_eq G hV h2 _ col hcol hla, TwoAdicMultiplicativeCoset.subgroup_generator,
    ← comp_eq_periodicPoly G hV hN
    c.shift_ne_zero c.log_size_le hl col hcol, eval_comp]
  simp

/-- The trait's default evaluates the same polynomial, for any nonempty column. -/
theorem default_evaluate_periodic_column_at_eq (hV : GenValid G) (h2 : (2 : K) ≠ 0)
    (c : Coset G) (col : List K) (hcol : col.length ≠ 0) (x : K) :
    Coset.default_evaluate_periodic_column_at G c col x =
      some ((periodicPoly c.shift c.subgroup_generator c.log_size col).eval x) := by
  simp only [Coset.default_evaluate_periodic_column_at, hcol, ite_false]
  rw [evaluate_polynomial_at_eq G hV h2 c _ (by simp [size_eq]) c.log_size_le]
  congr 3
  funext i
  simp [List.getD_eq_getElem?_getD, i.isLt, size_eq]

/-- The override panics on a length that is not a power of two. -/
theorem evaluate_periodic_column_at_not_pow (c : Coset G) (col : List K)
    (hcol : ∀ l, col.length ≠ 2 ^ l) (x : K) : Coset.evaluate_periodic_column_at G c col x = none := by
  simp [Coset.evaluate_periodic_column_at, log2Strict_eq_none hcol]

/-- The override panics on a power of two longer than the trace. -/
theorem evaluate_periodic_column_at_long (c : Coset G) (col : List K) {l : ℕ}
    (hcol : col.length = 2 ^ l) (hl : c.log_size < l) (x : K) :
    Coset.evaluate_periodic_column_at G c col x = none := by
  simp [Coset.evaluate_periodic_column_at, hcol, log2Strict_pow, not_le.mpr hl]

end Plonky3Lean.Proofs.Commit
