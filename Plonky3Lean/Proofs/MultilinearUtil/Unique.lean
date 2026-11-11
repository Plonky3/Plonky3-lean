module

public import Plonky3Lean.Proofs.MultilinearUtil.Mle

@[expose] public section

/-!
# The multilinear extension is the unique multilinear interpolant

This is Thaler, Lemma 3.6.

The extension is multilinear, agrees with the table on the cube, and is the only such polynomial.

Uniqueness is the combinatorial Nullstellensatz with the set {0, 1} in each variable.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil MvPolynomial Finset

variable {K : Type _} [CommRing K]

/-- The vertex b as a function of the coordinate. -/
def vertexFn (n b : ℕ) : Fin n → K := fun i => if b.testBit (n - 1 - i) then 1 else 0

theorem ofFn_vertexFn (n b : ℕ) : List.ofFn (vertexFn n b : Fin n → K) = vertex n b :=
  List.ext_getElem (by simp) fun i _ _ => by simp [vertexFn, vertex]

/-- eq(b, r) is the product, over the coordinates, of r_i where bit i of b is set and 1 - r_i elsewhere. -/
theorem eq_vertex_ofFn (n b : ℕ) (r : Fin n → K) :
    eq (vertex n b) (List.ofFn r) = ∏ i : Fin n, if b.testBit (n - 1 - i) then r i else 1 - r i := by
  induction n with
  | zero => simp [vertex]
  | succ n ih =>
    rw [vertex_succ, List.ofFn_succ, eq_cons, ih, Fin.prod_univ_succ]
    congr 1
    · split <;> simp_all
    · exact prod_congr rfl fun i _ => by
        simp only [Fin.val_succ, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]

/-- Two vertices of the n-cube: eq is 1 when they are equal and 0 otherwise. -/
theorem eq_vertex_vertex {n b c : ℕ} [Nontrivial K] (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
    eq (vertex n b) (vertex n c : List K) = if b = c then 1 else 0 := by
  rw [← ofFn_vertexFn n c, eq_vertex_ofFn]
  have hbit : ∀ i : Fin n, (if b.testBit (n - 1 - i) then vertexFn n c i else 1 - vertexFn n c i)
      = if b.testBit (n - 1 - i) = c.testBit (n - 1 - i) then (1 : K) else 0 := fun i => by
    unfold vertexFn; cases b.testBit (n - 1 - i) <;> cases c.testBit (n - 1 - i) <;> simp
  simp only [hbit, prod_ite_zero, prod_const_one]
  congr 1
  refine propext ⟨fun h => Nat.eq_of_testBit_eq fun j => ?_, fun h i _ => by rw [h]⟩
  by_cases hj : j < n
  · simpa [show n - 1 - (n - 1 - j) = j by omega] using h ⟨n - 1 - j, by omega⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right two_pos (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right two_pos (by omega)))]

/-- At a vertex, the extension is the table entry. -/
theorem mle_vertex [Nontrivial K] (f : List K) {n b : ℕ} (hb : b < 2 ^ n) :
    mle f (vertex n b) = f.getD b 0 := by
  rw [mle, length_vertex, sum_eq_single_of_mem b (mem_range.mpr hb) fun c hc hcb => by
    simp [eq_vertex_vertex (mem_range.mp hc) hb, hcb]]
  simp [eq_vertex_vertex hb hb]

/-- Evaluating the polynomial is evaluating the extension. -/
theorem eval_mlePoly (f : List K) {n : ℕ} (r : Fin n → K) :
    eval r (mlePoly f n) = mle f (List.ofFn r) := by
  simp only [mlePoly, mle, List.length_ofFn, eval_sum, eval_mul, eval_C, eval_prod,
    eq_vertex_ofFn]
  exact sum_congr rfl fun b _ => by
    rw [mul_comm]; congr 1; exact prod_congr rfl fun i _ => by split <;> simp

/-- Every point of {0, 1}^n is a vertex. -/
theorem exists_vertex {n : ℕ} (x : Fin n → K) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    ∃ b < 2 ^ n, List.ofFn x = vertex n b := by
  induction n with
  | zero => exact ⟨0, by simp, by simp [vertex]⟩
  | succ n ih =>
    obtain ⟨b, hb, h⟩ := ih (fun i => x i.succ) fun i => hx i.succ
    rw [List.ofFn_succ, h]
    rcases hx 0 with h0 | h0
    · exact ⟨b, by omega, by rw [vertex_low hb, h0]⟩
    · exact ⟨2 ^ n + b, by omega, by rw [vertex_high hb, h0]⟩

section Domain

variable [IsDomain K]

/-- The extension has degree at most 1 in each variable. -/
theorem mlePoly_isMultilinear (f : List K) (n : ℕ) : IsMultilinear (mlePoly f n) := fun i => by
  classical
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun b _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ j : Fin n, degreeOf i (if b.testBit (n - 1 - j) then X j else (1 - X j : MvPolynomial (Fin n) K))
      ≤ ∑ j : Fin n, if i = j then 1 else 0 := sum_le_sum fun j _ => by
        have hX := degreeOf_X (R := K) i j
        split
        · exact hX.le
        · exact (degreeOf_sub_le _ _ _).trans (by simp [hX])
    _ = 1 := by simp

/-- At a vertex, the polynomial is the table entry. -/
theorem eval_mlePoly_vertex (f : List K) {n b : ℕ} (hb : b < 2 ^ n) :
    eval (vertexFn n b) (mlePoly f n) = f.getD b 0 := by
  rw [eval_mlePoly, ofFn_vertexFn, mle_vertex f hb]

/-- A multilinear polynomial that agrees with the table on the cube is its extension. -/
theorem eq_mlePoly {n : ℕ} (f : List K) {p : MvPolynomial (Fin n) K} (hp : IsMultilinear p)
    (hf : ∀ b < 2 ^ n, eval (vertexFn n b) p = f.getD b 0) : p = mlePoly f n := by
  classical
  refine sub_eq_zero.mp (eq_zero_of_eval_zero_at_prod_finset _ (fun _ => {0, 1}) (fun i => ?_)
    fun x hx => ?_)
  · rw [card_pair zero_ne_one]
    exact lt_of_le_of_lt ((degreeOf_sub_le _ _ _).trans (max_le (hp i) (mlePoly_isMultilinear f n i)))
      one_lt_two
  · obtain ⟨b, hb, h⟩ := exists_vertex x fun i => by simpa using hx i
    rw [← ofFn_vertexFn, List.ofFn_inj] at h
    rw [eval_sub, h, hf b hb, eval_mlePoly_vertex f hb, sub_self]

end Domain

end Plonky3Lean.Proofs.MultilinearUtil
