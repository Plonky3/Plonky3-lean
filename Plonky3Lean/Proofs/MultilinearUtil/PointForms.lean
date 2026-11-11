module

public import Plonky3Lean.Proofs.MultilinearUtil.Point

@[expose] public section

/-!
# Points: the closed forms

Each loop that walks a point from its last coordinate reads the index bits from the bottom up.

So its factors are those of the vertex whose coordinate 0 is the top bit.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.point.mirror
open Finset

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem foldl_mul_one (l : List F) : l.foldl (· * ·) 1 = l.prod := List.prod_eq_foldl.symm

theorem testBit_iff (v n : ℕ) : v.testBit n = true ↔ v / 2 ^ n % 2 = 1 := by
  simp [Nat.testBit_eq_decide_div_mod_eq]

/-! ## A vertex weight -/

theorem equality_at_vertex_loop (p acc : List F) (v : ℕ) :
    ∃ T : List F, p.reverse.foldl vertexStep (acc, v) = (acc ++ T, v / 2 ^ p.length) ∧
      T.prod = eq (vertex p.length v) p := by
  induction p with
  | nil => exact ⟨[], by simp, by simp [vertex]⟩
  | cons c p ih =>
    obtain ⟨T, h, hT⟩ := ih
    refine ⟨T ++ [if v / 2 ^ p.length % 2 = 0 then 1 - c else c], ?_, ?_⟩
    · simp [h, vertexStep, pow_succ, Nat.div_div_eq_div_mul]
    · rw [List.prod_append, hT, List.length_cons, vertex_succ, eq_cons]
      rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ p.length) with h2 | h2 <;>
        simp [testBit_iff, h2] <;> ring

/-- The weight of one vertex: eq(b, p) when b < 2^n, and none otherwise. -/
theorem equality_at_vertex_eq (p : List F) {v : ℕ} (hv : v < 2 ^ 64) :
    Point.equality_at_vertex p v =
      if v < 2 ^ p.length then some (eq (vertex p.length v) p) else none := by
  obtain ⟨T, h, hT⟩ := equality_at_vertex_loop p [] v
  rw [Point.equality_at_vertex, h, foldl_mul_one, List.nil_append, hT, Nat.shiftRight_eq_div_pow]
  by_cases hn : p.length < 64
  · by_cases hl : v < 2 ^ p.length
    · simp [hl, Nat.div_eq_of_lt hl]
    · simp [hn, hl, Nat.div_eq_zero_iff]
  · have : v < 2 ^ p.length := lt_of_lt_of_le hv (Nat.pow_le_pow_right two_pos (by omega))
    simp [hn, this]

/-! ## Vertices, univariate points and the equality polynomial -/

/-- hypercube: the vertex with coordinate 0 on the top bit, when value < 2^n and n < 64. -/
theorem hypercube_eq {value n : ℕ} (hn : n < 64) (hv : value < 2 ^ n) :
    Point.hypercube value n = some (vertex n value : List F) := by
  simp only [Point.hypercube, show ¬ 64 ≤ n by omega, hv, ↓reduceIte, vertex,
    Nat.shiftRight_eq_div_pow, Option.some.injEq]
  exact List.map_congr_left fun i _ => by simp [testBit_iff]

theorem hypercube_panics {value n : ℕ} (h : 64 ≤ n ∨ 2 ^ n ≤ value) :
    Point.hypercube value n = (none : Option (List F)) := by
  rcases h with h | h
  · simp [Point.hypercube, h]
  · simp [Point.hypercube, Nat.not_lt.mpr h]

theorem expand_loop (x : F) (l : List F) {m : ℕ} (hm : m ≤ l.length) :
    (List.range m).reverse.foldl (fun (acc : List F × F) i => (acc.1.set i acc.2, acc.2 * acc.2))
      (l, x) = ((List.range m).map (fun i => x ^ 2 ^ (m - 1 - i)) ++ l.drop m, x ^ 2 ^ m) := by
  induction m generalizing l x with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ih (x * x) (l.set m x) (by simp; omega)]
    simp only [List.map_append, List.map_singleton, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      pow_one, List.append_assoc, List.singleton_append, Prod.mk.injEq]
    refine ⟨?_, by rw [← sq, ← pow_mul, pow_succ, Nat.mul_comm]⟩
    congr 1
    · exact List.map_congr_left fun i hi => by
        simp at hi
        rw [← sq, ← pow_mul, ← pow_succ', show m - 1 - i + 1 = m - i by omega]
    · rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp [List.drop_set_of_lt (hnm := Nat.lt_succ_self m)]

/-- expand_from_univariate: coordinate i is y^(2^(n - 1 - i)). -/
theorem expand_from_univariate_eq (y : F) (n : ℕ) :
    Point.expand_from_univariate y n = (List.range n).map fun i => y ^ 2 ^ (n - 1 - i) := by
  rw [Point.expand_from_univariate, expand_loop y _ (by simp)]
  simp

/-- The bits of b, read big-endian, sum back to b. -/
theorem prod_pow_bits (y : F) {n b : ℕ} (hb : b < 2 ^ n) :
    ∏ i : Fin n, (if b.testBit (n - 1 - i) then y ^ 2 ^ (n - 1 - i) else 1) = y ^ b := by
  induction n generalizing b with
  | zero => simp_all
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hrest : ∏ i : Fin n, (if b.testBit (n + 1 - 1 - (i.succ : ℕ)) then
        y ^ 2 ^ (n + 1 - 1 - (i.succ : ℕ)) else 1) = y ^ (b % 2 ^ n) := by
      rw [← ih (Nat.mod_lt _ (by positivity))]
      exact Finset.prod_congr rfl fun i _ => by
        rw [show n + 1 - 1 - (i.succ : ℕ) = n - 1 - i by simp; omega,
          Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and]
    rw [hrest]
    have hdiv : b / 2 ^ n < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hb; omega
    conv_rhs => rw [← Nat.div_add_mod b (2 ^ n), pow_add, pow_mul]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, testBit_iff, Nat.mod_eq_of_lt hdiv]
    generalize b / 2 ^ n = d at hdiv ⊢
    rcases d with _ | _ | d
    · simp
    · simp
    · omega

/-- Thaler's bijection: at the expanded point, the polynomial with coefficients c is sum_b c_b y^b. -/
theorem eval_coeffPoly_expand (c : List F) (y : F) (n : ℕ) :
    MvPolynomial.eval (fun i : Fin n => (Point.expand_from_univariate y n).getD i 0)
      (coeffPoly c n) = ∑ b ∈ range (2 ^ n), c.getD b 0 * y ^ b := by
  simp only [coeffPoly, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  refine sum_congr rfl fun b hb => ?_
  rw [← prod_pow_bits y (mem_range.mp hb)]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    split <;> simp [expand_from_univariate_eq, List.getD_eq_getElem?_getD]

/-- eval_eq: eq(p, q), with p mapped into EF, when the lengths agree. -/
theorem eval_eq_eq {p : List F} {q : List EF} (h : p.length = q.length) :
    Point.eval_eq p q = some (eq (p.map (algebraMap F EF)) q) := by
  simp only [Point.eval_eq, h, ne_eq, not_true_eq_false, ↓reduceIte, foldl_mul_one, eq,
    List.zipWith_map_left]
  congr 2
  exact congrArg (fun f => List.zipWith f p q) (by funext a b; ring)

theorem eval_eq_panics {p : List F} {q : List EF} (h : p.length ≠ q.length) :
    Point.eval_eq p q = none := by simp [Point.eval_eq, h]

/-! ## The selection polynomial -/

theorem select_loop (var : F) (point acc : List EF) :
    ∃ T : List EF, point.reverse.foldl selectStep (acc, var) = (acc ++ T, var ^ 2 ^ point.length) ∧
      T.prod = mle (powTable (algebraMap F EF var) point.length) point := by
  induction point with
  | nil => exact ⟨[], by simp, by simp [mle, powTable, vertex]⟩
  | cons c p ih =>
    obtain ⟨T, h, hT⟩ := ih
    refine ⟨T ++ [c * algebraMap F EF (-1 + var ^ 2 ^ p.length) + 1], ?_, ?_⟩
    · simp only [List.reverse_cons, List.foldl_append, h, List.foldl_cons, List.foldl_nil,
        selectStep, List.append_assoc, List.length_cons, Prod.mk.injEq, true_and]
      rw [← pow_two, ← pow_mul, pow_succ]
    · rw [List.prod_append, hT, List.length_cons, mle_powTable_cons]
      simp only [List.prod_singleton, map_add, map_neg, map_one, map_pow]
      ring

/-- eval_select: the extension of the table of powers var^b, at the point. -/
theorem eval_select_eq (var : F) (point : List EF) :
    Point.eval_select var point = mle (powTable (algebraMap F EF var) point.length) point := by
  obtain ⟨T, h, hT⟩ := select_loop var point []
  rw [Point.eval_select, h, foldl_mul_one, List.nil_append, hT]

end Plonky3Lean.Proofs.MultilinearUtil
