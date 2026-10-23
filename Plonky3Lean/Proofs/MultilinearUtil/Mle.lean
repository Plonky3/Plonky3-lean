module

public import Plonky3Lean.Spec.MultilinearUtil
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Multilinear extensions: the structure the algorithms use

The equality table of (c, r) is the table of r scaled by 1 - c, then by c.

The table of r ++ s is the outer product of the two tables.

The extension at (c, r) interpolates the two halves of the table along c.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil MvPolynomial Finset

variable {K : Type _} [CommRing K]

/-! ## Vertices -/

@[simp] theorem length_vertex (n b : ℕ) : (vertex n b : List K).length = n := by simp [vertex]

theorem vertex_succ (n b : ℕ) :
    (vertex (n + 1) b : List K) = (if b.testBit n then 1 else 0) :: vertex n b := by
  simp only [vertex, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.sub_zero,
    Nat.add_sub_cancel]
  congr 1
  exact List.map_congr_left fun i _ => by simp [show n - (i + 1) = n - 1 - i by omega]

theorem vertex_low {n b : ℕ} (h : b < 2 ^ n) : (vertex (n + 1) b : List K) = 0 :: vertex n b := by
  simp [vertex_succ, Nat.testBit_lt_two_pow h]

theorem vertex_high {n b : ℕ} (h : b < 2 ^ n) :
    (vertex (n + 1) (2 ^ n + b) : List K) = 1 :: vertex n b := by
  rw [vertex_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]
  simp only [Bool.not_false, ite_true, vertex]
  congr 1
  exact List.map_congr_left fun i hi => by
    rw [Nat.testBit_two_pow_add_gt (by simp at hi; omega)]

theorem vertex_bit (n b : ℕ) (e : Bool) :
    (vertex (n + 1) (Nat.bit e b) : List K) = vertex n b ++ [if e then 1 else 0] := by
  simp only [vertex, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · exact List.map_congr_left fun i hi => by
      simp at hi
      rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, Nat.testBit_bit_succ]
  · simp

/-! ## The equality polynomial -/

@[simp] theorem eq_nil (r : List K) : eq [] r = 1 := by simp [eq]

@[simp] theorem eq_cons (a c : K) (x r : List K) :
    eq (a :: x) (c :: r) = (a * c + (1 - a) * (1 - c)) * eq x r := by simp [eq]

theorem eq_append {x r x' r' : List K} (h : x.length = r.length) :
    eq (x ++ x') (r ++ r') = eq x r * eq x' r' := by
  simp [eq, List.zipWith_append h]

/-! ## The equality table -/

@[simp] theorem length_eqTable (r : List K) : (eqTable r).length = 2 ^ r.length := by
  simp [eqTable]

@[simp] theorem eqTable_nil : eqTable ([] : List K) = [1] := by simp [eqTable, vertex]

/-- Coordinate 0 is the top bit: the table of (c, r) is the table of r scaled by 1 - c, then by c. -/
theorem eqTable_cons (c : K) (r : List K) :
    eqTable (c :: r) = (eqTable r).map (· * (1 - c)) ++ (eqTable r).map (· * c) := by
  simp only [eqTable, List.length_cons, pow_succ, mul_two, List.range_add, List.map_append,
    List.map_map]
  congr 1 <;> refine List.map_congr_left fun b hb => ?_ <;> simp only [List.mem_range] at hb
  · simp [vertex_low hb, mul_comm]
  · simp [vertex_high hb, mul_comm]

/-- The last coordinate is the bottom bit: entry 2 b + e of the table of r ++ [c] is entry b times eq(e, c). -/
theorem getElem_eqTable_snoc (c : K) (r : List K) (b : ℕ) (e : Bool) :
    eq (vertex (r.length + 1) (Nat.bit e b)) (r ++ [c]) =
      eq (vertex r.length b) r * (if e then c else 1 - c) := by
  rw [vertex_bit, eq_append (by simp)]
  cases e <;> simp [eq]

/-- The table of r ++ s is the outer product of the two tables. -/
theorem eqTable_append (r s : List K) :
    eqTable (r ++ s) = (eqTable r).flatMap fun a => (eqTable s).map (a * ·) := by
  induction r with
  | nil => simp
  | cons c r ih =>
    simp only [List.cons_append, eqTable_cons, ih, List.flatMap_append, List.map_flatMap,
      List.flatMap_map, List.map_map]
    congr 1 <;> exact List.flatMap_congr fun a _ => List.map_congr_left fun _ _ => by
      simp only [Function.comp]; ring

/-! ## The extension -/

theorem mle_eq_sum (f r : List K) :
    mle f r = ∑ b ∈ range (2 ^ r.length), (eqTable r).getD b 0 * f.getD b 0 :=
  sum_congr rfl fun b hb => by simp [eqTable, List.getD_eq_getElem?_getD, mem_range.mp hb]

@[simp] theorem mle_nil (f : List K) : mle f [] = f.getD 0 0 := by simp [mle, vertex]

/-- Fixing the first variable: the extension at (c, r) interpolates the two halves along c. -/
theorem mle_cons (f : List K) (c : K) (r : List K) :
    mle f (c :: r) = (1 - c) * mle (f.take (2 ^ r.length)) r +
      c * mle (f.drop (2 ^ r.length)) r := by
  simp only [mle, List.length_cons, pow_succ, mul_two, sum_range_add, mul_sum]
  congr 1 <;> refine sum_congr rfl fun b hb => ?_ <;> simp only [mem_range] at hb
  · simp [vertex_low hb, List.getD_eq_getElem?_getD, hb]; ring
  · rw [vertex_high hb]; simp [List.getD_eq_getElem?_getD, add_comm]; ring

theorem getD_map_mul (a : K) (f : List K) (b : ℕ) :
    (f.map (a * ·)).getD b 0 = a * f.getD b 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases f[b]? <;> simp

theorem getD_map_mul_right (a : K) (f : List K) (b : ℕ) :
    (f.map (· * a)).getD b 0 = f.getD b 0 * a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases f[b]? <;> simp

/-- The extension is linear in the table: scaling the table scales the extension. -/
theorem mle_map_mul (a : K) (f r : List K) : mle (f.map (a * ·)) r = a * mle f r := by
  simp only [mle, mul_sum, getD_map_mul]
  exact sum_congr rfl fun _ _ => by ring

theorem powTable_succ (v : K) (n : ℕ) :
    powTable v (n + 1) = powTable v n ++ (powTable v n).map (v ^ 2 ^ n * ·) := by
  simp [powTable, pow_succ, mul_two, List.range_add, pow_add]

/-- The extension of the powers of v at (c, r) splits off the factor 1 - c + c v^(2^n). -/
theorem mle_powTable_cons (v c : K) (r : List K) :
    mle (powTable v (r.length + 1)) (c :: r) =
      (1 - c + c * v ^ 2 ^ r.length) * mle (powTable v r.length) r := by
  have hl : (powTable v r.length).length = 2 ^ r.length := by simp [powTable]
  rw [mle_cons, powTable_succ, List.take_left' hl, List.drop_left' hl, mle_map_mul]
  ring

end Plonky3Lean.Proofs.MultilinearUtil
