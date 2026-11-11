module

public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# The successor: eval_next

The successor sends vertex x to x + 1, and the last vertex to itself.

Its weight at (p, r) sums eq(x, p) eq(succ(x), r) over the cube.

The fold adds one to x bit by bit from the bottom, carrying as a binary adder does:

```text
    carry:  x and y agree on the bits so far as  x = 1...1,  y = 0...0
    done:   y = x + 1 on the bits so far, with no carry out
    omega:  x = y = 1...1 on the bits so far
```
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.point.mirror Finset

variable {F : Type _} [Field F]

/-- The weight of the pairs y = x + 1 that do not overflow. -/
def nextDone (p r : List F) : F :=
  ∑ x ∈ range (2 ^ p.length - 1), eq (vertex p.length x) p * eq (vertex p.length (x + 1)) r

/-- The weight of x all ones and y all zeros. -/
def nextCarry (p r : List F) : F :=
  eq (vertex p.length (2 ^ p.length - 1)) p * eq (vertex p.length 0) r

/-- The weight of x and y both all ones. -/
def nextOmega (p r : List F) : F :=
  eq (vertex p.length (2 ^ p.length - 1)) p * eq (vertex p.length (2 ^ p.length - 1)) r

theorem vertex_allOnes_succ (n : ℕ) :
    (vertex (n + 1) (2 ^ (n + 1) - 1) : List F) = 1 :: vertex n (2 ^ n - 1) := by
  rw [show 2 ^ (n + 1) - 1 = 2 ^ n + (2 ^ n - 1) by rw [pow_succ]; have := Nat.one_le_two_pow (n := n); omega]
  exact vertex_high (by have := Nat.one_le_two_pow (n := n); omega)

theorem vertex_zero_succ (n : ℕ) : (vertex (n + 1) 0 : List F) = 0 :: vertex n 0 :=
  vertex_low (by positivity)

theorem nextDone_cons (a b : F) (p r : List F) :
    nextDone (a :: p) (b :: r) =
      ((1 - a) * (1 - b) + a * b) * nextDone p r + (1 - a) * b * nextCarry p r := by
  have h1 := Nat.one_le_two_pow (n := p.length)
  have hlow : ∀ x ∈ range (2 ^ p.length - 1), eq (vertex (p.length + 1) x) (a :: p) *
      eq (vertex (p.length + 1) (x + 1)) (b :: r) =
      (1 - a) * (1 - b) * (eq (vertex p.length x) p * eq (vertex p.length (x + 1)) r) := fun x hx => by
    simp only [mem_range] at hx
    rw [vertex_low (by omega), vertex_low (by omega)]
    simp; ring
  have hhigh : ∀ y ∈ range (2 ^ p.length - 1),
      eq (vertex (p.length + 1) (2 ^ p.length - 1 + 1 + y)) (a :: p) *
      eq (vertex (p.length + 1) (2 ^ p.length - 1 + 1 + y + 1)) (b :: r) =
      a * b * (eq (vertex p.length y) p * eq (vertex p.length (y + 1)) r) := fun y hy => by
    simp only [mem_range] at hy
    rw [show 2 ^ p.length - 1 + 1 = 2 ^ p.length by omega, vertex_high (by omega), Nat.add_assoc,
      vertex_high (by omega)]
    simp; ring
  simp only [nextDone, nextCarry, List.length_cons]
  rw [show 2 ^ (p.length + 1) - 1 = (2 ^ p.length - 1 + 1) + (2 ^ p.length - 1) by
      rw [pow_succ]; omega,
    sum_range_add, sum_range_succ, sum_congr rfl hlow, sum_congr rfl hhigh, ← mul_sum, ← mul_sum,
    vertex_low (show 2 ^ p.length - 1 < 2 ^ p.length by omega),
    show 2 ^ p.length - 1 + 1 = 2 ^ p.length + 0 by omega, vertex_high (by positivity)]
  simp; ring

/-- The fold computes the three weights. -/
theorem eval_next_loop (p r : List F) (h : p.length = r.length) :
    (p.zip r).reverse.foldl evalNextStep (1, 0, 1) = (nextCarry p r, nextDone p r, nextOmega p r) := by
  induction p generalizing r with
  | nil =>
    obtain rfl : r = [] := List.eq_nil_of_length_eq_zero h.symm
    simp [nextCarry, nextDone, nextOmega, vertex]
  | cons a p ih =>
    obtain ⟨b, r, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.reverse_cons, List.foldl_append, ih r h, List.foldl_cons,
      List.foldl_nil, evalNextStep, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp only [nextCarry, List.length_cons, vertex_allOnes_succ, vertex_zero_succ, eq_cons]
      ring
    · rw [nextDone_cons a b p r]; ring
    · simp only [nextOmega, List.length_cons, vertex_allOnes_succ, eq_cons]
      ring

/-- eval_next: the three weights, when the point and the row have the same length. -/
theorem eval_next_eq (p r : List F) (h : p.length = r.length) :
    Point.eval_next p r = some (nextCarry p r, nextDone p r, nextOmega p r) := by
  simp [Point.eval_next, h, eval_next_loop p r h]

theorem eval_next_panics (p r : List F) (h : p.length ≠ r.length) : Point.eval_next p r = none := by
  simp [Point.eval_next, h]

/-- The completed and boundary weights add up to the successor weight. -/
theorem nextDone_add_nextOmega (p r : List F) :
    nextDone p r + nextOmega p r = ∑ x ∈ range (2 ^ p.length),
      eq (vertex p.length x) p * eq (vertex p.length (succRepeat p.length x)) r := by
  have h1 := Nat.one_le_two_pow (n := p.length)
  rw [show 2 ^ p.length = 2 ^ p.length - 1 + 1 by omega, sum_range_succ, nextDone, nextOmega]
  congr 1
  · exact sum_congr rfl fun x hx => by
      simp only [mem_range] at hx
      simp [succRepeat, show x + 1 < 2 ^ p.length by omega]
  · simp [succRepeat, show ¬ 2 ^ p.length - 1 + 1 < 2 ^ p.length by omega]

end Plonky3Lean.Proofs.MultilinearUtil
