module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The circle curve and its FFT

The definitions follow Haböck, Levit and Papini, "Circle STARKs", eprint 2024/278 (revision of December 2024).

The circle over a field K is the set of points with x^2 + y^2 = 1.

It is a group under the law of Section 3.1:

```text
    (x_0, y_0) . (x_1, y_1) = (x_0 x_1 - y_0 y_1, x_0 y_1 + y_0 x_1)
```

The group is written additively here, as Plonky3 writes it, so the paper's P . Q is P + Q.

* The squaring map pi of equation (1) is P + P.
* The inverse map J of equation (2) is the negation (x, -y).
* The vanishing polynomial v_n of equation (8) is the x-coordinate of pi^(n-1)(P).
* The FFT basis of Definition 4 is b_j = y^(j_0) v_1^(j_1) ... v_(n-1)^(j_(n-1)), for the bits j_k of j.
-/

namespace Plonky3Lean.Spec.Circle

open Finset

/-- The points (x, y) of the circle x^2 + y^2 = 1 over K. -/
def C (K : Type _) [CommRing K] := {q : K × K // q.1 ^ 2 + q.2 ^ 2 = 1}

namespace C

variable {K : Type _} [CommRing K]

/-- The x-coordinate. -/
def x (P : C K) : K := P.val.1

/-- The y-coordinate. -/
def y (P : C K) : K := P.val.2

theorem eq (P : C K) : P.x ^ 2 + P.y ^ 2 = 1 := P.property

@[ext] theorem ext {P Q : C K} (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q :=
  Subtype.ext (Prod.ext hx hy)

/-- The point with the given coordinates. -/
def mk (x y : K) (h : x ^ 2 + y ^ 2 = 1) : C K := ⟨(x, y), h⟩

@[simp] theorem mk_x (x y : K) (h) : (mk x y h).x = x := rfl
@[simp] theorem mk_y (x y : K) (h) : (mk x y h).y = y := rfl

instance : Zero (C K) := ⟨mk 1 0 (by ring)⟩

instance : Neg (C K) := ⟨fun P => mk P.x (-P.y) (by rw [neg_sq]; exact P.eq)⟩

instance : Add (C K) := ⟨fun P Q => mk (P.x * Q.x - P.y * Q.y) (P.x * Q.y + P.y * Q.x)
  (by linear_combination (Q.x ^ 2 + Q.y ^ 2) * P.eq + Q.eq)⟩

@[simp] theorem zero_x : (0 : C K).x = 1 := rfl
@[simp] theorem zero_y : (0 : C K).y = 0 := rfl
@[simp] theorem neg_x (P : C K) : (-P).x = P.x := rfl
@[simp] theorem neg_y (P : C K) : (-P).y = -P.y := rfl
@[simp] theorem add_x (P Q : C K) : (P + Q).x = P.x * Q.x - P.y * Q.y := rfl
@[simp] theorem add_y (P Q : C K) : (P + Q).y = P.x * Q.y + P.y * Q.x := rfl

instance : AddCommGroup (C K) where
  add_assoc P Q R := by ext <;> simp <;> ring
  zero_add P := by ext <;> simp
  add_zero P := by ext <;> simp
  add_comm P Q := by ext <;> simp <;> ring
  neg_add_cancel P := by ext <;> simp; linear_combination P.eq; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem sub_x (P Q : C K) : (P - Q).x = P.x * Q.x + P.y * Q.y := by
  rw [sub_eq_add_neg, add_x, neg_x, neg_y]; ring

@[simp] theorem sub_y (P Q : C K) : (P - Q).y = P.y * Q.x - P.x * Q.y := by
  rw [sub_eq_add_neg, add_y, neg_x, neg_y]; ring

/-- The squaring map pi(x, y) = (2 x^2 - 1, 2 x y) of equation (1). -/
theorem two_nsmul_x (P : C K) : (2 • P).x = 2 * P.x ^ 2 - 1 := by
  rw [two_nsmul, add_x]; linear_combination -P.eq

theorem two_nsmul_y (P : C K) : (2 • P).y = 2 * P.x * P.y := by
  rw [two_nsmul, add_y]; ring

/-- The antipode (-x, -y): the translation by the point (-1, 0) of order two. -/
def antipode (P : C K) : C K := P + mk (-1) 0 (by ring)

@[simp] theorem antipode_x (P : C K) : P.antipode.x = -P.x := by simp [antipode]
@[simp] theorem antipode_y (P : C K) : P.antipode.y = -P.y := by simp [antipode]

end C

variable {K : Type _} [CommRing K]

/-- The x-coordinate step of the squaring map, x -> 2 x^2 - 1. -/
def piX (x : K) : K := 2 * x ^ 2 - 1

/-- The vanishing polynomial v_n(P) = (pi^(n-1)(P)).x of equation (8), for n >= 1. -/
def vn (n : ℕ) (P : C K) : K := (2 ^ (n - 1) • P).x

/-- Bit k of j. -/
def bit (j k : ℕ) : ℕ := j / 2 ^ k % 2

/-- The FFT basis b_j^(n)(P) = y^(j_0) v_1(P)^(j_1) ... v_(n-1)(P)^(j_(n-1)) of Definition 4. -/
def basis (n j : ℕ) (P : C K) : K :=
  P.y ^ bit j 0 * ∏ k ∈ Ico 1 n, vn k P ^ bit j k

/-- The value at P of the polynomial with coefficients c in the FFT basis of order n. -/
def fftEval {V : Type _} [AddCommGroup V] [Module K V] (n : ℕ) (c : ℕ → V) (P : C K) : V :=
  ∑ j ∈ range (2 ^ n), basis n j P • c j

/-- The x-only part of the FFT basis on the projected domain S_j of Section 4.1: x^(k_0) pi(x)^(k_1) ... pi^(m-1)(x)^(k_(m-1)). -/
def xBasis (m k : ℕ) (x : K) : K := ∏ t ∈ range m, (piX^[t] x) ^ bit k t

/-- The value at x of the function with coefficients d in the x-only basis of order m. -/
def xEval {V : Type _} [AddCommGroup V] [Module K V] (m : ℕ) (d : ℕ → V) (x : K) : V :=
  ∑ k ∈ range (2 ^ m), xBasis m k x • d k

/-- The vanishing polynomial v_D(P) = v_n(P) - v_n(Q) of the twin coset D = Q + G_(n-1) ∪ -Q + G_(n-1), equation (7). -/
def vD (n : ℕ) (Q P : C K) : K := vn n P - vn n Q

/-- The building block v(x, y) = 1 - (x + i y) of the DEEP quotient, as the pair (1 - x, -y) of its real and imaginary parts. -/
def vBlock (x y : K) : K × K := (1 - x, -y)

/-- The single-point vanishing function v_P(x, y) = v(P_x x + P_y y, -P_y x + P_x y) of equation (11), as real and imaginary parts. -/
def vP (P Q : C K) : K × K := vBlock (P.x * Q.x + P.y * Q.y) (-P.y * Q.x + P.x * Q.y)

/-- The folding of Section 4.2, equations (14) to (19), with the challenge beta: f_0 + beta f_1, where f_0 = (f(P) + f(P'))/2 and f_1 = (f(P) - f(P'))/(2 t) for the fibre {P, P'} and its odd reference function t. -/
def foldPair {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V] (t β : F) (lo hi : V) : V :=
  (2 : F)⁻¹ • (lo + hi) + (β / (2 * t)) • (lo - hi)

end Plonky3Lean.Spec.Circle
