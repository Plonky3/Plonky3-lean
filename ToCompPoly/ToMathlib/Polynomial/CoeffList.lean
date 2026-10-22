/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Data.List.Prime
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Arithmetic in `R[X] / (f)` on coefficient lists, that the kernel evaluates

An element of `R[X] / (f)`, for `f` monic of degree `D`, is stored as its `D` coefficients.
Mathlib's `Polynomial` is not computable, so `decide` cannot check a fact such as `g ^ n = 1` there.

This file gives list versions of the operations and proves them correct:
- `toPoly l` is the polynomial `Σ i, l[i] · X ^ i`;
- `mul`, `reduce`, `mulMod` and `powMod` compute products and powers;
- `mk_toPoly_powMod`: `powMod` is the power in `AdjoinRoot f`, given `X ^ D = m` there;
- `mk_toPoly_ne_of_getD`: two short lists that differ in one coefficient stand for different elements.

`m` is the list of low coefficients of `X ^ D` modulo `f`: `X ^ D - toPoly m = f`.
-/

@[expose] public section

open Polynomial

namespace Polynomial.CoeffList

variable {R : Type*} [CommRing R]

/-- The polynomial `Σ i, l[i] · X ^ i`. -/
noncomputable def toPoly : List R → R[X]
  | [] => 0
  | c :: l => C c + X * toPoly l

@[simp] theorem toPoly_nil : toPoly ([] : List R) = 0 := rfl

@[simp] theorem toPoly_cons (c : R) (l : List R) : toPoly (c :: l) = C c + X * toPoly l := rfl

/-- The coefficient form with every exponent shifted by `k` is `X ^ k * toPoly l`. -/
theorem sum_mapIdx_shift (l : List R) (k : ℕ) :
    (l.mapIdx fun j c => C c * X ^ (j + k)).sum = X ^ k * toPoly l := by
  induction l generalizing k with
  | nil => simp
  | cons c l ih =>
    rw [List.mapIdx_cons, List.sum_cons]
    have h : (fun i c => C c * (X : R[X]) ^ (i + 1 + k)) =
        (fun i c => C c * X ^ (i + (k + 1))) := by
      funext i c; rw [Nat.add_assoc, Nat.add_comm 1 k]
    simp only [h, ih, toPoly_cons, Nat.zero_add]
    ring

/-- `toPoly` is the coefficient form `Σ j, C l[j] * X ^ j`. -/
theorem toPoly_eq_sum (l : List R) :
    toPoly l = (l.mapIdx fun j c => C c * X ^ j).sum := by
  simpa using (sum_mapIdx_shift l 0).symm

theorem coeff_toPoly (l : List R) (i : ℕ) : (toPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons c l ih =>
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih]

theorem degree_toPoly_lt (l : List R) : (toPoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  have hi' : l.length ≤ i := by exact_mod_cast hi
  simp [coeff_toPoly, List.getD_eq_getElem?_getD, hi']

/-! ## Addition and multiplication -/

/-- Coefficientwise sum, padding the shorter list with zeros. -/
def add : List R → List R → List R
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: add a b

@[simp] theorem toPoly_add (a b : List R) : toPoly (add a b) = toPoly a + toPoly b := by
  induction a generalizing b with
  | nil => simp [add]
  | cons x a ih =>
    cases b with
    | nil => simp [add]
    | cons y b => simp only [add, toPoly_cons, ih, map_add]; ring

/-- The product, by schoolbook multiplication. -/
def mul : List R → List R → List R
  | [], _ => []
  | x :: a, b => add (b.map (x * ·)) (0 :: mul a b)

theorem toPoly_map_mul (x : R) (b : List R) : toPoly (b.map (x * ·)) = C x * toPoly b := by
  induction b with
  | nil => simp
  | cons y b ih => simp only [List.map_cons, toPoly_cons, ih, map_mul]; ring

@[simp] theorem toPoly_mul (a b : List R) : toPoly (mul a b) = toPoly a * toPoly b := by
  induction a with
  | nil => simp [mul]
  | cons x a ih => simp only [mul, toPoly_add, toPoly_map_mul, toPoly_cons, ih, map_zero]; ring

theorem toPoly_append (a b : List R) :
    toPoly (a ++ b) = toPoly a + X ^ a.length * toPoly b := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, toPoly_cons, ih, List.length_cons]; ring

/-! ## Reduction modulo `f` -/

/-- Replace `X ^ D` by `m` until at most `D` coefficients remain (or `fuel` runs out). -/
def reduce (D : ℕ) (m : List R) : ℕ → List R → List R
  | 0, c => c
  | fuel + 1, c => if c.length ≤ D then c else reduce D m fuel (add (c.take D) (mul (c.drop D) m))

/-- The product of `a` and `b` in `R[X] / (f)`. -/
def mulMod (D : ℕ) (m a b : List R) : List R :=
  reduce D m (a.length + b.length) (mul a b)

/-- `a ^ e` in `R[X] / (f)`, by square-and-multiply, for `e < 2 ^ fuel`. -/
def powModAux (D : ℕ) (m : List R) : ℕ → List R → ℕ → List R
  | 0, _, _ => [1]
  | fuel + 1, a, e =>
    if e = 0 then [1]
    else
      let h := powModAux D m fuel (mulMod D m a a) (e / 2)
      if e % 2 = 1 then mulMod D m a h else h

/-- `a ^ e` in `R[X] / (f)`, for `e < 2 ^ 256`. -/
def powMod (D : ℕ) (m a : List R) (e : ℕ) : List R := powModAux D m 256 a e

variable {f : R[X]} {D : ℕ} {m : List R}

theorem mk_toPoly_reduce (hX : AdjoinRoot.mk f (X ^ D) = AdjoinRoot.mk f (toPoly m))
    (fuel : ℕ) (c : List R) :
    AdjoinRoot.mk f (toPoly (reduce D m fuel c)) = AdjoinRoot.mk f (toPoly c) := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    unfold reduce
    split_ifs with h
    · rfl
    · rw [ih]
      conv_rhs => rw [← List.take_append_drop D c, toPoly_append,
        List.length_take_of_le (by omega)]
      simp only [toPoly_add, toPoly_mul, map_add, map_mul, hX]
      ring

theorem mk_toPoly_mulMod (hX : AdjoinRoot.mk f (X ^ D) = AdjoinRoot.mk f (toPoly m))
    (a b : List R) :
    AdjoinRoot.mk f (toPoly (mulMod D m a b)) =
      AdjoinRoot.mk f (toPoly a) * AdjoinRoot.mk f (toPoly b) := by
  rw [mulMod, mk_toPoly_reduce hX, toPoly_mul, map_mul]

theorem mk_toPoly_powModAux (hX : AdjoinRoot.mk f (X ^ D) = AdjoinRoot.mk f (toPoly m))
    (fuel : ℕ) (a : List R) (e : ℕ) (he : e < 2 ^ fuel) :
    AdjoinRoot.mk f (toPoly (powModAux D m fuel a e)) = AdjoinRoot.mk f (toPoly a) ^ e := by
  induction fuel generalizing a e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powModAux]
  | succ fuel ih =>
    unfold powModAux
    by_cases h0 : e = 0
    · subst h0; simp
    · simp only [h0, ↓reduceIte]
      have he2 : e / 2 < 2 ^ fuel := by rw [pow_succ] at he; omega
      have hsq : AdjoinRoot.mk f (toPoly (powModAux D m fuel (mulMod D m a a) (e / 2))) =
          AdjoinRoot.mk f (toPoly a) ^ (2 * (e / 2)) := by
        rw [ih _ _ he2, mk_toPoly_mulMod hX, pow_mul, sq]
      rcases Nat.mod_two_eq_zero_or_one e with h | h
      · simp only [h, zero_ne_one, ↓reduceIte]
        rw [hsq]; congr 1; omega
      · simp only [h, ↓reduceIte]
        rw [mk_toPoly_mulMod hX, hsq, ← pow_succ']
        congr 1; omega

theorem mk_toPoly_powMod (hX : AdjoinRoot.mk f (X ^ D) = AdjoinRoot.mk f (toPoly m))
    (a : List R) (e : ℕ) (he : e < 2 ^ 256) :
    AdjoinRoot.mk f (toPoly (powMod D m a e)) = AdjoinRoot.mk f (toPoly a) ^ e :=
  mk_toPoly_powModAux hX 256 a e he

/-! ## Telling elements apart -/

/-- Two lists of at most `deg f` coefficients that differ at some index stand for different elements of `R[X] / (f)`. -/
theorem mk_toPoly_ne_of_getD [Nontrivial R] (hf : f.Monic) {a b : List R}
    (ha : a.length ≤ f.natDegree) (hb : b.length ≤ f.natDegree) {i : ℕ}
    (hi : a.getD i 0 ≠ b.getD i 0) :
    AdjoinRoot.mk f (toPoly a) ≠ AdjoinRoot.mk f (toPoly b) := by
  intro h
  rw [AdjoinRoot.mk_eq_mk] at h
  have hdeg : (toPoly a - toPoly b).degree < f.degree := by
    rw [degree_eq_natDegree hf.ne_zero]
    calc (toPoly a - toPoly b).degree ≤ max (toPoly a).degree (toPoly b).degree :=
          degree_sub_le _ _
      _ < f.natDegree := max_lt
          (lt_of_lt_of_le (degree_toPoly_lt a) (by exact_mod_cast ha))
          (lt_of_lt_of_le (degree_toPoly_lt b) (by exact_mod_cast hb))
  have h0 : toPoly a - toPoly b = 0 := by
    by_contra h0
    exact hf.not_dvd_of_degree_lt h0 hdeg h
  apply hi
  have := congrArg (fun p => p.coeff i) h0
  simpa [coeff_sub, coeff_toPoly, sub_eq_zero] using this

/-- Two lists that agree on their first `N` coefficients, and have no more, are the same polynomial. -/
theorem toPoly_eq_of_getD (N : ℕ) {a b : List R} (ha : a.length ≤ N) (hb : b.length ≤ N)
    (h : ∀ i < N, a.getD i 0 = b.getD i 0) : toPoly a = toPoly b := by
  ext i
  rw [coeff_toPoly, coeff_toPoly]
  by_cases hi : i < N
  · exact h i hi
  · simp [List.getD_eq_getElem?_getD, show a.length ≤ i by omega, show b.length ≤ i by omega]

/-! ## Multiplicative order -/

/-- The order of an element is `n`, from the factorisation `n = Π q ^ k` and kernel-checkable powers.

The element `g` is given by its coefficients, and every power is computed by `powMod`.
- `hpow`: `g ^ n` has the coefficients of `1`.
- `hdiv`: for each prime `q` of the factorisation, `g ^ (n / q)` differs from `1` in some coefficient. -/
theorem orderOf_mk_toPoly [Nontrivial R] (hf : f.Monic) (hD : f.natDegree = D) (hD1 : 1 ≤ D)
    (hX : AdjoinRoot.mk f (X ^ D) = AdjoinRoot.mk f (toPoly m)) (g : List R) {n : ℕ}
    (l : List (ℕ × ℕ)) (hl : ∀ q ∈ l, q.1.Prime) (hn : (l.map fun q => q.1 ^ q.2).prod = n)
    (hn0 : 0 < n) (hn256 : n < 2 ^ 256)
    (hpow : (powMod D m g n).length ≤ D ∧ ∀ i < D, (powMod D m g n).getD i 0 = [1].getD i 0)
    (hdiv : ∀ q ∈ l, (powMod D m g (n / q.1)).length ≤ D ∧
      ∃ i < D, (powMod D m g (n / q.1)).getD i 0 ≠ [(1 : R)].getD i 0) :
    orderOf (AdjoinRoot.mk f (toPoly g)) = n := by
  have h1 : AdjoinRoot.mk f (toPoly [(1 : R)]) = 1 := by simp
  refine orderOf_eq_of_pow_and_pow_div_prime hn0 ?_ ?_
  · rw [← mk_toPoly_powMod hX g n hn256, ← h1,
      toPoly_eq_of_getD D hpow.1 (by simpa using hD1) hpow.2]
  · intro q hq hqn
    obtain ⟨r, hr, hqr⟩ : ∃ r ∈ l, q ∣ r.1 ^ r.2 := by
      rw [← hn] at hqn
      obtain ⟨t, ht, hqt⟩ := (Prime.dvd_prod_iff hq.prime).mp hqn
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
      exact ⟨r, hr, hqt⟩
    have hqr' : q = r.1 := (Nat.prime_dvd_prime_iff_eq hq (hl r hr)).mp (hq.dvd_of_dvd_pow hqr)
    subst hqr'
    obtain ⟨hlen, i, hi, hne⟩ := hdiv r hr
    have hlt : n / r.1 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) hn256
    rw [← mk_toPoly_powMod hX g _ hlt, ← h1]
    exact mk_toPoly_ne_of_getD hf (by omega) (by simp [hD]; omega) hne

end Polynomial.CoeffList
