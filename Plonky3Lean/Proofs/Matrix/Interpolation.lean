module

public import P3Matrix
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# p3-matrix: interpolation

The transcribed interpolation routines against Lagrange interpolation.

On a coset g H, with H of order N = 2^k, the code uses the first barycentric form.

Its nodal polynomial is X^N - g^N, and its weights are x_i / (N g^N).

See Berrut and Trefethen, Barycentric Lagrange Interpolation, SIAM Review 46(3), 2004.
-/

open Polynomial Finset Lagrange
open p3_matrix.interpolation.mirror

namespace Plonky3Lean.Proofs.Matrix.Interp

variable {K : Type _} [Field K]

/-- The coset points g omega^i. -/
def cosetPt (ω g : K) (k : ℕ) : Fin (2 ^ k) → K := fun i => g * ω ^ i.val

theorem cosetPt_injective {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hg : g ≠ 0) :
    Function.Injective (cosetPt ω g k) := by
  intro i j h
  simp only [cosetPt, mul_right_inj' hg] at h
  exact Fin.ext (hω.pow_inj i.isLt j.isLt h)

theorem nodal_coset {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) :
    nodal univ (cosetPt ω g k) = X ^ 2 ^ k - C (g ^ 2 ^ k) := by
  rw [X_pow_sub_C_eq_prod hω (by positivity) rfl, nodal_eq,
    ← Fin.prod_univ_eq_prod_range (fun i => X - C (ω ^ i * g))]
  simp [cosetPt, mul_comm]

theorem cosetPt_pow {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (i : Fin (2 ^ k)) :
    cosetPt ω g k i ^ 2 ^ k = g ^ 2 ^ k := by
  rw [cosetPt, mul_pow, ← pow_mul, mul_comm i.val, pow_mul, hω.pow_eq_one, one_pow, mul_one]

/-- The barycentric weight of the coset point x_i is x_i / (N g^N). -/
theorem nodalWeight_coset [DecidableEq (Fin (2 ^ k))] {ω g : K} (hω : IsPrimitiveRoot ω (2 ^ k))
    (hg : g ≠ 0) (hN : (2 : K) ≠ 0) (i : Fin (2 ^ k)) :
    nodalWeight univ (cosetPt ω g k) i =
      cosetPt ω g k i / ((2 ^ k : K) * g ^ 2 ^ k) := by
  rw [nodalWeight_eq_eval_derivative_nodal (mem_univ i), nodal_coset hω]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
    eval_X]
  have hx : cosetPt ω g k i ≠ 0 := by
    simp only [cosetPt]; exact mul_ne_zero hg (pow_ne_zero _ (hω.ne_zero (by positivity)))
  have hpow := cosetPt_pow (g := g) hω i
  have hk : (2 : K) ^ k ≠ 0 := pow_ne_zero _ hN
  have hsucc : cosetPt ω g k i ^ (2 ^ k - 1) * cosetPt ω g k i = g ^ 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hpow]
  push_cast
  rw [eq_div_iff (mul_ne_zero hk (pow_ne_zero _ hg)), ← hsucc]
  field_simp

theorem cosetPt_ne_zero {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hg : g ≠ 0)
    (i : Fin (2 ^ k)) : cosetPt ω g k i ≠ 0 := by
  simp only [cosetPt]; exact mul_ne_zero hg (pow_ne_zero _ (hω.ne_zero (by positivity)))

/-- Off the coset, the interpolant evaluates by the first barycentric form. -/
theorem eval_coset_off {ω g z : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hg : g ≠ 0)
    (hN : (2 : K) ≠ 0) (hz : ∀ i, z ≠ cosetPt ω g k i) (f : Fin (2 ^ k) → K) :
    eval z (interpolate univ (cosetPt ω g k) f) = (z ^ 2 ^ k - g ^ 2 ^ k) *
      ∑ i, cosetPt ω g k i / ((2 ^ k : K) * g ^ 2 ^ k) * (z - cosetPt ω g k i)⁻¹ * f i := by
  classical
  rw [eval_interpolate_not_at_node f (fun i _ => hz i), nodal_coset hω]
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [nodalWeight_coset hω hg hN]

variable [DecidableEq K]

/-- Coset interpolation evaluates each column's interpolant at z, for every z.

A zero shift panics. -/
theorem interpolate_coset_eq {ω g z : K} {k w : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k))
    (hN : (2 : K) ≠ 0) (M : Fin (2 ^ k) → Fin w → K) :
    interpolate_coset k ω g z M = if g = 0 then none else
      some fun c => eval z (interpolate univ (cosetPt ω g k) fun i => M i c) := by
  unfold interpolate_coset
  by_cases hg : g = 0
  · simp [hg]
  simp only [hg, ite_false]
  have hinj := cosetPt_injective hω hg
  have hk : (2 : K) ^ k ≠ 0 := pow_ne_zero _ hN
  have hgN : g ^ 2 ^ k ≠ 0 := pow_ne_zero _ hg
  split
  · rename_i i hi
    have := List.find?_some hi
    simp only [decide_eq_true_eq, sub_eq_zero] at this
    congr 1; funext c
    rw [show z = cosetPt ω g k i from this,
      eval_interpolate_at_node _ (hinj.injOn) (mem_univ i)]
  · rename_i hnone
    have hz : ∀ i, z ≠ cosetPt ω g k i := by
      intro i h
      have := List.find?_eq_none.mp hnone i (List.mem_finRange i)
      exact this (by rw [h, cosetPt, sub_self]; exact decide_eq_true rfl)
    by_cases hz0 : z = 0
    · simp only [hz0, ite_true]
      congr 1; funext c
      rw [← hz0, eval_coset_off hω hg hN hz, hz0, columnwise, mul_sum, sum_mul]
      refine sum_congr rfl fun i _ => ?_
      have hx := cosetPt_ne_zero hω hg i
      field_simp
      ring
    · simp only [hz0, ite_false, compute_adjusted_weights, Option.bind_some,
        interpolate_coset_with_precomputation, mul_ne_zero hgN hk]
      congr 1; funext c
      rw [eval_coset_off hω hg hN hz, columnwise, mul_sum, sum_mul]
      refine sum_congr rfl fun i _ => ?_
      have hx := cosetPt_ne_zero hω hg i
      have hzx : z - cosetPt ω g k i ≠ 0 := sub_ne_zero.mpr (hz i)
      simp only [cosetPt] at hx hzx ⊢
      field_simp
      ring

/-! ## Arbitrary domains -/

/-- The factor one step (i, j) of the weight loop contributes to the denominator of t. -/
def pairFactor {n : ℕ} (x : Fin n → K) (t : Fin n) (p : Fin n × Fin n) : K :=
  if t = p.1 then x p.1 - x p.2 else if t = p.2 then -(x p.1 - x p.2) else 1

theorem foldl_barycentric_step {n : ℕ} (x : Fin n → K) (L : List (Fin n × Fin n)) (d : Fin n → K) :
    L.foldl (barycentric_step x) (some d) =
      if ∀ p ∈ L, x p.1 - x p.2 ≠ 0 then
        some fun t => d t * (L.map (pairFactor x t)).prod
      else none := by
  induction L generalizing d with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons]
    by_cases hp : x p.1 - x p.2 = 0
    · have : L.foldl (barycentric_step x) (barycentric_step x (some d) p) = none := by
        simp only [barycentric_step, Option.bind_some, hp, ite_true]
        clear ih; induction L with
        | nil => rfl
        | cons q L ih' => simpa [List.foldl_cons, barycentric_step] using ih'
      rw [this]; simp [hp]
    · simp only [barycentric_step, Option.bind_some, hp, ite_false]
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp, hp, not_false_eq_true, ne_eq, true_and,
        List.map_cons, List.prod_cons]
      split_ifs <;> try rfl
      congr 1; funext t
      simp only [pairFactor]
      split_ifs <;> ring

omit [DecidableEq K] in
theorem prod_flatMap {α β : Type _} (l : List α) (f : α → List β) (g : β → K) :
    ((l.flatMap f).map g).prod = (l.map fun a => ((f a).map g).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

omit [DecidableEq K] in
theorem prod_map_filter {α : Type _} (l : List α) (P : α → Bool) (f : α → K) :
    ((l.filter P).map f).prod = (l.map fun a => if P a then f a else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem mem_lowerPairs {n : ℕ} (p : Fin n × Fin n) : p ∈ lowerPairs n ↔ p.2.val < p.1.val := by
  obtain ⟨i, j⟩ := p
  simp [lowerPairs, List.mem_flatMap]

omit [DecidableEq K] in
/-- The weight loop's denominator for t is prod_{j != t} (x_t - x_j). -/
theorem prod_lowerPairs {n : ℕ} (x : Fin n → K) (t : Fin n) :
    ((lowerPairs n).map (pairFactor x t)).prod = ∏ j ∈ univ.erase t, (x t - x j) := by
  rw [lowerPairs, prod_flatMap]
  simp only [List.map_map, Function.comp_def, prod_map_filter]
  rw [← Fin.prod_univ_def]
  simp_rw [← Fin.prod_univ_def]
  -- Split each factor into the part where t is the row and the part where t is the column.
  have hsplit : ∀ i j : Fin n, (if decide (j.val < i.val) = true then pairFactor x t (i, j) else 1) =
      (if j.val < i.val ∧ t = i then x t - x j else 1) *
        (if j.val < i.val ∧ t = j then x t - x i else 1) := by
    intro i j
    by_cases hji : j.val < i.val
    · have hne : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
      by_cases hti : t = i
      · subst hti; simp [pairFactor, hji, hne]
      · by_cases htj : t = j
        · subst htj; simp [pairFactor, hji, hti]
        · simp [pairFactor, hji, hti, htj]
    · simp [hji]
  simp_rw [hsplit, prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i j => if j.val < i.val ∧ t = j then x t - x i else 1)]
  have h1 : ∀ i : Fin n, (∏ j, if j.val < i.val ∧ t = i then x t - x j else 1) =
      if t = i then ∏ j, (if j.val < t.val then x t - x j else 1) else 1 := by
    intro i; by_cases h : t = i
    · subst h; simp
    · simp [h]
  have h2 : ∀ j : Fin n, (∏ i, if j.val < i.val ∧ t = j then x t - x i else 1) =
      if t = j then ∏ i, (if t.val < i.val then x t - x i else 1) else 1 := by
    intro j; by_cases h : t = j
    · subst h; simp
    · simp [h]
  simp_rw [h1, h2, Finset.prod_ite_eq, mem_univ, ite_true, ← prod_mul_distrib]
  rw [← Finset.mul_prod_erase univ _ (mem_univ t)]
  simp only [lt_irrefl, ite_false, mul_one, one_mul]
  refine prod_congr rfl fun j hj => ?_
  have hjt : j ≠ t := (mem_erase.mp hj).1
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjt) with h | h
  · simp [h, not_lt.mpr h.le]
  · simp [h, not_lt.mpr h.le]

omit [DecidableEq K] in
theorem lowerPairs_ne_iff {n : ℕ} (x : Fin n → K) :
    (∀ p ∈ lowerPairs n, x p.1 - x p.2 ≠ 0) ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact h (j, i) ((mem_lowerPairs _).mpr hlt) (by simp [hij])
    · exact h (i, j) ((mem_lowerPairs _).mpr hlt) (by simp [hij])
  · intro hinj p hp heq
    have := hinj (sub_eq_zero.mp heq)
    have hlt := (mem_lowerPairs p).mp hp
    rw [this] at hlt; exact lt_irrefl _ hlt

/-- The barycentric weights are 1 / prod_{j != i} (x_i - x_j), and equal points give nothing.

See Berrut and Trefethen, equation (3.2). -/
theorem barycentric_weights_eq {n : ℕ} (x : Fin n → K) :
    barycentric_weights x =
      if Function.Injective x then some fun i => nodalWeight univ x i else none := by
  unfold barycentric_weights
  by_cases hn : n = 0
  · subst hn
    have : Function.Injective x := fun i => i.elim0
    simp only [this, ite_true]
    congr 1; funext i; exact i.elim0
  simp only [hn, ite_false, foldl_barycentric_step, lowerPairs_ne_iff]
  split_ifs with h
  · simp only [Option.map_some]
    congr 1; funext i
    rw [one_mul, prod_lowerPairs, nodalWeight, prod_inv_distrib]
  · rfl

/-- Interpolation at an arbitrary point evaluates each column's interpolant at z.

Equal points give nothing, and no points give zero.

Off the nodes it is the second barycentric form, Berrut and Trefethen equation (4.2). -/
theorem interpolate_arbitrary_point_eq {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (z : K) :
    interpolate_arbitrary_point M x z = if Function.Injective x then
      some fun c => eval z (interpolate univ x fun i => M i c) else none := by
  unfold interpolate_arbitrary_point
  rw [barycentric_weights_eq]
  by_cases hinj : Function.Injective x
  swap
  · simp [hinj]
  simp only [hinj, ite_true, Option.bind_some]
  split
  · rename_i i hi
    have := List.find?_some hi
    simp only [decide_eq_true_eq] at this
    congr 1; funext c
    rw [this, eval_interpolate_at_node _ hinj.injOn (mem_univ i)]
  · rename_i hnone
    have hz : ∀ i, z ≠ x i := by
      intro i h
      have := List.find?_eq_none.mp hnone i (List.mem_finRange i)
      simp [h] at this
    unfold interpolate_arbitrary_with_precomputation
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      congr 1; funext c
      rw [show (univ : Finset (Fin 0)) = ∅ from rfl, interpolate_empty, eval_zero]
    have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
    have hden : ∑ i, (z - x i)⁻¹ * nodalWeight univ x i ≠ 0 := by
      have := sum_nodalWeight_mul_inv_sub_ne_zero hinj.injOn (fun i _ => hz i) hne
      simpa [mul_comm] using this
    simp only [hn, ite_false, hden]
    congr 1; funext c
    rw [eval_interpolate_not_at_node' _ hinj.injOn hne (fun i _ => hz i), columnwise, div_eq_mul_inv]
    congr 1
    · exact sum_congr rfl fun i _ => by ring
    · congr 1; exact sum_congr rfl fun i _ => by ring

/-! ## Newton's recovery of the coefficients -/

section newton

omit [DecidableEq K] in
theorem foldl_mul_eq_prod {α : Type _} (l : List α) (f : α → K) (a : K) :
    l.foldl (fun acc i => acc * f i) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [ih, mul_assoc]

omit [DecidableEq K] in
theorem horner_eq (a : ℕ → K) (x s : K) (k : ℕ) :
    (List.range k).reverse.foldl (fun s i => s * x + a i) s =
      s * x ^ k + ∑ i ∈ range k, a i * x ^ i := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ih, sum_range_succ]
    ring

/-- The Newton basis polynomial B_k = prod_{i < k} (X - x_i). -/
noncomputable def newtonB {n : ℕ} (x : Fin n → K) (k : ℕ) : K[X] :=
  ∏ i ∈ univ.filter (fun i : Fin n => i.val < k), (X - C (x i))

omit [DecidableEq K] in
theorem natDegree_newtonB {n : ℕ} (x : Fin n → K) {k : ℕ} (hk : k ≤ n) :
    (newtonB x k).natDegree = k := by
  rw [newtonB, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
  have : (univ.filter fun i : Fin n => i.val < k).card = k := by
    rw [Fin.card_filter_val_lt]; omega
  exact this

omit [DecidableEq K] in
theorem eval_newtonB {n : ℕ} (x : Fin n → K) (k : ℕ) (z : K) :
    (newtonB x k).eval z =
      ((List.finRange n).filter (fun i => i.val < k)).foldl (fun acc i => acc * (z - x i)) 1 := by
  rw [foldl_mul_eq_prod, one_mul, prod_map_filter, ← Fin.prod_univ_def, newtonB, eval_prod,
    prod_filter]
  simp

omit [DecidableEq K] in
theorem newtonB_succ {n : ℕ} (x : Fin n → K) (k : Fin n) :
    newtonB x (k.val + 1) = newtonB x k.val * (X - C (x k)) := by
  have hs : univ.filter (fun i : Fin n => i.val < k.val + 1) =
      insert k (univ.filter (fun i : Fin n => i.val < k.val)) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
  rw [newtonB, newtonB, hs, prod_insert (by simp), mul_comm]

/-- The loop invariant after k iterations.

The basis holds B_k, and each result column holds a polynomial of degree below k through the first k points. -/
structure NewtonInv {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (k : ℕ)
    (st : RecoverState w K) : Prop where
  basis : ∀ i < n, st.basis i = (newtonB x k).coeff i
  result : ∀ c, ∃ Q : K[X], Q.degree < k ∧ (∀ m : Fin n, m.val < k → Q.eval (x m) = M m c) ∧
    ∀ i, st.result i c = Q.coeff i

omit [DecidableEq K] in
theorem eval_newtonB_node {n : ℕ} (x : Fin n → K) {k : ℕ} (m : Fin n) (hm : m.val < k) :
    (newtonB x k).eval (x m) = 0 := by
  rw [newtonB, eval_prod, prod_eq_zero_iff]
  exact ⟨m, by simp [hm], by simp⟩

omit [DecidableEq K] in
theorem eval_newtonB_ne_iff {n : ℕ} (x : Fin n → K) (k : Fin n) :
    (newtonB x k.val).eval (x k) ≠ 0 ↔ ∀ i : Fin n, i.val < k.val → x k ≠ x i := by
  rw [newtonB, eval_prod, prod_ne_zero_iff]
  simp [sub_eq_zero]

theorem recover_step_spec {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K)
    (k : Fin n) (hb : (newtonB x k.val).eval (x k) ≠ 0) (st : RecoverState w K)
    (h : NewtonInv M x k.val st) :
    ∃ st', recover_step M x k st = some st' ∧ NewtonInv M x (k.val + 1) st' := by
  have hdegB := natDegree_newtonB x (k := k.val) k.isLt.le
  unfold recover_step
  dsimp only
  rw [← eval_newtonB]
  simp only [hb, ite_false]
  refine ⟨_, rfl, ⟨?_, ?_⟩⟩
  · intro i hi
    rw [newtonB_succ]
    simp only
    rcases Nat.lt_trichotomy i (k.val + 1) with hlt | heq | hgt
    · by_cases hi0 : i = 0
      · subst hi0
        simp [mul_coeff_zero, h.basis 0 (by omega)]; ring
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        simp only [show i' + 1 ≠ k.val + 1 by omega, ite_false, show 1 ≤ i' + 1 by omega,
          show i' + 1 ≤ k.val by omega, and_self, ite_true, Nat.add_sub_cancel]
        rw [coeff_mul_X_sub_C, h.basis i' (by omega), h.basis (i' + 1) hi]; ring
    · subst heq
      simp only [ite_true, hi, coeff_mul_X_sub_C, h.basis k.val k.isLt]
      rw [coeff_eq_zero_of_natDegree_lt (by omega : (newtonB x k.val).natDegree < k.val + 1)]
      ring
    · simp only [show i ≠ k.val + 1 by omega, ite_false, show ¬ (1 ≤ i ∧ i ≤ k.val) by omega,
        show i ≠ 0 by omega]
      rw [h.basis i hi, coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_eq_zero_of_natDegree_lt]
      calc (newtonB x k.val * (X - C (x k))).natDegree
          ≤ (newtonB x k.val).natDegree + (X - C (x k)).natDegree := natDegree_mul_le
        _ < i := by rw [hdegB, natDegree_X_sub_C]; omega
  · intro c
    obtain ⟨Q, hQd, hQe, hQc⟩ := h.result c
    -- The Horner loop evaluates Q at x_k.
    have hscr : (List.range k.val).reverse.foldl (fun s i => s * x k + st.result i c) 0 =
        Q.eval (x k) := by
      rw [horner_eq, zero_mul, zero_add]
      simp_rw [hQc]
      rcases Nat.eq_zero_or_pos k.val with hk0 | hk0
      · rw [hk0] at hQd ⊢
        have : Q = 0 := by simpa using hQd
        simp [this]
      · have hnd : Q.natDegree < k.val := by
          by_cases hQ0 : Q = 0
          · simp [hQ0, hk0]
          · exact (natDegree_lt_iff_degree_lt hQ0).mpr hQd
        rw [eval_eq_sum_range' hnd]
    simp only [hscr]
    set coef := (M k c - Q.eval (x k)) * ((newtonB x k.val).eval (x k))⁻¹
    refine ⟨Q + C coef * newtonB x k.val, ?_, ?_, ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hQd (by exact_mod_cast Nat.le_succ _)
      · refine lt_of_le_of_lt degree_le_natDegree ?_
        have := natDegree_C_mul_le coef (newtonB x k.val)
        rw [hdegB] at this
        exact_mod_cast Nat.lt_succ_of_le this
    · intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
      · simp [eval_newtonB_node x m hlt, hQe m hlt]
      · have : m = k := Fin.ext heq
        subst this
        simp only [eval_add, eval_mul, eval_C, coef]
        field_simp
        ring
    · intro i
      simp only [coeff_add, coeff_C_mul, hQc]
      split_ifs with hik
      · rw [h.basis i (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : (newtonB x k.val).natDegree < i)]; ring

theorem recover_step_none {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K)
    (k : Fin n) (hb : (newtonB x k.val).eval (x k) = 0) (st : RecoverState w K) :
    recover_step M x k st = none := by
  unfold recover_step
  dsimp only
  rw [← eval_newtonB, hb, ite_eq_left_iff.mpr (fun h => absurd rfl h)]

/-- After k iterations, the state is empty when two of the first k points coincide.

Otherwise it satisfies the invariant. -/
theorem recover_prefix {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (k : ℕ) (hk : k ≤ n) :
    let r := ((List.finRange n).take k).foldl (fun st k => st.bind (recover_step M x k))
      (some { result := fun _ _ => 0, basis := fun i => if i = 0 then 1 else 0 })
    (r = none ↔ ∃ i j : Fin n, i.val < j.val ∧ j.val < k ∧ x i = x j) ∧
      ∀ st, r = some st → NewtonInv M x k st := by
  induction k with
  | zero =>
    refine ⟨by simp, ?_⟩
    rintro st hst
    simp only [List.take_zero, List.foldl_nil, Option.some.injEq] at hst
    subst hst
    refine ⟨fun i _ => ?_, fun c => ⟨0, by simp, fun m hm => absurd hm (by omega), fun i => by simp⟩⟩
    simp [newtonB, coeff_one]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk' : k < n := by omega
    have hget : (List.finRange n)[k]? = some ⟨k, hk'⟩ := by
      rw [List.getElem?_eq_getElem (by simp; omega)]; simp
    rw [List.take_add_one, hget, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    generalize hr : ((List.finRange n).take k).foldl (fun st k => st.bind (recover_step M x k))
      (some { result := fun _ _ => 0, basis := fun i => if i = 0 then 1 else 0 }) = r at ih1 ih2
    cases r with
    | none =>
      refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun st h => by simp at h⟩
      obtain ⟨i, j, h1, h2, h3⟩ := ih1.mp rfl
      exact ⟨i, j, h1, by omega, h3⟩
    | some st =>
      have hinv := ih2 st rfl
      have hnd : ¬ ∃ i j : Fin n, i.val < j.val ∧ j.val < k ∧ x i = x j := by
        intro h; simpa using ih1.mpr h
      by_cases hb : (newtonB x k).eval (x ⟨k, hk'⟩) = 0
      · rw [Option.bind_some, recover_step_none M x ⟨k, hk'⟩ hb]
        refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun st h => by simp at h⟩
        have := mt (eval_newtonB_ne_iff x ⟨k, hk'⟩).mpr (not_not.mpr hb)
        push Not at this
        obtain ⟨i, hi, heq⟩ := this
        exact ⟨i, ⟨k, hk'⟩, hi, by simp, heq.symm⟩
      · obtain ⟨st', hst', hinv'⟩ := recover_step_spec M x ⟨k, hk'⟩ hb st hinv
        rw [Option.bind_some, hst']
        refine ⟨⟨fun h => by simp at h, fun ⟨i, j, h1, h2, h3⟩ => ?_⟩, fun st'' h => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
          · exact absurd ⟨i, j, h1, h2, h3⟩ hnd
          · have := (eval_newtonB_ne_iff x ⟨k, hk'⟩).mp hb i (by simp; omega)
            exact absurd (by rw [show j = ⟨k, hk'⟩ from Fin.ext h2] at h3; exact h3.symm) this
        · simp only [Option.some.injEq] at h; subst h; exact hinv'

omit [Field K] [DecidableEq K] in
theorem injective_iff_no_dup {n : ℕ} (x : Fin n → K) :
    Function.Injective x ↔ ¬ ∃ i j : Fin n, i.val < j.val ∧ j.val < n ∧ x i = x j := by
  constructor
  · rintro hinj ⟨i, j, h1, -, h3⟩
    have := congrArg Fin.val (hinj h3); omega
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact h ⟨i, j, hlt, j.isLt, hij⟩
    · exact h ⟨j, i, hlt, i.isLt, hij.symm⟩

/-- Newton's recovery returns the coefficients of each column's interpolant, and nothing on equal points. -/
theorem recover_coefficients_eq {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) :
    recover_coefficients M x = if Function.Injective x then
      some fun i c => (interpolate univ x fun m => M m c).coeff i.val else none := by
  obtain ⟨h1, h2⟩ := recover_prefix M x n le_rfl
  rw [List.take_of_length_le (by simp)] at h1 h2
  unfold recover_coefficients
  by_cases hinj : Function.Injective x
  · simp only [hinj, ite_true]
    have hne := (injective_iff_no_dup x).mp hinj
    generalize hr : (List.finRange n).foldl _ _ = r at h1 h2
    cases r with
    | none => exact absurd (h1.mp rfl) hne
    | some st =>
      obtain ⟨-, hres⟩ := h2 st rfl
      simp only [Option.map_some]
      congr 1; funext i c
      obtain ⟨Q, hQd, hQe, hQc⟩ := hres c
      rw [hQc, eq_interpolate_of_eval_eq (s := univ) _ hinj.injOn
        (by rw [card_univ, Fintype.card_fin]; exact hQd) (fun m _ => hQe m m.isLt)]
  · simp only [hinj, ite_false]
    rw [h1.mpr (by simpa [injective_iff_no_dup] using hinj)]
    rfl

/-- Interpolation from pairs returns the interpolant's coefficients, and nothing on equal x. -/
theorem interpolate_lagrange_eq {n : ℕ} (pts : Fin n → K × K) :
    interpolate_lagrange pts = if Function.Injective (fun i => (pts i).1) then
      some fun i => (interpolate univ (fun i => (pts i).1) fun m => (pts m).2).coeff i.val
    else none := by
  unfold interpolate_lagrange
  by_cases hn : n = 0
  · subst hn
    have : Function.Injective (fun i : Fin 0 => (pts i).1) := fun i => i.elim0
    simp only [ite_true, this]
    congr 1
  simp only [hn, ite_false, recover_coefficients_eq]
  split_ifs <;> rfl

end newton

/-- The precomputed coset path at z = 0 returns zero in every column, whatever the weights.

Only a debug assertion rejects that point. -/
theorem interpolate_coset_with_precomputation_zero {k w : ℕ} (M : Fin (2 ^ k) → Fin w → K) (g : K)
    (adj : Fin (2 ^ k) → K) :
    interpolate_coset_with_precomputation k M g 0 adj =
      if g ^ 2 ^ k * (2 ^ k : K) = 0 then none else some fun _ => 0 := by
  unfold interpolate_coset_with_precomputation
  dsimp only
  split_ifs with h
  · rfl
  · congr 1; funext c; simp

/-- Any polynomial of degree below 2^k through the rows gives the value coset interpolation returns. -/
theorem interpolate_coset_unique {ω g z : K} {k w : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k))
    (hN : (2 : K) ≠ 0) (hg : g ≠ 0) (M : Fin (2 ^ k) → Fin w → K) (P : Fin w → K[X])
    (hP : ∀ c, (P c).degree < (2 ^ k : ℕ)) (hPe : ∀ c i, (P c).eval (cosetPt ω g k i) = M i c) :
    interpolate_coset k ω g z M = some fun c => (P c).eval z := by
  rw [interpolate_coset_eq hω hN, ite_eq_right_iff.mpr (fun h => absurd h hg)]
  congr 1; funext c
  rw [eq_interpolate_of_eval_eq (s := univ) _ (cosetPt_injective hω hg).injOn
    (by rw [card_univ, Fintype.card_fin]; exact hP c) (fun i _ => hPe c i)]

end Plonky3Lean.Proofs.Matrix.Interp

namespace Plonky3Lean.Proofs.Matrix.BitRevSwap

open p3_matrix.util.mirror

variable {R : Type _} {h : ℕ}

/-- One iteration t of the swap loop, row by row. -/
theorem step_value (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i) (rows : Fin h → R)
    (T : Fin h) (r : Fin h) :
    (if T < rev T then swap (fun r => if r.val < T.val ∨ (rev r).val < T.val then rows (rev r)
        else rows r) T (rev T)
      else fun r => if r.val < T.val ∨ (rev r).val < T.val then rows (rev r) else rows r) r =
      if r.val < T.val + 1 ∨ (rev r).val < T.val + 1 then rows (rev r) else rows r := by
  have hvi : ∀ a b : Fin h, a = b ↔ a.val = b.val := fun a b => Fin.ext_iff
  by_cases hT : T < rev T
  · have hT' : T.val < (rev T).val := hT
    simp only [hT, ite_true, swap]
    by_cases hr : r = T
    · subst hr
      simp [show ¬ (rev r).val < r.val by omega, hrev]
    · by_cases hr' : r = rev T
      · subst hr'
        simp [hr, hrev, show ¬ (rev T).val < T.val by omega]
      · have h3 : r.val ≠ T.val := fun e => hr (Fin.ext e)
        have h4 : (rev r).val ≠ T.val := fun e => hr' (by rw [← hrev r]; congr 1; exact Fin.ext e)
        simp only [hr, hr', ite_false]
        by_cases h5 : r.val < T.val ∨ (rev r).val < T.val
        · simp only [h5, ite_true, show (r.val < T.val + 1 ∨ (rev r).val < T.val + 1) by omega]
        · simp only [h5, ite_false, show ¬ (r.val < T.val + 1 ∨ (rev r).val < T.val + 1) by omega]
  · have hle : (rev T).val ≤ T.val := by
      have : ¬ T.val < (rev T).val := hT; omega
    simp only [hT, ite_false]
    by_cases h5 : r.val < T.val ∨ (rev r).val < T.val
    · simp only [h5, ite_true, show (r.val < T.val + 1 ∨ (rev r).val < T.val + 1) by omega]
    · have hr6 : r.val < T.val + 1 ∨ (rev r).val < T.val + 1 → rows (rev r) = rows r := by
        intro _
        by_cases h2 : r.val = T.val
        · have hrT : r = T := Fin.ext h2
          subst hrT
          have : rev r = r := Fin.ext (by omega)
          rw [this]
        · have h3 : (rev r).val = T.val := by omega
          have : rev r = T := Fin.ext h3
          have hr : r = rev T := by rw [← this, hrev]
          have : (rev T).val = T.val := by
            have := h5; rw [hr] at this; push Not at this; omega
          have hrT : rev T = T := Fin.ext this
          rw [hr, hrT, hrT]
      by_cases h6 : r.val < T.val + 1 ∨ (rev r).val < T.val + 1
      · simp only [h5, h6, ite_true, ite_false, hr6 h6]
      · simp only [h5, h6, ite_false]

/-- After the swaps started from rows 0 to t - 1, some rows already hold their partner.

Those are the rows r whose pair {r, rev(r)} has its smaller element below t. -/
theorem prefix_spec (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i) (rows : Fin h → R)
    (t : ℕ) (ht : t ≤ h) :
    ((List.finRange h).take t).foldl (fun acc i => if i < rev i then swap acc i (rev i) else acc)
        rows =
      fun r => if r.val < t ∨ (rev r).val < t then rows (rev r) else rows r := by
  induction t with
  | zero => funext r; simp
  | succ t ih =>
    have ht' : t < h := by omega
    have hget : (List.finRange h)[t]? = some ⟨t, ht'⟩ := by
      rw [List.getElem?_eq_getElem (by simp; omega)]; simp
    rw [List.take_add_one, hget, Option.toList_some, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih (by omega)]
    funext r
    exact step_value rev hrev rows ⟨t, ht'⟩ r

/-- The swap loop puts row rev(r) at row r, for an involution rev. -/
theorem reverse_matrix_index_bits_eq (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i)
    (rows : Fin h → R) : reverse_matrix_index_bits rev rows = fun r => rows (rev r) := by
  unfold reverse_matrix_index_bits
  have := prefix_spec rev hrev rows h le_rfl
  rw [List.take_of_length_le (by simp)] at this
  rw [this]; funext r; simp [r.isLt]

/-- Two swaps started from different rows touch four different rows.

The parallel raw-pointer swaps rely on this. -/
theorem swaps_disjoint (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i) (i i' : Fin h)
    (hi : i < rev i) (hi' : i' < rev i') (hne : i ≠ i') :
    i ≠ rev i' ∧ rev i ≠ i' ∧ rev i ≠ rev i' := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => hne (by rw [← hrev i, e, hrev])⟩
  · have : rev i = i' := by rw [e, hrev]
    rw [this] at hi; rw [← e] at hi'; exact absurd hi (not_lt.mpr hi'.le)
  · rw [← e, hrev] at hi'; exact absurd hi (not_lt.mpr hi'.le)

end Plonky3Lean.Proofs.Matrix.BitRevSwap

namespace Plonky3Lean.Proofs.Matrix.Flat

open p3_matrix.extension.mirror

variable {F EF : Type _} [Inhabited F] (D : ℕ) (coords : EF → List F)

omit [Inhabited F] in
/-- Moving past a fully read element changes nothing in what remains to be read. -/
theorem normalize (hc : ∀ a, (coords a).length = D) (hD : 0 < D) (inner : List EF) (idx : ℕ)
    (hidx : idx ≤ D) :
    (if idx = D then 0 else idx) < D ∧
      (((if idx = D then inner.tail else inner).flatMap coords).drop (if idx = D then 0 else idx)) =
        (inner.flatMap coords).drop idx := by
  by_cases h : idx = D
  · subst h
    refine ⟨by simpa using hD, ?_⟩
    cases inner with
    | nil => simp
    | cons a rest =>
      simp only [ite_true, List.tail_cons, List.drop_zero, List.flatMap_cons]
      rw [List.drop_append_of_le_length (by rw [hc]), List.drop_eq_nil_of_le (by rw [hc]),
        List.nil_append]
  · simp only [h, ite_false]; exact ⟨by omega, trivial⟩

/-- The flat iterator reads the coordinates of its elements in order.

It starts at a given coordinate of the first element. -/
theorem flat_iter_take_eq (hc : ∀ a, (coords a).length = D) (hD : 0 < D) :
    ∀ (len : ℕ) (inner : List EF) (idx : ℕ), idx ≤ D →
      flat_iter_take D coords inner idx len = ((inner.flatMap coords).drop idx).take len := by
  intro len
  induction len with
  | zero => intro inner idx _; simp [flat_iter_take]
  | succ len ih =>
    intro inner idx hidx
    obtain ⟨hlt, heq⟩ := normalize D coords hc hD inner idx hidx
    rw [← heq]
    unfold flat_iter_take
    generalize (if idx = D then inner.tail else inner) = inner' at hlt ⊢
    generalize (if idx = D then 0 else idx) = idx' at hlt ⊢
    cases inner' with
    | nil => simp
    | cons a rest =>
      simp only
      rw [ih (a :: rest) (idx' + 1) (by omega), List.flatMap_cons,
        List.drop_append_of_le_length (by rw [hc]; omega),
        List.drop_append_of_le_length (by rw [hc]; omega)]
      have hlen : idx' < (coords a).length := by rw [hc]; exact hlt
      rw [List.drop_eq_getElem_cons hlen, List.cons_append, List.take_succ_cons,
        getElem!_pos (coords a) idx' hlen]

/-- A run of a flat row is the slice [start, end) of the row's coordinates laid end to end. -/
theorem flat_row_subseq_eq (hc : ∀ a, (coords a).length = D) (hD : 0 < D) (row : List EF)
    (start stop : ℕ) :
    flat_row_subseq D coords row start stop = ((row.flatMap coords).drop start).take (stop - start) := by
  unfold flat_row_subseq
  rw [flat_iter_take_eq D coords hc hD _ _ _ (Nat.mod_lt _ hD).le]
  congr 1
  have hdrop : ∀ (q : ℕ) (l : List EF), (l.drop q).flatMap coords = (l.flatMap coords).drop (q * D) := by
    intro q
    induction q with
    | zero => intro l; simp
    | succ q ih =>
      intro l
      cases l with
      | nil => simp
      | cons a rest =>
        have h1 : ((a :: rest).flatMap coords).drop ((q + 1) * D) =
            ((rest.flatMap coords)).drop (q * D) := by
          rw [List.flatMap_cons, Nat.succ_mul, show q * D + D = D + q * D by ring,
            ← List.drop_drop, List.drop_left' (hc a)]
        rw [List.drop_succ_cons, ih, h1]
  rw [hdrop, List.drop_drop, Nat.div_add_mod' start D]

omit [Inhabited F] in
/-- Column c of the flat view reads coordinate c mod D of element c / D.

The bound c < w D is exactly what keeps both in range. -/
theorem flat_index_contract {w c : ℕ} (hD : 0 < D) :
    c < w * D ↔ c / D < w ∧ c % D < D :=
  ⟨fun h => ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h), Nat.mod_lt _ hD⟩,
    fun ⟨h, _⟩ => by have := (Nat.div_lt_iff_lt_mul hD).mp h; exact this⟩

end Plonky3Lean.Proofs.Matrix.Flat
