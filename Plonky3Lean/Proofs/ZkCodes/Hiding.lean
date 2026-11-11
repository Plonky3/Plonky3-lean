module

public import Plonky3Lean.Spec.ZkCodes
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Hiding of the Reed-Solomon zero-knowledge encoding

At d <= t distinct nonzero points, the masks reach every value.

So a uniform randomness gives a uniform view.

At t + 1 such points, two messages have disjoint views when l >= 1.

A zero point leaks the constant coefficient of the message.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.ZkCodes

open Polynomial Plonky3Lean.Spec.ZkCodes
open Finset (univ mem_univ sum_congr mem_filter card_univ sum_const mul_sum sum_add_distrib)

variable {K : Type _} [Field K] {m : ℕ}

/-- The mask part at the points x: rho maps to (sum_j rho_j x_i^(l+j))_i. -/
def maskMap {ι : Type _} (l t : ℕ) (x : ι → K) : (Fin t → K) →ₗ[K] (ι → K) where
  toFun ρ i := ∑ j, ρ j * x i ^ (l + (j : ℕ))
  map_add' a b := by funext i; simp [add_mul, sum_add_distrib]
  map_smul' c a := by funext i; simp [mul_sum, mul_assoc]

/-- The message part at a point: sum_j f_j x^j. -/
def msgEval {l : ℕ} (f : Fin l → K) (x : K) : K := ∑ j, f j * x ^ (j : ℕ)

theorem rsZkPoly_eval {l t : ℕ} (f : Fin l → K) (ρ : Fin t → K) (x : K) :
    (rsZkPoly f ρ).eval x = msgEval f x + ∑ j, ρ j * x ^ (l + (j : ℕ)) := by
  simp [rsZkPoly, msgEval, eval_finsetSum]

/-- The view at S is the message part plus the mask map at the points of S. -/
theorem restrict_rsZkEnc {l t : ℕ} (L : Fin m → K) (f : Fin l → K) (ρ : Fin t → K)
    (S : Finset (Fin m)) :
    restrict (rsZkEnc L f ρ) S = (fun i : S => msgEval f (L i)) + maskMap l t (fun i : S => L i) ρ := by
  funext i
  simp [Plonky3Lean.Spec.ZkCodes.restrict, rsZkEnc, rsZkPoly_eval, maskMap]

/-- At d <= t distinct nonzero points the mask map is onto.

Interpolate y_i / x_i^l and read its coefficients. -/
theorem maskMap_surjective {ι : Type _} [Fintype ι] [DecidableEq ι] (l t : ℕ) {x : ι → K}
    (hx : Function.Injective x) (h0 : ∀ i, x i ≠ 0) (hcard : Fintype.card ι ≤ t) :
    Function.Surjective (maskMap l t x) := by
  intro y
  set q := Lagrange.interpolate univ x (fun i => y i / x i ^ l) with hq
  have hdeg : q.degree < (Fintype.card ι : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := univ) (v := x) (fun i => y i / x i ^ l)
      (hx.injOn)
    rwa [card_univ] at this
  refine ⟨fun j => q.coeff j, ?_⟩
  funext i
  have ht : 0 < t := lt_of_lt_of_le (Fintype.card_pos_iff.mpr ⟨i⟩) hcard
  have hnat : q.natDegree < t := by
    rcases eq_or_ne q 0 with h | h
    · rw [h, natDegree_zero]; exact ht
    · have := (natDegree_lt_iff_degree_lt h).mpr hdeg
      omega
  simp only [maskMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hsum : ∑ j : Fin t, q.coeff (j : ℕ) * x i ^ (l + (j : ℕ)) = x i ^ l * q.eval (x i) := by
    rw [eval_eq_sum_range' hnat, mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, hq, Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i)]
  field_simp [pow_ne_zero l (h0 i)]

/-- Every fiber of b + A, for a surjective additive map A, has |V| / |W| elements. -/
theorem card_fiber_mul {V W : Type _} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W]
    [DecidableEq W] (A : V →+ W) (hA : Function.Surjective A) (b y : W) :
    (univ.filter fun v => b + A v = y).card * Fintype.card W = Fintype.card V := by
  classical
  have hfib : ∀ z : W, (univ.filter fun v => A v = z).card = (univ.filter fun v => A v = 0).card := by
    intro z
    obtain ⟨v0, hv0⟩ := hA z
    refine Finset.card_bij' (fun v _ => v - v0) (fun u _ => u + v0) ?_ ?_ ?_ ?_
    · intro v hv; simp only [mem_filter, mem_univ, true_and] at hv ⊢; simp [map_sub, hv, hv0]
    · intro u hu; simp only [mem_filter, mem_univ, true_and] at hu ⊢; simp [map_add, hu, hv0]
    · intro v _; simp
    · intro u _; simp
  have htot : Fintype.card V = ∑ z : W, (univ.filter fun v => A v = z).card :=
    Finset.card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := A) (fun _ _ => mem_univ _)
  have hy : (univ.filter fun v => b + A v = y) = (univ.filter fun v => A v = y - b) := by
    ext v; simp [eq_sub_iff_add_eq, add_comm]
  rw [hy, hfib, htot]
  simp_rw [hfib, sum_const, card_univ, smul_eq_mul, mul_comm]

/-- A push-forward of the uniform distribution whose fibers all have |alpha| / |beta| elements is uniform. -/
theorem pushUniform_eq_uniform {α β : Type _} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α]
    (g : α → β) (h : ∀ y, (univ.filter fun a => g a = y).card * Fintype.card β = Fintype.card α) :
    pushUniform g = uniform β := by
  funext y
  have hα : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    have : 0 < Fintype.card β := by
      rcases Nat.eq_zero_or_pos (Fintype.card β) with h0 | h0
      · have := h y; rw [h0, mul_zero] at this; exact absurd this.symm Fintype.card_ne_zero
      · exact h0
    exact_mod_cast this.ne'
  simp only [pushUniform, uniform]
  rw [div_eq_div_iff hα hβ, one_mul]
  exact_mod_cast h y

variable [Fintype K] [DecidableEq K] {S : Finset (Fin m)}

/-- The view at S, for at most t distinct nonzero points.

Each value is reached by |K|^(t - |S|) randomness vectors. -/
theorem card_view_fiber {l t : ℕ} (L : Fin m → K) (hL : Set.InjOn L S) (h0 : ∀ i ∈ S, L i ≠ 0)
    (hS : S.card ≤ t) (f : Fin l → K) (y : S → K) :
    (univ.filter fun ρ : Fin t → K => restrict (rsZkEnc L f ρ) S = y).card * Fintype.card (S → K) =
      Fintype.card (Fin t → K) := by
  have hx : Function.Injective (fun i : S => L i) := fun a b h =>
    Subtype.ext (hL a.2 b.2 h)
  have hsurj := maskMap_surjective l t hx (fun i => h0 i i.2) (by simpa using hS)
  simp_rw [restrict_rsZkEnc]
  exact card_fiber_mul (maskMap l t (fun i : S => L i)).toAddMonoidHom hsurj _ y

/-- The view at S is uniform, for every message. -/
theorem realView_rsZkEnc {l t : ℕ} (L : Fin m → K) (hL : Set.InjOn L S) (h0 : ∀ i ∈ S, L i ≠ 0)
    (hS : S.card ≤ t) (f : Fin l → K) :
    realView (rsZkEnc (t := t) L) f S = uniform (S → K) :=
  pushUniform_eq_uniform _ (card_view_fiber L hL h0 hS f)

/-- With t randomness entries the view at exactly t points is a bijection of the randomness. -/
theorem view_bijective {l t : ℕ} (L : Fin m → K) (hL : Set.InjOn L S) (h0 : ∀ i ∈ S, L i ≠ 0)
    (hS : S.card = t) (f : Fin l → K) :
    Function.Bijective fun ρ : Fin t → K => restrict (rsZkEnc L f ρ) S := by
  have hx : Function.Injective (fun i : S => L i) := fun a b h =>
    Subtype.ext (hL a.2 b.2 h)
  have hsurj := maskMap_surjective l t hx (fun i => h0 i i.2) (by simp [hS])
  have hs : Function.Surjective fun ρ : Fin t → K => restrict (rsZkEnc L f ρ) S := by
    intro y
    obtain ⟨ρ, hρ⟩ := hsurj (y - fun i : S => msgEval f (L i))
    exact ⟨ρ, by simp only; rw [restrict_rsZkEnc, hρ]; abel⟩
  rw [Fintype.bijective_iff_surjective_and_card]
  exact ⟨hs, by simp [hS]⟩

/-- Proposition 3.19.

On distinct nonzero points, the encoding is t-query zero knowledge with error zero. -/
theorem rsZkEnc_isZk {l t : ℕ} (L : Fin m → K) (hL : Function.Injective L) (h0 : ∀ i, L i ≠ 0) :
    IsZkEncoding (rsZkEnc (l := l) (t := t) L) t 0 uniformSim := by
  intro f S hS
  rw [realView_rsZkEnc L hL.injOn (fun i _ => h0 i) hS f]
  simp [statDist, uniformSim]

/-- Every codeword is a Reed-Solomon codeword of degree below l + t. -/
theorem rsZkEnc_mem {l t : ℕ} (L : Fin m → K) (f : Fin l → K) (ρ : Fin t → K) :
    rsZkEnc L f ρ ∈ rsCode L (l + t) := by
  refine ⟨rsZkPoly f ρ, ?_, fun i => rfl⟩
  have hmem : rsZkPoly f ρ ∈ degreeLT K (l + t) := by
    unfold rsZkPoly
    refine add_mem (sum_mem fun j _ => ?_) (sum_mem fun j _ => ?_) <;> rw [mem_degreeLT] <;>
      refine (degree_C_mul_X_pow_le _ _).trans_lt ?_ <;> exact_mod_cast (by omega)
  exact mem_degreeLT.mp hmem

/-- The generating matrix of Definition 3.17.

Its rows are powers: the message block, then the randomness block. -/
theorem rsZkEnc_generating {l t : ℕ} (L : Fin m → K) :
    IsGeneratingMatrix (rsZkEnc (l := l) (t := t) L) (rsMsgMatrix L) (rsRandMatrix (l := l) L) := by
  intro f ρ
  funext i
  simp [rsZkEnc, rsZkPoly_eval, msgEval, rsMsgMatrix, rsRandMatrix, Matrix.mulVec, dotProduct,
    mul_comm]


/-! ## The bound is tight, and zero must stay out of the domain -/

omit [Fintype K] [DecidableEq K] in
/-- Two distributions with disjoint supports.

No function is within distance below 1/2 of both. -/
theorem one_le_statDist_add {β : Type _} [Fintype β] {p q : β → ℚ} (hp : ∑ b, p b = 1)
    (hq : ∑ b, q b = 1) (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hdis : ∀ b, p b = 0 ∨ q b = 0) (s : β → ℚ) : 1 ≤ statDist p s + statDist q s := by
  have key : ∀ b, p b + q b ≤ |p b - s b| + |q b - s b| := by
    intro b
    have h1 : p b + q b = |p b - q b| := by
      rcases hdis b with h | h
      · rw [h, zero_add, zero_sub, abs_neg, abs_of_nonneg (hq0 b)]
      · rw [h, add_zero, sub_zero, abs_of_nonneg (hp0 b)]
    rw [h1]
    calc |p b - q b| = |(p b - s b) - (q b - s b)| := by ring_nf
      _ ≤ |p b - s b| + |q b - s b| := abs_sub _ _
  have := Finset.sum_le_sum fun b (_ : b ∈ univ) => key b
  rw [sum_add_distrib, sum_add_distrib, hp, hq] at this
  simp only [statDist]
  linarith

omit [Fintype K] [DecidableEq K] in
theorem sum_pushUniform {α β : Type _} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α]
    (g : α → β) : ∑ y, pushUniform g y = 1 := by
  have hα : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [pushUniform, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hα]
  exact_mod_cast (Finset.card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := g)
    (fun _ _ => mem_univ _)).symm

omit [Fintype K] [DecidableEq K] in
theorem pushUniform_nonneg {α β : Type _} [Fintype α] [DecidableEq β] (g : α → β) (y : β) :
    0 ≤ pushUniform g y := by
  unfold pushUniform; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype K] [DecidableEq K] in
theorem pushUniform_eq_zero {α β : Type _} [Fintype α] [DecidableEq β] {g : α → β} {y : β}
    (h : ∀ a, g a ≠ y) : pushUniform g y = 0 := by
  have : (univ.filter fun a => g a = y) = ∅ := by
    ext a; simp [h a]
  simp [pushUniform, this]

/-- Take two messages whose views at some S of at most t' positions never meet.

They rule out t'-query zero knowledge with error below 1/2. -/
theorem not_isZk_of_disjoint {l r : ℕ} (enc : (Fin l → K) → (Fin r → K) → Fin m → K) {t' : ℕ}
    {ζ : ℚ} (hζ : ζ < 1 / 2) (sim : (S : Finset (Fin m)) → (S → K) → ℚ) (f f' : Fin l → K)
    (S : Finset (Fin m)) (hS : S.card ≤ t')
    (hdis : ∀ ρ ρ', restrict (enc f ρ) S ≠ restrict (enc f' ρ') S) :
    ¬ IsZkEncoding enc t' ζ sim := by
  intro hzk
  have h1 := hzk f S hS
  have h2 := hzk f' S hS
  have := one_le_statDist_add (sum_pushUniform _) (sum_pushUniform _) (pushUniform_nonneg _)
    (pushUniform_nonneg _) (p := realView enc f S) (q := realView enc f' S) (fun y => by
      by_cases hy : ∃ ρ, restrict (enc f ρ) S = y
      · obtain ⟨ρ, rfl⟩ := hy
        exact Or.inr (pushUniform_eq_zero fun ρ' h => hdis ρ ρ' h.symm)
      · simp only [not_exists] at hy
        exact Or.inl (pushUniform_eq_zero hy)) (sim S)
  linarith

/-- At t + 1 distinct nonzero points, the messages 0 and X^(l-1) have disjoint views when l >= 1. -/
theorem views_disjoint {l t : ℕ} (hl : 1 ≤ l) (L : Fin m → K) (hL : Set.InjOn L S)
    (h0 : ∀ i ∈ S, L i ≠ 0) (hS : S.card = t + 1) (ρ ρ' : Fin t → K) :
    restrict (rsZkEnc L (0 : Fin l → K) ρ) S ≠
      restrict (rsZkEnc L (Pi.single (⟨l - 1, by omega⟩ : Fin l) (1 : K)) ρ') S := by
  intro heq
  set Q : K[X] := 1 + ∑ j : Fin t, C (ρ' j - ρ j) * X ^ ((j : ℕ) + 1) with hQ
  have hQdeg : Q.degree < S.card := by
    have : Q ∈ degreeLT K (t + 1) := by
      refine add_mem ?_ (sum_mem fun j _ => ?_) <;> rw [mem_degreeLT]
      · exact (degree_one_le).trans_lt (by exact_mod_cast (by omega : 0 < t + 1))
      · exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (by omega))
    rw [hS]; exact mem_degreeLT.mp this
  have hQeval : ∀ i ∈ S, Q.eval (L i) = 0 := by
    intro i hi
    have hi' := congrFun heq ⟨i, hi⟩
    simp only [Plonky3Lean.Spec.ZkCodes.restrict, rsZkEnc, rsZkPoly_eval, msgEval] at hi'
    have hmsg : ∑ j : Fin l, (Pi.single (⟨l - 1, by omega⟩ : Fin l) (1 : K) : Fin l → K) j *
        L i ^ (j : ℕ) = L i ^ (l - 1) := by
      rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hmsg] at hi'
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at hi'
    have hx := pow_ne_zero (l - 1) (h0 i hi)
    have : L i ^ (l - 1) * Q.eval (L i) = 0 := by
      have hsplit : ∀ j : ℕ, L i ^ (l + j) = L i ^ (l - 1) * L i ^ (j + 1) := by
        intro j; rw [← pow_add]; congr 1; omega
      simp only [hQ, eval_add, eval_one, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      simp only [hsplit] at hi'
      rw [mul_add, mul_one, mul_sum]
      have : ∑ j : Fin t, L i ^ (l - 1) * ((ρ' j - ρ j) * L i ^ ((j : ℕ) + 1)) =
          ∑ j : Fin t, ρ' j * (L i ^ (l - 1) * L i ^ ((j : ℕ) + 1)) -
            ∑ j : Fin t, ρ j * (L i ^ (l - 1) * L i ^ ((j : ℕ) + 1)) := by
        rw [← Finset.sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
      rw [this]
      linear_combination -hi'
    exact (mul_eq_zero.mp this).resolve_left hx
  have hQ0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero S hL hQdeg hQeval
  have hc : Q.coeff 0 = 1 := by
    simp [hQ]
  rw [hQ0, coeff_zero] at hc
  exact zero_ne_one hc

/-- The query bound is tight.

Take l >= 1 and m >= t + 1 distinct nonzero points.

The encoding is not (t + 1)-query zero knowledge, with any simulator and any error below 1/2. -/
theorem not_isZk_succ {l t : ℕ} (hl : 1 ≤ l) (L : Fin m → K) (hL : Function.Injective L)
    (h0 : ∀ i, L i ≠ 0) (hm : t + 1 ≤ m) {ζ : ℚ} (hζ : ζ < 1 / 2)
    (sim : (S : Finset (Fin m)) → (S → K) → ℚ) :
    ¬ IsZkEncoding (rsZkEnc (l := l) (t := t) L) (t + 1) ζ sim := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin m)))
    (n := t + 1) (by simpa using hm)
  exact not_isZk_of_disjoint _ hζ sim _ _ S hS.le
    (views_disjoint hl L hL.injOn (fun i _ => h0 i) hS)

/-- At a zero point the codeword is the constant coefficient of the message, for l >= 1. -/
theorem rsZkEnc_zero_point {l t : ℕ} (hl : 1 ≤ l) (L : Fin m → K) {i : Fin m} (hi : L i = 0)
    (f : Fin l → K) (ρ : Fin t → K) : rsZkEnc L f ρ i = f ⟨0, by omega⟩ := by
  simp only [rsZkEnc, rsZkPoly_eval, msgEval, hi]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin l)]
  · rw [Finset.sum_eq_zero fun j _ => by rw [zero_pow (by omega), mul_zero]]
    simp
  · intro b _ hb
    rw [zero_pow (fun h => hb (Fin.ext h)), mul_zero]
  · simp

/-- A zero point leaks the constant coefficient.

With l >= 1 and t >= 1, the encoding is then not t-query zero knowledge. -/
theorem not_isZk_of_zero {l t : ℕ} (hl : 1 ≤ l) (ht : 1 ≤ t) (L : Fin m → K) {i : Fin m}
    (hi : L i = 0) {ζ : ℚ} (hζ : ζ < 1 / 2) (sim : (S : Finset (Fin m)) → (S → K) → ℚ) :
    ¬ IsZkEncoding (rsZkEnc (l := l) (t := t) L) t ζ sim := by
  refine not_isZk_of_disjoint _ hζ sim 0 (Pi.single ⟨0, by omega⟩ 1) {i} (by simpa using ht) ?_
  intro ρ ρ' h
  have := congrFun h ⟨i, Finset.mem_singleton_self i⟩
  simp only [Plonky3Lean.Spec.ZkCodes.restrict, rsZkEnc_zero_point hl L hi] at this
  simp at this

end Plonky3Lean.Proofs.ZkCodes
