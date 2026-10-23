module

public import Plonky3Lean.Proofs.Air.Builder
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

/-!
# Constraint degrees and quotient chunks

The polynomial degree walk bounds the degree of a constraint polynomial.

The cached degree multiple d bounds it by d (n - 1) plus the number of transition selectors along a product.

The quotient takes c = 2^(ceil(log_2(max(D, 2) - 1))) chunks of n coefficients for the largest degree D.

That holds a constraint polynomial of degree at most d (n - 1) + 1 for d <= D.

The cached degree multiple does not count transition selectors, so it misses a product of two.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air
open SymbolicExpr

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Degree bounds for one expression -/

/-- The constraint polynomial of an expression, for an assignment of univariate polynomials. -/
theorem constraintPoly_toPoly (σ : Var → Polynomial F) (e : SymbolicExpression F) :
    constraintPoly σ (toPoly e) = denote (fun a => MvPolynomial.aeval σ (leafPoly a)) e :=
  map_denote (MvPolynomial.aeval σ) leafPoly e

variable {σ : Var → Polynomial F} {n : ℕ} {periods : List ℕ}

/-- The polynomial degree walk bounds the degree of the constraint polynomial. -/
theorem natDegree_le_poly_degree (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) (e : SymbolicExpression F) :
    (constraintPoly σ (toPoly e)).natDegree ≤ e.poly_degree n periods := by
  rw [constraintPoly_toPoly]
  exact natDegree_denote_le (natDegree_leaf_le hσ hp) e

/-- A periodic column of period p dividing n is f(X^(n/p)) with deg f < p, of degree at most n - n/p. -/
theorem natDegree_periodic_comp_le {K : Type _} [Field K] {f : Polynomial K} {n p : ℕ}
    (hp : p ∣ n) (hf : f.natDegree < p) :
    (f.comp (Polynomial.X ^ (n / p))).natDegree ≤ n - n / p := by
  obtain ⟨k, rfl⟩ := hp
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp at hf
  refine Polynomial.natDegree_comp_le.trans ?_
  rw [Polynomial.natDegree_X_pow, Nat.mul_div_cancel_left _ hp0]
  have : f.natDegree * k ≤ (p - 1) * k := Nat.mul_le_mul_right _ (by omega)
  have : (p - 1) * k = p * k - k := by rw [Nat.sub_mul, one_mul]
  omega

/-- The number of transition selectors along a product: the walk with weight 1 on that selector only. -/
def transitionCount (e : SymbolicExpression F) : ℕ :=
  e.degree_with fun
    | .IsTransition => 1
    | _ => 0

theorem degree_with_mono {A : Type _} {f g : A → ℕ} (h : ∀ a, f a ≤ g a) (e : SymbolicExpr A) :
    e.degree_with f ≤ e.degree_with g := by
  induction e with
  | Leaf a => exact h a
  | Add _ _ _ hx hy | Sub _ _ _ hx hy => exact max_le_max hx hy
  | Neg _ _ hx => exact hx
  | Mul _ _ _ hx hy => exact add_le_add hx hy

/-- A leaf's polynomial degree is at most its degree multiple times n - 1, plus 1 for the transition selector. -/
theorem leaf_poly_degree_le (a : BaseLeaf F) :
    SymLeaf.poly_degree a n periods ≤ SymLeaf.degree_multiple a * (n - 1) +
      (match a with | .IsTransition => 1 | _ => 0) := by
  rcases a with ⟨e, j⟩ | _ | _ | _ | c <;>
    simp [SymLeaf.poly_degree, SymLeaf.degree_multiple]
  rcases e with o | o | _ | _ <;>
    simp [SymbolicVariable.poly_degree, SymbolicVariable.degree_multiple]
  generalize hq : min (periods[j]?.getD n) n = q
  rcases q with _ | q
  · exact le_rfl
  · show n - n / (q + 1) ≤ n - 1
    have : 1 ≤ n / (q + 1) := Nat.div_pos (hq ▸ min_le_right _ _) (Nat.succ_pos q)
    omega

/-- The cached degree multiple bounds the polynomial degree, plus one per transition selector along a product. -/
theorem poly_degree_le_degree_multiple {e : SymbolicExpression F} (he : WF e) :
    e.poly_degree n periods ≤ e.degree_multiple * (n - 1) + transitionCount e := by
  rw [he.degree_multiple_eq]
  exact (degree_with_mono leaf_poly_degree_le e).trans (degree_with_le_mul_add _ _ _ e)

/-! ## The constraint degree of a polynomial degree -/

theorem constraint_degree_from_poly_degree_eq {pd n : ℕ} (hn : 2 ≤ n) (h0 : pd ≠ 0) :
    constraint_degree_from_poly_degree pd n = (pd - 1 + (n - 1) - 1) / (n - 1) := by
  simp [constraint_degree_from_poly_degree, h0, show n > 1 by omega]

/-- For n >= 2, the conversion gives a d with poly_degree <= d (n - 1) + 1. -/
theorem le_constraint_degree_from_poly_degree (pd : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    pd ≤ constraint_degree_from_poly_degree pd n * (n - 1) + 1 := by
  rcases Nat.eq_zero_or_pos pd with rfl | h0
  · omega
  rw [constraint_degree_from_poly_degree_eq hn h0.ne']
  have := Nat.lt_div_mul_add (a := pd - 1 + (n - 1) - 1) (show 0 < n - 1 by omega)
  omega

/-- For n >= 2, no smaller d works. -/
theorem constraint_degree_from_poly_degree_le {pd d n : ℕ} (hn : 2 ≤ n)
    (h : pd ≤ d * (n - 1) + 1) : constraint_degree_from_poly_degree pd n ≤ d := by
  rcases Nat.eq_zero_or_pos pd with rfl | h0
  · simp [constraint_degree_from_poly_degree]
  rw [constraint_degree_from_poly_degree_eq hn h0.ne',
    Nat.div_le_iff_le_mul_add_pred (by omega), mul_comm]
  omega

/-! ## Quotient chunks -/

/-- m <= 2^(ceil(log_2 m)). -/
theorem le_two_pow_log2_ceil (m : ℕ) : m ≤ 2 ^ log2_ceil_usize m := by
  have := Nat.lt_size_self (m - 1)
  unfold log2_ceil_usize
  omega

/-- 2^(ceil(log_2 m)) is the least power of two at least m. -/
theorem log2_ceil_le {m k : ℕ} (h : m ≤ 2 ^ k) : log2_ceil_usize m ≤ k :=
  Nat.size_le.mpr (by have := Nat.two_pow_pos k; omega)

/-- The chunk count 2^(ceil(log_2(max(d + z, 2) - 1)) + z) is 2^z times the least power of two at least max(d + z, 2) - 1. -/
theorem num_quotient_chunks_eq (d z : ℕ) :
    2 ^ (log2_ceil_usize (max (d + z) 2 - 1) + z) =
      2 ^ z * 2 ^ log2_ceil_usize (max (d + z) 2 - 1) ∧
    max (d + z) 2 - 1 ≤ 2 ^ log2_ceil_usize (max (d + z) 2 - 1) ∧
    ∀ k, max (d + z) 2 - 1 ≤ 2 ^ k → log2_ceil_usize (max (d + z) 2 - 1) ≤ k :=
  ⟨by rw [pow_add, mul_comm], le_two_pow_log2_ceil _, fun _ => log2_ceil_le⟩

/-- A polynomial of degree at most d (n - 1) + 1 fits c chunks of n coefficients when d <= D and c >= max(D, 2) - 1. -/
theorem fitsChunks_of_le {C : Polynomial F} {n d D c : ℕ} (hn : 1 ≤ n)
    (hC : C.natDegree ≤ d * (n - 1) + 1) (hd : d ≤ D) (hc : max D 2 - 1 ≤ c) :
    FitsChunks n c C := by
  unfold FitsChunks
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hC
  have hdk : d * k ≤ D * k := Nat.mul_le_mul_right _ hd
  rcases le_or_gt 2 D with hD | hD
  · have : D * (k + 1) ≤ (c + 1) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have : D * (k + 1) = D * k + D := by ring
    omega
  · have : 2 * (k + 1) ≤ (c + 1) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have : D * k ≤ 1 * k := Nat.mul_le_mul_right _ (by omega)
    omega

/-- The degree the debug-free quotient sizing reads: the largest constraint degree, raised to the AIR's hint. -/
theorem get_log_quotient_degree_ok {air : Air F} {layout : AirLayout} {n L : ℕ}
    (h : get_log_quotient_degree air layout n 0 = .ok L) :
    ∃ D, get_max_constraint_degree air layout n = .ok D ∧
      L = log2_ceil_usize (max (max D (air.max_constraint_degree.getD 0)) 2 - 1) := by
  unfold get_log_quotient_degree at h
  rcases hD : get_max_constraint_degree air layout n with e | D <;>
    simp [hD, bind, Except.bind, pure, Except.pure] at h
  exact ⟨D, rfl, by simpa [max_assoc] using h.symm⟩

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

variable [Inhabited F]

/-- With periodic columns, every constraint polynomial fits the quotient chunks, for n >= 2.

The periods must divide n, as the checker and the prover require. -/
theorem quotient_fits_periodic {air : Air F} {L : ℕ} (hn : 2 ≤ n)
    (hper : (AirLayout.from_air air).num_periodic_columns ≠ 0)
    (h : get_log_quotient_degree air (AirLayout.from_air air) n 0 = .ok L)
    (hσ : DegreeBounds σ n (air.periodic_columns.map List.length))
    (hp : ∀ j p : ℕ, (air.periodic_columns.map List.length)[j]? = some p → 0 < p → p < n →
      p ∣ n) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      FitsChunks n (2 ^ L) (constraintPoly σ (toPoly e)) := by
  obtain ⟨D, hD, rfl⟩ := get_log_quotient_degree_ok h
  intro e he
  simp only [get_max_constraint_degree, get_symbolic_constraints_from_air, hper, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hD
  subst hD
  set pds := (air.eval (symbolicBuilder (AirLayout.from_air air)) []).map
    (SymbolicExpr.poly_degree · n (air.periodic_columns.map List.length))
  have hmax : e.poly_degree n (air.periodic_columns.map List.length) ≤ pds.foldr max 0 :=
    le_foldr_max (List.mem_map_of_mem he)
  refine fitsChunks_of_le (by omega) ?_ (le_max_left _ _) (le_two_pow_log2_ceil _)
  exact (natDegree_le_poly_degree hσ hp e).trans
    (hmax.trans (le_constraint_degree_from_poly_degree _ hn))

/-- Without periodic columns, every constraint polynomial with at most one transition selector along a product fits the quotient chunks. -/
theorem quotient_fits_fast {air : Air F} {L : ℕ} (hn : 1 ≤ n)
    (hper : (AirLayout.from_air air).num_periodic_columns = 0)
    (h : get_log_quotient_degree air (AirLayout.from_air air) n 0 = .ok L)
    (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n)
    (ht : ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [], transitionCount e ≤ 1) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      FitsChunks n (2 ^ L) (constraintPoly σ (toPoly e)) := by
  obtain ⟨D, hD, rfl⟩ := get_log_quotient_degree_ok h
  intro e he
  simp only [get_max_constraint_degree, get_symbolic_constraints_from_air, hper, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hD
  subst hD
  refine fitsChunks_of_le hn ?_ ((le_foldr_max (List.mem_map_of_mem he)).trans (le_max_left _ _))
    (le_two_pow_log2_ceil _)
  exact (natDegree_le_poly_degree hσ hp e).trans
    ((poly_degree_le_degree_multiple (symbolic_wf air _ e he)).trans (by have := ht e he; omega))

end Plonky3Lean.Proofs.Air
