module

public import P3Air
public import Plonky3Lean.Spec.Air

@[expose] public section

/-!
# Symbolic expressions: meaning and degree

An expression denotes an element of a commutative ring once each leaf does.

The simplifying operators denote the ring operations, whatever simplification fires.

A well-formed expression caches the degree multiple its children determine.

The degree walk bounds the degree of the polynomial an expression denotes.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror Plonky3Lean.Spec.Air

namespace SymbolicExpr

variable {A F : Type _} [SymLeaf A F] [Field F] [DecidableEq F]

/-! ## Denotation -/

section denote

variable {R : Type _} [CommRing R] [Algebra F R]

/-- The value of an expression, given the value of each leaf. -/
def denote (den : A → R) : SymbolicExpr A → R
  | .Leaf a => den a
  | .Add x y _ => denote den x + denote den y
  | .Sub x y _ => denote den x - denote den y
  | .Neg x _ => -denote den x
  | .Mul x y _ => denote den x * denote den y

/-- A ring map commutes with denotation. -/
theorem map_denote {S G : Type _} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (den : A → R) (e : SymbolicExpr A) : f (denote den e) = denote (fun a => f (den a)) e := by
  induction e <;> simp_all [denote]

/-- A leaf valuation that sends each constant leaf to its constant.

This covers a leaf holding a constant and the leaf built from one. -/
structure LeafDen (den : A → R) : Prop where
  as_const : ∀ a c, SymLeaf.as_const a = some c → den a = algebraMap F R c
  from_const : ∀ c, den (SymLeaf.from_const c) = algebraMap F R c

variable {den : A → R}

theorem denote_of_as_const (h : LeafDen den) {x : SymbolicExpr A} {c : F}
    (hx : x.as_const = some c) : denote den x = algebraMap F R c := by
  cases x with
  | Leaf a => exact h.as_const a c hx
  | _ => simp [p3_air.symbolic.mirror.SymbolicExpr.as_const] at hx

theorem denote_of_any (h : LeafDen den) {x : SymbolicExpr A} {c : F}
    (hx : x.as_const.any (· = c)) : denote den x = algebraMap F R c := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, x.as_const = some d ∧ d = c := by
    cases hc : x.as_const <;> simp_all
  exact denote_of_as_const h hd

@[simp] theorem denote_const (h : LeafDen den) (c : F) :
    denote den (p3_air.symbolic.mirror.SymbolicExpr.const c : SymbolicExpr A) = algebraMap F R c :=
  h.from_const c

theorem denote_sym_neg (h : LeafDen den) (x : SymbolicExpr A) :
    denote den x.sym_neg = -denote den x := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_neg
  split <;> simp_all [denote, h.from_const, denote_of_as_const h]

theorem denote_sym_add (h : LeafDen den) (x y : SymbolicExpr A) :
    denote den (x.sym_add y) = denote den x + denote den y := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_add
  split
  · simp_all [denote, h.from_const, denote_of_as_const h]
  · split_ifs with h0 h1
    · simp [denote_of_any h h0]
    · simp [denote_of_any h h1]
    · rfl

theorem denote_sym_sub (h : LeafDen den) (x y : SymbolicExpr A) :
    denote den (x.sym_sub y) = denote den x - denote den y := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_sub
  split
  · simp_all [denote, h.from_const, denote_of_as_const h]
  · split_ifs with h0 h1
    · simp [denote_sym_neg h, denote_of_any h h0]
    · simp [denote_of_any h h1]
    · rfl

theorem denote_sym_mul (h : LeafDen den) (x y : SymbolicExpr A) :
    denote den (x.sym_mul y) = denote den x * denote den y := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_mul
  split
  · simp_all [denote, h.from_const, denote_of_as_const h]
  · split_ifs with h0 h1 h2
    · rcases Bool.or_eq_true_iff.mp h0 with h0 | h0 <;> simp [denote, h.from_const, denote_of_any h h0]
    · simp [denote_of_any h h1]
    · simp [denote_of_any h h2]
    · rfl

end denote

/-! ## Well-formed expressions -/

/-- Every node caches the degree multiple of its children: the max for a sum, the sum for a product. -/
def WF : SymbolicExpr A → Prop
  | .Leaf _ => True
  | .Add x y d | .Sub x y d => WF x ∧ WF y ∧ d = max x.degree_multiple y.degree_multiple
  | .Neg x d => WF x ∧ d = x.degree_multiple
  | .Mul x y d => WF x ∧ WF y ∧ d = x.degree_multiple + y.degree_multiple

theorem WF.degree_multiple_eq {e : SymbolicExpr A} (h : WF e) :
    e.degree_multiple = e.degree_with SymLeaf.degree_multiple := by
  induction e with
  | Leaf => rfl
  | Add x y d hx hy | Sub x y d hx hy =>
    obtain ⟨h1, h2, rfl⟩ := h
    exact congrArg₂ max (hx h1) (hy h2)
  | Mul x y d hx hy =>
    obtain ⟨h1, h2, rfl⟩ := h
    exact congrArg₂ (· + ·) (hx h1) (hy h2)
  | Neg x d hx =>
    obtain ⟨h1, rfl⟩ := h
    exact hx h1

theorem wf_leaf (a : A) : WF (.Leaf a : SymbolicExpr A) := trivial

theorem wf_const (c : F) : WF (p3_air.symbolic.mirror.SymbolicExpr.const c : SymbolicExpr A) :=
  trivial

theorem wf_sym_neg {x : SymbolicExpr A} (hx : WF x) : WF x.sym_neg := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_neg; split <;> simp_all [WF]

theorem wf_sym_add {x y : SymbolicExpr A} (hx : WF x) (hy : WF y) : WF (x.sym_add y) := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_add
  split
  · trivial
  · split_ifs <;> simp_all [WF]

theorem wf_sym_sub {x y : SymbolicExpr A} (hx : WF x) (hy : WF y) : WF (x.sym_sub y) := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_sub
  split
  · trivial
  · split_ifs
    · exact wf_sym_neg hy
    · exact hx
    · exact ⟨hx, hy, rfl⟩

theorem wf_sym_mul {x y : SymbolicExpr A} (hx : WF x) (hy : WF y) : WF (x.sym_mul y) := by
  unfold p3_air.symbolic.mirror.SymbolicExpr.sym_mul
  split
  · trivial
  · split_ifs
    · trivial
    · exact hy
    · exact hx
    · exact ⟨hx, hy, rfl⟩

/-! ## Degree -/

section degree

variable {K : Type _} [Field K] [Algebra F K]

/-- The degree walk bounds the degree of the denoted polynomial, once it bounds each leaf. -/
theorem natDegree_denote_le {den : A → Polynomial K} {ld : A → ℕ}
    (hleaf : ∀ a, (den a).natDegree ≤ ld a) (e : SymbolicExpr A) :
    (denote den e).natDegree ≤ e.degree_with ld := by
  induction e with
  | Leaf a => exact hleaf a
  | Add x y _ hx hy =>
    exact (Polynomial.natDegree_add_le _ _).trans (max_le_max hx hy)
  | Sub x y _ hx hy =>
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max hx hy)
  | Neg x _ hx => simpa [denote, p3_air.symbolic.mirror.SymbolicExpr.degree_with] using hx
  | Mul x y _ hx hy =>
    exact Polynomial.natDegree_mul_le.trans (add_le_add hx hy)

/-- The walk of k f + g is at most k times the walk of f plus the walk of g. -/
theorem degree_with_le_mul_add (f g : A → ℕ) (k : ℕ) (e : SymbolicExpr A) :
    e.degree_with (fun a => f a * k + g a) ≤ e.degree_with f * k + e.degree_with g := by
  induction e with
  | Leaf => exact le_rfl
  | Add x y _ hx hy | Sub x y _ hx hy =>
    simp only [p3_air.symbolic.mirror.SymbolicExpr.degree_with]
    refine max_le (hx.trans ?_) (hy.trans ?_) <;> gcongr <;> simp
  | Neg x _ hx => exact hx
  | Mul x y _ hx hy =>
    simp only [p3_air.symbolic.mirror.SymbolicExpr.degree_with]; nlinarith

end degree

end SymbolicExpr

/-! ## Base expressions as polynomials -/

open SymbolicExpr

variable {F : Type _} [Field F] [DecidableEq F]

/-- The polynomial variable a symbolic variable names, and 0 for a row offset past 1. -/
noncomputable def varPoly (v : SymbolicVariable) : MvPolynomial Var F :=
  match v.entry with
  | .Main 0 => .X (.main 0 v.index)
  | .Main 1 => .X (.main 1 v.index)
  | .Preprocessed 0 => .X (.prep 0 v.index)
  | .Preprocessed 1 => .X (.prep 1 v.index)
  | .Public => .X (.pub v.index)
  | .Periodic => .X (.periodic v.index)
  | _ => 0

/-- The polynomial a base leaf names. -/
noncomputable def leafPoly : BaseLeaf F → MvPolynomial Var F
  | .Variable v => varPoly v
  | .IsFirstRow => .X .isFirstRow
  | .IsLastRow => .X .isLastRow
  | .IsTransition => .X .isTransition
  | .Constant c => .C c

/-- The polynomial a base expression denotes. -/
noncomputable def toPoly (e : SymbolicExpression F) : MvPolynomial Var F := denote leafPoly e

theorem leafDen_leafPoly : LeafDen (A := BaseLeaf F) (R := MvPolynomial Var F) leafPoly where
  as_const a c h := by cases a <;> simp_all [SymLeaf.as_const, leafPoly, MvPolynomial.algebraMap_eq]
  from_const c := by simp [SymLeaf.from_const, leafPoly, MvPolynomial.algebraMap_eq]

section bounds

variable {K : Type _} [Field K] [Algebra F K] {σ : Var → Polynomial K} {n : ℕ} {periods : List ℕ}

/-- A periodic column stays within the walk's degree.

That degree is n - n / p, or n - 1 when the period is missing, at least n, or 0. -/
theorem natDegree_periodic_le (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) (j : ℕ) :
    (σ (.periodic j)).natDegree ≤ SymbolicVariable.poly_degree ⟨.Periodic, j⟩ n periods := by
  simp only [SymbolicVariable.poly_degree]
  generalize hq : min (periods[j]?.getD n) n = q
  rcases q with _ | q
  · exact hσ.periodic_default j
  · show _ ≤ n - n / (q + 1)
    rcases hj : periods[j]? with _ | p
    · simp only [hj, Option.getD_none, min_self] at hq
      rw [← hq, Nat.div_self (by omega)]
      exact hσ.periodic_default j
    · simp only [hj, Option.getD_some] at hq
      rcases lt_or_ge p n with hpn | hpn
      · rw [min_eq_left hpn.le] at hq
        subst hq
        exact hσ.periodic j _ hj (by omega) (hp j _ hj (by omega) hpn)
      · rw [min_eq_right hpn] at hq
        rw [← hq, Nat.div_self (by omega)]
        exact hσ.periodic_default j

/-- A variable's polynomial stays within the walk's degree. -/
theorem natDegree_varPoly_le (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) (v : SymbolicVariable) :
    (MvPolynomial.aeval σ (varPoly v : MvPolynomial Var F)).natDegree ≤
      v.poly_degree n periods := by
  obtain ⟨e, j⟩ := v
  cases e with
  | Main o => rcases o with _ | _ | o <;> simp [varPoly, SymbolicVariable.poly_degree, hσ.main]
  | Preprocessed o =>
    rcases o with _ | _ | o <;> simp [varPoly, SymbolicVariable.poly_degree, hσ.prep]
  | Public => simp [varPoly, SymbolicVariable.poly_degree, hσ.pub]
  | Periodic => simpa [varPoly] using natDegree_periodic_le hσ hp j

/-- Under the degree bounds of the variables, every leaf's polynomial stays within its leaf degree. -/
theorem natDegree_leaf_le (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) (a : BaseLeaf F) :
    (MvPolynomial.aeval σ (leafPoly a)).natDegree ≤ SymLeaf.poly_degree a n periods := by
  cases a <;> simp [leafPoly, SymLeaf.poly_degree, natDegree_varPoly_le hσ hp, hσ.isFirstRow,
    hσ.isLastRow, hσ.isTransition]

end bounds

end Plonky3Lean.Proofs.Air
