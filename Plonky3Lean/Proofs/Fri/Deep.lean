module

public import Plonky3Lean.Proofs.Fri.Reduce
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# The DEEP quotients

The opening argument replaces each claim f(z) = y by the quotient (f(X) - y) / (X - z).

This is the DEEP technique of Ben-Sasson, Goldberg, Kopparty and Saraf (eprint 2019/336).

The batched form follows Haböck's summary of FRI (eprint 2022/1216):

```text
    Q(X) = sum_k sum_i alpha^(off_k + i) (f_(k,i)(X) - f_(k,i)(z_k)) / (X - z_k)
```

The verifier's reduced opening at a query point x is Q(x), when the claims are honest.

Each quotient has degree below its column's degree.

A constant column has quotient zero.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.verifier.mirror p3_dft.mirror
open p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- The DEEP quotient of f at z: (f - f(z)) / (X - z). -/
noncomputable def deepQuot (f : K[X]) (z : K) : K[X] := (f - C (f.eval z)) /ₘ (X - C z)

/-- Off the point z, the quotient takes the value (f(x) - f(z)) / (x - z). -/
theorem eval_deepQuot (f : K[X]) {z x : K} (hx : x ≠ z) :
    (deepQuot f z).eval x = (f.eval x - f.eval z) / (x - z) := by
  have hroot : IsRoot (f - C (f.eval z)) z := by simp
  have hmul := congrArg (eval x) ((mul_divByMonic_eq_iff_isRoot).2 hroot)
  rw [eval_mul, eval_sub, eval_X, eval_C, eval_sub, eval_C] at hmul
  rw [deepQuot, eq_div_iff (sub_ne_zero.2 hx), mul_comm, hmul]

/-- A non-constant column's quotient has smaller degree. -/
theorem degree_deepQuot_lt {f : K[X]} (hf : 0 < f.degree) (z : K) : (deepQuot f z).degree < f.degree := by
  have hne : f - C (f.eval z) ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hf
    exact absurd (lt_of_lt_of_le hf degree_C_le) (lt_irrefl _)
  rw [deepQuot, ← degree_sub_C hf (a := f.eval z)]
  exact degree_divByMonic_lt _ _ hne (by rw [degree_X_sub_C]; exact zero_lt_one)

/-- A constant column has quotient zero. -/
theorem deepQuot_C (c z : K) : deepQuot (C c) z = 0 := by simp [deepQuot]

/-- The batched DEEP polynomial of claims (z, columns), from ladder position off. -/
noncomputable def deepPoly (α : K) : ℕ → List (K × List K[X]) → K[X]
  | _, [] => 0
  | off, (z, fs) :: L =>
    ∑ i ∈ range fs.length, C (α ^ (off + i)) * deepQuot (fs.getD i 0) z + deepPoly α (off + fs.length) L

/-- The honest reduced opening at x is the batched DEEP polynomial at x.

The claimed values are the columns at z, and the opened row is the columns at x. -/
theorem reducedOpening_eq_deepPoly (α x : K) : ∀ (off : ℕ) (L : List (K × List K[X])), (∀ e ∈ L, e.1 ≠ x) →
    reducedOpening α x off (L.map fun e => (e.1, e.2.map (·.eval e.1), e.2.map (·.eval x))) =
      (deepPoly α off L).eval x
  | _, [], _ => by simp [reducedOpening, deepPoly]
  | off, (z, fs) :: L, hz => by
    simp only [List.map_cons, reducedOpening, List.length_map, deepPoly, eval_add, eval_finsetSum, eval_mul,
      eval_C]
    rw [reducedOpening_eq_deepPoly α x _ L fun e he => hz e (List.mem_cons_of_mem _ he), Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hzx : x ≠ z := fun h => hz _ List.mem_cons_self h.symm
    rw [eval_deepQuot _ hzx, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map]
    rw [mul_div_assoc, ← neg_sub (eval x _), ← neg_sub x z, neg_div_neg_eq]

/-- A quotient has degree below d when its column has. -/
theorem degree_deepQuot_lt_of {f : K[X]} {d : WithBot ℕ} (hf : f.degree < d) (z : K) :
    (deepQuot f z).degree < d := by
  rcases le_or_gt f.degree 0 with h0 | h0
  · rw [eq_C_of_degree_le_zero h0, deepQuot_C, degree_zero]; exact lt_of_le_of_lt bot_le hf
  · exact (degree_deepQuot_lt h0 z).trans hf

/-- The batched DEEP polynomial has degree below d when every column has. -/
theorem degree_deepPoly_lt (α : K) {d : WithBot ℕ} (hbot : ⊥ < d) : ∀ (off : ℕ) (L : List (K × List K[X])),
    (∀ e ∈ L, ∀ f ∈ e.2, f.degree < d) → (deepPoly α off L).degree < d
  | _, [], _ => by rw [deepPoly, degree_zero]; exact hbot
  | off, (z, fs) :: L, hL => by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_
      (degree_deepPoly_lt α hbot _ L fun e he => hL e (List.mem_cons_of_mem _ he)))
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 fun i hi => ?_)
    have hf : (fs.getD i 0).degree < d := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      exact hL _ List.mem_cons_self _ (List.getElem_mem _)
    rw [C_mul']
    exact lt_of_le_of_lt (degree_smul_le _ _) (degree_deepQuot_lt_of hf z)

/-! ## The verifier's reduced openings -/

section verifier

variable [DecidableEq K]

/-- The claims at log height h of a query's matrices, as points with their matrix's columns. -/
noncomputable def deepClaims {G : Gen K} (b h : ℕ)
    (cols : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) → List K[X])
    (mats : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K)) :
    List (K × List K[X]) :=
  (mats.filter fun mr => mr.1.domain.log_size + b = h).flatMap fun mr => mr.1.points.map fun p => (p.point, cols mr.1)

theorem matsEntries_honest {G : Gen K} (b h : ℕ) (xOf : ℕ → K)
    (cols : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) → List K[X]) :
    ∀ (mats : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K)),
      (∀ mr ∈ mats, mr.2 = (cols mr.1).map (·.eval (xOf (mr.1.domain.log_size + b)))) →
      (∀ mr ∈ mats, ∀ p ∈ mr.1.points, p.values = (cols mr.1).map (·.eval p.point)) →
      ((matsEntries b mats).filter (·.1 = h)).map (·.2) =
        (deepClaims b h cols mats).map fun e => (e.1, e.2.map (·.eval e.1), e.2.map (·.eval (xOf h)))
  | [], _, _ => rfl
  | mr :: mats, hrow, hval => by
    have ih := matsEntries_honest b h xOf cols mats (fun m hm => hrow m (List.mem_cons_of_mem _ hm))
      (fun m hm => hval m (List.mem_cons_of_mem _ hm))
    simp only [matsEntries, deepClaims] at ih ⊢
    by_cases hh : mr.1.domain.log_size + b = h
    · simp only [List.flatMap_cons, List.filter_append, List.map_append, List.filter_cons, hh, decide_true,
        ↓reduceIte]
      rw [ih]; congr 1
      simp only [matEntries, List.filter_map, List.map_map]
      rw [List.filter_eq_self.2 (by simp)]
      refine List.map_congr_left fun p hp => ?_
      simp only [Function.comp, Prod.mk.injEq, true_and]
      exact ⟨hval mr List.mem_cons_self p hp, by rw [hrow mr List.mem_cons_self, hh]⟩
    · simp only [List.flatMap_cons, List.filter_append, List.map_append, List.filter_cons, hh, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp only [matEntries, List.filter_map]
      rw [List.filter_eq_nil_iff.2 (by simp [hh])]
      rfl

/-- The verifier's reduction of one query computes the batched DEEP polynomials.

Take matrices whose opened rows are their columns at the query point.

Take claimed values that are the columns at each opening point, none equal to the query point.

Then the value at each height is the DEEP polynomial of the claims at that height.

It is evaluated at the query point of that height. -/
theorem reduceQuery_deep {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) (ro : List (ℕ × K))
    (cols : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) → List K[X])
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    (hrow : ∀ mr ∈ queryMats claims rows,
      mr.2 = (cols mr.1).map (·.eval (xOfQuery G g H index (mr.1.domain.log_size + b))))
    (hval : ∀ mr ∈ queryMats claims rows, ∀ p ∈ mr.1.points, p.values = (cols mr.1).map (·.eval p.point))
    (hz : ∀ mr ∈ queryMats claims rows, ∀ p ∈ mr.1.points,
      p.point ≠ xOfQuery G g H index (mr.1.domain.log_size + b))
    (h : reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index = pure ro) :
    ∀ e ∈ ro, e.2 = (deepPoly α 0 (deepClaims b e.1 cols (queryMats claims rows))).eval
      (xOfQuery G g H index e.1) := by
  intro e he
  rw [reduceQuery_spec G g b H α claims rows index ro halign h e he,
    matsEntries_honest b e.1 _ cols _ hrow hval]
  refine reducedOpening_eq_deepPoly α _ 0 _ fun c hc => ?_
  simp only [deepClaims, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq] at hc
  obtain ⟨mr, ⟨hmr, hh⟩, p, hp, rfl⟩ := hc
  rw [← hh]
  exact hz mr hmr p hp

end verifier

end Plonky3Lean.Proofs.Fri
