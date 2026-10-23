module

public import Plonky3Lean.Proofs.Stir.Virtual
public import Plonky3Lean.Proofs.Stir.PolyFold

@[expose] public section

/-!
# Completeness of one round

An honest round folds f, quotients the fold by its answers on G, and degree-corrects back to the next degree bound:

```text
    deg f < k d   =>   deg PolyFold(f, k, r) < d
                  =>   deg PolyQuotient(g, G) < d - |G|
                  =>   deg DegCor(d, r', PolyQuotient(g, G), d - |G|) < d
```

Off G, the polynomial agrees with the oracle the verifier reads.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

theorem eval_vanishingPoly (G : Finset K) (x : K) : (vanishingPoly G).eval x = ∏ y ∈ G, (x - y) := by
  simp [vanishingPoly, eval_prod]

theorem vanishingPoly_monic (G : Finset K) : (vanishingPoly G).Monic :=
  monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y

theorem natDegree_vanishingPoly (G : Finset K) : (vanishingPoly G).natDegree = G.card := by
  rw [vanishingPoly, natDegree_prod_of_monic _ _ fun y _ => monic_X_sub_C y]; simp

/-- The answers of g on G interpolate g on G. -/
theorem eval_ansPoly (g : K[X]) (G : Finset K) {x : K} (hx : x ∈ G) :
    (ansPoly G fun y => g.eval y).eval x = g.eval x :=
  Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hx

/-- The vanishing polynomial divides g - Ans exactly. -/
theorem vanishingPoly_dvd (g : K[X]) (G : Finset K) :
    vanishingPoly G ∣ g - ansPoly G fun y => g.eval y := by
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) fun y hy => ?_
  · exact pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id hab
  · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_ansPoly g G hy, sub_self]

/-- PolyQuotient multiplies back to g - Ans. -/
theorem polyQuotient_mul (g : K[X]) (G : Finset K) :
    vanishingPoly G * polyQuotient g G = g - ansPoly G fun y => g.eval y := by
  have h := modByMonic_add_div (g - ansPoly G fun y => g.eval y) (vanishingPoly G)
  rw [(modByMonic_eq_zero_iff_dvd (vanishingPoly_monic G)).2 (vanishingPoly_dvd g G), zero_add] at h
  exact h

/-- PolyQuotient lowers the degree bound by |G|. -/
theorem degree_polyQuotient_lt (g : K[X]) (G : Finset K) {d : ℕ} (hG : G.card ≤ d)
    (hg : g.degree < d) : (polyQuotient g G).degree < (d - G.card : ℕ) := by
  have hans : (ansPoly G fun y => g.eval y).degree < d := by
    have := Lagrange.degree_interpolate_lt (s := G) (v := id) (fun y => g.eval y) (Set.injOn_id _)
    exact this.trans_le (by exact_mod_cast hG)
  have hsub : (g - ansPoly G fun y => g.eval y).degree < d := (degree_sub_le _ _).trans_lt (max_lt hg hans)
  by_cases hQ : polyQuotient g G = 0
  · rw [hQ]; simp
  have hV := vanishingPoly_monic G
  rw [← polyQuotient_mul] at hsub
  have hne : vanishingPoly G * polyQuotient g G ≠ 0 := mul_ne_zero hV.ne_zero hQ
  have h1 : (vanishingPoly G * polyQuotient g G).natDegree < d := (natDegree_lt_iff_degree_lt hne).2 hsub
  rw [hV.natDegree_mul' hQ,
    natDegree_vanishingPoly] at h1
  exact (natDegree_lt_iff_degree_lt hQ).1 (by omega)

/-- Off G, PolyQuotient is (g - Ans) / V. -/
theorem eval_polyQuotient (g : K[X]) (G : Finset K) {x : K} (hx : x ∉ G) :
    (polyQuotient g G).eval x =
      (g.eval x - (ansPoly G fun y => g.eval y).eval x) / (vanishingPoly G).eval x := by
  have hV : (vanishingPoly G).eval x ≠ 0 := by
    rw [eval_vanishingPoly]; exact prod_ne_zero_iff.2 fun y hy h => hx (sub_eq_zero.1 h ▸ hy)
  rw [eq_div_iff hV, mul_comm, ← eval_mul, polyQuotient_mul, eval_sub]

/-- Round completeness: an input of degree below k d gives a next polynomial of degree below d. -/
theorem degree_nextPoly_lt (f : K[X]) {k d : ℕ} (hk : 0 < k) (hf : f.degree < (k * d : ℕ))
    (rFold rComb : K) (G : Finset K) (hG : G.card ≤ d) :
    (nextPoly f k rFold rComb G d).degree < d :=
  degree_polyDegCor_lt (Nat.sub_le _ _) rComb
    (degree_polyQuotient_lt _ G hG (degree_polyFold_lt hk hf rFold))

/-- Off G, the next polynomial is DegCor of Definition 4.12 applied to Quotient of Definition 4.2, for any fill. -/
theorem eval_nextPoly (f : K[X]) (k : ℕ) (rFold rComb : K) (G : Finset K) (d : ℕ) (fill : K → K)
    {x : K} (hx : x ∉ G) :
    (nextPoly f k rFold rComb G d).eval x =
      degCor d (d - G.card) rComb
        (quotient (fun y => (polyFold f k rFold).eval y) G (fun y => (polyFold f k rFold).eval y) fill) x := by
  rw [nextPoly, eval_polyDegCor, degCor, degCor, eval_polyQuotient _ _ hx, quotient, ite_eq_right hx]

/-- The verifier's virtual oracle is the honest next polynomial off the interpolation points. -/
theorem virtualVal_eq_nextPoly (f : K[X]) (k : ℕ) (rFold rComb : K) (pts ans : List K) {d : ℕ}
    (hnd : pts.Nodup) (hd : pts.length ≤ d)
    (hans : coeffPoly ans = ansPoly pts.toFinset fun y => (polyFold f k rFold).eval y)
    {x : K} (hx : x ∉ pts) :
    virtualVal rComb ans pts x ((polyFold f k rFold).eval x) =
      (nextPoly f k rFold rComb pts.toFinset d).eval x := by
  have hcard : pts.toFinset.card = pts.length := List.toFinset_card_of_nodup hnd
  rw [nextPoly, eval_polyDegCor, degCor, eval_polyQuotient _ _ (by simpa using hx), virtualVal, hans,
    eval_vanishingPoly, hcard, show d - (d - pts.length) = pts.length by omega,
    ← List.prod_toFinset _ hnd]

end Plonky3Lean.Proofs.Stir
