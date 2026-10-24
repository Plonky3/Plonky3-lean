module

public import Plonky3Lean.Proofs.Sumcheck.Kernel
public import Plonky3Lean.Proofs.Sumcheck.Verifier
public import Plonky3Lean.Proofs.MultilinearUtil.Fold

@[expose] public section

/-!
# The honest prover of a product of two multilinears

For tables f and w of 2^(n+1) entries, the round polynomial of g = f~ w~ is

```text
    s(X) = sum_{b in {0,1}^n} f~(X, b) w~(X, b)
```

Each factor is linear in X, so s has degree 2.

Its value s(0) is the sum over the lower half of f w.

Its X^2 coefficient is the sum of the products of the differences.

The round kernel sends exactly these two values.

Folding both tables at the challenge leaves the tables of f~(r, .) and w~(r, .).
-/

namespace Plonky3Lean.Proofs.Sumcheck

open MvPolynomial Finset Plonky3Lean.Spec.Sumcheck Plonky3Lean.Spec.MultilinearUtil
  Plonky3Lean.Proofs.MultilinearUtil

variable {F : Type _} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem vertexFn_low {n j : ℕ} (hj : j < 2 ^ n) :
    (vertexFn (n + 1) j : Fin (n + 1) → F) = Fin.cons 0 (vertexFn n j) :=
  List.ofFn_injective (by rw [ofFn_vertexFn, List.ofFn_succ, vertex_low hj, ← ofFn_vertexFn]; rfl)

omit [DecidableEq F] in
theorem vertexFn_high {n j : ℕ} (hj : j < 2 ^ n) :
    (vertexFn (n + 1) (2 ^ n + j) : Fin (n + 1) → F) = Fin.cons 1 (vertexFn n j) :=
  List.ofFn_injective (by rw [ofFn_vertexFn, List.ofFn_succ, vertex_high hj, ← ofFn_vertexFn]; rfl)

/-- The cube, enumerated by the vertices 0, ..., 2^n - 1 with coordinate 0 on the top bit. -/
theorem sum_cube_eq_sum_vertex {M : Type _} [AddCommMonoid M] :
    ∀ {n : ℕ} (φ : (Fin n → F) → M), ∑ b ∈ cube n, φ b = ∑ j ∈ range (2 ^ n), φ (vertexFn n j)
  | 0, φ => by simp [cube, Subsingleton.elim (vertexFn 0 0 : Fin 0 → F) (fun i => i.elim0)]; rfl
  | n + 1, φ => by
    rw [sum_cube_succ, sum_pair zero_ne_one, sum_cube_eq_sum_vertex, sum_cube_eq_sum_vertex,
      pow_succ, mul_two, sum_range_add]
    congr 1
    · exact sum_congr rfl fun j hj => by rw [vertexFn_low (mem_range.mp hj)]
    · exact sum_congr rfl fun j hj => by rw [vertexFn_high (mem_range.mp hj)]

omit [DecidableEq F] in
/-- With the other variables at b, the extension is a polynomial of degree at most 1 in the first. -/
theorem natDegree_map_finSuccEquiv_mlePoly (f : List F) (n : ℕ) (b : Fin n → F) :
    ((finSuccEquiv F n (mlePoly f (n + 1))).map (eval b)).natDegree ≤ 1 :=
  Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv _).le.trans (mlePoly_isMultilinear f _ 0))

omit [DecidableEq F] in
theorem eval_map_finSuccEquiv {n : ℕ} (P : MvPolynomial (Fin (n + 1)) F) (b : Fin n → F) (a : F) :
    ((finSuccEquiv F n P).map (eval b)).eval a = eval (Fin.cons a b) P :=
  (eval_eq_eval_mv_eval' b a P).symm

/-- The round kernel on two tables of 2^(n+1) entries sends the honest message of their product.

That message is its value at 0 and its X^2 coefficient. -/
theorem sumcheck_coefficients_prefix_honest (f w : List F) {n : ℕ} (hf : f.length = 2 ^ (n + 1))
    (hw : w.length = 2 ^ (n + 1)) :
    p3_sumcheck.strategy.mirror.sumcheck_coefficients_prefix f w =
      some (encEval (honestMessage (mlePoly f (n + 1) * mlePoly w (n + 1)))) := by
  have hh : f.length / 2 = 2 ^ n := by rw [hf, pow_succ]; omega
  rw [sumcheck_coefficients_prefix_eq f w (by omega) (by rw [hf, pow_succ]; omega), hh]
  have hlo : ∀ j ∈ range (2 ^ n), ∀ g : List F, g.length = 2 ^ (n + 1) →
      eval (Fin.cons 0 (vertexFn n j)) (mlePoly g (n + 1)) = g.getD j 0 := fun j hj g _ => by
    rw [← vertexFn_low (mem_range.mp hj), eval_mlePoly_vertex g (by have := mem_range.mp hj; rw [pow_succ]; omega)]
  have hhi : ∀ j ∈ range (2 ^ n), ∀ g : List F, g.length = 2 ^ (n + 1) →
      eval (Fin.cons 1 (vertexFn n j)) (mlePoly g (n + 1)) = g.getD (2 ^ n + j) 0 := fun j hj g _ => by
    rw [← vertexFn_high (mem_range.mp hj),
      eval_mlePoly_vertex g (by have := mem_range.mp hj; rw [pow_succ]; omega)]
  simp only [encEval, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [eval_honestMessage, cubeSum, sum_cube_eq_sum_vertex]
    exact sum_congr rfl fun j hj => by
      rw [eval_fixFirst, eval_mul, hlo j hj f hf, hlo j hj w hw, mul_comm]
  · rw [honestMessage, Polynomial.finsetSum_coeff, sum_cube_eq_sum_vertex]
    refine sum_congr rfl fun j hj => ?_
    rw [map_mul, Polynomial.map_mul, coeff_two_mul_of_linear (natDegree_map_finSuccEquiv_mlePoly _ _ _)
      (natDegree_map_finSuccEquiv_mlePoly _ _ _)]
    simp only [eval_map_finSuccEquiv, hlo j hj f hf, hlo j hj w hw, hhi j hj f hf, hhi j hj w hw]
    ring

/-! ## The honest prover over all rounds -/

/-- The prover of a product, round after round.

Each round runs the kernel on both tables, then folds both tables at the challenge. -/
def proveProduct (f w : List F) : List F → Option (List (F × F))
  | [] => some []
  | r :: rs => do
    let m ← p3_sumcheck.strategy.mirror.sumcheck_coefficients_prefix f w
    let f' ← p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut f r
    let w' ← p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut w r
    let ms ← proveProduct f' w' rs
    pure (m :: ms)

omit [DecidableEq F] in
/-- Folding a table at a is setting the first variable of its extension to a. -/
theorem fixFirst_mlePoly (f : List F) {n : ℕ} (hf : f.length = 2 ^ (n + 1)) (a : F) :
    ∃ f', p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut f a = some f' ∧
      f'.length = 2 ^ n ∧ fixFirst a (mlePoly f (n + 1)) = mlePoly f' n := by
  obtain ⟨f', hf', hlen, -⟩ := fix_prefix_var_mut_spec f a hf
  refine ⟨f', hf', hlen, eq_mlePoly f' (individualDegreeLE_fixFirst (mlePoly_isMultilinear f _) a)
    fun b hb => ?_⟩
  have h1 : f.length ≠ 1 := by rw [hf, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have hh : f.length / 2 = 2 ^ n := by rw [hf, pow_succ]; omega
  simp only [p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut, h1, ↓reduceIte, hh,
    Option.some.injEq] at hf'
  subst hf'
  have hb2 : b < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hb3 : 2 ^ n + b < 2 ^ (n + 1) := by rw [pow_succ]; omega
  rw [eval_fixFirst, ← eval_map_finSuccEquiv,
    Polynomial.eq_X_add_C_of_natDegree_le_one (natDegree_map_finSuccEquiv_mlePoly f n _)]
  have e0 := eval_map_finSuccEquiv (mlePoly f (n + 1)) (vertexFn n b) 0
  have e1 := eval_map_finSuccEquiv (mlePoly f (n + 1)) (vertexFn n b) 1
  rw [← vertexFn_low hb, eval_mlePoly_vertex f hb2] at e0
  rw [← vertexFn_high hb, eval_mlePoly_vertex f hb3] at e1
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (natDegree_map_finSuccEquiv_mlePoly f n _)] at e0 e1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero,
    zero_add, mul_one, Polynomial.coeff_map] at e0 e1 ⊢
  have hz : (List.zipWith (fun a0 a1 => a0 + (a1 - a0) * algebraMap F F a) (f.take (2 ^ n))
      (f.drop (2 ^ n))).getD b 0 = f.getD b 0 + (f.getD (2 ^ n + b) 0 - f.getD b 0) * a := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, hb, show b < f.length by omega,
      show 2 ^ n + b < f.length by omega]
  rw [hz, ← e0, ← e1]
  ring

/-- Completeness of the shipped quadratic sumcheck on a product.

The kernel-and-fold prover's messages, replayed by the verifier's round identity, end at g(r). -/
theorem proveProduct_complete : ∀ {n : ℕ} (f w : List F), f.length = 2 ^ n → w.length = 2 ^ n →
    ∀ r : Fin n → F, ∃ ms, proveProduct f w (List.ofFn r) = some ms ∧
      eval r (mlePoly f n * mlePoly w n) =
        replay .Evaluation (cubeSum (mlePoly f n * mlePoly w n)) ms (List.ofFn r)
  | 0, f, w, _, _, r => ⟨[], rfl, by
      simp [replay, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]; rfl⟩
  | n + 1, f, w, hf, hw, r => by
    obtain ⟨f', hf', hfl, hff⟩ := fixFirst_mlePoly f hf (r 0)
    obtain ⟨w', hw', hwl, hww⟩ := fixFirst_mlePoly w hw (r 0)
    obtain ⟨ms, hms, hev⟩ := proveProduct_complete f' w' hfl hwl (Fin.tail r)
    set g := mlePoly f (n + 1) * mlePoly w (n + 1)
    have hg : IndividualDegreeLE g 2 := fun i =>
      (degreeOf_mul_le _ _ _).trans (add_le_add (mlePoly_isMultilinear f _ i) (mlePoly_isMultilinear w _ i))
    refine ⟨encEval (honestMessage g) :: ms, ?_, ?_⟩
    · simp [proveProduct, List.ofFn_succ, sumcheck_coefficients_prefix_honest f w hf hw, hf', hw',
        ← Fin.tail_def, hms, g]
    · rw [replay_evaluation, List.ofFn_succ, finalClaim,
        decEval_encEval (natDegree_honestMessage_le hg) (honestMessage_sum g), eval_honestMessage,
        ← replay_evaluation]
      have hfix : fixFirst (r 0) g = mlePoly f' n * mlePoly w' n := by
        rw [← hff, ← hww]; simp [fixFirst, g]
      rw [hfix, show (List.ofFn fun i : Fin n => r i.succ) = List.ofFn (Fin.tail r) from rfl, ← hev,
        ← hfix, eval_fixFirst, Fin.cons_self_tail]

end Plonky3Lean.Proofs.Sumcheck
