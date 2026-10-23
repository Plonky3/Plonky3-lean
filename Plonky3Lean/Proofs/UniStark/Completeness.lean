module

public import Plonky3Lean.Proofs.UniStark.Quotient
public import Plonky3Lean.Proofs.Air.Degree

@[expose] public section

/-!
# Completeness of the out-of-domain check

On a trace that satisfies the STARK's relation:

* the prover's quotient values are the quotient polynomial Q at the quotient coset's points;
* when every constraint fits the chunks p3-air's sizing gives, Q has degree below the quotient coset's size;
* the verifier then recovers Q(zeta) from the honest chunk openings, and its check at zeta accepts.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_air.builder.mirror p3_air.air.mirror p3_air.symbolic.mirror p3_uni_stark.folder.mirror
open p3_uni_stark.prover.mirror p3_uni_stark.verifier.mirror
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Air

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-! ## Base polynomials read in the extension -/

theorem aeval_starkAssignK (s ω : F) (k : ℕ) (main prep : ℕ → F[X]) (pub : ℕ → F)
    (periodic : ℕ → F[X]) (c : MvPolynomial Var F) :
    MvPolynomial.aeval (starkAssignK (K := K) s ω k main prep pub periodic) c =
      (MvPolynomial.aeval (starkAssign s ω k main prep pub periodic) c).map (algebraMap F K) := by
  unfold starkAssignK
  have := congrArg (· c) (MvPolynomial.comp_aeval (R := F)
    (f := starkAssign s ω k main prep pub periodic) (Polynomial.mapAlg F K))
  simpa [Polynomial.mapAlg_eq_map] using this.symm

theorem vanishing_map (f : F →+* K) (s ω : F) (k : ℕ) :
    (vanishing s ω k).map f = vanishing (f s) (f ω) k := by
  simp [vanishing, Lagrange.nodal, Polynomial.map_prod, cosetPoints]

/-- Each constraint polynomial below M keeps the combined polynomial below M. -/
theorem natDegree_combinedPoly_lt {s ω : F} {k : ℕ} {main prep periodic : ℕ → F[X]} {pub : ℕ → F}
    {C : List (MvPolynomial Var F)} {M : ℕ} (hM : 0 < M)
    (h : ∀ c ∈ C, (MvPolynomial.aeval (starkAssign s ω k main prep pub periodic) c).natDegree < M)
    (α : K) :
    (combinedPoly α (starkAssignK s ω k main prep pub periodic) C).natDegree < M := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := M - 1) fun i hi => ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [aeval_starkAssignK]
  refine (natDegree_map_le).trans ?_
  have hi := mem_range.mp hi
  have := h _ (List.getD_eq_getElem C 0 hi ▸ List.getElem_mem hi)
  omega

/-- When every constraint fits c >= 1 chunks of n, the quotient has degree below c n. -/
theorem degree_quotient_lt {s ω : F} {k c : ℕ} (hc : 1 ≤ c) {main prep periodic : ℕ → F[X]}
    {pub : ℕ → F} {C : List (MvPolynomial Var F)}
    (hfit : ∀ e ∈ C, FitsChunks (2 ^ k) c
      (constraintPoly (starkAssign s ω k main prep pub periodic) e)) (α : K) :
    (quotientPoly (algebraMap F K s) (algebraMap F K ω) k
      (combinedPoly α (starkAssignK s ω k main prep pub periodic) C)).degree < (c * 2 ^ k : ℕ) :=
  degree_quotientPoly_lt hc (natDegree_combinedPoly_lt (by positivity) hfit α)

/-! ## The prover's values are the quotient -/

/-- Off the trace coset, the prover's value C_alpha(x) s^n / Z(x) is the quotient at x. -/
theorem prover_value_eq_quotient {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ k) {main prep periodic : ℕ → F[X]} {pub : ℕ → F}
    (hmain : ∀ i < 2 ^ k, ∀ c, (main c).eval (s * ω ^ i) = T.main i c)
    (hprep : ∀ i < 2 ^ k, ∀ c, (prep c).eval (s * ω ^ i) = T.prep i c)
    (hpub : ∀ j, pub j = T.pub j)
    (hper : ∀ i < 2 ^ k, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    {C : List (MvPolynomial Var F)} (hsat : SatisfiesStark C T ω) (α : K) {x : F}
    (hx : (vanishing s ω k).eval x ≠ 0) :
    combine α (C.map fun c => algebraMap F K (MvPolynomial.eval
        (fun v => (starkAssign s ω k main prep pub periodic v).eval x) c)) *
      algebraMap F K (s ^ 2 ^ k / (vanishing s ω k).eval x) =
    (quotientPoly (algebraMap F K s) (algebraMap F K ω) k
      (combinedPoly α (starkAssignK s ω k main prep pub periodic) C)).eval (algebraMap F K x) := by
  have hZ : (vanishing (algebraMap F K s) (algebraMap F K ω) k).eval (algebraMap F K x) =
      algebraMap F K ((vanishing s ω k).eval x) := by
    rw [← vanishing_map, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval]
  have hZ0 : (vanishing (algebraMap F K s) (algebraMap F K ω) k).eval (algebraMap F K x) ≠ 0 := by
    rw [hZ]; exact (_root_.map_ne_zero _).mpr hx
  rw [eval_quotientPoly (vanishing_dvd_combinedPoly hω hs hT hmain hprep hpub hper hsat α) hZ0,
    eval_combinedPoly, hZ]
  have henv : ∀ c, MvPolynomial.aeval (fun v => (starkAssignK (K := K) s ω k main prep pub periodic
      v).eval (algebraMap F K x)) c = algebraMap F K (MvPolynomial.eval
        (fun v => (starkAssign s ω k main prep pub periodic v).eval x) c) := fun c => by
    have : (fun v => (starkAssignK (K := K) s ω k main prep pub periodic v).eval
        (algebraMap F K x)) =
        algebraMap F K ∘ fun v => (starkAssign s ω k main prep pub periodic v).eval x := by
      funext v
      rw [starkAssignK, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
        Polynomial.coe_aeval_eq_eval, Function.comp_apply]
    rw [this, MvPolynomial.aeval_algebraMap_apply]
    simp
  rw [List.map_congr_left fun c _ => henv c]
  simp only [map_div₀, map_pow]
  ring

/-! ## The chunk count is p3-air's -/

/-- On a two-adic domain the prover and verifier size the quotient with p3-air's sizing. -/
theorem get_log_num_quotient_chunks_for_domain_eq (air : Air F) (layout : AirLayout) (n z : ℕ) :
    get_log_num_quotient_chunks_for_domain air layout n z = get_log_quotient_degree air layout n z :=
  rfl

/-! ## The out-of-domain check accepts an honest proof -/

variable [DecidableEq K]

/-- Completeness of the identity at zeta.

* The trace satisfies the STARK's relation on the trace subgroup s H of order n.
* Every constraint fits the 2^L chunks of n that p3-air's sizing gives.
* The quotient coset has order 2^L n.
* Each chunk's opening rebuilds to its interpolant of the quotient at zeta, as an honest scheme opens it.
* zeta lies off s H.

Then the recombined quotient is Q(zeta), and the check at zeta accepts it. -/
theorem honest_ood_check (GK : Gen K) (hV : GenValid GK) (hN : GenNested GK) (h2 : (2 : K) ≠ 0)
    {air : Air F} (hb : air.public_boundary_io = []) (c : Coset GK) {s ω : F}
    (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]} {pv : List F}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpv : pv.length = air.num_public_values)
    (hsat : SatisfiesStark (constraints air) T ω)
    (qd : Coset GK) {L : ℕ} (hqd : qd.log_size = L + c.log_size)
    (hfit : ∀ e ∈ constraints air, FitsChunks (2 ^ c.log_size) (2 ^ L)
      (constraintPoly (starkAssign s ω c.log_size main prep (pv.getD · 0) periodic) e))
    {D : ℕ} (B : Module.Basis (Fin D) F K) (α ζ : K) (chunks : List (List K))
    (hlen : chunks.length = 2 ^ L)
    (hv : ∀ i (hi : i < 2 ^ L), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) =
      some ((chunkInterp hV qd L (quotientPoly c.shift c.subgroup_generator c.log_size
        (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
          (constraints air))) i).eval ζ))
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) {pl pn : Option (List K)}
    (hpre : (pl = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 0) air.preprocessed_width ζ) ∧
      pn = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 1) air.preprocessed_width ζ)) ∨
      (pl = none ∧ pn = none ∧ air.preprocessed_width = 0)) :
    ∃ q, recompose_quotient_from_chunks GK B ((List.range (2 ^ L)).map (chunk GK hV qd L)) chunks ζ =
        some q ∧
      verify_constraints GK air
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
        pl pn
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) .periodic
          air.num_periodic_columns ζ) pv c ζ α q = some (.ok ()) := by
  have hdeg := degree_quotient_lt (K := K) Nat.one_le_two_pow hfit α
  rw [← hcs, ← hcg, ← pow_add, ← hqd] at hdeg
  exact ⟨_, recompose_quotient hV qd L B hN (by omega) _ hdeg chunks hlen hv,
    verify_constraints_complete GK hV h2 hb c hcs hcg hω hs hT hmain hprep hpub hper hpv hsat hζ α hpre⟩

end Plonky3Lean.Proofs.UniStark
