module

public import Plonky3Lean.Proofs.UniStark.Completeness
public import Plonky3Lean.Proofs.UniStark.Transcript
public import Plonky3Lean.Proofs.UniStark.Extracted
public import Plonky3Lean.Proofs.UniStark.Zk
public import Plonky3Lean.Proofs.UniStark.ZkCompleteness
public import Plonky3Lean.Proofs.UniStark.EndToEnd
public import Plonky3Lean.Proofs.Commit.BabyBear
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-uni-stark: claims

The integer helpers are extracted.

The folders, the quotient, the recombination, the verifier's checks and the transcript are transcribed.

The trace lives on a subgroup s H of order n = 2^k, with generator omega.

The quotient lives on a disjoint coset of order 2^L n.

```text
    C_alpha(X) = sum_i alpha^(m - 1 - i) C_i(X)     m constraints, in emission order
    Q(X)       = s^n C_alpha(X) / Z(X)              Z the monic vanishing polynomial of s H
```

The STARK evaluates the selectors as p3-commit's unnormalized Lagrange selectors, not as 0/1 values.

The commitment scheme enters only through the openings its contract guarantees.

The instances at BabyBear and its quartic extension use CompPoly's fields.
-/

open Polynomial Finset
open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror
open p3_uni_stark.folder.mirror p3_uni_stark.prover.mirror p3_uni_stark.verifier.mirror
open p3_uni_stark.transcript.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.UniStark

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.UniStark

/-! ## The constraint folders -/

section folders

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- Horner's rule from an accumulator a: the fold is a alpha^m plus the combination. -/
theorem foldl_horner (α a : K) (vs : List K) :
    vs.foldl (fun acc x => acc * α + x) a = a * α ^ vs.length + combine α vs :=
  Plonky3Lean.Proofs.UniStark.foldl_horner α a vs

/-- The verifier's accumulator is the combination of the constraint polynomials at the opened values. -/
theorem verifier_accumulator {air : Air F} {env : Var → K} {main preprocessed : RowWindow K}
    {pv : List F} {periodic : List K} {first last trans : K}
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans) (α : K) :
    air.eval (verifierFolder main preprocessed pv periodic first last trans α) 0 =
      combine α ((constraints air).map (MvPolynomial.aeval env)) :=
  Plonky3Lean.Proofs.UniStark.verifier_accumulator h α

/-- The prover's folder collects the values of the constraint polynomials on the row, in emission order. -/
theorem prover_constraints {air : Air F} {env : Var → F} {main preprocessed : RowWindow F}
    {pv periodic : List F} {first last trans : F}
    (h : Holds air env main preprocessed pv periodic first last trans) :
    air.eval (proverFolder main preprocessed pv periodic first last trans) [] =
      (constraints air).map (MvPolynomial.eval env) :=
  Plonky3Lean.Proofs.UniStark.prover_constraints h

/-- The symbolic builder records one base constraint per constraint polynomial. -/
theorem get_constraint_layout.from_air (air : Air F) :
    get_constraint_layout air (AirLayout.from_air air) =
      .ok ⟨List.range (constraints air).length, []⟩ :=
  Plonky3Lean.Proofs.UniStark.get_constraint_layout_from_air air

/-- The prover's combination, with the powers the layout decomposes, is the combination of the embedded values. -/
theorem finalize_decompose {D : ℕ} (B : Module.Basis (Fin D) F K) (α : K) (base : List F) :
    finalize_constraints B
        (ConstraintLayout.decompose_alpha B ⟨List.range base.length, []⟩ α).1
        (ConstraintLayout.decompose_alpha B ⟨List.range base.length, []⟩ α).2 base [] =
      some (combine α (base.map (algebraMap F K))) :=
  Plonky3Lean.Proofs.UniStark.finalize_decompose B α base

/-- The two folders weight the constraints with the same powers of alpha, in the same order.

On a row whose values embed in the verifier's, the prover's combination is the verifier's accumulator. -/
theorem prover_eq_verifier {D : ℕ} (B : Module.Basis (Fin D) F K) {air : Air F} {env : Var → F}
    {main preprocessed : RowWindow F} {pv periodic : List F} {first last trans : F}
    (hp : Holds air env main preprocessed pv periodic first last trans)
    {mainK preprocessedK : RowWindow K} {periodicK : List K} {firstK lastK transK : K}
    (hv : Holds air (algebraMap F K ∘ env) mainK preprocessedK (pv.map (algebraMap F K)) periodicK
      firstK lastK transK) (α : K) :
    ∃ l, get_constraint_layout air (AirLayout.from_air air) = .ok l ∧
      finalize_constraints B (l.decompose_alpha B α).1 (l.decompose_alpha B α).2
        (air.eval (proverFolder main preprocessed pv periodic first last trans) []) [] =
      some (air.eval (verifierFolder mainK preprocessedK pv periodicK firstK lastK transK α) 0) :=
  Plonky3Lean.Proofs.UniStark.prover_eq_verifier B hp hv α

end folders

/-! ## The STARK's selector values -/

section selectors

variable {F : Type _} [Field F]

/-- On a row of the trace, a selector of the STARK vanishes exactly where the 0/1 selector does. -/
theorem starkRowEnv_eq_zero_iff {T : Instance F} {ω : F} (hω : IsPrimitiveRoot ω T.height)
    (hn : (T.height : F) ≠ 0) {i : ℕ} (hi : i < T.height) {v : Var} (hv : IsSelector v) :
    starkRowEnv T ω i v = 0 ↔ rowEnv T i v = 0 :=
  Plonky3Lean.Proofs.UniStark.starkRowEnv_eq_zero_iff hω hn hi hv

/-- On constraints in selector form, the STARK's relation is the AIR's. -/
theorem satisfiesStark_iff {C : List (MvPolynomial Var F)} {T : Instance F} {ω : F}
    (hω : IsPrimitiveRoot ω T.height) (hn : (T.height : F) ≠ 0)
    (hC : ∀ c ∈ C, SelectorSeparated c) : SatisfiesStark C T ω ↔ Satisfies C T :=
  Plonky3Lean.Proofs.UniStark.satisfiesStark_iff hω hn hC

/-- When (1 - n)^n != 1, the two semantics disagree in both directions.

The trace with (a, b) = (1, -1) on row 0 satisfies the AIR, and the STARK rejects it.

The trace with (a, b) = ((1 - omega^(n-1)) / n, -1) on row 0 satisfies the STARK, and the AIR rejects it. -/
theorem firstPlusTransition_disagree {n : ℕ} (hn : 2 ≤ n) {ω : F} (hω : IsPrimitiveRoot ω n)
    (hn0 : (n : F) ≠ 0) (h : (1 - n : F) ^ n ≠ 1) :
    (Satisfies [firstPlusTransition] (rowZeroTrace (F := F) n 1 (-1)) ∧
      ¬ SatisfiesStark [firstPlusTransition] (rowZeroTrace (F := F) n 1 (-1)) ω) ∧
    (SatisfiesStark [firstPlusTransition] (rowZeroTrace n ((1 - ω ^ (n - 1)) / n) (-1)) ω ∧
      ¬ Satisfies [firstPlusTransition] (rowZeroTrace n ((1 - ω ^ (n - 1)) / n) (-1))) :=
  Plonky3Lean.Proofs.UniStark.firstPlusTransition_disagree hn hω hn0 h

end selectors

/-! ## The constraint polynomial and its quotient -/

section quotientPoly

variable {F K : Type _} [Field F] [Field K] [Algebra F K]

/-- On a trace that satisfies the STARK's relation, the vanishing polynomial divides the combined polynomial. -/
theorem vanishing_dvd_combinedPoly {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ k) {main prep : ℕ → F[X]} {pub : ℕ → F}
    {periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ k, ∀ c, (main c).eval (s * ω ^ i) = T.main i c)
    (hprep : ∀ i < 2 ^ k, ∀ c, (prep c).eval (s * ω ^ i) = T.prep i c)
    (hpub : ∀ j, pub j = T.pub j)
    (hper : ∀ i < 2 ^ k, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    {C : List (MvPolynomial Var F)} (hsat : SatisfiesStark C T ω) (α : K) :
    vanishing (algebraMap F K s) (algebraMap F K ω) k ∣
      combinedPoly α (starkAssignK s ω k main prep pub periodic) C :=
  Plonky3Lean.Proofs.UniStark.vanishing_dvd_combinedPoly hω hs hT hmain hprep hpub hper hsat α

end quotientPoly

section quotientPolyK

variable {F : Type _} [Field F] {K : Type _} [Field K]

/-- Take a trace and its interpolant.

At the point s omega^i, the STARK's assignment takes the STARK's values on row i. -/
theorem eval_starkAssign {s ω : F} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ k) {main prep : ℕ → F[X]} {pub : ℕ → F}
    {periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ k, ∀ c, (main c).eval (s * ω ^ i) = T.main i c)
    (hprep : ∀ i < 2 ^ k, ∀ c, (prep c).eval (s * ω ^ i) = T.prep i c)
    (hpub : ∀ j, pub j = T.pub j)
    (hper : ∀ i < 2 ^ k, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    {i : ℕ} (hi : i < 2 ^ k) (v : Var) :
    (starkAssign s ω k main prep pub periodic v).eval (s * ω ^ i) = starkRowEnv T ω i v :=
  Plonky3Lean.Proofs.UniStark.eval_starkAssign hω hs hT hmain hprep hpub hper hi v

/-- When Z divides P, off the coset the quotient is s^n P / Z. -/
theorem eval_quotientPoly {s ω : K} {k : ℕ} {P : K[X]} (hdvd : vanishing s ω k ∣ P) {x : K}
    (hx : (vanishing s ω k).eval x ≠ 0) :
    (quotientPoly s ω k P).eval x = s ^ 2 ^ k * (P.eval x / (vanishing s ω k).eval x) :=
  Plonky3Lean.Proofs.UniStark.eval_quotientPoly hdvd hx

/-- A combined polynomial below (c + 1) n has a quotient below c n, for c >= 1. -/
theorem degree_quotientPoly_lt {s ω : K} {k c : ℕ} (hc : 1 ≤ c) {P : K[X]}
    (hP : P.natDegree < (c + 1) * 2 ^ k) : (quotientPoly s ω k P).degree < (c * 2 ^ k : ℕ) :=
  Plonky3Lean.Proofs.UniStark.degree_quotientPoly_lt hc hP

end quotientPolyK

/-! ## The chunks and their recombination -/

section chunks

variable {K : Type _} [Field K] [DecidableEq K] {G : Gen K} (hV : GenValid G) (qd : Coset G) (l : ℕ)

/-- Z_j vanishes at the first point of chunk j, and only there among the first points. -/
theorem vanishing_chunk_first {i j : ℕ} (hi : i < 2 ^ l) (hj : j < 2 ^ l) (hl : l ≤ qd.log_size) :
    Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift = 0 ↔ i = j :=
  Plonky3Lean.Proofs.UniStark.vanishing_chunk_first hV qd l hi hj hl

/-- Recombining the chunk interpolants of Q with the Lagrange factors gives Q, when deg Q < N. -/
theorem recombine (hN : GenNested G) (hl : l ≤ qd.log_size) (Q : K[X])
    (hQ : Q.degree < (2 ^ qd.log_size : ℕ)) (ζ : K) :
    ∑ i ∈ range (2 ^ l), (chunkL hV qd l i).eval ζ * (chunkInterp hV qd l Q i).eval ζ = Q.eval ζ :=
  Plonky3Lean.Proofs.UniStark.recombine hV qd l hN hl Q hQ ζ

/-- The transcribed recombination returns sum_i L_i(zeta) v_i, when chunk i rebuilds to v_i. -/
theorem recompose_eq {D : ℕ} {F : Type} [Field F] [Algebra F K] (B : Module.Basis (Fin D) F K)
    (hl : l ≤ qd.log_size) (chunks : List (List K)) (hlen : chunks.length = 2 ^ l) (v : ℕ → K)
    (hv : ∀ i (hi : i < 2 ^ l), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) = some (v i))
    (ζ : K) :
    recompose_quotient_from_chunks G B ((List.range (2 ^ l)).map (chunk G hV qd l)) chunks ζ =
      some (∑ i ∈ range (2 ^ l), (chunkL hV qd l i).eval ζ * v i) :=
  Plonky3Lean.Proofs.UniStark.recompose_eq hV qd l B hl chunks hlen v hv ζ

/-- With the chunk interpolants of a quotient below N, the verifier recovers the quotient at zeta. -/
theorem recompose_quotient {D : ℕ} {F : Type} [Field F] [Algebra F K] (B : Module.Basis (Fin D) F K)
    (hN : GenNested G) (hl : l ≤ qd.log_size) (Q : K[X]) (hQ : Q.degree < (2 ^ qd.log_size : ℕ))
    (chunks : List (List K)) (hlen : chunks.length = 2 ^ l)
    (hv : ∀ i (hi : i < 2 ^ l), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) =
      some ((chunkInterp hV qd l Q i).eval ζ)) :
    recompose_quotient_from_chunks G B ((List.range (2 ^ l)).map (chunk G hV qd l)) chunks ζ =
      some (Q.eval ζ) :=
  Plonky3Lean.Proofs.UniStark.recompose_quotient hV qd l B hN hl Q hQ chunks hlen hv

end chunks

/-! ## The prover's quotient values -/

section prover

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K] (G : Gen F)

/-- The selector vectors on the quotient coset hold, at each point, the STARK's selector polynomials and 1 / Z. -/
theorem selector_entries (hV : GenValid G) (hN : GenNested G) (h2 : (2 : F) ≠ 0)
    {td qd : Coset G} (h1 : td.shift = 1) (hle : td.log_size ≤ qd.log_size)
    (hdisj : qd.shift ^ 2 ^ qd.log_size ≠ 1) {sel : LagrangeSelectors (List F)}
    (hsel : Coset.selectors_on_coset G td qd = some sel) {m : ℕ} (hm : m < 2 ^ qd.log_size)
    (main prep periodic : ℕ → F[X]) (pub : ℕ → F) :
    let σ := starkAssign td.shift td.subgroup_generator td.log_size main prep pub periodic
    let x := qd.shift * qd.subgroup_generator ^ m
    sel.is_first_row.getD m 0 = (σ .isFirstRow).eval x ∧
      sel.is_last_row.getD m 0 = (σ .isLastRow).eval x ∧
      sel.is_transition.getD m 0 = (σ .isTransition).eval x ∧
      sel.inv_vanishing.getD m 0 =
        td.shift ^ 2 ^ td.log_size / (vanishing td.shift td.subgroup_generator td.log_size).eval x :=
  Plonky3Lean.Proofs.UniStark.selector_entries G hV hN h2 h1 hle hdisj hsel hm main prep periodic pub

/-- The quotient's values on the quotient coset.

Take these inputs at the points x_i of the quotient coset:

- the extended trace and the extended preprocessed trace
- a periodic table that reads each periodic polynomial at x_i.

Then the value at x_i is C_alpha(x_i) s^n / Z(x_i), for the trace subgroup's selectors. -/
theorem quotient_values_eq {D : ℕ} (B : Module.Basis (Fin D) F K) (hV : GenValid G)
    (hN : GenNested G) (h2 : (2 : F) ≠ 0) (air : Air F) {pv : List F}
    (hpv : pv.length = air.num_public_values) {td qd : Coset G} (h1 : td.shift = 1)
    (hle : td.log_size ≤ qd.log_size) (hdisj : qd.shift ^ 2 ^ qd.log_size ≠ 1)
    {tq : p3_commit.pcs.univariate.mirror.Mat F} {pq : Option (p3_commit.pcs.univariate.mirror.Mat F)}
    {main prep periodic : ℕ → F[X]} {t : PeriodicLdeTable F}
    (htw : tq.width = air.width) (hth : tq.height = 2 ^ qd.log_size)
    (htrace : ∀ i < 2 ^ qd.log_size, ∀ j : Fin tq.width,
      tq.entry i j = (main j).eval (qd.shift * qd.subgroup_generator ^ i))
    (hpq : match pq with
      | none => air.preprocessed_width = 0
      | some p => p.width = air.preprocessed_width ∧ p.height = 2 ^ qd.log_size ∧
          ∀ i < 2 ^ qd.log_size, ∀ j : Fin p.width,
            p.entry i j = (prep j).eval (qd.shift * qd.subgroup_generator ^ i))
    (hper : build_periodic_lde_table G air.periodic_columns td qd = some t)
    (hte : t.is_empty = true → air.num_periodic_columns = 0)
    (htw' : t.is_empty = false → t.width = air.num_periodic_columns)
    (htg : ∀ i, ∀ j < air.num_periodic_columns,
      t.get i j = some ((periodic j).eval (qd.shift * qd.subgroup_generator ^ i))) (α : K) :
    quotient_values G B air pv (AirLayout.from_air air) td qd tq pq α =
      some ((List.range (2 ^ qd.log_size)).map fun i =>
        combine α ((constraints air).map fun c => algebraMap F K (MvPolynomial.eval
          (fun v => (starkAssign td.shift td.subgroup_generator td.log_size main prep (pv.getD · 0)
            periodic v).eval (qd.shift * qd.subgroup_generator ^ i)) c)) *
        algebraMap F K (td.shift ^ 2 ^ td.log_size /
          (vanishing td.shift td.subgroup_generator td.log_size).eval
            (qd.shift * qd.subgroup_generator ^ i))) :=
  Plonky3Lean.Proofs.UniStark.quotient_values_eq G B hV hN h2 air hpv h1 hle hdisj htw hth htrace hpq hper hte htw' htg α

end prover

/-! ## The verifier's checks -/

section verifier

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K] (G : Gen K)

/-- The check panics exactly when zeta lies on the trace domain, for an AIR without boundary cells. -/
theorem verify_constraints_none_iff (hV : GenValid G) (air : Air F)
    (hb : air.public_boundary_io = []) (trace_local trace_next : List K)
    (pl pn : Option (List K)) (periodic : List K) (pv : List F) (c : Coset G) (ζ α q : K) :
    verify_constraints G air trace_local trace_next pl pn periodic pv c ζ α q = none ↔
      InCoset c.shift c.subgroup_generator c.log_size ζ :=
  Plonky3Lean.Proofs.UniStark.verify_constraints_none_iff G hV air hb trace_local trace_next pl pn periodic pv c ζ α q

/-- When the check returns, it accepts exactly when both hold:

- both preprocessed rows have one width
- the fold times the inverse vanishing value is the quotient. -/
theorem verify_constraints_ok_iff (air : Air F) (trace_local trace_next : List K)
    (pl pn : Option (List K)) (periodic : List K) (pv : List F) (c : Coset G) (ζ α q : K)
    (r : Except VerificationError Unit)
    (h : verify_constraints G air trace_local trace_next pl pn periodic pv c ζ α q = some r) :
    r = .ok () ↔ ∃ sels, Coset.selectors_at_point G c ζ = some sels ∧
      (pl.map List.length).getD 0 = (pn.map List.length).getD 0 ∧
      air.eval (verifierFolder ⟨trace_local, trace_next⟩ (preprocessedWindow pl pn) pv periodic
        sels.is_first_row sels.is_last_row sels.is_transition α) 0 * sels.inv_vanishing = q :=
  Plonky3Lean.Proofs.UniStark.verify_constraints_ok_iff G air trace_local trace_next pl pn periodic pv c ζ α q r h

/-- The shape checks accept exactly when every documented shape holds. -/
theorem check_shape_ok_iff (air : Air F) (opens zk : Bool) (D n bits : ℕ) (pv : List F)
    (tl : List K) (tn : Option (List K)) (qcs : List (List K)) (r : Option (List K)) (rc : Bool)
    (w : F) :
    check_shape air opens zk D n bits pv tl tn qcs r rc w = .ok () ↔
      r.isSome = zk ∧ rc = zk ∧ pv.length = air.num_public_values ∧
      (if opens then ∃ v, tn = some v ∧ v.length = air.width else tn = none) ∧
      tl.length = air.width ∧ qcs.length = n ∧ (∀ qc ∈ qcs, qc.length = D) ∧
      (∀ x ∈ r, x.length = D) ∧ (bits = 0 → w = 0) :=
  Plonky3Lean.Proofs.UniStark.check_shape_ok_iff air opens zk D n bits pv tl tn qcs r rc w

/-- Once zeta passes the domain check, the selectors at zeta do not panic. -/
theorem check_ood_point_ok (hV : GenValid G) (c : Coset G) (ζ : K)
    (h : check_ood_point G c ζ = .ok ()) : (Coset.selectors_at_point G c ζ).isSome :=
  Plonky3Lean.Proofs.UniStark.check_ood_point_ok G hV c ζ h

/-- Completeness of the check at zeta.

Take a trace that satisfies the STARK's relation on the subgroup s H, interpolated by the trace polynomials.

Open the trace honestly at a point zeta off s H.

The check then accepts the quotient s^n C_alpha / Z at zeta. -/
theorem verify_constraints_complete (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) {s ω : F}
    (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]} {pv : List F}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpv : pv.length = air.num_public_values)
    (hsat : SatisfiesStark (constraints air) T ω) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) (α : K) {pl pn : Option (List K)}
    (hpre : (pl = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 0) air.preprocessed_width ζ) ∧
      pn = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 1) air.preprocessed_width ζ)) ∨
      (pl = none ∧ pn = none ∧ air.preprocessed_width = 0)) :
    verify_constraints G air
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
      pl pn
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) .periodic
        air.num_periodic_columns ζ) pv c ζ α
      ((quotientPoly c.shift c.subgroup_generator c.log_size
        (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
          (constraints air))).eval ζ) = some (.ok ()) :=
  Plonky3Lean.Proofs.UniStark.verify_constraints_complete G hV h2 hb c hcs hcg hω hs hT hmain hprep hpub hper hpv hsat hζ α hpre

end verifier

/-! ## Completeness -/

section completeness

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- On a two-adic domain the prover and verifier size the quotient with p3-air's sizing. -/
theorem get_log_num_quotient_chunks_for_domain_eq (air : Air F) (layout : AirLayout) (n z : ℕ) :
    get_log_num_quotient_chunks_for_domain air layout n z = get_log_quotient_degree air layout n z :=
  Plonky3Lean.Proofs.UniStark.get_log_num_quotient_chunks_for_domain_eq air layout n z

/-- When every constraint fits c >= 1 chunks of n, the quotient has degree below c n. -/
theorem degree_quotient_lt {s ω : F} {k c : ℕ} (hc : 1 ≤ c) {main prep periodic : ℕ → F[X]}
    {pub : ℕ → F} {C : List (MvPolynomial Var F)}
    (hfit : ∀ e ∈ C, FitsChunks (2 ^ k) c
      (constraintPoly (starkAssign s ω k main prep pub periodic) e)) (α : K) :
    (quotientPoly (algebraMap F K s) (algebraMap F K ω) k
      (combinedPoly α (starkAssignK s ω k main prep pub periodic) C)).degree < (c * 2 ^ k : ℕ) :=
  Plonky3Lean.Proofs.UniStark.degree_quotient_lt hc hfit α

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
      (combinedPoly α (starkAssignK s ω k main prep pub periodic) C)).eval (algebraMap F K x) :=
  Plonky3Lean.Proofs.UniStark.prover_value_eq_quotient hω hs hT hmain hprep hpub hper hsat α hx

variable [DecidableEq K]

/-- Completeness of the identity at zeta.

Assume these hold:

- the trace satisfies the STARK's relation on the trace subgroup s H of order n
- every constraint fits the 2^L chunks of n that p3-air's sizing gives
- the quotient coset has order 2^L n
- each chunk's opening rebuilds to its interpolant of the quotient at zeta, as an honest scheme opens it
- zeta lies off s H.

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
          air.num_periodic_columns ζ) pv c ζ α q = some (.ok ()) :=
  Plonky3Lean.Proofs.UniStark.honest_ood_check GK hV hN h2 hb c hcs hcg hω hs hT hmain hprep hpub hper hpv hsat qd hqd hfit B α ζ chunks hlen hv hζ hpre

end completeness

/-! ## The Fiat-Shamir order -/

/-- The transcript pattern runs in this order:

- the trace, preprocessed and public steps
- alpha
- the quotient, randomization and grind steps
- zeta
- the opening argument. -/
theorem pattern_order (s : StarkShape) :
    ∃ a b, s.pattern = a ++ [.alpha] ++ b ++ [.zeta, .begin_opening_argument, .end_opening_argument] ∧
      .trace_commitment ∈ a ∧ .public_values s.num_public_values ∈ a ∧
      (s.preprocessed_width > 0 → .preprocessed_commitment ∈ a) ∧
      .quotient_commitment ∈ b ∧ (s.has_randomization → .random_commitment ∈ b) ∧
      (s.ood_pow_bits > 0 → .ood_pow s.ood_pow_bits ∈ b) ∧
      .alpha ∉ a ∧ .zeta ∉ a ∧ .zeta ∉ b :=
  Plonky3Lean.Proofs.UniStark.pattern_order s

section transcript

variable {C F E : Type}

/-- The first phase accepts exactly when a preprocessed commitment is present for a positive preprocessed width.

Alpha is then the oracle at three inputs, in order:

- the trace commitment
- the preprocessed commitment, when present
- the public values. -/
theorem constraint_phase_eq (shape : StarkShape) (H : List (Msg C F) → E) (st : List (Msg C F))
    (trace : C) (prep : Option C) (pv : List F) :
    constraint_phase shape H st trace prep pv =
      match decide (shape.preprocessed_width > 0), prep with
      | true, some c =>
        .ok (st ++ [.com trace, .com c] ++ pv.map .scalar ++ [.challenge .alpha],
          H (st ++ [.com trace, .com c] ++ pv.map .scalar))
      | false, none =>
        .ok (st ++ [.com trace] ++ pv.map .scalar ++ [.challenge .alpha],
          H (st ++ [.com trace] ++ pv.map .scalar))
      | true, none => .error .MissingPreprocessedCommitment
      | false, some _ => .error .UnexpectedPreprocessedCommitment :=
  Plonky3Lean.Proofs.UniStark.constraint_phase_eq shape H st trace prep pv

/-- When the second phase accepts, zeta is the oracle at the input state extended by these, in order:

- the quotient commitment
- the randomization commitment, when present
- the grind witness, when there is a grind. -/
theorem ood_phase_ok {shape : StarkShape} {H : List (Msg C F) → E}
    {powOk : List (Msg C F) → ℕ → F → Bool} {st st' : List (Msg C F)} {quotient : C}
    {random : Option C} {w : F} {ζ : E}
    (h : ood_phase shape H powOk st quotient random w = .ok (st', ζ)) :
    random.isSome = shape.has_randomization ∧
      ζ = H (st ++ [.com quotient] ++ (random.map .com).toList ++
        (if shape.ood_pow_bits > 0 then [.scalar w] else [])) :=
  Plonky3Lean.Proofs.UniStark.ood_phase_ok h

/-- After both phases accept, zeta is the oracle at a state that holds these:

- every commitment of the proof
- every public value
- alpha's draw. -/
theorem zeta_binds {shape : StarkShape} {H : List (Msg C F) → E}
    {powOk : List (Msg C F) → ℕ → F → Bool} {st st₁ st₂ : List (Msg C F)} {trace quotient : C}
    {prep random : Option C} {pv : List F} {w : F} {α ζ : E}
    (h₁ : constraint_phase shape H st trace prep pv = .ok (st₁, α))
    (h₂ : ood_phase shape H powOk st₁ quotient random w = .ok (st₂, ζ)) :
    ∃ pre, ζ = H pre ∧ .com trace ∈ pre ∧ (∀ x ∈ pv, .scalar x ∈ pre) ∧
      .challenge .alpha ∈ pre ∧ .com quotient ∈ pre ∧ (∀ c, prep = some c → .com c ∈ pre) ∧
      (∀ r, random = some r → .com r ∈ pre) :=
  Plonky3Lean.Proofs.UniStark.zeta_binds h₁ h₂

end transcript

/-! ## The extracted integer helpers -/

section extracted

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Proofs.UniStark.Extracted

/-- The power of two is 2^n below the word size, and absent from it on. -/
theorem checked_pow2_spec (n : Std.Usize) :
    p3_util.checked_pow2 n ⦃ o => match o with
      | .Some v => n.val < W ∧ v.val = 2 ^ n.val
      | .None => W ≤ n.val ⦄ :=
  Plonky3Lean.Proofs.UniStark.Extracted.checked_pow2_spec n

/-- The degree-bits validation, when the minimum fits the word.

Write b for the degree bits, z for the zero-knowledge bit, and [lo, hi] for the allowed range.

- below z + lo, it reports the bits too small, with that minimum
- above hi, it reports them too large, with that maximum
- at the word size or above, it reports them too large, with the word size minus one
- otherwise it returns the base domain's bits b - z, and the extended domain's size 2^b. -/
theorem validate_degree_bits_spec (air : core.option.Option Std.Usize) (db zk lo hi : Std.Usize)
    (h : zk.val + lo.val ≤ Usize.max) :
    p3_uni_stark.verifier.validate_degree_bits air db zk lo hi ⦃ r =>
      if db.val < zk.val + lo.val then
        ∃ m : Std.Usize, m.val = zk.val + lo.val ∧
          r = .Err (.DegreeBitsTooSmall air m db)
      else if hi.val < db.val then r = .Err (.DegreeBitsTooLarge air hi db)
      else if W ≤ db.val then
        ∃ m : Std.Usize, m.val = W - 1 ∧ r = .Err (.DegreeBitsTooLarge air m db)
      else ∃ a b : Std.Usize, a.val = db.val - zk.val ∧ b.val = 2 ^ db.val ∧ r = .Ok (a, b) ⦄ :=
  Plonky3Lean.Proofs.UniStark.Extracted.validate_degree_bits_spec air db zk lo hi h

/-- The opening rounds come in this order:

- the randomization round, when hiding
- the trace
- the quotient
- the preprocessed trace. -/
theorem StarkOpeningLayout_new_spec (zk : Bool) :
    p3_uni_stark.config.StarkOpeningLayout.new zk ⦃ l =>
      l.trace.val = zk.toNat ∧ l.quotient.val = zk.toNat + 1 ∧ l.preprocessed.val = zk.toNat + 2 ⦄ :=
  Plonky3Lean.Proofs.UniStark.Extracted.StarkOpeningLayout_new_spec zk

end extracted

/-! ## The zero-knowledge variant -/

/-- With the zero-knowledge bit, a degree d (2n - 1) + 1 fits 2^(L + 1) chunks of n plus one.

Here L is the sizing of d + 1. -/
theorem zk_fits (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {D : ℕ} (hD : D ≤ d * (2 * n - 1) + 1) :
    D < (2 ^ (log2_ceil_usize (max (d + 1) 2 - 1) + 1) + 1) * n :=
  Plonky3Lean.Proofs.UniStark.zk_fits d hn hD

section zk

variable {K : Type _} [Field K] [DecidableEq K] {G : Gen K} (hV : GenValid G) (qd : Coset G) (l : ℕ)

/-- Masking chunk i by Z_i times its mask leaves the recombination polynomial unchanged. -/
theorem recombination_masked (hl : l ≤ qd.log_size) (q t : ℕ → K[X]) :
    ∑ i ∈ range (2 ^ l), chunkL hV qd l i * (q i + chunkZ hV qd l i * mask hV qd l t i) =
      ∑ i ∈ range (2 ^ l), chunkL hV qd l i * q i :=
  Plonky3Lean.Proofs.UniStark.recombination_masked hV qd l hl q t

/-- A mask of degree below m keeps a chunk below the randomized chunk's size 2m. -/
theorem natDegree_masked_lt {m : ℕ} (hm : m = 2 ^ (qd.log_size - l)) {q t : K[X]} {i : ℕ}
    (hq : q.natDegree < m) (ht : t.natDegree < m) :
    (q + chunkZ hV qd l i * t).natDegree < 2 * m :=
  Plonky3Lean.Proofs.UniStark.natDegree_masked_lt hV qd l hm hq ht

/-- Openings of the masked chunks recompose to the quotient at zeta, as the unmasked openings do. -/
theorem recompose_quotient_masked : type_of% @Plonky3Lean.Proofs.UniStark.recompose_quotient_masked :=
  @Plonky3Lean.Proofs.UniStark.recompose_quotient_masked

/-- Completeness of the identity at zeta on masked quotient chunks.

Each chunk opens to its interpolant plus Z_i times its mask, the last mask balancing the others.

Then the recombined quotient is Q(zeta), and the check at zeta accepts it. -/
theorem honest_ood_check_masked : type_of% @Plonky3Lean.Proofs.UniStark.honest_ood_check_masked :=
  @Plonky3Lean.Proofs.UniStark.honest_ood_check_masked

end zk

/-! ## The full verifier -/

/-
The verifier is transcribed end to end, over the FRI transcription's sponge.

Write b for the proof's degree bits, z for the zero-knowledge bit and L for the quotient sizing.

```text
    trace domain     subgroup of order 2^b
    base domain      subgroup of order 2^(b - z)
    quotient coset   shift g, order 2^(b + L), split into 2^(L + z) chunks
    chunk domains    each committed over the trace domain
```
-/

section verify

open p3_uni_stark.verify.mirror

/-- When every step accepts, the verifier accepts.

The steps are the shape checks, the transcript and the opening argument on the claims at zeta.

The last two are the recombination and the check at zeta. -/
theorem verify_accepts : type_of% @Plonky3Lean.Proofs.UniStark.verify_accepts :=
  @Plonky3Lean.Proofs.UniStark.verify_accepts

/-- Completeness of the verifier, given the chunks' recombination.

The trace satisfies the STARK's relation on the base subgroup.

It is opened honestly at the drawn zeta, off that subgroup.

The AIR reads the next row of both traces. -/
theorem verify_complete : type_of% @Plonky3Lean.Proofs.UniStark.verify_complete :=
  @Plonky3Lean.Proofs.UniStark.verify_complete

/-- Completeness over Merkle commitments and the two-adic FRI scheme.

The quotient chunks open to their interpolants, and the FRI prover is honest on the verifier's claims. -/
theorem verify_complete_merkle : type_of% @Plonky3Lean.Proofs.UniStark.verify_complete_merkle :=
  @Plonky3Lean.Proofs.UniStark.verify_complete_merkle

/-- Completeness of the zero-knowledge path, over the hiding FRI scheme and Merkle commitments.

- The quotient chunks open to their interpolants plus Z_i times their masks.
- The verifier's claims are the public part of a randomized batch.
- The proof's hidden values are the rest of it.
- The FRI prover is honest on the randomized batch. -/
theorem verify_complete_hiding : type_of% @Plonky3Lean.Proofs.UniStark.verify_complete_hiding :=
  @Plonky3Lean.Proofs.UniStark.verify_complete_hiding

/-- The verifier never panics on any proof, under these conditions:

- the AIR binds its public values by constraints
- the largest trace height lies within the generator table
- the quotient sizing returns
- the grinding difficulty before zeta is zero, or b < 64 with 2^b < p
- the opening argument never panics
- the configured extension degree is the basis's. -/
theorem verify_ne_none : type_of% @Plonky3Lean.Proofs.UniStark.verify_ne_none :=
  @Plonky3Lean.Proofs.UniStark.verify_ne_none

/-- The grind before zeta panics exactly when it is reached at an unsafe difficulty.

It is reached when the randomization commitment matches the scheme and the difficulty is positive. -/
theorem ood_phase_run_eq_none : type_of% @Plonky3Lean.Proofs.UniStark.ood_phase_run_eq_none :=
  @Plonky3Lean.Proofs.UniStark.ood_phase_run_eq_none

/-- An AIR with boundary cells panics on every proof. -/
theorem verify_boundary_none : type_of% @Plonky3Lean.Proofs.UniStark.verify_boundary_none :=
  @Plonky3Lean.Proofs.UniStark.verify_boundary_none

/-- At the pin, a supplied verifier key is never compared with the AIR.

A key of positive width w, with an opening of width w, passes whatever width the AIR declares. -/
theorem process_preprocessed_trace_any_key :
    type_of% @Plonky3Lean.Proofs.UniStark.process_preprocessed_trace_any_key :=
  @Plonky3Lean.Proofs.UniStark.process_preprocessed_trace_any_key

end verify

/-! ## BabyBear and its quartic extension -/

section babyBear

/-- At BabyBear and its quartic extension, the two folders weight the constraints with the same powers of alpha.

This holds for any basis of the extension. -/
theorem babyBear.prover_eq_verifier {D : ℕ} (B : Module.Basis (Fin D) BabyBear.Field BabyBear.Ext4)
    {air : Air BabyBear.Field} {env : Var → BabyBear.Field} {main preprocessed : RowWindow BabyBear.Field}
    {pv periodic : List BabyBear.Field} {first last trans : BabyBear.Field}
    (hp : Holds air env main preprocessed pv periodic first last trans)
    {mainK preprocessedK : RowWindow BabyBear.Ext4} {periodicK : List BabyBear.Ext4}
    {firstK lastK transK : BabyBear.Ext4}
    (hv : Holds air (algebraMap BabyBear.Field BabyBear.Ext4 ∘ env) mainK preprocessedK
      (pv.map (algebraMap BabyBear.Field BabyBear.Ext4)) periodicK firstK lastK transK)
    (α : BabyBear.Ext4) :
    ∃ l, get_constraint_layout air (AirLayout.from_air air) = .ok l ∧
      finalize_constraints B (l.decompose_alpha B α).1 (l.decompose_alpha B α).2
        (air.eval (proverFolder main preprocessed pv periodic first last trans) []) [] =
      some (air.eval (verifierFolder mainK preprocessedK pv periodicK firstK lastK transK α) 0) :=
  Plonky3Lean.Proofs.UniStark.prover_eq_verifier B hp hv α

/-- Take a 4-row BabyBear trace and the constraint (first-row selector) a + (transition selector) b.

It separates the two semantics in both directions. -/
theorem babyBear.selectors_disagree {ω : BabyBear.Field} (hω : IsPrimitiveRoot ω 4) :
    (Satisfies [firstPlusTransition] (rowZeroTrace (F := BabyBear.Field) 4 1 (-1)) ∧
      ¬ SatisfiesStark [firstPlusTransition] (rowZeroTrace (F := BabyBear.Field) 4 1 (-1)) ω) ∧
    (SatisfiesStark [firstPlusTransition] (rowZeroTrace 4 ((1 - ω ^ (4 - 1)) / 4) (-1)) ω ∧
      ¬ Satisfies [firstPlusTransition] (rowZeroTrace 4 ((1 - ω ^ (4 - 1)) / 4) (-1))) :=
  firstPlusTransition_disagree (by norm_num) hω (by decide) (by decide)

/-- BabyBear's generator table, read in the quartic extension, is primitive and nested up to 27.

Also, 2 is invertible there.

So the recombination and completeness claims above hold for the extension's cosets. -/
theorem babyBear.ext4_table :
    ∃ t, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field BabyBear.Ext4)).adicity = 27 ∧
      GenValid (Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field BabyBear.Ext4)) ∧
      GenNested (Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field BabyBear.Ext4)) ∧
      (2 : BabyBear.Ext4) ≠ 0 := by
  obtain ⟨t, -, ht, -, ha, hV, hN, -⟩ := babyBear_facts
  refine ⟨t, ht, ha, genValid_map hV _, genNested_map hN _, ?_⟩
  rw [← map_ofNat (algebraMap BabyBear.Field BabyBear.Ext4) 2, ne_eq,
    map_eq_zero_iff _ (algebraMap BabyBear.Field BabyBear.Ext4).injective]
  exact babyBear_two_ne_zero

end babyBear

end Plonky3Lean.Claims.UniStark
