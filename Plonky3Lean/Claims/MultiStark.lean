module

public import Plonky3Lean.Proofs.MultiStark.Selectors
public import Plonky3Lean.Proofs.MultiStark.Successor
public import Plonky3Lean.Proofs.MultiStark.Zerocheck
public import Plonky3Lean.Proofs.MultiStark.Verifier
public import Plonky3Lean.Proofs.MultiStark.Transcript
public import Plonky3Lean.Proofs.MultiStark.Security
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-multi-stark: claims

Nothing is extracted: the crate's dependencies do not compile in the extraction variant.

The selectors, the next-row scatter, the zerocheck's claim and closing checks, the two transcript shapes and the AIR security terms are transcribed.

The claims are stated at the quartic extension K of BabyBear, where the challenges live.

The reduction is the multilinear AIR zerocheck of SuperSpartan (eprint 2023/552) over the Boolean hypercube:

```text
    g(b)  = sum_i beta^i sum_j alpha^(k_i - 1 - j) C_ij(b mod 2^(n_i))
    claim = sum_{b in {0,1}^m} eq(b, tau) g(b) = 0
    close:  final_sum = eq(tau, r) * g(r) + lambda * bus(r)
```

A row reads its successor, which repeats the last row, and three selectors that are exact 0/1 indicators on the cube.
-/

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultiStark
  p3_multi_stark.selectors.mirror p3_multi_stark.opening.mirror p3_multi_stark.zerocheck.mirror
  p3_multi_stark.transcript.mirror p3_multi_stark.security.mirror Finset

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.MultiStark

local notation "K" => BabyBear.Ext4

/-! ## Selectors and the next row -/

/-- **The selectors are extensions.** At any point the verifier's closed-form selectors are the multilinear extensions of the first-row, last-row and transition indicators. -/
theorem selectors_are_extensions (rs : List K) :
    BoundaryEvals.at rs =
      ⟨rowExt firstRow rs, rowExt (lastRow rs.length) rs, rowExt (transitionRow rs.length) rs⟩ :=
  at_eq_rowExt rs

/-- **The selectors are 0/1 on the cube.** At row b of a 2^n-row trace the selectors are that row's indicators. -/
theorem selectors_on_rows {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.at (vertex n b : List K) = BoundaryEvals.from_row b (2 ^ n) :=
  at_vertex hb

/-- **The prover's selectors agree.** After binding a prefix p, the prover's selectors at row b of the residual cube are the closed form at p followed by b's vertex. -/
theorem prover_selectors (p : List K) {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.from_row_with_prefix b (2 ^ n) (BoundaryEvals.at p) =
      BoundaryEvals.at (p ++ vertex n b) :=
  from_row_with_prefix_at p hb

/-- **Gated transitions.** A constraint gated by the transition selector holds on every row of the repeat-last successor exactly when it holds on every transition b -> b + 1. -/
theorem transition_gated (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, transitionRow n b * Q b (succRepeat n b) = 0) ↔
      ∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0 :=
  transition_gated_iff n Q

/-- **Ungated next-row reads do not wrap.** An ungated constraint reading the next row holds on every row exactly when it holds on every transition and on the last row paired with itself, not with row 0. -/
theorem ungated_next_row (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, Q b (succRepeat n b) = 0) ↔
      (∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0) ∧ Q (2 ^ n - 1) (2 ^ n - 1) = 0 :=
  ungated_iff n Q

/-- **The next-row opening.** The extension of the shifted table is the successor table's weighting of the table. -/
theorem next_row_opening (f : ℕ → K) (r : List K) :
    rowExt (fun b => f (succRepeat r.length b)) r =
      ∑ y ∈ range (2 ^ r.length), (nextTable r).getD y 0 * f y :=
  rowExt_succRepeat f r

/-- **Shorter tables and periodic columns read the point's suffix.** A table read on the low n bits of the row index has, at p ++ s with s of length n, the extension of the narrow table at s. -/
theorem suffix_point (f : ℕ → K) (p s : List K) :
    rowExt (fun b => f (b % 2 ^ s.length)) (p ++ s) = rowExt f s :=
  ext_mod_append f p s

/-! ## The zerocheck -/

/-- **The zerocheck splits by instance.** The zerocheck sum is the sum over instances of beta^i times the extension of instance i's batched constraint at the suffix of tau of its own arity. -/
theorem zerocheck_by_instance (batch : List (Instance K)) (α β : K) (τ : List K)
    (h : ∀ A ∈ batch, A.log_height ≤ τ.length) :
    zerocheckSum batch α β τ = ∑ i : Fin batch.length,
      β ^ (i : ℕ) * rowExt (batch[i].batched α) (τ.drop (τ.length - batch[i].log_height)) :=
  zerocheckSum_eq_suffix batch α β τ h

/-- **Completeness of the zerocheck.** A satisfied batch has a zero zerocheck sum at every alpha, beta and tau. -/
theorem zerocheck_complete {batch : List (Instance K)} (h : Satisfied batch) (α β : K) (τ : List K) :
    zerocheckSum batch α β τ = 0 :=
  zerocheckSum_of_satisfied h α β τ

/-- **Soundness of the zerocheck.** An unsatisfied batch of A instances over at most m variables, with at most k constraints each, has a zero zerocheck sum on at most (k - 1) q (q - 1)^m + q (A - 1) (q - 1)^m + q^2 m (q - 1)^(m - 1) of the q^2 (q - 1)^m draws of alpha, beta and a point with nonzero coordinates. -/
theorem zerocheck_sound {batch : List (Instance K)} (hsat : ¬ Satisfied batch) {m k : ℕ}
    (hm : ∀ A ∈ batch, A.log_height ≤ m) (hk : ∀ A ∈ batch, A.constraints.length ≤ k) :
    #{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0}
      ≤ (k - 1) * (Fintype.card K * (Fintype.card K - 1) ^ m) +
        Fintype.card K * ((batch.length - 1) * (Fintype.card K - 1) ^ m) +
        Fintype.card K * (Fintype.card K * (m * (Fintype.card K - 1) ^ (m - 1))) :=
  card_zerocheck_eq_zero_le hsat hm hk

/-- **The charged terms bound the zerocheck.** That fraction is at most the constraint-batching, air-batching and zerocheck terms p3-security charges: (k - 1)/q + (A - 1)/q + m/(q - 1). -/
theorem zerocheck_priced {batch : List (Instance K)} (hsat : ¬ Satisfied batch) {m k : ℕ}
    (hm : ∀ A ∈ batch, A.log_height ≤ m) (hk : ∀ A ∈ batch, A.constraints.length ≤ k) (d : ℕ) :
    (#{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0} : ℚ) /
      ((Fintype.card K : ℚ) ^ 2 * ((Fintype.card K - 1 : ℕ) : ℚ) ^ m) ≤
      ((zerocheckTerms ⟨batch.length, k, m, d⟩).map (Term.value (Fintype.card K))).sum :=
  zerocheck_error_le_terms hsat hm hk d

/-- **The round degree is the charged one.** The sumcheck the verifier runs has one more than the degree p3-security charges, with or without a bus. -/
theorem round_degree_charged (ds : List ℕ) (bus : Option ℕ) :
    round_degree ds bus = charged_degree ds bus + 1 :=
  round_degree_eq ds bus

/-! ## The zerocheck verifier -/

/-- **The claim check.** The sumcheck's claim is accepted exactly when the bus output is well formed and the claim is eta times the lookup claim plus lambda times the bus claim; with neither, exactly when it is zero. -/
theorem claim_check {claimed : K} {lookup : Option K} {bus : Option (Except Unit K)}
    {eta lambda : K} :
    check_claimed_sum claimed lookup bus eta lambda = .ok () ↔
      (∀ e, bus ≠ some (.error e)) ∧
        claimed = (match lookup with | none => 0 | some l => eta * l) +
          lambda * (match bus with | some (.ok c) => c | _ => 0) := by
  rcases lookup with _ | l <;> rcases bus with _ | (e | c) <;> simp [check_claimed_sum_ok]

/-- **The closing check never panics.** Given a well-formed statement, it returns a verdict for any openings, any bus family and any reduced sum. -/
theorem closing_never_panics {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K)) :
    check_constraint airs pvs log_heights main prep red bus ≠ none :=
  check_constraint_ne_none hs bus

/-- **Acceptance implies the closing equation.** An accepted closing check has a loop value g, a bus value b, zero without a bus, and a reduced sum equal to eq(tau, r) g + lambda b. -/
theorem closing_accepts {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) {bus : Option (BusTerm K)}
    (h : check_constraint airs pvs log_heights main prep red bus = some (.ok ())) :
    ∃ g ps b, accumulate red (entries airs pvs log_heights main prep) 0 1 = some (.ok (g, ps)) ∧
      ((bus = none ∧ b = 0) ∨
        ∃ f, bus = some f ∧ f (main.map (·.local_values)) (prep.map (·.local_values)) ps = .ok b) ∧
      red.final_sum = eq red.tau red.point * g + red.lambda * b :=
  check_constraint_accepts hs h

/-- **Completeness of the closing check.** Matching counts, an accepted loop, a bus value and the closing equation are accepted. -/
theorem closing_complete {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) {bus : Option (BusTerm K)}
    (hmain : main.length = airs.length) (hprep : prep.length = airs.length) {g b : K}
    {ps : List (List K)} (hacc : accumulate red (entries airs pvs log_heights main prep) 0 1 =
      some (.ok (g, ps)))
    (hbus : (bus = none ∧ b = 0) ∨
      ∃ f, bus = some f ∧ f (main.map (·.local_values)) (prep.map (·.local_values)) ps = .ok b)
    (hsum : red.final_sum = eq red.tau red.point * g + red.lambda * b) :
    check_constraint airs pvs log_heights main prep red bus = some (.ok ()) :=
  check_constraint_complete hs hmain hprep hacc hbus hsum

/-- **The loop sums one term per instance.** An accepted loop's value is the sum of the instances' terms, instance k's step taken at beta^k. -/
theorem closing_loop {red : ZerocheckReduction K} (l : List (Entry K)) {g' : K}
    {ps : List (List K)} (h : accumulate red l 0 1 = some (.ok (g', ps))) :
    ∃ ts : List (K × List K), ts.length = l.length ∧ g' = 0 + (ts.map Prod.fst).sum ∧
      ps = ts.map Prod.snd ∧ ∀ k (hk : k < l.length) (hk' : k < ts.length),
        checkAir red l[k].1 l[k].2.1 l[k].2.2.1 l[k].2.2.2.1 l[k].2.2.2.2 (1 * red.beta ^ k) =
          some (.ok ts[k]) :=
  accumulate_ok l 0 1 g' ps h

/-- **One instance's term.** An instance's step returns a term exactly when its widths match, its next rows exist and its periodic values fit; the term is beta^i times its folder value at the suffix of the point, with the closed-form selectors there, plus eta times its lookup link. -/
theorem instance_term {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) {bp t : K} {per : List K} :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp = some (.ok (t, per)) ↔
      WidthsMatch e ∧ ∃ next prep_next,
        next_row e.2.2.2.1.next_columns e.2.2.2.1.next_values e.1.main_width = some next ∧
        next_row e.2.2.2.2.next_columns e.2.2.2.2.next_values e.1.preprocessed_width =
          some prep_next ∧
        e.1.periodic (suffix red e.2.2.1) = some per ∧ t = term red e bp next prep_next per :=
  checkAir_ok he hpt

/-- **A wrong opening count is named.** More or fewer main openings than AIRs is rejected with that count mismatch. -/
theorem closing_wrong_count {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K))
    (hm : main.length ≠ airs.length) :
    check_constraint airs pvs log_heights main prep red bus =
      some (.error (.OpeningCountMismatch airs.length main.length)) :=
  check_constraint_main_count hs bus hm

/-- **A wrong width is named.** An instance whose current row has the wrong width is rejected with that width and that count. -/
theorem instance_wrong_width {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) (bp : K)
    (hw : e.2.2.2.1.local_values.length ≠ e.1.main_width) :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp =
      some (.error (.OpeningCountMismatch e.1.main_width e.2.2.2.1.local_values.length)) :=
  checkAir_width he hpt bp hw

/-! ## Fiat-Shamir -/

/-- **Everything is bound before the first challenge.** The statement's pattern is its commitments and public values, then delegation markers only; every challenge is drawn inside a delegation. -/
theorem statement_before_challenges (s : MultiStarkShape) :
    s.pattern = statementSteps s ++ delegationSteps s ∧
      (statementSteps s).all isStatementStep ∧ (delegationSteps s).all isDelegationMarker :=
  ⟨pattern_eq s, statement_steps s, delegation_only s⟩

/-- **The statement seed binds the shape.** Two statement shapes with the same pattern and instance label are equal: every arity, width, successor column, public-value count, difficulty and flag. -/
theorem statement_seed_binds {s t : MultiStarkShape} (hp : s.pattern = t.pattern)
    (hl : s.label = t.label) : s = t :=
  shape_injective hp hl

/-- **The zerocheck draws before its sumcheck, and its seed binds its shape.** -/
theorem zerocheck_transcript (s t : ZerocheckShape) :
    (∃ challenges, s.pattern = challenges ++ [.BeginSumcheck, .EndSumcheck] ∧
      .BeginSumcheck ∉ challenges ∧ .EndSumcheck ∉ challenges) ∧
      (s.label = t.label → s = t) :=
  ⟨zerocheck_pattern_eq s, zerocheck_shape_injective⟩

end Plonky3Lean.Claims.MultiStark
