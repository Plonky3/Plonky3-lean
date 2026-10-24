module

public import Plonky3Lean.Proofs.MultiStark.Selectors
public import Plonky3Lean.Proofs.MultiStark.Successor
public import Plonky3Lean.Proofs.MultiStark.Zerocheck
public import Plonky3Lean.Proofs.MultiStark.Verifier
public import Plonky3Lean.Proofs.MultiStark.Transcript
public import Plonky3Lean.Proofs.MultiStark.Security
public import Plonky3Lean.Proofs.MultiStark.FractionalGkr
public import Plonky3Lean.Proofs.MultiStark.LookupPlan
public import Plonky3Lean.Proofs.MultiStark.LogupStar
public import Plonky3Lean.Proofs.MultiStark.BusComposition
public import Plonky3Lean.Proofs.MultiStark.LookupSecurity
public import Plonky3Lean.Proofs.MultiStark.Extracted
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-multi-stark: claims

The verifier's arithmetic that needs no transcript and no AIR is extracted, generic over the field trait:

- the boundary selectors at a point and at a row;
- the successor row rebuilt from the opened columns;
- the zerocheck's free coordinates.

These parts are transcribed:

- the selectors and the next-row scatter
- the zerocheck's claim and closing checks
- the two transcript shapes
- the AIR security terms.

The transcription claims are stated at the quartic extension K of BabyBear, where the challenges live.

The reduction is the multilinear AIR zerocheck of SuperSpartan (eprint 2023/552).

It runs over the Boolean hypercube:

```text
    g(b)  = sum_i beta^i sum_j alpha^(k_i - 1 - j) C_ij(b mod 2^(n_i))
    claim = sum_{b in {0,1}^m} eq(b, tau) g(b) = 0
    close:  final_sum = eq(tau, r) * g(r) + lambda * bus(r)
```

A row reads its successor, and the last row is its own successor.

A row also reads three selectors, which are exact 0/1 indicators on the cube.
-/

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultiStark
  p3_multi_stark.selectors.mirror p3_multi_stark.opening.mirror p3_multi_stark.zerocheck.mirror
  p3_multi_stark.transcript.mirror p3_multi_stark.security.mirror Finset
open Plonky3Lean.Spec.Lookup Plonky3Lean.Spec.Sumcheck Plonky3Lean.Proofs.Sumcheck
  p3_sumcheck.generic_degree.mirror
open Plonky3Lean.Proofs.Lookup (Key)

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.MultiStark

local notation "K" => BabyBear.Ext4
instance : CharP K BabyBear.fieldSize :=
  charP_of_injective_algebraMap (algebraMap BabyBear.Field K).injective _

/-! ## Selectors and the next row -/

/-- **The selectors are extensions.**

At any point, the verifier's closed-form selectors are multilinear extensions.

They extend the first-row, last-row and transition indicators. -/
theorem selectors_are_extensions (rs : List K) :
    BoundaryEvals.at rs =
      ⟨rowExt firstRow rs, rowExt (lastRow rs.length) rs, rowExt (transitionRow rs.length) rs⟩ :=
  at_eq_rowExt rs

/-- **The selectors are 0/1 on the cube.**

At row b of a 2^n-row trace, the selectors are that row's indicators. -/
theorem selectors_on_rows {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.at (vertex n b : List K) = BoundaryEvals.from_row b (2 ^ n) :=
  at_vertex hb

/-- **The prover's selectors agree.**

Bind a prefix p.

The prover's selectors at row b of the residual cube are the closed form at p followed by b's vertex. -/
theorem prover_selectors (p : List K) {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.from_row_with_prefix b (2 ^ n) (BoundaryEvals.at p) =
      BoundaryEvals.at (p ++ vertex n b) :=
  from_row_with_prefix_at p hb

/-- **Gated transitions.**

Take a constraint gated by the transition selector, read with the repeat-last successor.

It holds on every row exactly when it holds on every transition b -> b + 1. -/
theorem transition_gated (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, transitionRow n b * Q b (succRepeat n b) = 0) ↔
      ∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0 :=
  transition_gated_iff n Q

/-- **Ungated next-row reads do not wrap.**

Take an ungated constraint reading the next row.

It holds on every row exactly when it holds on these:

- every transition b -> b + 1
- the last row paired with itself, not with row 0. -/
theorem ungated_next_row (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, Q b (succRepeat n b) = 0) ↔
      (∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0) ∧ Q (2 ^ n - 1) (2 ^ n - 1) = 0 :=
  ungated_iff n Q

/-- **The next-row opening.**

The extension of the shifted table is the table weighted by the successor table. -/
theorem next_row_opening (f : ℕ → K) (r : List K) :
    rowExt (fun b => f (succRepeat r.length b)) r =
      ∑ y ∈ range (2 ^ r.length), (nextTable r).getD y 0 * f y :=
  rowExt_succRepeat f r

/-- **Shorter tables and periodic columns read the point's suffix.**

Take a table read on the low n bits of the row index, and a point p ++ s with s of length n.

Its extension at p ++ s is the extension of the narrow table at s. -/
theorem suffix_point (f : ℕ → K) (p s : List K) :
    rowExt (fun b => f (b % 2 ^ s.length)) (p ++ s) = rowExt f s :=
  ext_mod_append f p s

/-! ## The zerocheck -/

/-- **The zerocheck splits by instance.**

The zerocheck sum is a sum over instances i of beta^i times one extension.

That extension is instance i's batched constraint, at the suffix of tau of the instance's own arity. -/
theorem zerocheck_by_instance (batch : List (Instance K)) (α β : K) (τ : List K)
    (h : ∀ A ∈ batch, A.log_height ≤ τ.length) :
    zerocheckSum batch α β τ = ∑ i : Fin batch.length,
      β ^ (i : ℕ) * rowExt (batch[i].batched α) (τ.drop (τ.length - batch[i].log_height)) :=
  zerocheckSum_eq_suffix batch α β τ h

/-- **Completeness of the zerocheck.**

A satisfied batch has a zero zerocheck sum at every alpha, beta and tau. -/
theorem zerocheck_complete {batch : List (Instance K)} (h : Satisfied batch) (α β : K) (τ : List K) :
    zerocheckSum batch α β τ = 0 :=
  zerocheckSum_of_satisfied h α β τ

/-- **Soundness of the zerocheck.**

Take an unsatisfied batch of A instances over at most m variables, with at most k constraints each.

Draw alpha, beta and a point with nonzero coordinates, among q^2 (q - 1)^m choices.

The zerocheck sum is zero on at most this many draws:

(k - 1) q (q - 1)^m + q (A - 1) (q - 1)^m + q^2 m (q - 1)^(m - 1). -/
theorem zerocheck_sound {batch : List (Instance K)} (hsat : ¬ Satisfied batch) {m k : ℕ}
    (hm : ∀ A ∈ batch, A.log_height ≤ m) (hk : ∀ A ∈ batch, A.constraints.length ≤ k) :
    #{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0}
      ≤ (k - 1) * (Fintype.card K * (Fintype.card K - 1) ^ m) +
        Fintype.card K * ((batch.length - 1) * (Fintype.card K - 1) ^ m) +
        Fintype.card K * (Fintype.card K * (m * (Fintype.card K - 1) ^ (m - 1))) :=
  card_zerocheck_eq_zero_le hsat hm hk

/-- **The charged terms bound the zerocheck.**

The fraction of bad draws is at most the terms p3-security charges:

- constraint batching, (k - 1)/q
- AIR batching, (A - 1)/q
- the zerocheck, m/(q - 1). -/
theorem zerocheck_priced {batch : List (Instance K)} (hsat : ¬ Satisfied batch) {m k : ℕ}
    (hm : ∀ A ∈ batch, A.log_height ≤ m) (hk : ∀ A ∈ batch, A.constraints.length ≤ k) (d : ℕ) :
    (#{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0} : ℚ) /
      ((Fintype.card K : ℚ) ^ 2 * ((Fintype.card K - 1 : ℕ) : ℚ) ^ m) ≤
      ((zerocheckTerms ⟨batch.length, k, m, d⟩).map (Term.value (Fintype.card K))).sum :=
  zerocheck_error_le_terms hsat hm hk d

/-- **The round degree is the charged one.**

The verifier's sumcheck has degree one more than the degree p3-security charges, with or without a bus. -/
theorem round_degree_charged (ds : List ℕ) (bus : Option ℕ) :
    round_degree ds bus = charged_degree ds bus + 1 :=
  round_degree_eq ds bus

/-! ## The zerocheck verifier -/

/-- **The claim check.**

The sumcheck's claim is accepted exactly when both hold:

- the bus output is well formed
- the claim is eta times the lookup claim plus lambda times the bus claim.

A missing lookup or bus claim counts as zero. -/
theorem claim_check {claimed : K} {lookup : Option K} {bus : Option (Except Unit K)}
    {eta lambda : K} :
    check_claimed_sum claimed lookup bus eta lambda = .ok () ↔
      (∀ e, bus ≠ some (.error e)) ∧
        claimed = (match lookup with | none => 0 | some l => eta * l) +
          lambda * (match bus with | some (.ok c) => c | _ => 0) := by
  rcases lookup with _ | l <;> rcases bus with _ | (e | c) <;> simp [check_claimed_sum_ok]

/-- **The closing check never panics.**

Given a well-formed statement, it returns a verdict for any openings, any bus family and any reduced sum. -/
theorem closing_never_panics {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K)) :
    check_constraint airs pvs log_heights main prep red bus ≠ none :=
  check_constraint_ne_none hs bus

/-- **Acceptance implies the closing equation.**

An accepted closing check has these:

- a loop value g
- a bus value b, which is zero without a bus
- a reduced sum equal to eq(tau, r) g + lambda b. -/
theorem closing_accepts {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) {bus : Option (BusTerm K)}
    (h : check_constraint airs pvs log_heights main prep red bus = some (.ok ())) :
    ∃ g ps b, accumulate red (entries airs pvs log_heights main prep) 0 1 = some (.ok (g, ps)) ∧
      ((bus = none ∧ b = 0) ∨
        ∃ f, bus = some f ∧ f (main.map (·.local_values)) (prep.map (·.local_values)) ps = .ok b) ∧
      red.final_sum = eq red.tau red.point * g + red.lambda * b :=
  check_constraint_accepts hs h

/-- **Completeness of the closing check.**

The check accepts when all of these hold:

- the opening counts match
- the loop is accepted
- the bus value exists
- the closing equation holds. -/
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

/-- **The loop sums one term per instance.**

An accepted loop's value is the sum of the instances' terms.

Instance k's step is taken at beta^k. -/
theorem closing_loop {red : ZerocheckReduction K} (l : List (Entry K)) {g' : K}
    {ps : List (List K)} (h : accumulate red l 0 1 = some (.ok (g', ps))) :
    ∃ ts : List (K × List K), ts.length = l.length ∧ g' = 0 + (ts.map Prod.fst).sum ∧
      ps = ts.map Prod.snd ∧ ∀ k (hk : k < l.length) (hk' : k < ts.length),
        checkAir red l[k].1 l[k].2.1 l[k].2.2.1 l[k].2.2.2.1 l[k].2.2.2.2 (1 * red.beta ^ k) =
          some (.ok ts[k]) :=
  accumulate_ok l 0 1 g' ps h

/-- **One instance's term.**

An instance's step returns a term exactly when all of these hold:

- its widths match
- its next rows exist
- its periodic values fit.

The term is beta^i times its folder value at the suffix of the point, plus eta times its lookup link.

The folder reads the closed-form selectors at that suffix. -/
theorem instance_term {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) {bp t : K} {per : List K} :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp = some (.ok (t, per)) ↔
      WidthsMatch e ∧ ∃ next prep_next,
        next_row e.2.2.2.1.next_columns e.2.2.2.1.next_values e.1.main_width = some next ∧
        next_row e.2.2.2.2.next_columns e.2.2.2.2.next_values e.1.preprocessed_width =
          some prep_next ∧
        e.1.periodic (suffix red e.2.2.1) = some per ∧ t = term red e bp next prep_next per :=
  checkAir_ok he hpt

/-- **A wrong opening count is named.**

More or fewer main openings than AIRs is rejected with that count mismatch. -/
theorem closing_wrong_count {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K))
    (hm : main.length ≠ airs.length) :
    check_constraint airs pvs log_heights main prep red bus =
      some (.error (.OpeningCountMismatch airs.length main.length)) :=
  check_constraint_main_count hs bus hm

/-- **A wrong width is named.**

An instance whose current row has the wrong width is rejected with that width and that count. -/
theorem instance_wrong_width {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) (bp : K)
    (hw : e.2.2.2.1.local_values.length ≠ e.1.main_width) :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp =
      some (.error (.OpeningCountMismatch e.1.main_width e.2.2.2.1.local_values.length)) :=
  checkAir_width he hpt bp hw

/-! ## Fiat-Shamir -/

/-- **Everything is bound before the first challenge.**

The statement's pattern is its commitments and public values, then delegation markers only.

Every challenge is drawn inside a delegation. -/
theorem statement_before_challenges (s : MultiStarkShape) :
    s.pattern = statementSteps s ++ delegationSteps s ∧
      (statementSteps s).all isStatementStep ∧ (delegationSteps s).all isDelegationMarker :=
  ⟨pattern_eq s, statement_steps s, delegation_only s⟩

/-- **The statement seed binds the shape.**

Two statement shapes with the same pattern and instance label are equal.

So they agree on every arity, width, successor column, public-value count, difficulty and flag. -/
theorem statement_seed_binds {s t : MultiStarkShape} (hp : s.pattern = t.pattern)
    (hl : s.label = t.label) : s = t :=
  shape_injective hp hl

/-- **The zerocheck draws before its sumcheck.**

Its seed also binds its shape. -/
theorem zerocheck_transcript (s t : ZerocheckShape) :
    (∃ challenges, s.pattern = challenges ++ [.BeginSumcheck, .EndSumcheck] ∧
      .BeginSumcheck ∉ challenges ∧ .EndSumcheck ∉ challenges) ∧
      (s.label = t.label → s = t) :=
  ⟨zerocheck_pattern_eq s, zerocheck_shape_injective⟩

/-! ## The fraction tree -/

/-- **The root of the fraction tree.**

Fold a table of 2^n fractions in halves down to one fraction.

It is a zero numerator over a nonzero denominator exactly when two things hold:

- every leaf denominator is nonzero
- the leaves sum to zero. -/
theorem fraction_root (t : ℕ → K × K) (n : ℕ) :
    (fracLevel t n 0 0).1 = 0 ∧ (fracLevel t n 0 0).2 ≠ 0 ↔
      (∀ x < 2 ^ n, (t x).2 ≠ 0) ∧ ∑ x ∈ range (2 ^ n), (t x).1 / (t x).2 = 0 :=
  root_iff t n

/-! ## The fractional-GKR verifier -/

section Gkr

open p3_multi_stark.fractional_gkr.mirror

variable {S : Type} (node : ℕ → K) (T : p3_multi_stark.fractional_gkr.mirror.VerifierTranscript K S)

/-- **The verifier.**

It checks, in order:

- the variable count, the layer count, then each layer's round count
- the root denominator.

It then panics exactly when two of the nodes 0, 1, 2, 3 coincide.

Otherwise it replays every layer from the claim (0, d) at the empty point.

It rejects at the first layer whose final check fails, and returns the last claim otherwise. -/
theorem gkr_verifier (proof : FractionGkrProof K) (n : ℕ) :
    verify_fractional_gkr node T proof n =
      if n < 1 then some (.error .InvalidVariableCount)
      else if proof.layers.length ≠ n then some (.error (.InvalidLayerCount n proof.layers.length))
      else match firstBadRound proof.layers with
        | some (i, a) => some (.error (.InvalidRoundCount i i a))
        | none =>
          if proof.root_denominator = 0 then some (.error .ZeroRootDenominator)
          else if ¬ Function.Injective (fun i : Fin 4 => node i) then none
          else
            let R := replay T [] 0 proof.root_denominator
              (T.init n proof.root_denominator) proof.layers
            some (match firstFail node R.records with
              | some k => .error (.LayerConsistency k)
              | none => .ok ⟨R.point, R.num, R.den⟩) :=
  verify_fractional_gkr_eq node T proof n

/-- **The round-count check.**

It passes exactly when layer i carries i round polynomials. -/
theorem gkr_round_counts (ls : List (FractionGkrLayerProof K)) :
    firstBadRound ls = none ↔ ∀ i (h : i < ls.length), ls[i].round_polys.length = i :=
  firstBadRound_eq_none ls

/-- **One layer of the verifier.**

The rounds reduce the batched claim N + lambda D to one value, by interpolating each cubic.

The layer then checks that value against eq(rho, r) times the batched sum of the two children.

It passes down the line through the children at the branch challenge, at the point (b, r). -/
theorem gkr_layer {weights : Fin 4 → K} (hw : RoundPolyInterpolator.new node 3 = some weights)
    (st : VerifyState K S) (k : ℕ) (l : FractionGkrLayerProof K)
    (hlen : st.point.length = l.round_polys.length) :
    verify_layer node T weights st k l =
      let L := layerRec T st.point st.numerator st.denominator st.transcript l
      some ⟨L.nextPoint, L.nextNum, L.nextDen,
        if L.passes node then st.inconsistent else st.inconsistent.or (some k),
        layerEnd T st.transcript l⟩ :=
  verify_layer_eq node T hw st k l hlen

/-- **Soundness of one layer.**

Take a passing layer that passes down the true claim of the level below.

Its own claim is then the true claim of its level, unless one of three events happened:

- lambda mapped a false claim onto the true one
- the rounds carried a false batched claim to the true value
- the branch carried false children to the true claim below. -/
theorem gkr_layer_sound (t : ℕ → K × K) (n : ℕ) {k : ℕ} (L : LayerRec K) (hpass : L.passes node)
    (hnext : L.nextNum = trueNum t n (k + 1) L.nextPoint ∧
      L.nextDen = trueDen t n (k + 1) L.nextPoint) :
    (L.num = trueNum t n k L.point ∧ L.den = trueDen t n k L.point) ∨ L.bad node t n k :=
  layer_sound node t n L hpass hnext

/-- **Lambda is bad at most once.** -/
theorem gkr_lambda_bad {N D N' D' : K} (h : N ≠ N' ∨ D ≠ D') :
    #{lam | N + lam * D = N' + lam * D'} ≤ 1 :=
  lam_bad_card h

/-- **The branch is bad at most once.** -/
theorem gkr_branch_bad (t : ℕ → K × K) (n : ℕ) {k : ℕ} {rs : List K} (hrs : rs.length = k)
    {c : SplitFraction K} (hc : c ≠ trueChildren t n k rs) :
    #{b | c.n0 + b * (c.n1 - c.n0) = trueNum t n (k + 1) (b :: rs) ∧
      c.d0 + b * (c.d1 - c.d0) = trueDen t n (k + 1) (b :: rs)} ≤ 1 :=
  branch_bad_card t n hrs hc

open scoped Classical in
/-- **The rounds are bad rarely.**

Take a false batched claim at layer k, and any causal strategy for the round polynomials.

At most 3 k |K|^(k - 1) of the |K|^k challenge vectors carry it to the true value. -/
theorem gkr_rounds_bad (t : ℕ → K × K) (n : ℕ) (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin 4 => node i) {k : ℕ} (hk : k < n) {ρ : List K}
    (hρ : ρ.length = k) {num den lam : K}
    (hb : num + lam * den ≠ trueNum t n k ρ + lam * trueDen t n k ρ)
    (M : Fin k → (Fin k → K) → Fin 3 → K) (hM : Causal M) :
    #{r | finalClaim (decGen node 3) (num + lam * den) (List.ofFn fun i => M i r) (List.ofFn r) =
      eq ρ (List.ofFn r) * (trueChildren t n k (List.ofFn r)).gate lam} * Fintype.card K ≤
        k * 3 * Fintype.card K ^ k :=
  round_bad_card node t n h0 h1 hinj hk hρ hb M hM

/-- **Completeness of one layer.**

From the true batched claim, the honest round polynomials replay to the right side of the check.

That right side reads the true children, whose line at any branch is the true claim below. -/
theorem gkr_layer_complete (t : ℕ → K × K) (n : ℕ) (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin 4 => node i) {k : ℕ} (hk : k < n) {ρ : List K}
    (hρ : ρ.length = k) (lam : K) (r : Fin k → K) :
    finalClaim (decGen node 3) (trueNum t n k ρ + lam * trueDen t n k ρ)
        (List.ofFn fun i => encGen node (honestProver (levelPoly t n k ρ lam) i r)) (List.ofFn r) =
      eq ρ (List.ofFn r) * (trueChildren t n k (List.ofFn r)).gate lam ∧
    ∀ b, (trueChildren t n k (List.ofFn r)).n0 + b * ((trueChildren t n k (List.ofFn r)).n1 -
        (trueChildren t n k (List.ofFn r)).n0) = trueNum t n (k + 1) (b :: List.ofFn r) ∧
      (trueChildren t n k (List.ofFn r)).d0 + b * ((trueChildren t n k (List.ofFn r)).d1 -
        (trueChildren t n k (List.ofFn r)).d0) = trueDen t n (k + 1) (b :: List.ofFn r) :=
  ⟨layer_complete node t n h0 h1 hinj hk hρ lam r,
    fun b => trueChildren_line t n (by simp) b⟩

/-- **Soundness of the fractional-GKR verifier.**

Take an accepting run whose output claim is the true extension of the leaves at the output point.

Then every leaf denominator is nonzero and the leaves sum to zero.

Otherwise some layer i had one of its three events. -/
theorem gkr_sound (t : ℕ → K × K) (n : ℕ) {proof : FractionGkrProof K} {out : FractionGkrOutput K}
    (hacc : verify_fractional_gkr node T proof n = some (.ok out))
    (hnum : out.numerator = rowExt (fun x => (t x).1) out.point)
    (hden : out.denominator = rowExt (fun x => (t x).2) out.point) :
    ((∀ x < 2 ^ n, (t x).2 ≠ 0) ∧ ∑ x ∈ range (2 ^ n), (t x).1 / (t x).2 = 0) ∨
      ∃ i, ∃ h : i < (replay T [] 0 proof.root_denominator
          (T.init n proof.root_denominator) proof.layers).records.length,
        ((replay T [] 0 proof.root_denominator
          (T.init n proof.root_denominator) proof.layers).records[i]).bad node t n i :=
  verify_sound node T t n hacc hnum hden

end Gkr

/-! ## The lookup link -/

section Link

open p3_multi_stark.lookup.mirror

/-- **The bus capacity.**

The plan's bus-count check passes exactly when the coefficients 1, ..., B of beta^W are distinct. -/
theorem bus_capacity (B : ℕ) :
    bus_capacity_ok BabyBear.fieldSize B = true ↔ ∀ i < B, ∀ j < B, ((i : K) + 1 = (j : K) + 1 → i = j) :=
  bus_capacity_ok_iff BabyBear.fieldSize B

/-- **Placement.**

Instances sorted by decreasing height, placed from zero, own aligned blocks.

The blocks never overlap and fit the next power of two. -/
theorem lookup_placed (insts : List LookupInstancePlan)
    (hs : insts.Pairwise fun a b => b.num_variables ≤ a.num_variables) (m d : ℕ → ℕ → ℕ → K) :
    Placed (planFracBlocks (place 0 insts).1 m d) (log2_ceil_usize (place 0 insts).2) :=
  plan_placed insts hs m d

/-- **The verifier's weights.**

For an instance at an offset its height divides, the verifier computes eq(vertex c, prefix).

There is one weight per tuple, for the blocks c in order. -/
theorem lookup_weights {M : ℕ} {point : List K} {inst : LookupInstancePlan}
    (hn : inst.num_variables ≤ M) (hlen : point.length = M) (hpl : M - inst.num_variables < 64)
    (hfit : inst.base_offset / 2 ^ inst.num_variables + inst.tuple_counts.sum ≤
      2 ^ (M - inst.num_variables)) :
    ∃ ws, blockWeights (F := K) M point inst = some ws ∧
      ws.flatten = (List.range inst.tuple_counts.sum).map fun t =>
        eq (vertex (M - inst.num_variables) (inst.base_offset / 2 ^ inst.num_variables + t))
          (point.take (M - inst.num_variables)) :=
  blockWeights_eq hn hlen hpl hfit

/-- **The link.**

The folded claim N(q) + theta (D(q) - 1) is the sum, over the blocks, of each block's share.

A block's share is its weight times m~ + theta (d~ - 1), read at the point's suffix.

The padding drops out. -/
theorem lookup_link (insts : List LookupInstancePlan)
    (hs : insts.Pairwise fun a b => b.num_variables ≤ a.num_variables) (m d : ℕ → ℕ → ℕ → K)
    (q : List K) (hq : q.length = log2_ceil_usize (place 0 insts).2) (θ : K) :
    claimed_sum (rowExt (numTable (planFracBlocks (place 0 insts).1 m d)) q)
        (rowExt (denTable (planFracBlocks (place 0 insts).1 m d)) q) θ =
      ((planBlocks (place 0 insts).1).map fun nc =>
        eq (vertex (q.length - nc.1) nc.2) (q.take (q.length - nc.1)) *
          (rowExt (m nc.1 nc.2) (q.drop (q.length - nc.1)) +
            θ * (rowExt (d nc.1 nc.2) (q.drop (q.length - nc.1)) - 1))).sum :=
  plan_link insts hs m d q hq θ

/-- **The leaf sum.**

The leaves of placed blocks sum to the sum, over every block and row, of m / d. -/
theorem lookup_leaf_sum {bs : List (FracBlock K)} {M : ℕ} (hp : Placed bs M) :
    ∑ x ∈ range (2 ^ M), numTable bs x / denTable bs x =
      (bs.map fun b => ∑ y ∈ range (2 ^ b.n), b.m y / b.d y).sum :=
  leaf_sum hp

/-- **The leaf denominators.**

On placed blocks, every leaf denominator is nonzero exactly when every block's is. -/
theorem lookup_leaf_denominators {bs : List (FracBlock K)} {M : ℕ} (hp : Placed bs M) :
    (∀ x < 2 ^ M, denTable bs x ≠ 0) ↔ ∀ b ∈ bs, ∀ y < 2 ^ b.n, b.d y ≠ 0 :=
  leaf_den_iff hp

/-- **The denominator opening.**

The padded denominator's opening is the blocks' openings, each times its weight.

The padding adds one minus the sum of the weights. -/
theorem padded_denominator (bs : List (FracBlock K)) (q : List K)
    (hb : ∀ b ∈ bs, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n)) :
    rowExt (denTable bs) q =
      (bs.map fun b => b.weight q * rowExt b.d (q.drop (q.length - b.n))).sum +
        (1 - (bs.map fun b => b.weight q).sum) :=
  rowExt_denTable bs q hb

end Link

/-! ## The indexed lookup -/

section LogupStar

open p3_multi_stark.logup_star.mirror

/-- **The closed form is the extension.**

For a point of at most 64 coordinates, sum_s y_s iota(2^(m - 1 - s)) is the extension of the embedding. -/
theorem position_closed_form (node : ℕ → K) (y : List K) (hy : y.length ≤ 64) :
    eval (F := K) node y = rowExt (fun v => embed node v) y := by
  simpa using eval_eq_rowExt node y hy

/-- **The size check.**

Over BabyBear, of 31 bits, a table that fits has distinct embeddings for its entries. -/
theorem position_fits {m : ℕ} (hfit : fits 31 m = true) {v w : ℕ} (hv : v < 2 ^ m) (hw : w < 2 ^ m)
    (h : embed (fun i => (i : BabyBear.Field)) v = embed (fun i => (i : BabyBear.Field)) w) :
    v = w :=
  fits_injective BabyBear.fieldSize (by norm_num [BabyBear.fieldSize]) (by norm_num) hfit hv hw h

/-- **The pushforward identity.**

The readers' sum of w / (X - I), minus the table's sum of Y / (X - iota), vanishes in K(X).

That holds exactly when two things hold:

- the table's weight on each entry is the readers' net weight on its embedding
- every other key carries net weight zero. -/
theorem pushforward_identity (msgs : List (K × K)) (ι Y : ℕ → K) (m : ℕ)
    (hinj : ∀ v < 2 ^ m, ∀ w < 2 ^ m, ι v = ι w → v = w) :
    logDerivSum (msgs ++ tableMsgs ι Y m) = 0 ↔
      (∀ v < 2 ^ m, Y v = netMult msgs (ι v)) ∧
        ∀ a, (∀ v < 2 ^ m, ι v ≠ a) → netMult msgs a = 0 :=
  logDerivSum_eq_zero_iff_pushforward msgs ι Y m hinj

/-- **The claimed identity.**

Weigh reader j's rows by rho^j eq(r_j, i), and keep its positions inside the table.

The inner product of the pushforward with T is then the readers' batched claim.

```text
    sum_v Y(v) T(v)  =  sum_j rho^j X_j~(r_j),     X_j(i) = T(pos_j(i))
``` -/
theorem logup_star_claim {J : ℕ} (r : Fin J → List K) (pos : Fin J → ℕ → ℕ) (ρ : K) (T : ℕ → K)
    {m : ℕ} (hpos : ∀ j, ∀ i < 2 ^ (r j).length, pos j i < 2 ^ m) :
    ∑ v ∈ range (2 ^ m),
        pushforward (fun j => (r j).length) pos
          (fun j i => ρ ^ (j : ℕ) * eq (vertex (r j).length i) (r j)) v * T v =
      ∑ j : Fin J, ρ ^ (j : ℕ) * rowExt (fun i => T (pos j i)) (r j) :=
  pushforward_claim r pos ρ T hpos

end LogupStar

/-! ## The bus family -/

section BusFamily

open p3_multi_stark.bus.mirror

/-- **The closing value.**

With the plan's dimensions and every factor evaluating, the closing value is the sum of the share terms.

The push shares come first, then the pull shares. -/
theorem bus_closing (shares : List TerminalShare) {M H : ℕ}
    (factor : TerminalShare → List K → Except Unit K) {pp : List K} (lam : K) {r : List K}
    (h1 : M ≤ r.length) (h2 : pp.length = H) (v : TerminalShare → K)
    (hv : ∀ s ∈ shares, shareTerm H factor pp lam r s = .ok (v s)) :
    terminal_composition shares M H factor pp lam r =
      .ok (((shares.filter (!·.pull) ++ shares.filter (·.pull)).map v).sum) :=
  terminal_composition_eq shares factor lam h1 h2 v hv

/-- **One share's term.**

It is the direction weight, times eq(c, q_prefix), times the product of the unused coordinates.

It is then times eq(q_rows, r_rows), and times the factor minus one. -/
theorem bus_share_term (H : ℕ) (factor : TerminalShare → List K → Except Unit K) (pp : List K)
    (lam : K) (r : List K) (s : TerminalShare) (hrow : s.row_variables ≤ r.length)
    (hpp : s.prefix_variables + s.row_variables = pp.length)
    (hidx : s.prefix_index < 2 ^ s.prefix_variables) (h64 : s.prefix_index < 2 ^ 64) {f : K}
    (hf : factor s (r.drop (r.length - s.row_variables)) = .ok f) :
    shareTerm H factor pp lam r s = .ok ((if s.pull then lam else 1) *
      eq (vertex s.prefix_variables s.prefix_index) (pp.take s.prefix_variables) *
      (r.take (r.length - s.row_variables)).prod *
      eq (pp.drop s.prefix_variables) (r.drop (r.length - s.row_variables)) * (f - 1)) :=
  shareTerm_eq H factor pp lam r s hrow hpp hidx h64 hf

/-- **The cube sum of the bus family.**

Lift every block of the two product trees onto the shared cube, on its all-ones prefix.

The family sums over the cube to the two product claims:

```text
    (L_push(q) - 1) + lambda (L_pull(q) - 1)
``` -/
theorem bus_family (push pull : List (FracBlock K)) (q : List K) (lam : K) (M : ℕ)
    (hpush : ∀ b ∈ push, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n) ∧ b.n ≤ M)
    (hpull : ∀ b ∈ pull, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n) ∧ b.n ≤ M) :
    ∑ y ∈ range (2 ^ M),
        ((push.map fun b => b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y).sum +
          lam * (pull.map fun b => b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y).sum) =
      (rowExt (denTable push) q - 1) + lam * (rowExt (denTable pull) q - 1) :=
  bus_family_sum push pull q lam M hpush hpull

end BusFamily

/-! ## The lookup terms of the security report -/

/-- **The reduction's charge is its count of bad draws.**

Layer i has one bad lambda, 3 i bad round challenges per |K| draws, and one bad branch. -/
theorem gkr_charge (L : ℕ) : 2 * L + 3 * (L * (L - 1) / 2) = ∑ i ∈ range L, (3 * i + 2) :=
  gkr_charge_eq L

/-- **The fingerprint's soundness.**

Take an unbalanced list of N messages, at most W wide, with at most p buses and one width per bus.

Count the pairs (alpha, beta) where a denominator vanishes or the fractions sum to zero.

There are at most N (W + 2) |K| of them, out of |K|^2. -/
theorem logup_fingerprint (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ q ∈ msgs, q.1.2.length ≤ W)
    (hbus : ∀ a ∈ msgs, ∀ b ∈ msgs, (a.1.1 : K) = b.1.1 → a.1.1 = b.1.1)
    (hwidth : ∀ a ∈ msgs, ∀ b ∈ msgs, a.1.1 = b.1.1 → a.1.2.length = b.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ q ∈ msgs, msDenom x.1 x.2 W q.1.1 q.1.2 = 0) ∨
        (msgs.map fun q => q.2 / msDenom x.1 x.2 W q.1.1 q.1.2).sum = 0} ≤
      msgs.length * (W + 2) * Fintype.card K :=
  logup_bad_card msgs hW hlen hbus hwidth hunbal

/-! ## The extracted verifier arithmetic

Each claim holds for any field L and any instance of the field trait.

It assumes one thing of that instance: each member the code calls computes the operation it names.
-/

section Extracted

open CoreModels Aeneas Aeneas.Std Plonky3Lean.Proofs.MultiStark.Extracted

variable {L : Type} [Field L] {inst : p3_field.field.Field L}

/-- The shipped selectors at a point are the multilinear extensions of the first-row, last-row and transition indicators.

They never panic. -/
theorem selectors.BoundaryEvals.at.eq_spec (h : FieldComputes inst) (rs : Slice L) :
    p3_multi_stark.selectors.BoundaryEvals.at inst rs =
      .ok ⟨rowExt firstRow rs.val, rowExt (lastRow rs.val.length) rs.val,
        rowExt (transitionRow rs.val.length) rs.val⟩ := by
  rw [at_eq h, at_eq_rowExt]; rfl

/-- The shipped fold of one more coordinate r multiplies the first-row selector by 1 - r and the last-row selector by r.

The transition is one minus the new last-row selector.

It never panics. -/
theorem selectors.BoundaryEvals.apply.eq_mirror (h : FieldComputes inst)
    (b : p3_multi_stark.selectors.mirror.BoundaryEvals L) (r : L) :
    p3_multi_stark.selectors.BoundaryEvals.apply inst (ofMirror b) r = .ok (ofMirror (b.apply r)) :=
  apply_eq h b r

/-- The shipped indicators of a row b of a 2^n-row trace are the selectors at b's vertex. -/
theorem selectors.BoundaryEvals.from_row.eq_spec (h : FieldComputes inst) {n : ℕ} (row height : Std.Usize)
    (hheight : height.val = 2 ^ n) (hrow : row.val < height.val) :
    p3_multi_stark.selectors.BoundaryEvals.from_row inst row height =
      .ok (ofMirror (BoundaryEvals.at (vertex n row.val : List L))) := by
  rw [from_row_eq h row height (by have := height.hBounds; scalar_tac), hheight,
    at_vertex (by omega)]

/-- The shipped indicators panic on the largest row, whose successor overflows. -/
theorem selectors.BoundaryEvals.from_row.panics (h : FieldComputes inst) (row height : Std.Usize)
    (hrow : row.val = Usize.max) :
    p3_multi_stark.selectors.BoundaryEvals.from_row inst row height = .fail .panic :=
  from_row_max h row height hrow

/-- Bind a prefix p.

The shipped selectors at row b of the 2^n-row residual cube are the selectors at p followed by b's vertex. -/
theorem selectors.BoundaryEvals.from_row_with_prefix.eq_spec (h : FieldComputes inst) {n : ℕ}
    (p : List L) (row height : Std.Usize) (hheight : height.val = 2 ^ n) (hrow : row.val < height.val) :
    p3_multi_stark.selectors.BoundaryEvals.from_row_with_prefix inst row height
        (ofMirror (BoundaryEvals.at p)) =
      .ok (ofMirror (BoundaryEvals.at (p ++ vertex n row.val))) := by
  rw [from_row_with_prefix_eq h row height (by have := height.hBounds; scalar_tac), hheight,
    from_row_with_prefix_at p (by omega)]

/-- The shipped successor row writes each claimed value into its column of a zero row, in order.

It panics exactly when a column lies past the width. -/
theorem opening.OpeningClaims.next_row.eq_mirror (h : FieldComputes inst)
    (claims : p3_multi_stark.opening.OpeningClaims L) (width : Std.Usize) :
    Agrees (p3_multi_stark.opening.OpeningClaims.next_row inst claims width)
      ((pairs (Slice.val claims.next)).foldl scatterStep (some (List.replicate width.val 0))) :=
  next_row_eq h claims width

/-- The shipped free coordinates are the cube's variables minus the lookup's, clamped at 0. -/
theorem zerocheck.transcript.ZerocheckShape.free_coordinates.eq_spec
    (s : p3_multi_stark.zerocheck.transcript.ZerocheckShape) :
    ∃ n : Std.Usize, p3_multi_stark.zerocheck.transcript.ZerocheckShape.free_coordinates s = .ok n ∧
      n.val = s.log_height.val - s.lookup_point_len.val :=
  free_coordinates_eq s

end Extracted

end Plonky3Lean.Claims.MultiStark
