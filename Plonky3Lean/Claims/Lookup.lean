module

public import Plonky3Lean.Proofs.Lookup.Combine
public import Plonky3Lean.Proofs.Lookup.Extracted
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-lookup: claims

The count record, the indexed column check and the gadget's constructor are extracted.

The gadget, the lookup list, the prover and the checks are transcribed over a field.

The claims are stated at BabyBear F and its quartic extension K = F[X] / (X^4 - 11), where the challenges live.

The specification is LogUp, after Haböck (eprint 2022/1530) and its AIR encoding (eprint 2023/1284):

```text
    sum_k m_k / (X - v_k) = 0 in K(X)   <->   every key has net multiplicity 0

    denominator(bus, e) = alpha + (bus + 1) beta^W - fingerprint(e)
    fingerprint(e)      = sum_i e_i beta^(k - 1 - i)

    acc_0 = 0,   acc_(r+1) = acc_r + sum_c f_(r,c),   terminal = acc_(n-1) + sum_c f_(n-1,c)
    U f = V on every row,   sum of terminals = 0
```
-/

open Plonky3Lean.Spec.Lookup Plonky3Lean.Proofs.Lookup p3_lookup.mirror Polynomial Finset
  p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Lookup

local notation "F" => BabyBear.Field
local notation "K" => BabyBear.Ext4
local notation "p" => BabyBear.fieldSize

instance : CharP K p :=
  charP_of_injective_algebraMap (algebraMap F K).injective p

/-! ## The log-derivative identity -/

/-- **LogUp.** A sum of m / (X - v) vanishes in K(X) exactly when every key has net multiplicity zero. -/
theorem logDeriv_eq_zero_iff (l : List (K × K)) : logDerivSum l = 0 ↔ Balanced l :=
  logDerivSum_eq_zero_iff l

/-- **Set inclusion (Lemma 5).** With fewer than p queries, the queries lie in the table exactly when sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i) for some multiplicities. -/
theorem set_inclusion (f t : List K) (hf : f.length < p) :
    LookupRelation f t ↔
      ∃ m : List K, m.length = t.length ∧ logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) :=
  lookupRelation_iff_logDeriv f t (cast_ne_zero_of_lt p hf)

/-- **Permutations (Lemma 3).** Lists shorter than p are permutations of each other exactly when their sums of 1 / (X - x) agree. -/
theorem permutation (a b : List K) (ha : a.length < p) (hb : b.length < p) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) :=
  perm_iff_logDeriv a b (L := max a.length b.length) (le_max_left _ _) (le_max_right _ _)
    (cast_ne_zero_of_lt p (max_lt ha hb))

/-- **Overflow.** p queries of one value satisfy the identity against an empty table. -/
theorem overflow (v : K) :
    logDerivSum ((List.replicate p v).map (·, (1 : K))) = logDerivSum [] :=
  logDeriv_overflow p v

/-- **Multiplicity bound.** Integer counts whose absolute values sum below p balance in K exactly when they balance over the integers. -/
theorem integer_balance {κ : Type} [DecidableEq κ] (l : List (κ × ℤ))
    (hl : (l.map fun q => q.2.natAbs).sum < p) :
    Balanced (l.map fun q => (q.1, (q.2 : K))) ↔ Balanced l :=
  balanced_cast_iff p l hl

/-- **Lookup soundness.** With query counts whose absolute values sum below p, and provided entries of any multiplicity, a key no entry provides has integer net query count zero. -/
theorem query_without_entry {κ : Type} [DecidableEq κ] (queries : List (κ × ℤ))
    (provided : List (κ × K)) (hq : (queries.map fun q => q.2.natAbs).sum < p)
    (hbal : Balanced (queries.map (fun q => (q.1, (q.2 : K))) ++ provided))
    (k : κ) (hk : k ∉ provided.map (·.1)) : netMult queries k = 0 :=
  query_net_zero_of_not_provided p queries provided hq hbal k hk

/-! ## The height bound -/

/-- **The height bound** accepts exactly when sum_i w_i h_i < p, and panics on unequal lengths. -/
theorem height_bound (lookups : List (List (Lookup F))) (heights : List ℕ)
    (h : lookups.length = heights.length) :
    check_multiplicity_height_bound p lookups heights = some (.ok ()) ↔
      ((lookups.zip heights).map fun x => total_count_weight x.1 * x.2).sum < p :=
  check_multiplicity_height_bound_iff p lookups heights h

/-- An accepted height bound makes every bounded query count exact: when the AIRs keep each count within its weight, no key without an entry can be queried. -/
theorem height_bound_soundness {κ : Type} [DecidableEq κ] (lookups : List (List (Lookup F)))
    (heights : List ℕ) (h : lookups.length = heights.length)
    (hok : check_multiplicity_height_bound p lookups heights = some (.ok ()))
    (queries : List (κ × ℤ)) (provided : List (κ × K))
    (hweights : (queries.map fun q => q.2.natAbs).sum ≤
      ((lookups.zip heights).map fun x => total_count_weight x.1 * x.2).sum)
    (hbal : Balanced (queries.map (fun q => (q.1, (q.2 : K))) ++ provided))
    (k : κ) (hk : k ∉ provided.map (·.1)) : netMult queries k = 0 :=
  query_net_zero_of_not_provided p queries provided
    (hweights.trans_lt ((height_bound lookups heights h).1 hok)) hbal k hk

/-- A local lookup's weight is the exact sum of its tuples' weights, and a sum above u32::MAX panics. -/
theorem local_weight_exact (i : SymbolicLocalInteraction F) :
    i.tuples.foldlM (fun acc t => checked_add_u32 acc t.2.2) 0 =
      if (i.tuples.map (·.2.2)).sum ≤ U32_MAX then some (i.tuples.map (·.2.2)).sum else none :=
  local_weight i

/-! ## Fingerprints and buses -/

/-- Horner's rule computes the fingerprint. -/
theorem horner (β : K) (e : List K) : e.foldl (fun acc x => acc * β + x) 0 = fingerprint β e :=
  foldl_horner_zero β e

/-- Tuples of one width with equal fingerprint polynomials are equal. -/
theorem fingerprint_injective {e e' : List K} (hl : e.length = e'.length)
    (h : fingerprintPoly e = fingerprintPoly e') : e = e' :=
  fingerprintPoly_inj hl h

/-- A shorter tuple aliases a longer one padded with zeros: [x] and [0, x] share every fingerprint. -/
theorem fingerprint_width_alias (β x : K) : fingerprint β [x] = fingerprint β [0, x] :=
  fingerprint_pad β x

/-- The challenge table: a width of 0 panics; otherwise bus i is offset by (i + 1) beta^W. -/
theorem challenge_table (α β : K) (W n : ℕ) :
    Challenges.new α β W n =
      if W = 0 then none else
        some (α, β, (List.range n).map fun i : ℕ => α + ((i : K) + 1) * β ^ W) :=
  challenges_new α β W n

/-- **Soundness of the bus sum.** An unbalanced list of N messages, of widths at most W and one width per bus, passes on at most N (W + 1) |K| of the |K|^2 challenge pairs. -/
theorem bus_soundness (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ q ∈ msgs, q.1.2.length ≤ W)
    (hbus : ∀ q ∈ msgs, ∀ q' ∈ msgs, (q.1.1 : K) = q'.1.1 → q.1.1 = q'.1.1)
    (hwidth : ∀ q ∈ msgs, ∀ q' ∈ msgs, q.1.1 = q'.1.1 → q.1.2.length = q'.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ q ∈ msgs, busDenom x.1 x.2 W q.1.1 q.1.2 = 0) ∨ busSum x.1 x.2 W msgs = 0}
      ≤ msgs.length * (W + 1) * Fintype.card K :=
  card_bad_challenges_le msgs hW hlen hbus hwidth hunbal

/-- The same count at p3-security's rate N (W + 2) / |K|. -/
theorem bus_soundness_security (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ q ∈ msgs, q.1.2.length ≤ W)
    (hbus : ∀ q ∈ msgs, ∀ q' ∈ msgs, (q.1.1 : K) = q'.1.1 → q.1.1 = q'.1.1)
    (hwidth : ∀ q ∈ msgs, ∀ q' ∈ msgs, q.1.1 = q'.1.1 → q.1.2.length = q'.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ q ∈ msgs, busDenom x.1 x.2 W q.1.1 q.1.2 = 0) ∨ busSum x.1 x.2 W msgs = 0}
      ≤ msgs.length * (W + 2) * Fintype.card K :=
  card_bad_challenges_le_security msgs hW hlen hbus hwidth hunbal

/-! ## The running sum -/

/-- With nonzero denominators, a row's pin holds exactly for the sum of m / d. -/
theorem pin_iff (terms : List (K × K)) (h : ∀ i < terms.length, den terms i ≠ 0) (f : K) :
    Pinned terms f ↔ f = fracSum terms :=
  pinned_iff h f

/-- **A pole frees the fraction.** Two vanishing denominators on a row satisfy the pin for every value. -/
theorem pole_pair_frees (terms : List (K × K)) {i j : ℕ} (hij : i ≠ j) (hi : i < terms.length)
    (hj : j < terms.length) (hdi : den terms i = 0) (hdj : den terms j = 0) (f : K) :
    Pinned terms f :=
  pinned_of_two_zero hij hi hj hdi hdj f

/-- **A pole frees the fraction.** A vanishing denominator with a zero count satisfies the pin for every value. -/
theorem pole_zero_count_frees (terms : List (K × K)) {i : ℕ} (hi : i < terms.length)
    (hdi : den terms i = 0) (hmi : mul terms i = 0) (f : K) : Pinned terms f :=
  pinned_of_zero_mul hi hdi hmi f

/-- A single pole with a nonzero count satisfies no pin, so the honest prover fails. -/
theorem pole_blocks_prover (terms : List (K × K)) {i : ℕ} (hi : i < terms.length)
    (hdi : den terms i = 0) (hmi : mul terms i ≠ 0)
    (hrest : ∀ j < terms.length, j ≠ i → den terms j ≠ 0) (f : K) : ¬ Pinned terms f :=
  not_pinned_of_one_zero hi hdi hmi hrest f

/-- The honest fraction is pinned whenever each denominator with a nonzero count is nonzero. -/
theorem honest_pinned (terms : List (K × K))
    (h : ∀ i < terms.length, mul terms i ≠ 0 → den terms i ≠ 0) : Pinned terms (fracSum terms) :=
  pinned_fracSum h

/-- The constrained terminal is the sum of the fractions over the trace. -/
theorem terminal_is_sum (t : RunningSum K) {n w : ℕ} (h : t.Constrained n w) (hn : 0 < n) :
    t.terminal = ∑ r ∈ range n, t.rowSum w r :=
  terminal_eq_sum h hn

/-- On one row, the terminal is that row's fractions. -/
theorem terminal_height_one (t : RunningSum K) {w : ℕ} (h : t.Constrained 1 w) :
    t.terminal = t.rowSum w 0 :=
  terminal_eq_height_one h

/-- The honest accumulator and terminal satisfy the running-sum constraints. -/
theorem honest_running_sum (frac : ℕ → ℕ → K) {n : ℕ} (hn : 0 < n) (w : ℕ) :
    (honest frac n w).Constrained n w :=
  honest_constrained frac hn w

/-- **Satisfied constraints imply the bus relation.** When the verifier accepts and no denominator vanishes, the sum of m / d over every message of every AIR is zero. -/
theorem accepts_bus_relation {α β : K} {W : ℕ} {airs : List (AirMessages K)}
    {cols : ℕ → RunningSum K} (h : Accepts α β W airs cols)
    (hD : ∀ q ∈ allMessages airs, busDenom α β W q.1.1 q.1.2 ≠ 0) :
    busSum α β W (allMessages airs) = 0 :=
  busSum_eq_zero_of_accepts h hD

open Classical in
/-- **Soundness of the AIR encoding.** For unbalanced messages, at most N (W + 1) |K| challenge pairs admit permutation columns the verifier accepts, the columns chosen after the challenges. -/
theorem air_soundness (airs : List (AirMessages K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ q ∈ allMessages airs, q.1.2.length ≤ W)
    (hbus : ∀ q ∈ allMessages airs, ∀ q' ∈ allMessages airs, (q.1.1 : K) = q'.1.1 → q.1.1 = q'.1.1)
    (hwidth : ∀ q ∈ allMessages airs, ∀ q' ∈ allMessages airs, q.1.1 = q'.1.1 →
      q.1.2.length = q'.1.2.length)
    (hunbal : ¬ Balanced (allMessages airs)) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 W airs cols}
      ≤ (allMessages airs).length * (W + 1) * Fintype.card K :=
  card_accepting_le airs hW hlen hbus hwidth hunbal

/-! ## The gadget -/

/-- The constraint-side combiner is alpha minus the fingerprint. -/
theorem combine_elements_spec (elements : List (List K)) (α β : K) :
    combine_elements (fieldOps K) elements α β = elements.map fun e => α - fingerprint β e :=
  combine_elements_field elements α β

/-- The additive fold computes V = sum_i m_i prod_(j != i) d_j and U = prod_i d_i. -/
theorem combined_sum_terms_spec (elements : List (List K)) (mults : List K) (α β : K)
    (h : mults.length = elements.length) :
    compute_combined_sum_terms (fieldOps K) elements mults α β =
      some (numerator (rowTerms elements mults α β), denominator (rowTerms elements mults α β)) :=
  compute_combined_sum_terms_field elements mults α β h

/-- The exclusive fold computes N = sum_k f_k m_k and D = sum_k f_k t_k + 1 - sum_k f_k. -/
theorem exclusive_terms_spec (flags : List K) (elements : List (List K)) (mults : List K)
    (α β : K) (hf : flags.length = elements.length) (hm : mults.length = elements.length) :
    let xs := (flags.zip (elements.map fun e => α - fingerprint β e)).zip mults
    compute_exclusive_terms (fieldOps K) flags elements mults α β =
      some ((xs.map fun x => x.1.1 * x.2).sum,
        (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum)) :=
  compute_exclusive_terms_field flags elements mults α β hf hm

/-- With one active branch, the exclusive column holds that branch: N = m_j and D = t_j. -/
theorem exclusive_selects (xs : List ((K × K) × K)) {j : ℕ} (hj : j < xs.length)
    (hflag : ∀ k (h : k < xs.length), xs[k].1.1 = if k = j then 1 else 0) :
    (xs.map fun x => x.1.1 * x.2).sum = xs[j].2 ∧
      (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum) = xs[j].1.2 :=
  exclusive_one_hot xs hj hflag

/-- With no active branch, the exclusive column holds zero: N = 0 and D = 1. -/
theorem exclusive_idle (xs : List ((K × K) × K)) (hflag : ∀ x ∈ xs, x.1.1 = 0) :
    (xs.map fun x => x.1.1 * x.2).sum = 0 ∧
      (xs.map fun x => x.1.1 * x.1.2).sum + (1 - (xs.map fun x => x.1.1).sum) = 1 :=
  exclusive_none xs hflag

/-- **The fraction pin on a row** asserts U f - V for the resolved tuples and counts and the lookup's challenges. -/
theorem fraction_pin_row (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
    (periodic : List F) (perm : RowWindow K) (randomness values : List K) (s : DebugState)
    (lookup : Lookup F) (hflags : lookup.flags = none)
    (hlen : lookup.elements.length = lookup.multiplicities.length) {ev : List (List K)} {mv : List K}
    (hev : lookup.elements.mapM (fun exprs => exprs.mapM fun e =>
      (resolve (debugBuilder main preprocessed pv first last trans periodic) s e).map
        (algebraMap F K)) = some ev)
    (hmv : lookup.multiplicities.mapM (fun e =>
      (resolve (debugBuilder main preprocessed pv first last trans periodic) s e).map
        (algebraMap F K)) = some mv)
    {α β f : K} (hα : randomness[2 * lookup.column]? = some α)
    (hβ : randomness[2 * lookup.column + 1]? = some β) (hf : perm.current[lookup.column + 1]? = some f) :
    eval_fraction (rowPermBuilder main preprocessed pv first last trans periodic perm randomness values)
      s lookup =
      some (s.assert_zero (denominator (rowTerms ev mv α β) * f - numerator (rowTerms ev mv α β))) :=
  eval_fraction_additive main preprocessed pv first last trans periodic perm randomness values s
    lookup hflags hlen hev hmv hα hβ hf

/-- **The accumulator over a trace.** On n >= 1 rows, the accumulator constraints pass on every row exactly when the columns form a constrained running sum. -/
theorem accumulator_trace (main preprocessed : ℕ → RowWindow F) (pv : List F)
    (periodic : ℕ → List F) (randomness values : List K) (s : ℕ → DebugState)
    (P : ℕ → ℕ → K) {n : ℕ} (hn : 0 < n) (lookups : List (Lookup F))
    (hcol : ∀ i (h : i < lookups.length), lookups[i].column = i) (T : K) :
    (∀ r < n, ∃ s', eval_accumulator (rowPermBuilder (main r) (preprocessed r) pv
      (if r = 0 then 1 else 0) (if r = n - 1 then 1 else 0) (if r ≠ n - 1 then 1 else 0)
      (periodic r) (permWindow P n (lookups.length + 1) r) randomness values) (s r) lookups T =
        some s' ∧ s'.failures = (s r).failures) ↔
      (columnsOf P T).Constrained n lookups.length :=
  accumulator_trace_iff main preprocessed pv periodic randomness values s P hn lookups hcol T

/-- The cross-AIR check accepts exactly when the present terminals sum to zero. -/
theorem terminal_sum (t : List (Option K)) :
    verify_terminal_sum t = true ↔ (t.filterMap id).sum = 0 :=
  verify_terminal_sum_iff t

/-! ## The degree -/

/-- **The pin's degree.** With denominators of degree at most D_i n, counts at most M_i n, and a fraction at most n, U f - V has degree at most d n, for the degree d the gadget reports. -/
theorem pin_degree (terms : List (K[X] × K[X])) (f : K[X]) (N : ℕ) (D M : ℕ → ℕ)
    (hd : ∀ i < terms.length, (den terms i).natDegree ≤ D i * N)
    (hm : ∀ i < terms.length, (mul terms i).natDegree ≤ M i * N) (hf : f.natDegree ≤ N) :
    (denominator terms * f - numerator terms).natDegree ≤
      max (1 + ∑ i ∈ range terms.length, D i)
        ((range terms.length).sup fun i => M i + (∑ j ∈ range terms.length, D j) - D i) * N :=
  natDegree_pin_le terms f N D M hd hm hf

/-- A denominator alpha - fingerprint(e) has at most the degree of its widest entry. -/
theorem denominator_degree (α β : K) (e : List K[X]) (D N : ℕ)
    (he : ∀ x ∈ e, x.natDegree ≤ D * N) : (C α - fingerprint (C β) e).natDegree ≤ D * N :=
  natDegree_denom_le α β e D N he

/-- The gadget reports max(1 + sum_i D_i, max_i (deg m_i + sum_(j != i) D_j)) for an additive column. -/
theorem reported_degree (lookup : Lookup F) (hflags : lookup.flags = none)
    (hlen : lookup.multiplicities.length = lookup.elements.length) (t : ℕ) :
    constraint_degree_with_transition lookup t =
      some (max (1 + ∑ i ∈ range lookup.elements.length, tupleDegree lookup t i)
        ((range lookup.elements.length).sup fun i => countDegree lookup t i +
          (∑ j ∈ range lookup.elements.length, tupleDegree lookup t j) - tupleDegree lookup t i)) :=
  constraint_degree_additive lookup hflags hlen t

/-! ## The prover -/

/-- The prover's power-table combiner is the fingerprint, as the verifier's Horner fold is. -/
theorem prover_combiner (elts : List (SymbolicExpression F)) (β : K) {W : ℕ}
    (ctx : AirBuilder F F Unit) {v : List F} (hv : elts.mapM (resolve ctx ()) = some v)
    (hW : elts.length ≤ W) :
    combine_tuple elts (powerTable β W) ctx = some (fingerprint β (v.map (algebraMap F K))) :=
  combine_tuple_eq elts β ctx hv hW

/-- The prover's pairs on a row: denominator 1 for a zero count, else alpha - fingerprint. -/
theorem prover_pairs (ctx : AirBuilder F F Unit) (lookup : Lookup F) (hflags : lookup.flags = none)
    (α β : K) {W : ℕ} (hW : ∀ e ∈ lookup.elements, e.length ≤ W) {ev : List (List F)} {mv : List F}
    (hev : lookup.elements.mapM (fun e => e.mapM (resolve ctx ())) = some ev)
    (hmv : lookup.multiplicities.mapM (resolve ctx ()) = some mv)
    (hlen : lookup.multiplicities.length = lookup.elements.length) :
    lookup_row_terms ctx lookup α (powerTable β W) = some (proverTerms α β ev mv) :=
  lookup_row_terms_additive ctx lookup hflags α β hW hev hmv hlen

/-- The prover's fraction, inverses times counts, is the honest sum of m / d. -/
theorem prover_fraction_honest (α β : K) (ev : List (List F)) (mv : List F)
    (hlen : mv.length = ev.length) :
    dot_product ((proverTerms α β ev mv).map fun x => x.1⁻¹) ((proverTerms α β ev mv).map (·.2)) =
      fracSum (rowTerms (ev.map (·.map (algebraMap F K))) (mv.map (algebraMap F K)) α β) :=
  prover_fraction α β ev mv hlen

/-- **A periodic count stops the prover.** On every trace with a row, the generator fails for a lookup whose first count reads a periodic column, though keygen accepts it. -/
theorem prover_rejects_periodic (main : Mat F) (preprocessed : Option (Mat F)) (pv : List F)
    (lookups : List (Lookup F)) (challenges : List K) (num_threads min_task_len : ℕ)
    (hh : 0 < main.height) {lookup : Lookup F} (hl : lookup ∈ lookups) (hflags : lookup.flags = none)
    (he : lookup.elements ≠ [])
    {j : ℕ} (hm : lookup.multiplicities[0]? = some (.Leaf (.Variable ⟨.Periodic, j⟩))) :
    generate_permutation main preprocessed pv lookups challenges num_threads min_task_len = none :=
  generate_permutation_periodic main preprocessed pv lookups challenges num_threads min_task_len hh hl
    hflags he hm

/-! ## Counts and buses -/

/-- A constant count is bounded by its absolute value. -/
theorem constant_count_weight (c : ℤ) : (Count.from_i32 c : F × ℕ).2 = c.natAbs :=
  count_from_weight c

/-- A receive records the negated count with the same weight. -/
theorem receive_weight (bus : String) (r : Recorded F) (fields : List F) (c : F × ℕ) :
    (PermutationCheckBus.receive Neg.neg bus r fields c).global =
      r.global ++ [(bus, fields, (-c.1, c.2))] :=
  receive_records Neg.neg bus r fields c

/-- A table entry records the negated count with weight 0. -/
theorem table_entry_weight (bus : String) (r : Recorded F) (key : List F) (n : F) :
    (LookupBus.table_entry Neg.neg bus r key n).global = r.global ++ [(bus, key, (-n, 0))] :=
  table_entry_records Neg.neg bus r key n

/-! ## The extracted helpers -/

open Aeneas Aeneas.Std in
/-- The extracted bounded count keeps its expression and weight. -/
theorem extracted_bounded (e : F) (w : U32) :
    p3_lookup.count.Count.bounded e w = .ok ⟨e, w⟩ :=
  Extracted.bounded_spec e w

open Aeneas Aeneas.Std in
/-- The extracted provided count has weight 0. -/
theorem extracted_provided (e : F) : p3_lookup.count.Count.provided e = .ok ⟨e, 0#u32⟩ :=
  Extracted.provided_spec e

end Plonky3Lean.Claims.Lookup
