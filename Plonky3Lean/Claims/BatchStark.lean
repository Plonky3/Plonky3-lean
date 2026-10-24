module

public import Plonky3Lean.Proofs.BatchStark.Accept
public import Plonky3Lean.Proofs.BatchStark.Soundness
public import Plonky3Lean.Proofs.BatchStark.Check
public import Plonky3Lean.Proofs.BatchStark.Extracted
public import Plonky3Lean.Proofs.BatchStark.Zeta
public import Plonky3Lean.Proofs.BatchStark.BusWidths
public import Plonky3Lean.Proofs.BatchStark.LogUpCount
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-batch-stark: claims

The opening count and the shape's counters are extracted.

The transcript, the challenge layout, the verifier and the debug checker are transcribed.

The claims are stated at BabyBear F and its quartic extension K, where the challenges live.

One batch proves several tables at once:

```text
    per table:   degree bits, public values, main trace, quotient chunks, openings
    shared:      one LogUp pair (alpha, beta), one bus offset per bus, one alpha, one zeta
    cross-table: the terminals of the tables with lookups sum to zero
```

The challenger is a random oracle of the messages absorbed so far.

The opening argument enters as a predicate.

Each table's check at zeta is transcribed, and compared with its constraint polynomial.
-/

open p3_batch_stark.transcript.mirror p3_batch_stark.verifier.mirror p3_batch_stark.checker.mirror
  p3_lookup.mirror p3_air.air.mirror p3_air.builder.mirror Plonky3Lean.Spec.Lookup
  Plonky3Lean.Spec.UniStark Plonky3Lean.Spec.Air Plonky3Lean.Proofs.BatchStark
  Plonky3Lean.Proofs.BatchStark.Extracted Plonky3Lean.Proofs.Lookup Finset
  p3_batch_stark.constraints.mirror p3_uni_stark.verifier.mirror p3_commit.domain.mirror
  p3_field.coset.mirror p3_dft.mirror Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.UniStark
  Plonky3Lean.Proofs.Dft Polynomial

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.BatchStark

local notation "F" => BabyBear.Field
local notation "K" => BabyBear.Ext4
local notation "p" => BabyBear.fieldSize

instance : CharP K p :=
  charP_of_injective_algebraMap (algebraMap F K).injective p

/-! ## The transcript -/

/-- **The seed binds the shape.**

Two shapes with one seed agree on:

- the instance count
- every trace and preprocessed width
- every public-value count
- the three flags
- the lookup count
- both difficulties, when they are played. -/
theorem seed_binds_shape {s s' : BatchShape} (h : s.domain_separator = s'.domain_separator) :
    s.trace_widths = s'.trace_widths ∧ s.preprocessed_widths = s'.preprocessed_widths ∧
      s.public_value_counts = s'.public_value_counts ∧
      s.has_preprocessed_commitment = s'.has_preprocessed_commitment ∧
      s.num_lookup_instances = s'.num_lookup_instances ∧
      (s.has_lookups → s.lookup_pow_bits = s'.lookup_pow_bits) ∧
      s.has_randomization_commitment = s'.has_randomization_commitment ∧
      s.ood_pow_bits = s'.ood_pow_bits :=
  domain_separator_injective h

variable {C : Type}

/-- **The replay never panics.**

Assume the shape checks accept and the lookups pass the layout's width checks.

Then the replay returns:

- when it accepts, it has played exactly the pattern
- when a grind rejects, it has played a prefix of the pattern. -/
theorem replay_never_panics {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hW : WidthsOk common.lookups.flatten)
    (H : List (Msg C F K) → K) (powOk : List (Msg C F K) → ℕ → F → Bool) :
    ∃ st r, replay cfg airs proof pvs common checked H powOk = some (st, r) ∧
      (∀ x, r = .ok x → st.played = (shapeOf cfg airs common checked).pattern) ∧
      (∀ e, r = .error e → st.played <+: (shapeOf cfg airs common checked).pattern) :=
  replay_played hS hW H powOk

/-- **The Fiat-Shamir order.**

When the replay accepts, each challenge is drawn after the messages it must bind:

- the lookup pair follows every degree bit, the main commitment and every public value
- the lookup pair also follows the preprocessed commitment and the grind
- alpha follows the pair, the permutation commitment and every terminal
- zeta follows alpha, the quotient and randomization commitments and the second grind. -/
theorem fiat_shamir_order {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    {H : List (Msg C F K) → K} {powOk : List (Msg C F K) → ℕ → F → Bool} {st : St C F K}
    {ch : List (List K)} {α ζ : K}
    (h : replay cfg airs proof pvs common checked H powOk = some (st, .ok (ch, α, ζ))) :
    let shape := shapeOf cfg airs common checked
    let pre : List (Msg C F K) :=
      preLookup shape proof.degree_bits proof.main pvs (common.preprocessed.map (·.1))
    ∃ mid : List (Msg C F K),
      (if shape.has_lookups then
        ∃ w αL βL, proof.lookup_pow_witness = some w ∧
          αL = H (pre ++ powMsgs shape.lookup_pow_bits w) ∧
          βL = H (pre ++ powMsgs shape.lookup_pow_bits w ++ [.challenge .lookup_alpha]) ∧
          lay_out_lookup_challenges 2 common.lookups αL βL = some ch ∧
          mid = pre ++ powMsgs shape.lookup_pow_bits w ++ [.challenge .lookup_alpha, .challenge .lookup_beta]
      else ch = common.lookups.map (fun _ => []) ∧ mid = pre) ∧
      α = H (mid ++ (proof.permutation.map .com).toList ++ (proof.lookup_terminals.filterMap id).map .ext) ∧
      ζ = H (mid ++ (proof.permutation.map .com).toList ++ (proof.lookup_terminals.filterMap id).map .ext ++
        [.challenge .constraint_challenge, .com proof.quotient_chunks] ++ (proof.random.map .com).toList ++
        powMsgs shape.ood_pow_bits proof.ood_pow_witness) :=
  replay_ok h

/-! ## The verifier -/

/-- **Wrong table count.**

A per-instance list whose length differs from the AIRs' is rejected first, with the count error. -/
theorem wrong_table_count (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (h : ¬ CountsOk airs proof pvs common) :
    check_shape cfg airs proof pvs common = .error .InstanceCountMismatch :=
  check_shape_count cfg airs proof pvs common h

/-- **Randomization.**

With the right counts, the next check is the hiding flag.

A randomization opening or commitment that disagrees with it is rejected with the randomization error. -/
theorem randomization_mismatch (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (hc : CountsOk airs proof pvs common)
    (h : ¬ ((∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk) ∧ proof.random.isSome = cfg.zk)) :
    check_shape cfg airs proof pvs common = .error .RandomizationError :=
  check_shape_random cfg airs proof pvs common hc h

/-- **One table's openings.**

Its checks accept exactly the documented shape:

- public values and row widths
- next rows exactly when they are read
- chunk counts and dimensions
- preprocessed rows
- permutation rows of (L + 1) D values
- a terminal exactly when the table has lookups. -/
theorem table_shape (cfg : Config) (common : CommonData C F) (air : AirInfo) (i : ℕ) (pv : List F)
    (ov : Opened K) (terminal : Option K) (n_chunks : ℕ) :
    check_instance cfg common air i pv ov terminal n_chunks = .ok () ↔
      InstanceOk cfg common air i pv ov terminal n_chunks :=
  check_instance_ok_iff cfg common air i pv ov terminal n_chunks

/-- **The permutation round.**

The instances with a nonempty permutation opening are exactly those with lookups.

They come in the prover's commit order. -/
theorem permutation_round_order {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hD : 1 ≤ cfg.dimension) :
    (List.range airs.length).filter (fun i => !(proof.opened.getD i default).permutation_local.isEmpty) =
      (List.range airs.length).filter (fun i => !(common.lookups.getD i []).isEmpty) :=
  permutation_round hS hD

/-- **The verifier never panics on a proof.**

This needs two conditions:

- every AIR binds its public values by constraints
- the cached lookups pass the layout's width checks. -/
theorem verify_never_panics (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (H : List (Msg C F K) → K)
    (powOk : List (Msg C F K) → ℕ → F → Bool) (pcsOk : List (Msg C F K) → K → Bool)
    (checkAt : ℕ → List K → K → K → Except BatchError Unit)
    (hb : airs.all (·.boundary_io_empty)) (hW : WidthsOk common.lookups.flatten) :
    verify_batch cfg airs proof pvs common H powOk pcsOk checkAt ≠ none :=
  verify_batch_ne_none cfg airs proof pvs common H powOk pcsOk checkAt hb hW

/-- **What acceptance means.**

An accepted proof satisfies all of:

- the shape checks and the height bound pass
- the replay plays the pattern
- the opening argument passes at zeta
- every table passes its check at the shared zeta and alpha
- the terminals sum to zero. -/
theorem verify_accepts {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {H : List (Msg C F K) → K}
    {powOk : List (Msg C F K) → ℕ → F → Bool} {pcsOk : List (Msg C F K) → K → Bool}
    {checkAt : ℕ → List K → K → K → Except BatchError Unit}
    (h : verify_batch cfg airs proof pvs common H powOk pcsOk checkAt = some (.ok ())) :
    ∃ checked st ch α ζ, Shaped cfg airs proof pvs common checked ∧
      replay cfg airs proof pvs common checked H powOk = some (st, .ok (ch, α, ζ)) ∧
      pcsOk st.msgs ζ ∧ (∀ i < airs.length, checkAt i (ch.getD i []) α ζ = .ok ()) ∧
      (proof.lookup_terminals.filterMap id).sum = 0 :=
  verify_batch_accepts h

/-- An accepted shape keeps the weighted height sum below p. -/
theorem accepted_height_bound {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (s : ℕ) :
    check_multiplicity_height_bound cfg.characteristic common.lookups
      (checked.base_degree_bits.map (2 ^ ·)) ≠ some (.error s) :=
  hS.height s

/-! ## The lookup challenges -/

/-- **The bus ids.**

- two lookups share an id exactly when they are the same lookup, or global lookups naming one bus
- every id is below the number of lookups
- every lookup has one payload width, at most the widest width W >= 1. -/
theorem bus_ids {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) :
    ids.map List.length = all.map List.length ∧
      (∀ a < ids.flatten.length, ∀ b < ids.flatten.length,
        ids.flatten.getD a 0 = ids.flatten.getD b 0 ↔ SameBus all.flatten a b) ∧
      (∀ a < ids.flatten.length, ids.flatten.getD a 0 < st.next_bus) ∧ st.next_bus ≤ all.flatten.length ∧
      (∀ a < all.flatten.length, ∃ w, (all.flatten[a]?.bind width) = some w ∧ w ≤ st.max_message_width) ∧
      1 ≤ st.max_message_width := by
  obtain ⟨hl, hI⟩ := busIds_spec h
  exact ⟨hl, hI.eq_iff, hI.lt, hI.bound, hI.wd, hI.max_pos⟩

/-- **The layout.**

Lookup j of instance i reads alpha + (id + 1) beta^W and then beta. -/
theorem challenge_layout {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (α β : K) :
    lay_out_lookup_challenges 2 all α β =
      some (ids.map fun l : List ℕ => l.flatMap fun b : ℕ => [α + ((b : K) + 1) * β ^ st.max_message_width, β]) :=
  lay_out_eq h α β

/-- **When the layout panics.**

It panics exactly when one of two width mismatches occurs:

- a lookup's tuples differ in width
- two global lookups naming one bus differ in width. -/
theorem layout_panics (all : List (List (Lookup F))) (α β : K) :
    lay_out_lookup_challenges 2 all α β = none ↔ ¬ WidthsOk all.flatten :=
  lay_out_none_iff all α β

/-- The combiner on a lookup's bus offset is the domain-separated denominator of its bus. -/
theorem combiner_is_bus_denominator (α β : K) (W b : ℕ) (e : List K) :
    (α + ((b : K) + 1) * β ^ W) - fingerprint β e = busDenom α β W b e :=
  combiner_eq_busDenom α β W b e

open Classical in
/-- **The cross-table bus.**

Take messages keyed by the layout's bus ids, with at most p lookups.

An unbalanced bus passes on at most N (W + 1) |K| of the |K|^2 challenge pairs.

This holds whatever columns the prover picks after seeing the pair. -/
theorem cross_table_soundness {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (hp : all.flatten.length ≤ p) (airs : List (AirMessages K))
    (hkey : KeyedBy all.flatten ids.flatten (allMessages airs))
    (hunbal : ¬ Balanced (allMessages airs)) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 st.max_message_width airs cols}
      ≤ (allMessages airs).length * (st.max_message_width + 1) * Fintype.card K :=
  batch_soundness h hp airs hkey hunbal

/-! ## The opening count -/

open Aeneas Aeneas.Std CoreModels in
/-- p3-uni-stark's extracted count is its formula when that fits the word. -/
theorem uni_stark_opening_count (mw pw q D : Aeneas.Std.Usize) (mn pn : Bool)
    (o : p3_uni_stark.security.OpeningShape)
    (h : uniCount mw.val mn pw.val pn q.val D.val o ≤ Aeneas.Std.Usize.max) :
    p3_uni_stark.security.num_batched_openings mw mn pw pn q D o ⦃ r =>
      r.val = uniCount mw.val mn pw.val pn q.val D.val o ⦄ :=
  uni_spec mw pw q D mn pn o h

open Aeneas Aeneas.Std CoreModels in
/-- p3-batch-stark's extracted count is its formula when that fits the word and D >= 1. -/
theorem batch_opening_count (mw pw q L D : Aeneas.Std.Usize) (mn pn : Bool)
    (o : p3_uni_stark.security.OpeningShape) (hD : 1 ≤ D.val)
    (h : batchCount mw.val mn pw.val pn q.val L.val D.val o ≤ Aeneas.Std.Usize.max) :
    p3_batch_stark.security.num_batched_openings mw mn pw pn q L D o ⦃ r =>
      r.val = batchCount mw.val mn pw.val pn q.val L.val D.val o ⦄ :=
  batch_spec mw pw q L D mn pn o hD h

/-- **The count is a sum over the committed matrices.**

Each matrix contributes its width times its points, and the sum is multiplied by the powers per pair. -/
theorem opening_count_sum (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q L D : ℕ)
    (o : p3_uni_stark.security.OpeningShape) :
    batchCount mw mn pw pn q L D o =
      ((matrices mw mn pw pn q L D o).map fun m => m.1 * m.2).sum * shapePpo o :=
  batchCount_eq mw mn pw pn q L D o

/-! ## The debug checker -/

/-- **The checker.**

With traces of one height, it passes exactly when every row passes its constraints.

Both the AIR and the lookup constraints are evaluated with the 0/1 selectors. -/
theorem checker_accepts (air : Air F) (main : Mat F) (prep : Option (Mat F)) (perm : Mat K)
    (ch vals : List K) (pv : List F) (lookups : List (Lookup F)) :
    p3_batch_stark.checker.mirror.check_constraints air main prep perm ch vals pv lookups = some () ↔
      (∀ q ∈ prep, q.height = main.height) ∧ perm.height = main.height ∧
      ∀ r < main.height, ∃ s, eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r)
        (DebugState.new r) lookups = some s ∧ s.failures = [] :=
  check_constraints_eq_some air main prep perm ch vals pv lookups

/-- **A selector in a lookup count.**

The prover's fraction is m / d, with m the 0/1 selector value.

It satisfies the STARK's pin exactly when the STARK's selector value is also m. -/
theorem selector_count_pin (T : Instance K) (ω : K) (i : ℕ) (v : Var) {d : K} (hd : d ≠ 0) :
    Pinned [(d, starkRowEnv T ω i v)] (rowEnv T i v / d) ↔ starkRowEnv T ω i v = rowEnv T i v :=
  selector_count_pinned_iff T ω i v hd

/-- **The transition selector in a count stops the honest prover on row 0.** -/
theorem selector_count_row0 (T : Instance K) {ω : K} (hω : IsPrimitiveRoot ω T.height) (hn : 2 ≤ T.height)
    {d : K} (hd : d ≠ 0) :
    starkRowEnv T ω 0 .isTransition ≠ rowEnv T 0 .isTransition ∧
      ¬ Pinned [(d, starkRowEnv T ω 0 .isTransition)] (rowEnv T 0 .isTransition / d) :=
  transition_row0_ne T hω hn hd

/-- **The first-row selector in a count.**

On 8 rows, the STARK counts a first-row message 8 times.

So a bus that sends it under that count and receives it once per row balances.

With 0/1 counts, the same bus is unbalanced. -/
theorem selector_count_balance (k : ℕ × List K) :
    Balanced ([(k, (8 : K))] ++ List.replicate 8 (k, -1)) ∧
      ¬ Balanced ([(k, (1 : K))] ++ List.replicate 8 (k, -1)) := by
  have h7 : (7 : K) ≠ 0 := by
    have := (CharP.cast_eq_zero_iff K p 7).not.2 (by simp [BabyBear.fieldSize])
    exact_mod_cast this
  refine ⟨fun k' => ?_, fun hb => h7 ?_⟩
  · by_cases h : k = k'
    · subst h; simp [netMult]; norm_num
    · simp [netMult, h]
  · have := hb k
    simp [netMult] at this
    linear_combination -this

/-! ## The check at zeta -/

section zeta

variable (G : Gen K)

/-- **The check at zeta, against the constraint polynomial.**

Take one table with its trace coset s H of size n, its trace polynomials and its permutation columns.

Open them honestly at zeta, off s H.

The verifier folds the AIR's constraints, then the lookup constraints, with the Lagrange selectors at zeta.

That fold is C(zeta), with C the table's combined constraint polynomial:

- the AIR's constraint polynomials
- the pin D_c P_(c+1) - N_c of each lookup column c
- L_first P_0, for the accumulator P_0
- L_trans (P_0(omega X) - P_0 - sum_c P_(c+1))
- L_last (T - P_0 - sum_c P_(c+1)), for the terminal T.

So the check accepts exactly when C(zeta) s^n / Z(zeta) is the quotient value. -/
theorem check_at_zeta (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) (main prep periodic : ℕ → K[X]) {pv : List F}
    (hpv : pv.length = air.num_public_values) (P : ℕ → K[X]) {ch : List K}
    {lookups : List (Lookup F)} (hL : LaidOut air ch lookups) (T α q : K) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) :
    let σ := instAssign G c main prep periodic pv
    let perm := permOpening c.subgroup_generator ζ P lookups
    verify_constraints_with_lookups G air (openRow σ (.main 0) air.width ζ)
      (openRow σ (.main 1) air.width ζ) (openRow σ (.prep 0) air.preprocessed_width ζ)
      (openRow σ (.prep 1) air.preprocessed_width ζ) perm.current perm.next ch
      (if lookups = [] then [] else [T]) (openRow σ .periodic air.num_periodic_columns ζ) lookups pv c
      ζ α q =
      some (if (instancePoly G air c main prep periodic pv P ch T α lookups).eval ζ *
          (c.shift ^ 2 ^ c.log_size / (vanishing c.shift c.subgroup_generator c.log_size).eval ζ) = q
        then .ok () else .error .OodEvaluationMismatch) :=
  verify_constraints_with_lookups_eq G hV h2 hb c main prep periodic hpv P hL T α q hζ

/-- A zeta on the trace coset is rejected with the domain error, whatever the openings. -/
theorem check_at_zeta_in_domain (hV : GenValid G) {air : Air F} (hb : air.public_boundary_io = [])
    (tl tn pl pn ml mn ch vals per : List K) (lookups : List (Lookup F)) (pv : List F) (c : Coset G)
    {ζ : K} (hζ : InCoset c.shift c.subgroup_generator c.log_size ζ) (α q : K) :
    verify_constraints_with_lookups G air tl tn pl pn ml mn ch vals per lookups pv c ζ α q =
      some (.error .OodPointInDomain) :=
  verify_constraints_with_lookups_in_domain G hV hb tl tn pl pn ml mn ch vals per lookups pv c hζ α q

/-- **Completeness at zeta.**

Assume Z divides the table's constraint polynomial C.

Then the honest quotient s^n C / Z passes the check at zeta. -/
theorem check_at_zeta_complete (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) (main prep periodic : ℕ → K[X]) {pv : List F}
    (hpv : pv.length = air.num_public_values) (P : ℕ → K[X]) {ch : List K}
    {lookups : List (Lookup F)} (hL : LaidOut air ch lookups) (T α : K) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ)
    (hdvd : vanishing c.shift c.subgroup_generator c.log_size ∣
      instancePoly G air c main prep periodic pv P ch T α lookups) :
    let σ := instAssign G c main prep periodic pv
    let perm := permOpening c.subgroup_generator ζ P lookups
    verify_constraints_with_lookups G air (openRow σ (.main 0) air.width ζ)
      (openRow σ (.main 1) air.width ζ) (openRow σ (.prep 0) air.preprocessed_width ζ)
      (openRow σ (.prep 1) air.preprocessed_width ζ) perm.current perm.next ch
      (if lookups = [] then [] else [T]) (openRow σ .periodic air.num_periodic_columns ζ) lookups pv c
      ζ α ((quotientPoly c.shift c.subgroup_generator c.log_size
        (instancePoly G air c main prep periodic pv P ch T α lookups)).eval ζ) = some (.ok ()) :=
  verify_constraints_with_lookups_complete G hV h2 hb c main prep periodic hpv P hL T α hζ hdvd

/-- **Several tables at one zeta.**

Each table has its own trace coset, of its own size.

All share zeta and alpha.

Every check passes exactly when each table's constraint polynomial meets its quotient at zeta. -/
theorem checks_at_zeta (hV : GenValid G) (h2 : (2 : K) ≠ 0) (n : ℕ) (airs : ℕ → Air F)
    (hb : ∀ i < n, (airs i).public_boundary_io = []) (cs : ℕ → Coset G) (mains preps pers : ℕ → ℕ → K[X])
    (pvs : ℕ → List F) (hpv : ∀ i < n, (pvs i).length = (airs i).num_public_values)
    (Ps : ℕ → ℕ → K[X]) (ch : List (List K)) (all : List (List (Lookup F)))
    (hL : ∀ i < n, LaidOut (airs i) (ch.getD i []) (all.getD i [])) (Ts : ℕ → K) (α ζ : K) (qs : ℕ → K)
    (hζ : ∀ i < n, ¬ InCoset (cs i).shift (cs i).subgroup_generator (cs i).log_size ζ) :
    (∀ i < n,
      let σ := instAssign G (cs i) (mains i) (preps i) (pers i) (pvs i)
      let perm := permOpening (cs i).subgroup_generator ζ (Ps i) (all.getD i [])
      verify_constraints_with_lookups G (airs i) (openRow σ (.main 0) (airs i).width ζ)
        (openRow σ (.main 1) (airs i).width ζ) (openRow σ (.prep 0) (airs i).preprocessed_width ζ)
        (openRow σ (.prep 1) (airs i).preprocessed_width ζ) perm.current perm.next (ch.getD i [])
        (if all.getD i [] = [] then [] else [Ts i]) (openRow σ .periodic (airs i).num_periodic_columns ζ)
        (all.getD i []) (pvs i) (cs i) ζ α (qs i) = some (.ok ())) ↔
      ∀ i < n,
        (instancePoly G (airs i) (cs i) (mains i) (preps i) (pers i) (pvs i) (Ps i) (ch.getD i []) (Ts i)
          α (all.getD i [])).eval ζ *
          ((cs i).shift ^ 2 ^ (cs i).log_size /
            (vanishing (cs i).shift (cs i).subgroup_generator (cs i).log_size).eval ζ) = qs i :=
  batch_checks_at_zeta G hV h2 n airs hb cs mains preps pers pvs hpv Ps ch all hL Ts α ζ qs hζ

end zeta

/-- **A lookup column's pair under the batch layout.**

Lookup j of table i, in slot j, reads alpha + (id + 1) beta^W and beta, with id its bus id.

So each tuple's denominator is the domain-separated denominator of its bus. -/
theorem lookup_pair_layout {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (αL βL : K) (env : Var → K) {i j : ℕ} (hi : i < ids.length)
    (hj : j < ids[i].length) (l : Lookup F) (hl : l.column = j) :
    ∃ ch, lay_out_lookup_challenges 2 all αL βL = some ch ∧
      ∀ e, (columnAt env (ch.getD i []) l).alpha - fingerprint (columnAt env (ch.getD i []) l).beta e =
        busDenom αL βL st.max_message_width ids[i][j] e := by
  obtain ⟨ch, h1, -, -, h4⟩ := columnAt_layout h αL βL env hi hj l hl
  exact ⟨ch, h1, h4⟩

/-- **A one-row trace.**

On a coset of one point s, the boundary selectors are the constant 1.

The transition selector is (X - s) / s, a multiple of the vanishing polynomial. -/
theorem one_row_trace (s : K) (main prep : ℕ → K[X]) (pub : ℕ → K) (periodic : ℕ → K[X]) :
    starkAssign s 1 0 main prep pub periodic .isFirstRow = 1 ∧
      starkAssign s 1 0 main prep pub periodic .isLastRow = 1 ∧
      starkAssign s 1 0 main prep pub periodic .isTransition = Polynomial.C s⁻¹ * vanishing s 1 0 :=
  one_row_selectors s main prep pub periodic

/-! ## One width per bus -/

/-- **p3-lookup's width check** passes exactly when every tuple on one bus has one width. -/
theorem bus_width_check (all : List (List (Lookup F))) :
    (∃ w, check_bus_widths all = .ok w) ↔
      ∀ c ∈ all.flatten, ∀ d ∈ all.flatten, ∀ n, c.kind = .Global n → d.kind = .Global n →
        ∀ e ∈ c.elements, ∀ e' ∈ d.elements, e.length = e'.length :=
  check_bus_widths_ok_iff all

/-- **The width check rejects nothing the layout accepts.**

Run before the transcript, it turns the layout's width panic into an error.

An honest batch never meets it. -/
theorem bus_width_check_before_layout (all : List (List (Lookup F))) (α β : K)
    (h : lay_out_lookup_challenges 2 all α β ≠ none) : ∃ w, check_bus_widths all = .ok w :=
  (check_bus_widths_ok_iff all).2 (busWidthsOk_of_widthsOk (not_not.1 fun hn =>
    h ((lay_out_none_iff all α β).2 hn)))

/-- **What the width check leaves to the layout.**

The layout accepts a batch the width check accepts, given two more conditions:

- every lookup's own tuples have one width
- every global lookup has a tuple. -/
theorem bus_width_check_layout (all : List (List (Lookup F))) (α β : K)
    (hc : ∃ w, check_bus_widths all = .ok w) (hu : ∀ c ∈ all.flatten, (width c).isSome)
    (hne : ∀ c ∈ all.flatten, ∀ n, c.kind = .Global n → c.elements ≠ []) :
    lay_out_lookup_challenges 2 all α β ≠ none := fun h =>
  (lay_out_none_iff all α β).1 h (widthsOk_of_busWidthsOk ((check_bus_widths_ok_iff all).1 hc) hu hne)

/-- **A bus the width check passes and the layout panics on.**

An exclusive group with no branch shares a bus with a send of width 2.

The width check sees only the send.

The layout gives the group width 0, and panics. -/
theorem empty_group_panics (x : F) (α β : K) :
    check_bus_widths [[emptyGroup], [widthTwoSend x]] = .ok 2 ∧
      lay_out_lookup_challenges 2 [[(emptyGroup : Lookup F)], [widthTwoSend x]] α β = none :=
  empty_group_gap x α β

/-! ## The LogUp count -/

open Classical in
/-- **p3-security's LogUp charge bounds a batch of several heights.**

Table i emits at most n_i messages per row, over at most 2^L rows.

An unbalanced bus then passes on at most (sum_i n_i) 2^L (W + 2) |K| of the |K|^2 pairs.

That is the rate p3-security charges with the summed per-row count and the largest height. -/
theorem logup_charge_bounds_batch {all : List (List (Lookup F))} {ids : List (List ℕ)}
    {st : LayoutState} (h : busIds all = some (ids, st)) (hp : all.flatten.length ≤ p)
    (airs : List (AirMessages K)) (hkey : KeyedBy all.flatten ids.flatten (allMessages airs))
    (hunbal : ¬ Balanced (allMessages airs)) (n : ℕ → ℕ) (L : ℕ)
    (hrow : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i)
    (hh : ∀ a ∈ airs, a.height ≤ 2 ^ L) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 st.max_message_width airs cols}
      ≤ (∑ i ∈ range airs.length, n i) * 2 ^ L * (st.max_message_width + 2) * Fintype.card K :=
  batch_soundness_max_height h hp airs hkey hunbal n L hrow hh

/-- **The exact count** of a batch is at most sum_i n_i h_i. -/
theorem logup_exact_count (airs : List (AirMessages K)) (n : ℕ → ℕ)
    (hrow : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i) :
    (allMessages airs).length ≤
      ∑ i ∈ range airs.length, n i * (airs.getD i ⟨0, 0, fun _ _ => []⟩).height :=
  length_allMessages_le airs n hrow

/-- **p sends with no receiver balance.**

This is why the height bound keeps every multiplicity below p. -/
theorem p_sends_balance (k : Key K) : Balanced (List.replicate p (k, (1 : K))) :=
  balanced_replicate_char k

/-- **A bus with one sender** is unbalanced once it sends anything, with fewer than p unit sends. -/
theorem one_sender_unbalanced (msgs : List (Key K × K)) (hne : msgs ≠ []) (hone : ∀ q ∈ msgs, q.2 = 1)
    (hlen : msgs.length < p) : ¬ Balanced msgs :=
  one_sided_unbalanced msgs hne hone hlen

end Plonky3Lean.Claims.BatchStark
