module

public import Plonky3Lean.Proofs.BatchStark.Accept
public import Plonky3Lean.Proofs.BatchStark.Soundness
public import Plonky3Lean.Proofs.BatchStark.Check
public import Plonky3Lean.Proofs.BatchStark.Extracted
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

The opening argument and each table's check at zeta enter as predicates.
-/

open p3_batch_stark.transcript.mirror p3_batch_stark.verifier.mirror p3_batch_stark.checker.mirror
  p3_lookup.mirror p3_air.air.mirror p3_air.builder.mirror Plonky3Lean.Spec.Lookup
  Plonky3Lean.Spec.UniStark Plonky3Lean.Spec.Air Plonky3Lean.Proofs.BatchStark
  Plonky3Lean.Proofs.BatchStark.Extracted Plonky3Lean.Proofs.Lookup Finset

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.BatchStark

local notation "F" => BabyBear.Field
local notation "K" => BabyBear.Ext4
local notation "p" => BabyBear.fieldSize

instance : CharP K p :=
  charP_of_injective_algebraMap (algebraMap F K).injective p

/-! ## The transcript -/

/-- **The seed binds the shape.** Two shapes with one seed agree on the instance count, every trace and preprocessed width, every public-value count, the three flags, the lookup count, both difficulties when they are played. -/
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

/-- **The replay never panics.** After the shape checks accept, with lookups that pass the layout's width checks, the replay returns, playing exactly the pattern when it accepts and a prefix of it when a grind rejects. -/
theorem replay_never_panics {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hW : WidthsOk common.lookups.flatten)
    (H : List (Msg C F K) → K) (powOk : List (Msg C F K) → ℕ → F → Bool) :
    ∃ st r, replay cfg airs proof pvs common checked H powOk = some (st, r) ∧
      (∀ x, r = .ok x → st.played = (shapeOf cfg airs common checked).pattern) ∧
      (∀ e, r = .error e → st.played <+: (shapeOf cfg airs common checked).pattern) :=
  replay_played hS hW H powOk

/-- **The Fiat-Shamir order.** When the replay accepts, the lookup pair follows every degree bit, the main commitment, every public value, the preprocessed commitment and the grind; alpha follows the pair, the permutation commitment and every terminal; zeta follows alpha, the quotient and randomization commitments and the second grind. -/
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

/-- **Wrong table count.** A per-instance list of another length than the AIRs is rejected first, with the count error. -/
theorem wrong_table_count (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (h : ¬ CountsOk airs proof pvs common) :
    check_shape cfg airs proof pvs common = .error .InstanceCountMismatch :=
  check_shape_count cfg airs proof pvs common h

/-- **Randomization.** With the right counts, a randomization opening or commitment that disagrees with the hiding flag is rejected next, with the randomization error. -/
theorem randomization_mismatch (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (hc : CountsOk airs proof pvs common)
    (h : ¬ ((∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk) ∧ proof.random.isSome = cfg.zk)) :
    check_shape cfg airs proof pvs common = .error .RandomizationError :=
  check_shape_random cfg airs proof pvs common hc h

/-- **One table's openings.** Its checks accept exactly the documented shape: public values, row widths, next rows exactly when read, chunk counts and dimensions, preprocessed rows, permutation rows of (L + 1) D values, and a terminal exactly with lookups. -/
theorem table_shape (cfg : Config) (common : CommonData C F) (air : AirInfo) (i : ℕ) (pv : List F)
    (ov : Opened K) (terminal : Option K) (n_chunks : ℕ) :
    check_instance cfg common air i pv ov terminal n_chunks = .ok () ↔
      InstanceOk cfg common air i pv ov terminal n_chunks :=
  check_instance_ok_iff cfg common air i pv ov terminal n_chunks

/-- **The permutation round.** The instances with a nonempty permutation opening are exactly those with lookups, in the prover's commit order. -/
theorem permutation_round_order {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hD : 1 ≤ cfg.dimension) :
    (List.range airs.length).filter (fun i => !(proof.opened.getD i default).permutation_local.isEmpty) =
      (List.range airs.length).filter (fun i => !(common.lookups.getD i []).isEmpty) :=
  permutation_round hS hD

/-- **The verifier never panics on a proof**, once every AIR binds its public values by constraints and the cached lookups pass the layout's width checks. -/
theorem verify_never_panics (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (H : List (Msg C F K) → K)
    (powOk : List (Msg C F K) → ℕ → F → Bool) (pcsOk : List (Msg C F K) → K → Bool)
    (checkAt : ℕ → List K → K → K → Except BatchError Unit)
    (hb : airs.all (·.boundary_io_empty)) (hW : WidthsOk common.lookups.flatten) :
    verify_batch cfg airs proof pvs common H powOk pcsOk checkAt ≠ none :=
  verify_batch_ne_none cfg airs proof pvs common H powOk pcsOk checkAt hb hW

/-- **What acceptance means.** The shape checks and the height bound pass, the replay plays the pattern, the opening argument passes at zeta, every table passes its check at the shared zeta and alpha, and the terminals sum to zero. -/
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

/-- The height bound is among the guarantees of an accepted shape: the weighted height sum stays below p. -/
theorem accepted_height_bound {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (s : ℕ) :
    check_multiplicity_height_bound cfg.characteristic common.lookups
      (checked.base_degree_bits.map (2 ^ ·)) ≠ some (.error s) :=
  hS.height s

/-! ## The lookup challenges -/

/-- **The bus ids.** Two lookups share an id exactly when they are the same lookup or global lookups naming one bus; every id is below the number of lookups; every lookup has one payload width, at most the widest W >= 1. -/
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

/-- **The layout.** Lookup j of instance i reads alpha + (id + 1) beta^W and then beta. -/
theorem challenge_layout {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (α β : K) :
    lay_out_lookup_challenges 2 all α β =
      some (ids.map fun l : List ℕ => l.flatMap fun b : ℕ => [α + ((b : K) + 1) * β ^ st.max_message_width, β]) :=
  lay_out_eq h α β

/-- **When the layout panics:** exactly when a lookup's tuples differ in width, or two global lookups naming one bus differ in width. -/
theorem layout_panics (all : List (List (Lookup F))) (α β : K) :
    lay_out_lookup_challenges 2 all α β = none ↔ ¬ WidthsOk all.flatten :=
  lay_out_none_iff all α β

/-- The combiner on a lookup's bus offset is the domain-separated denominator of its bus. -/
theorem combiner_is_bus_denominator (α β : K) (W b : ℕ) (e : List K) :
    (α + ((b : K) + 1) * β ^ W) - fingerprint β e = busDenom α β W b e :=
  combiner_eq_busDenom α β W b e

open Classical in
/-- **The cross-table bus.** For messages keyed by the layout's bus ids, with at most p lookups, an unbalanced bus passes on at most N (W + 1) |K| of the |K|^2 challenge pairs, whatever columns the prover picks after them. -/
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

/-- **The count is a sum over the committed matrices** of width times points, times the powers per pair. -/
theorem opening_count_sum (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q L D : ℕ)
    (o : p3_uni_stark.security.OpeningShape) :
    batchCount mw mn pw pn q L D o =
      ((matrices mw mn pw pn q L D o).map fun m => m.1 * m.2).sum * shapePpo o :=
  batchCount_eq mw mn pw pn q L D o

/-! ## The debug checker -/

/-- **The checker.** With traces of one height, it passes exactly when every row's AIR and lookup constraints pass with the 0/1 selectors. -/
theorem checker_accepts (air : Air F) (main : Mat F) (prep : Option (Mat F)) (perm : Mat K)
    (ch vals : List K) (pv : List F) (lookups : List (Lookup F)) :
    p3_batch_stark.checker.mirror.check_constraints air main prep perm ch vals pv lookups = some () ↔
      (∀ q ∈ prep, q.height = main.height) ∧ perm.height = main.height ∧
      ∀ r < main.height, ∃ s, eval_air_and_lookups air (rowBuilder air main prep perm ch vals pv r)
        (DebugState.new r) lookups = some s ∧ s.failures = [] :=
  check_constraints_eq_some air main prep perm ch vals pv lookups

/-- **A selector in a lookup count.** The prover's fraction m / d, with m the 0/1 selector value, satisfies the STARK's pin exactly when the STARK's selector value is the same. -/
theorem selector_count_pin (T : Instance K) (ω : K) (i : ℕ) (v : Var) {d : K} (hd : d ≠ 0) :
    Pinned [(d, starkRowEnv T ω i v)] (rowEnv T i v / d) ↔ starkRowEnv T ω i v = rowEnv T i v :=
  selector_count_pinned_iff T ω i v hd

/-- **The transition selector in a count stops the honest prover on row 0.** -/
theorem selector_count_row0 (T : Instance K) {ω : K} (hω : IsPrimitiveRoot ω T.height) (hn : 2 ≤ T.height)
    {d : K} (hd : d ≠ 0) :
    starkRowEnv T ω 0 .isTransition ≠ rowEnv T 0 .isTransition ∧
      ¬ Pinned [(d, starkRowEnv T ω 0 .isTransition)] (rowEnv T 0 .isTransition / d) :=
  transition_row0_ne T hω hn hd

/-- **The first-row selector in a count.** On 8 rows, the STARK counts a first-row message 8 times, so a bus that sends it under that count and receives it once per row balances, though with 0/1 counts it is unbalanced. -/
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

end Plonky3Lean.Claims.BatchStark
