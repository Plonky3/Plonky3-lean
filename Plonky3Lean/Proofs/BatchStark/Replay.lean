module

public import Plonky3Lean.Proofs.BatchStark.Verifier

@[expose] public section

/-!
# The batch verifier's transcript replay

Assume the shape checks accept and the keygen-cached lookups pass the layout's width checks.

Then:

- the replay never panics
- it plays exactly the pattern when it accepts, and a prefix of it when a grind rejects
- the lookup pair, alpha and zeta are the oracle at explicit transcripts, in pattern order.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.verifier.mirror p3_batch_stark.transcript.mirror p3_lookup.mirror

variable {C F K : Type} [Zero F] [DecidableEq F] [Field K]

/-- The messages before the lookup phase:

- the seed
- every degree bit
- the main commitment
- every public value
- the preprocessed commitment. -/
def preLookup (shape : BatchShape) (db : List ℕ) (main : C) (pvs : List (List F)) (prep : Option C) :
    List (Msg C F K) :=
  [.seed shape.domain_separator] ++ db.map (fun b => .ext (b : K)) ++ [.com main] ++
    pvs.flatMap (·.map .base) ++ (prep.map .com).toList

/-- The steps before the lookup phase. -/
def stepsBefore (shape : BatchShape) : List Step :=
  shape.trace_widths.map (fun _ => .degree_bits) ++ [.main_commitment] ++
    shape.public_value_counts.map .public_values ++
    (if shape.has_preprocessed_commitment then [.preprocessed_commitment] else [])

/-- The steps after the folding challenge. -/
def stepsAfter (shape : BatchShape) : List Step :=
  [.quotient_commitment] ++ (if shape.has_randomization_commitment then [.randomization_commitment] else []) ++
    [.ood_pow shape.ood_pow_bits, .zeta, .begin_opening_argument, .end_opening_argument]

theorem pattern_split (s : BatchShape) :
    s.pattern = stepsBefore s ++ (if s.has_lookups then s.lookupSteps else []) ++ [.constraint_challenge] ++
      stepsAfter s := by
  simp [BatchShape.pattern, stepsBefore, stepsAfter]

theorem map_const_eq {α β γ : Type} (c : γ) {l : List α} {l' : List β} (h : l.length = l'.length) :
    l.map (fun _ => c) = l'.map (fun _ => c) := by
  simp [List.map_const', h]

theorem opt_steps {α β γ : Type} (o : Option α) (f : α → β) (c : γ) :
    ((o.map f).map fun _ => c).toList = if o.isSome then [c] else [] := by
  cases o <;> rfl

/-- Under an accepted shape, the steps before the lookup phase are those of the pattern. -/
theorem played_before {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) :
    (preprocessed_phase (main_phase (instance_bindings (new (shapeOf cfg airs common checked) : St C F K)
      proof.degree_bits) proof.main pvs) (common.preprocessed.map (·.1))).played =
      stepsBefore (shapeOf cfg airs common checked) := by
  obtain ⟨ho, hp, hd, -, -, -⟩ := hS.counts
  have hpv : pvs.map (·.length) = airs.map (·.num_public_values) := by
    refine List.ext_getElem (by simp [hp]) fun i h1 h2 => ?_
    have := (hS.instances i (by simpa using h2)).1
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < pvs.length by simpa using h1),
      List.getElem?_eq_getElem (show i < airs.length by simpa using h2)] using this
  have hpv' : pvs.map (fun x => Step.public_values x.length) =
      (airs.map (·.num_public_values)).map Step.public_values := by
    rw [← hpv, List.map_map]; rfl
  rw [preprocessed_phase_eq, main_phase_eq, instance_bindings_eq]
  have hdb : proof.degree_bits.map (fun _ => Step.degree_bits) =
      (airs.map (·.width)).map (fun _ => Step.degree_bits) := map_const_eq _ (by simp [hd])
  simp only [new, List.nil_append, stepsBefore, shapeOf, hpv', hdb]
  congr 1
  exact opt_steps _ _ _

theorem filterMap_length {α : Type} (t : List (Option K)) (ls : List (List α))
    (h : t.map Option.isSome = ls.map fun l => !l.isEmpty) :
    (t.filterMap id).length = (ls.filter fun l => !l.isEmpty).length := by
  induction t generalizing ls with
  | nil => cases ls <;> simp_all
  | cons x t ih =>
    cases ls with
    | nil => simp at h
    | cons l ls =>
      simp only [List.map_cons, List.cons.injEq] at h
      have := ih ls h.2
      rcases x with _ | x <;> cases l <;> simp_all

/-- After the lookup phase, the replay plays the rest of the pattern.

When the grind rejects, it plays a prefix of it. -/
theorem tail_played (shape : BatchShape) (H : List (Msg C F K) → K)
    (powOk : List (Msg C F K) → ℕ → F → Bool) (st : St C F K) (perm : Option C) (terms : List K) (q : C)
    (rand : Option C) (w : F)
    (hst : st.played = stepsBefore shape ++
      (if shape.has_lookups then [.lookup_pow shape.lookup_pow_bits, .lookup_alpha, .lookup_beta] else []))
    (hperm : perm.isSome = shape.has_lookups) (hterm : terms.length = shape.num_lookup_instances)
    (hrand : rand.isSome = shape.has_randomization_commitment) :
    (∀ z, (ood_phase shape H powOk (quotient_phase (permutation_phase H st perm terms).1 q rand) w).2 =
        .ok z →
      (delegate (ood_phase shape H powOk (quotient_phase (permutation_phase H st perm terms).1 q rand) w).1).played
        = shape.pattern) ∧
    (∀ e, (ood_phase shape H powOk (quotient_phase (permutation_phase H st perm terms).1 q rand) w).2 =
        .error e →
      (ood_phase shape H powOk (quotient_phase (permutation_phase H st perm terms).1 q rand) w).1.played <+:
        shape.pattern) := by
  -- The steps up to the grind, in closed form.
  have hmid : (quotient_phase (permutation_phase H st perm terms).1 q rand).played =
      stepsBefore shape ++ (if shape.has_lookups then shape.lookupSteps else []) ++ [.constraint_challenge] ++
        ([.quotient_commitment] ++ if shape.has_randomization_commitment then [.randomization_commitment] else []) := by
    have hk : ¬ shape.has_lookups → shape.num_lookup_instances = 0 := by
      simp [BatchShape.has_lookups]
    have hp : (perm.map fun _ => Step.permutation_commitment).toList =
        if shape.has_lookups then [.permutation_commitment] else [] := by
      rw [← hperm]; cases perm <;> rfl
    have hr : (rand.map fun _ => Step.randomization_commitment).toList =
        if shape.has_randomization_commitment then [.randomization_commitment] else [] := by
      rw [← hrand]; cases rand <;> rfl
    rw [quotient_phase_eq, permutation_phase_eq]
    simp only [hst, hp, hr, List.map_const', hterm, BatchShape.lookupSteps]
    by_cases hl : shape.has_lookups
    · simp [hl]
    · simp [hl, hk hl]
  -- The grind either rejects, leaving a prefix, or accepts and the bracket follows.
  set st2 := quotient_phase (permutation_phase H st perm terms).1 q rand
  constructor
  · intro z hz
    obtain ⟨-, hp⟩ := ood_phase_ok (show ood_phase shape H powOk st2 w = (_, .ok z) from Prod.ext rfl hz)
    rw [delegate_eq]
    simp only [hp, hmid, pattern_split, stepsAfter]
    simp
  · intro e he
    rcases ood_phase_error (show ood_phase shape H powOk st2 w = (_, .error e) from Prod.ext rfl he) with
      ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
    · simp only [h, hmid, pattern_split, stepsAfter]
      exact ⟨[.ood_pow shape.ood_pow_bits, .zeta, .begin_opening_argument, .end_opening_argument], by simp⟩
    · simp only [hmid] at h
      simp only [h, pattern_split, stepsAfter]
      exact ⟨[.zeta, .begin_opening_argument, .end_opening_argument], by simp⟩

theorem lookup_phase_isSome {shape : BatchShape} {H : List (Msg C F K) → K}
    {powOk : List (Msg C F K) → ℕ → F → Bool} {st : St C F K} {ls : List (List (Lookup F))} {w : Option F}
    (hW : ∀ α β : K, lay_out_lookup_challenges 2 ls α β ≠ none) :
    ∃ st' r, lookup_phase shape H powOk 2 st ls w = some (st', r) := by
  unfold lookup_phase
  by_cases hl : shape.has_lookups
  · rcases w with _ | x
    · simp [hl]
    · simp only [hl, not_true_eq_false, ↓reduceIte]
      split_ifs
      · simp
      · rcases observe_pow powOk st (.lookup_pow shape.lookup_pow_bits) shape.lookup_pow_bits x with _ | st1
        · simp
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (hW (St.draw H st1 .lookup_alpha).2
            (St.draw H (St.draw H st1 .lookup_alpha).1 .lookup_beta).2)
          simp [hc]
  · rcases w <;> simp [hl]

/-- **The replay never panics.**

Assume the shape checks accept and the keygen-cached lookups pass the layout's width checks.

Then the replay returns.

It plays exactly the pattern when it accepts, and a prefix of it when a grind rejects. -/
theorem replay_played {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hW : WidthsOk common.lookups.flatten)
    (H : List (Msg C F K) → K) (powOk : List (Msg C F K) → ℕ → F → Bool) :
    ∃ st r, replay cfg airs proof pvs common checked H powOk = some (st, r) ∧
      (∀ x, r = .ok x → st.played = (shapeOf cfg airs common checked).pattern) ∧
      (∀ e, r = .error e → st.played <+: (shapeOf cfg airs common checked).pattern) := by
  set shape := shapeOf cfg airs common checked with hshape
  have hlay : ∀ α β : K, lay_out_lookup_challenges 2 common.lookups α β ≠ none := fun α β h =>
    (lay_out_none_iff common.lookups α β).1 h hW
  set st0 := preprocessed_phase (main_phase (instance_bindings (new shape : St C F K)
      proof.degree_bits) proof.main pvs) (common.preprocessed.map (·.1)) with hst0
  have h0 : st0.played = stepsBefore shape := played_before hS
  -- The facts the tail needs.
  have hk : (proof.lookup_terminals.filterMap id).length = shape.num_lookup_instances := by
    obtain ⟨-, -, -, ht, hl, -⟩ := hS.counts
    rw [hshape, shapeOf, hS.num_lookups]
    refine filterMap_length _ _ (List.ext_getElem (by simp [ht, hl]) fun i h1 h2 => ?_)
    have := (hS.instances i (by simpa [ht] using h1)).2.2.2.2.2.2.2.2.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < proof.lookup_terminals.length by
      simpa using h1), List.getElem?_eq_getElem (show i < common.lookups.length by simpa using h2)] using this
  have hperm : proof.permutation.isSome = shape.has_lookups := by
    rw [hS.perm]; rfl
  have hrand : proof.random.isSome = shape.has_randomization_commitment := hS.random_com
  obtain ⟨st1, r1, hl1⟩ := lookup_phase_isSome (shape := shape) (H := H) (powOk := powOk) (st := st0)
    (w := proof.lookup_pow_witness) hlay
  -- The steps after the lookup phase, when it accepts.
  have hst1 : ∀ ch, r1 = .ok ch → st1.played = stepsBefore shape ++
      (if shape.has_lookups then [.lookup_pow shape.lookup_pow_bits, .lookup_alpha, .lookup_beta] else []) := by
    intro ch hch
    subst hch
    by_cases hl : shape.has_lookups
    · obtain ⟨x, -, α, β, -, -, -, -, hp⟩ := lookup_phase_ok hl1 hl
      simp [hp, h0, hl]
    · rw [lookup_phase_no_lookups (by simpa using hl)] at hl1
      simp only [Option.some.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      simp [h0, hl]
  unfold replay
  simp only [← hshape, ← hst0, hl1, Option.bind_eq_bind, Option.bind_some]
  rcases r1 with e | ch
  · -- A rejected lookup grind: a prefix of the steps of the lookup phase.
    refine ⟨st1, _, rfl, by simp, fun _ _ => ?_⟩
    rw [pattern_split]
    by_cases hl : shape.has_lookups
    · rcases lookup_phase_error hl1 hl with ⟨-, -, rfl⟩ | ⟨x, -, -, -, -, rfl⟩ | ⟨x, -, -, -, -, hp⟩
      · rw [h0]; simp only [List.append_assoc]; exact List.prefix_append _ _
      · rw [h0]; simp only [List.append_assoc]; exact List.prefix_append _ _
      · rw [hp, h0]
        exact ⟨[.lookup_alpha, .lookup_beta, .permutation_commitment] ++
          List.replicate shape.num_lookup_instances .lookup_terminal ++ [.constraint_challenge] ++
          stepsAfter shape, by simp [hl, BatchShape.lookupSteps]⟩
    · rw [lookup_phase_no_lookups (by simpa using hl)] at hl1
      simp only [Option.some.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      rw [h0]; simp only [List.append_assoc]; exact List.prefix_append _ _
  · have ht := tail_played shape H powOk st1 proof.permutation (proof.lookup_terminals.filterMap id)
      proof.quotient_chunks proof.random proof.ood_pow_witness (hst1 ch rfl) hperm hk hrand
    rcases hood : ood_phase shape H powOk (quotient_phase (permutation_phase H st1 proof.permutation
      (proof.lookup_terminals.filterMap id)).1 proof.quotient_chunks proof.random) proof.ood_pow_witness
      with ⟨st3, e | z⟩
    · refine ⟨st3, _, rfl, by simp, fun _ _ => ?_⟩
      have := ht.2 e (by rw [hood])
      rwa [hood] at this
    · refine ⟨delegate st3, _, rfl, fun _ _ => ?_, by simp⟩
      have := ht.1 z (by rw [hood])
      rwa [hood] at this

omit [Zero F] [DecidableEq F] in
theorem msgs_before [Zero F] [DecidableEq F] (shape : BatchShape) (db : List ℕ) (main : C)
    (pvs : List (List F)) (prep : Option C) :
    (preprocessed_phase (main_phase (instance_bindings (new shape : St C F K) db) main pvs) prep).msgs =
      preLookup shape db main pvs prep := by
  rw [preprocessed_phase_eq, main_phase_eq, instance_bindings_eq]
  simp [new, preLookup]

/-- **The Fiat-Shamir order.** When the replay accepts:

- with lookups, the lookup alpha is the oracle at the messages before the lookup phase and the grind witness
- with lookups, beta is drawn one step later
- without lookups, no pair is drawn and every instance gets no challenge
- alpha is the oracle one step after the permutation commitment and every terminal
- zeta is the oracle after the quotient and randomization commitments and the second grind witness. -/
theorem replay_ok {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
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
        powMsgs shape.ood_pow_bits proof.ood_pow_witness) := by
  intro shape pre
  have h0 := msgs_before (K := K) shape proof.degree_bits proof.main pvs (common.preprocessed.map (·.1))
  unfold replay at h
  generalize hT : List.filterMap id proof.lookup_terminals = T at h ⊢
  simp only [Option.bind_eq_bind] at h
  rcases hl1 : lookup_phase shape H powOk 2 (preprocessed_phase (main_phase (instance_bindings
    (new shape : St C F K) proof.degree_bits) proof.main pvs) (common.preprocessed.map (·.1)))
    common.lookups proof.lookup_pow_witness with _ | ⟨st1, r1⟩
  · simp [shape, hl1] at h
  · simp only [shape] at hl1
    rw [hl1] at h
    simp only [Option.bind_some] at h
    rcases r1 with e | ch1
    · simp at h
    · -- The phases after the pair, in closed form.
      rcases hood : ood_phase shape H powOk (quotient_phase (permutation_phase H st1 proof.permutation
          T).1 proof.quotient_chunks proof.random) proof.ood_pow_witness
        with ⟨st3, e | z⟩
      · simp only [shape] at hood; simp [hood] at h
      · simp only [shape] at hood
        simp only [hood] at h
        obtain ⟨-, rfl, rfl, rfl⟩ := h
        obtain ⟨hz, -⟩ := ood_phase_ok hood
        rw [hz, quotient_phase_eq, permutation_phase_eq]
        refine ⟨st1.msgs, ?_, by simp, by simp [shape]⟩
        split_ifs with hl
        · obtain ⟨w, hw, αL, βL, h1, h2, h3, h4, -⟩ := lookup_phase_ok hl1 hl
          rw [h0] at h1 h2 h4
          exact ⟨w, αL, βL, hw, h1, h2, h3, h4⟩
        · rw [lookup_phase_no_lookups (by simpa using hl)] at hl1
          simp only [Option.some.injEq, Prod.mk.injEq] at hl1
          obtain ⟨rfl, hc⟩ := hl1
          refine ⟨?_, h0⟩
          split_ifs at hc
          cases hc
          rfl

end Plonky3Lean.Proofs.BatchStark
