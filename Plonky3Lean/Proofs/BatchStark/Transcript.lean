module

public import P3BatchStark.Assumptions.Mirror.Transcript

@[expose] public section

/-!
# The batch transcript

Each verifier phase plays its steps and absorbs its messages in closed form.

The seed determines:

- the instance count
- every trace and preprocessed width
- every public-value count
- every flag and difficulty the pattern holds.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.transcript.mirror p3_lookup.mirror

variable {C F E : Type}

/-! ## The phases in closed form -/

theorem foldl_step {α : Type} (st : St C F E) (l : List α) (s : α → Step) (m : α → List (Msg C F E)) :
    l.foldl (fun st a => st.step (s a) (m a)) st = ⟨st.msgs ++ l.flatMap m, st.played ++ l.map s⟩ := by
  induction l generalizing st with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; simp [St.step]

theorem flatMap_singleton_eq {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

section

variable [Zero F] [DecidableEq F] [NatCast E]

theorem instance_bindings_eq (st : St C F E) (bits : List ℕ) :
    instance_bindings st bits =
      ⟨st.msgs ++ bits.map (fun b => .ext (b : E)), st.played ++ bits.map fun _ => .degree_bits⟩ := by
  simp only [instance_bindings, foldl_step, flatMap_singleton_eq]

theorem main_phase_eq (st : St C F E) (c : C) (pv : List (List F)) :
    main_phase st c pv = ⟨st.msgs ++ [.com c] ++ pv.flatMap (·.map .base),
      st.played ++ [.main_commitment] ++ pv.map (.public_values ·.length)⟩ := by
  simp only [main_phase, foldl_step]
  simp [St.step]

end

theorem preprocessed_phase_eq (st : St C F E) (c : Option C) :
    preprocessed_phase st c =
      ⟨st.msgs ++ (c.map .com).toList, st.played ++ (c.map fun _ => .preprocessed_commitment).toList⟩ := by
  cases c <;> simp [preprocessed_phase, St.step]

theorem permutation_phase_eq (H : List (Msg C F E) → E) (st : St C F E) (c : Option C) (ts : List E) :
    permutation_phase H st c ts =
      (⟨st.msgs ++ (c.map .com).toList ++ ts.map .ext ++ [.challenge .constraint_challenge],
        st.played ++ (c.map fun _ => .permutation_commitment).toList ++ ts.map (fun _ => .lookup_terminal) ++
          [.constraint_challenge]⟩,
        H (st.msgs ++ (c.map .com).toList ++ ts.map .ext)) := by
  cases c <;> simp only [permutation_phase, foldl_step] <;> simp [St.step, St.draw, flatMap_singleton_eq]

theorem quotient_phase_eq (st : St C F E) (q : C) (r : Option C) :
    quotient_phase st q r = ⟨st.msgs ++ [.com q] ++ (r.map .com).toList,
      st.played ++ [.quotient_commitment] ++ (r.map fun _ => .randomization_commitment).toList⟩ := by
  cases r <;> simp [quotient_phase, St.step]

theorem delegate_eq (st : St C F E) :
    delegate st = ⟨st.msgs, st.played ++ [.begin_opening_argument, .end_opening_argument]⟩ := by
  simp [delegate, St.step]

section

variable [Zero F] [DecidableEq F]

/-- The witness a grind absorbs: none at zero difficulty. -/
def powMsgs (bits : ℕ) (w : F) : List (Msg C F E) := if bits = 0 then [] else [.base w]

theorem observe_pow_eq {powOk : List (Msg C F E) → ℕ → F → Bool} {st : St C F E} {s : Step} {bits : ℕ}
    {w : F} :
    observe_pow powOk st s bits w =
      if bits = 0 ∨ powOk st.msgs bits w then some (st.step s (powMsgs bits w)) else none := by
  unfold observe_pow powMsgs; split_ifs <;> simp_all

/-- When the out-of-domain phase accepts, zeta is the oracle at the input state.

At positive difficulty, that state is first extended by the witness. -/
theorem ood_phase_ok {shape : BatchShape} {H : List (Msg C F E) → E}
    {powOk : List (Msg C F E) → ℕ → F → Bool} {st st' : St C F E} {w : F} {ζ : E}
    (h : ood_phase shape H powOk st w = (st', .ok ζ)) :
    ζ = H (st.msgs ++ powMsgs shape.ood_pow_bits w) ∧
      st'.played = st.played ++ [.ood_pow shape.ood_pow_bits, .zeta] := by
  simp only [ood_phase, observe_pow_eq] at h
  split_ifs at h with h1 h2 <;> simp only [St.draw, St.step, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, h⟩ := h <;> simp_all

/-- The out-of-domain phase rejects exactly two witnesses:

- a nonzero witness at zero difficulty
- a witness the grind check refuses. -/
theorem ood_phase_error {shape : BatchShape} {H : List (Msg C F E) → E}
    {powOk : List (Msg C F E) → ℕ → F → Bool} {st st' : St C F E} {w : F}
    {e : BatchTranscriptFailure} (h : ood_phase shape H powOk st w = (st', .error e)) :
    (shape.ood_pow_bits = 0 ∧ w ≠ 0 ∧ e = .NonCanonicalOodPowWitness ∧ st' = st) ∨
      (shape.ood_pow_bits ≠ 0 ∧ powOk st.msgs shape.ood_pow_bits w = false ∧
        e = .OodPowWitness shape.ood_pow_bits ∧ st'.played = st.played ++ [.ood_pow shape.ood_pow_bits]) := by
  simp only [ood_phase, observe_pow_eq] at h
  split_ifs at h with h1 h2 <;> simp only [St.draw, St.step, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, h⟩ := h <;> simp_all

/-- When the lookup phase accepts with lookups, the pair comes from the oracle.

Alpha is the oracle at the input state extended by the witness.

Beta is the oracle one draw later. -/
theorem lookup_phase_ok [Field E] {shape : BatchShape} {H : List (Msg C F E) → E}
    {powOk : List (Msg C F E) → ℕ → F → Bool} {nc : ℕ} {st st' : St C F E}
    {ls : List (List (Lookup F))} {w : Option F} {ch : List (List E)}
    (h : lookup_phase shape H powOk nc st ls w = some (st', .ok ch)) (hl : shape.has_lookups) :
    ∃ x, w = some x ∧
      ∃ α β, α = H (st.msgs ++ powMsgs shape.lookup_pow_bits x) ∧
        β = H (st.msgs ++ powMsgs shape.lookup_pow_bits x ++ [.challenge .lookup_alpha]) ∧
        lay_out_lookup_challenges nc ls α β = some ch ∧
        st'.msgs = st.msgs ++ powMsgs shape.lookup_pow_bits x ++
          [.challenge .lookup_alpha, .challenge .lookup_beta] ∧
        st'.played = st.played ++ [.lookup_pow shape.lookup_pow_bits, .lookup_alpha, .lookup_beta] := by
  simp only [lookup_phase] at h
  simp only [hl, not_true_eq_false, ↓reduceIte] at h
  rcases w with _ | x
  · simp at h
  · refine ⟨x, rfl, ?_⟩
    simp only [observe_pow_eq] at h
    split_ifs at h with h1 h2
    · simp at h
    · simp only [St.draw, St.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, he⟩ := h
      cases he
      exact ⟨_, _, rfl, rfl, by simpa using hc, by simp, by simp⟩
    · simp at h

/-- With no lookup, the lookup phase plays nothing, and rejects exactly a present witness. -/
theorem lookup_phase_no_lookups [Field E] {shape : BatchShape} {H : List (Msg C F E) → E}
    {powOk : List (Msg C F E) → ℕ → F → Bool} {nc : ℕ} {st : St C F E}
    {ls : List (List (Lookup F))} {w : Option F} (hl : shape.has_lookups = false) :
    lookup_phase shape H powOk nc st ls w =
      some (st, if w.isSome then .error .UnexpectedLookupPowWitness else .ok (ls.map fun _ => [])) := by
  unfold lookup_phase
  rcases w with _ | x <;> simp [hl]

/-- With lookups, the lookup phase rejects exactly:

- a missing witness
- a nonzero witness at zero difficulty
- a witness the grind check refuses. -/
theorem lookup_phase_error [Field E] {shape : BatchShape} {H : List (Msg C F E) → E}
    {powOk : List (Msg C F E) → ℕ → F → Bool} {nc : ℕ} {st st' : St C F E}
    {ls : List (List (Lookup F))} {w : Option F} {e : BatchTranscriptFailure}
    (h : lookup_phase shape H powOk nc st ls w = some (st', .error e)) (hl : shape.has_lookups) :
    (w = none ∧ e = .MissingLookupPowWitness shape.lookup_pow_bits ∧ st' = st) ∨
      (∃ x, w = some x ∧ shape.lookup_pow_bits = 0 ∧ x ≠ 0 ∧ e = .NonCanonicalLookupPowWitness ∧ st' = st) ∨
      (∃ x, w = some x ∧ shape.lookup_pow_bits ≠ 0 ∧ powOk st.msgs shape.lookup_pow_bits x = false ∧
        e = .LookupPowWitness shape.lookup_pow_bits ∧
        st'.played = st.played ++ [.lookup_pow shape.lookup_pow_bits]) := by
  simp only [lookup_phase] at h
  simp only [hl, not_true_eq_false, ↓reduceIte] at h
  rcases w with _ | x
  · simp_all
  · simp only [observe_pow_eq] at h
    split_ifs at h with h1 h2
    · simp_all
    · simp only [St.draw, St.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨c, -, he⟩ := h
      cases he
    · simp only [St.step, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h; simp_all

end

/-! ## The seed binds the shape -/

/-- The public-value counts a step list announces. -/
def pvCounts : List Step → List ℕ := List.filterMap fun | .public_values n => some n | _ => none

/-- The lookup difficulties a step list announces. -/
def lookupBits : List Step → List ℕ := List.filterMap fun | .lookup_pow n => some n | _ => none

/-- The out-of-domain difficulties a step list announces. -/
def oodBits : List Step → List ℕ := List.filterMap fun | .ood_pow n => some n | _ => none

theorem pvCounts_pattern (s : BatchShape) : pvCounts s.pattern = s.public_value_counts := by
  simp only [pvCounts, BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs <;> simp [List.filterMap_append, List.filterMap_map]

theorem lookupBits_pattern (s : BatchShape) :
    lookupBits s.pattern = if s.has_lookups then [s.lookup_pow_bits] else [] := by
  simp only [lookupBits, BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs <;> simp [List.filterMap_append, List.filterMap_map]

theorem oodBits_pattern (s : BatchShape) : oodBits s.pattern = [s.ood_pow_bits] := by
  simp only [oodBits, BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs <;> simp [List.filterMap_append, List.filterMap_map]

theorem count_terminal_pattern (s : BatchShape) :
    s.pattern.count .lookup_terminal = s.num_lookup_instances := by
  simp only [BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs with h1 h2 h3 <;> simp_all [List.count_replicate, BatchShape.has_lookups, List.count_eq_zero]

theorem count_preprocessed_pattern (s : BatchShape) :
    s.pattern.count .preprocessed_commitment = s.has_preprocessed_commitment.toNat := by
  simp only [BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs <;> simp_all [List.count_replicate, List.count_eq_zero]

theorem count_randomization_pattern (s : BatchShape) :
    s.pattern.count .randomization_commitment = s.has_randomization_commitment.toNat := by
  simp only [BatchShape.pattern, BatchShape.lookupSteps]
  split_ifs <;> simp_all [List.count_replicate, List.count_eq_zero]

/-- **The seed binds the shape.**

Two shapes with one seed agree on:

- the instance count
- every trace and preprocessed width
- every public-value count
- the preprocessed flag, the lookup count and the randomization flag
- the out-of-domain difficulty
- the lookup difficulty, when there are lookups. -/
theorem domain_separator_injective {s s' : BatchShape} (h : s.domain_separator = s'.domain_separator) :
    s.trace_widths = s'.trace_widths ∧ s.preprocessed_widths = s'.preprocessed_widths ∧
      s.public_value_counts = s'.public_value_counts ∧
      s.has_preprocessed_commitment = s'.has_preprocessed_commitment ∧
      s.num_lookup_instances = s'.num_lookup_instances ∧
      (s.has_lookups → s.lookup_pow_bits = s'.lookup_pow_bits) ∧
      s.has_randomization_commitment = s'.has_randomization_commitment ∧
      s.ood_pow_bits = s'.ood_pow_bits := by
  simp only [BatchShape.domain_separator, DomainSeparator.mk.injEq, true_and, List.cons.injEq] at h
  obtain ⟨hp, hn, hl⟩ := h
  have hk : s.num_lookup_instances = s'.num_lookup_instances := by
    rw [← count_terminal_pattern, hp, count_terminal_pattern]
  refine ⟨(List.append_inj hl hn).1, (List.append_inj hl hn).2, by
    rw [← pvCounts_pattern, hp, pvCounts_pattern], ?_, hk, fun hs => ?_, ?_, ?_⟩
  · have := count_preprocessed_pattern s; rw [hp, count_preprocessed_pattern] at this
    revert this; cases s.has_preprocessed_commitment <;> cases s'.has_preprocessed_commitment <;> simp
  · have hs' : s'.has_lookups := by simpa [BatchShape.has_lookups, hk] using hs
    have := lookupBits_pattern s; rw [hp, lookupBits_pattern] at this
    simpa [hs, hs'] using this.symm
  · have := count_randomization_pattern s; rw [hp, count_randomization_pattern] at this
    revert this; cases s.has_randomization_commitment <;> cases s'.has_randomization_commitment <;> simp
  · have := oodBits_pattern s; rw [hp, oodBits_pattern] at this
    simpa using this.symm

end Plonky3Lean.Proofs.BatchStark
