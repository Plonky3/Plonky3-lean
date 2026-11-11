module

public import P3UniStark

@[expose] public section

/-!
# The Fiat-Shamir order

- Alpha is drawn after the trace commitment and the public values.
- When the AIR has preprocessed columns, alpha also follows the preprocessed commitment.
- Zeta is drawn after every commitment of the proof and the grind.
- The opening argument starts after zeta.
- A preprocessed or randomization commitment that disagrees with the shape is rejected.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open p3_uni_stark.transcript.mirror

/-- The pattern orders the steps:

- alpha after the trace, preprocessed and public steps
- zeta after the quotient, randomization and grind steps
- the opening argument last. -/
theorem pattern_order (s : StarkShape) :
    ∃ a b, s.pattern = a ++ [.alpha] ++ b ++ [.zeta, .begin_opening_argument, .end_opening_argument] ∧
      .trace_commitment ∈ a ∧ .public_values s.num_public_values ∈ a ∧
      (s.preprocessed_width > 0 → .preprocessed_commitment ∈ a) ∧
      .quotient_commitment ∈ b ∧ (s.has_randomization → .random_commitment ∈ b) ∧
      (s.ood_pow_bits > 0 → .ood_pow s.ood_pow_bits ∈ b) ∧
      .alpha ∉ a ∧ .zeta ∉ a ∧ .zeta ∉ b := by
  refine ⟨[.trace_commitment] ++ (if s.preprocessed_width > 0 then [.preprocessed_commitment] else []) ++
    [.public_values s.num_public_values],
    [.quotient_commitment] ++ (if s.has_randomization then [.random_commitment] else []) ++
    (if s.ood_pow_bits > 0 then [.ood_pow s.ood_pow_bits] else []), by simp [StarkShape.pattern],
    by simp, by simp, fun h => by simp [h], by simp, fun h => by simp [h], fun h => by simp [h],
    ?_, ?_, ?_⟩ <;> split_ifs <;> simp

variable {C F E : Type}

/-- The first phase accepts exactly when two conditions hold:

- a preprocessed commitment is present for a positive preprocessed width
- alpha is the oracle at the trace commitment, that commitment, and the public values. -/
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
      | false, some _ => .error .UnexpectedPreprocessedCommitment := by
  rcases h : decide (shape.preprocessed_width > 0) <;> rcases prep with _ | c <;>
    simp_all [constraint_phase, optional_commitment, bind, Except.bind, pure, Except.pure]

/-- When the second phase accepts, zeta is the oracle at the input state extended by:

- the quotient commitment
- the randomization commitment, when present
- the grind witness, when there is a grind. -/
theorem ood_phase_ok {shape : StarkShape} {H : List (Msg C F) → E}
    {powOk : List (Msg C F) → ℕ → F → Bool} {st st' : List (Msg C F)} {quotient : C}
    {random : Option C} {w : F} {ζ : E}
    (h : ood_phase shape H powOk st quotient random w = .ok (st', ζ)) :
    random.isSome = shape.has_randomization ∧
      ζ = H (st ++ [.com quotient] ++ (random.map .com).toList ++
        (if shape.ood_pow_bits > 0 then [.scalar w] else [])) := by
  unfold ood_phase optional_commitment at h
  rcases hr : shape.has_randomization <;> rcases random with _ | r <;>
    simp only [hr, bind, Except.bind, pure, Except.pure] at h <;>
    first
    | (split_ifs at h <;> simp_all)
    | simp at h

/-- After both phases accept, zeta is the oracle at a state that holds three things:

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
      (∀ r, random = some r → .com r ∈ pre) := by
  obtain ⟨-, rfl⟩ := ood_phase_ok h₂
  rw [constraint_phase_eq] at h₁
  refine ⟨_, rfl, ?_⟩
  rcases hd : decide (shape.preprocessed_width > 0) <;> rcases prep with _ | c <;>
    simp only [hd] at h₁ <;> cases h₁ <;> simp_all

end Plonky3Lean.Proofs.UniStark
