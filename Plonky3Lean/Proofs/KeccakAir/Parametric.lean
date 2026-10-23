module

public import P3KeccakAir
public import Plonky3Lean.Proofs.Air.Builder

@[expose] public section

/-!
# The Keccak-f AIR is parametric

The transcribed evaluation is a program over any builder.

Related builders and related states give related states, as for every Rust evaluation generic in the builder.

That makes it an AIR in the sense of the p3-air model, with 2633 main columns.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror

variable {F : Type} [Field F]

section rel

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop}

/-- A filtered builder is related to a filtered builder when the conditions are related. -/
theorem BuilderRel.when' (h : BuilderRel B₁ B₂ R Q) {c₁ : E₁} {c₂ : E₂} (hc : R c₁ c₂) :
    BuilderRel (B₁.when c₁) (B₂.when c₂) R Q where
  add := h.add
  sub := h.sub
  mul := h.mul
  neg := h.neg
  const := h.const
  main_current := h.main_current
  main_next := h.main_next
  preprocessed_current := h.preprocessed_current
  preprocessed_next := h.preprocessed_next
  public_values := h.public_values
  periodic_values := h.periodic_values
  is_first_row := h.is_first_row
  is_last_row := h.is_last_row
  is_transition := h.is_transition
  assert_zero hs hx := h.assert_zero hs (h.mul hc hx)
  window := rfl

theorem rel_foldl {α σ₁ σ₂ : Type} {P : σ₁ → σ₂ → Prop} {f₁ : σ₁ → α → σ₁} {f₂ : σ₂ → α → σ₂}
    (l : List α) (hf : ∀ a s₁ s₂, P s₁ s₂ → P (f₁ s₁ a) (f₂ s₂ a)) {s₁ : σ₁} {s₂ : σ₂}
    (hs : P s₁ s₂) : P (l.foldl f₁ s₁) (l.foldl f₂ s₂) := by
  induction l generalizing s₁ s₂ with
  | nil => exact hs
  | cons a l ih => exact ih (hf a _ _ hs)

theorem rel_assert_zeros (h : BuilderRel B₁ B₂ R Q) {s₁ : S₁} {s₂ : S₂} {xs : List E₁}
    {ys : List E₂} (hx : List.Forall₂ R xs ys) (hs : Q s₁ s₂) :
    Q (B₁.assert_zeros s₁ xs) (B₂.assert_zeros s₂ ys) := by
  induction hx generalizing s₁ s₂ with
  | nil => exact hs
  | cons hxy _ ih => exact ih (h.assert_zero hs hxy)

theorem rel_map {α : Type} {f₁ : α → E₁} {f₂ : α → E₂} (l : List α) (hf : ∀ a, R (f₁ a) (f₂ a)) :
    List.Forall₂ R (l.map f₁) (l.map f₂) :=
  Plonky3Lean.Proofs.Air.forall₂_map_map fun a _ => hf a

theorem rel_getD {l₁ : List E₁} {l₂ : List E₂} (hl : List.Forall₂ R l₁ l₂) {d₁ : E₁} {d₂ : E₂}
    (hd : R d₁ d₂) (i : ℕ) : R (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction hl generalizing i with
  | nil => exact hd
  | cons hab _ ih => cases i with
    | zero => exact hab
    | succ i => exact ih i

theorem rel_sum (h : BuilderRel B₁ B₂ R Q) {l₁ : List E₁} {l₂ : List E₂}
    (hl : List.Forall₂ R l₁ l₂) : R (sum B₁.toExprOps l₁) (sum B₂.toExprOps l₂) := by
  cases hl with
  | nil => exact h.const 0
  | cons hab hl =>
    simp only [sum]
    induction hl generalizing ‹E₁› ‹E₂› with
    | nil => exact hab
    | cons hcd _ ih => exact ih (h.add hab hcd)

theorem rel_ite {p : Prop} [Decidable p] {a₁ b₁ : E₁} {a₂ b₂ : E₂} (ha : p → R a₁ a₂)
    (hb : ¬ p → R b₁ b₂) : R (if p then a₁ else b₁) (if p then a₂ else b₂) := by
  split_ifs with hp
  · exact ha hp
  · exact hb hp

end rel

/-- Close a relation goal between two runs of one transcribed program, step by step. -/
macro "rel_tac" : tactic => `(tactic| repeat' (first
  | (with_reducible apply rel_foldl <;> intros <;> try beta_reduce)
  | with_reducible apply rel_assert_zeros
  | with_reducible apply BuilderRel.when'
  | (with_reducible apply rel_map <;> intros)
  | (with_reducible apply rel_ite <;> intros)
  | with_reducible apply rel_getD
  | with_reducible apply rel_sum
  | with_reducible apply BuilderRel.add
  | with_reducible apply BuilderRel.sub
  | with_reducible apply BuilderRel.mul
  | with_reducible apply BuilderRel.const
  | with_reducible apply BuilderRel.main_current
  | with_reducible apply BuilderRel.main_next
  | with_reducible apply BuilderRel.is_first_row
  | with_reducible apply BuilderRel.is_transition
  | with_reducible apply BuilderRel.assert_zero
  | with_reducible apply_assumption))

section steps

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
  {loc₁ nxt₁ : ℕ → E₁} {loc₂ nxt₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i))
  (hn : ∀ i, R (nxt₁ i) (nxt₂ i)) {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂)
  {c₁ : E₁} {c₂ : E₂} (hc : R c₁ c₂)
include h hs

theorem rel_eval_round_flags : Q (eval_round_flags B₁ s₁) (eval_round_flags B₂ s₂) := by
  simp only [eval_round_flags, AirBuilder.assert_one, AirBuilder.when_first_row,
    AirBuilder.when_transition]
  rel_tac

include hl

include hc in
theorem rel_assert_first_step :
    Q (assert_first_step B₁ loc₁ c₁ s₁) (assert_first_step B₂ loc₂ c₂ s₂) := by
  simp only [assert_first_step]; rel_tac

include hn hc in
theorem rel_assert_preimage_carry :
    Q (assert_preimage_carry B₁ loc₁ nxt₁ c₁ s₁) (assert_preimage_carry B₂ loc₂ nxt₂ c₂ s₂) := by
  simp only [assert_preimage_carry]; rel_tac

include hc in
theorem rel_assert_export : Q (assert_export B₁ loc₁ c₁ s₁) (assert_export B₂ loc₂ c₂ s₂) := by
  simp only [assert_export, AirBuilder.assert_bool, AirBuilder.bool_check]; rel_tac

theorem rel_assert_c_prime : Q (assert_c_prime B₁ loc₁ s₁) (assert_c_prime B₂ loc₂ s₂) := by
  simp only [assert_c_prime, AirBuilder.assert_bools, AirBuilder.bool_check, List.map_map,
    Function.comp_def, xor3, p3_keccak_air.mirror.xor, double]
  rel_tac

theorem rel_assert_a_limbs : Q (assert_a_limbs B₁ loc₁ s₁) (assert_a_limbs B₂ loc₂ s₂) := by
  simp only [assert_a_limbs, AirBuilder.assert_bools, AirBuilder.bool_check, List.map_map,
    Function.comp_def, p3_keccak_air.mirror.xor, double, limbOf]
  rel_tac

theorem rel_assert_parity : Q (assert_parity B₁ loc₁ s₁) (assert_parity B₂ loc₂ s₂) := by
  simp only [assert_parity, double]; rel_tac

theorem rel_assert_chi : Q (assert_chi B₁ loc₁ s₁) (assert_chi B₂ loc₂ s₂) := by
  simp only [assert_chi, andn, p3_keccak_air.mirror.xor, double, limbOf, b]; rel_tac

theorem rel_assert_a_prime_prime_0_0 :
    Q (assert_a_prime_prime_0_0 B₁ loc₁ s₁) (assert_a_prime_prime_0_0 B₂ loc₂ s₂) := by
  simp only [assert_a_prime_prime_0_0, AirBuilder.assert_bools, AirBuilder.bool_check,
    List.map_map, Function.comp_def, double, limbOf]
  rel_tac

theorem rel_assert_iota : Q (assert_iota B₁ loc₁ s₁) (assert_iota B₂ loc₂ s₂) := by
  simp only [assert_iota, p3_keccak_air.mirror.xor, double, limbOf]; rel_tac

include hn hc in
theorem rel_assert_output :
    Q (assert_output B₁ loc₁ nxt₁ c₁ s₁) (assert_output B₂ loc₂ nxt₂ c₂ s₂) := by
  simp only [assert_output, a_prime_prime_prime]; rel_tac

end steps

theorem eval_parametric : IsParametric (eval (F := F)) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hf := rel_eval_round_flags h hs
  have hl := rel_getD (h.main_current hf) (h.const 0)
  have hn := rel_getD (h.main_next hf) (h.const 0)
  have hnf := h.sub (h.const 1) (hl (col.step_flags (NUM_ROUNDS - 1)))
  have ht := h.mul (h.is_transition hf) hnf
  simp only [eval]
  exact rel_assert_output h hl hn (rel_assert_iota h hl (rel_assert_a_prime_prime_0_0 h hl
    (rel_assert_chi h hl (rel_assert_parity h hl (rel_assert_a_limbs h hl (rel_assert_c_prime h hl
    (rel_assert_export h hl (rel_assert_preimage_carry h hl hn
    (rel_assert_first_step h hl hf (hl _)) ht) hnf))))))) ht

/-- The Keccak-f AIR: 2633 main columns and the transcribed evaluation. -/
def keccakAir : Air F where
  width := NUM_KECCAK_COLS
  eval := eval
  parametric := eval_parametric

end Plonky3Lean.Proofs.KeccakAir
