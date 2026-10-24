module

public import P3Blake3Air
public import Plonky3Lean.Proofs.KeccakAir.Parametric

@[expose] public section

/-!
# The BLAKE3 AIRs are parametric

Each transcribed evaluation is a program over any builder.

Related builders and related states give related states, as for every Rust evaluation generic in the builder.

That makes each an AIR in the sense of the p3-air model:

- over a prime field, 9168 main columns and the degree hint 3,
- over a field of characteristic 2, 11536 main columns and the degree hint 2.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror
open Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

section rel

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
include h

theorem rel_pack {l₁ : List E₁} {l₂ : List E₂} (hl : List.Forall₂ R l₁ l₂) :
    R (pack_bits_le B₁.toExprOps l₁) (pack_bits_le B₂.toExprOps l₂) := by
  unfold pack_bits_le
  have hr := List.forall₂_reverse_iff.mpr hl
  generalize l₁.reverse = r₁ at hr ⊢
  generalize l₂.reverse = r₂ at hr ⊢
  cases hr with
  | nil => exact h.const 0
  | cons hab hl =>
    induction hl generalizing ‹E₁› ‹E₂› with
    | nil => exact hab
    | cons hcd _ ih => exact ih (h.add (h.add hab hab) hcd)

theorem rel_low16 {f₁ : ℕ → E₁} {f₂ : ℕ → E₂} (hf : ∀ k, R (f₁ k) (f₂ k)) :
    R (low16 B₁.toExprOps f₁) (low16 B₂.toExprOps f₂) := rel_pack h (rel_map _ hf)

theorem rel_high16 {f₁ : ℕ → E₁} {f₂ : ℕ → E₂} (hf : ∀ k, R (f₁ k) (f₂ k)) :
    R (high16 B₁.toExprOps f₁) (high16 B₂.toExprOps f₂) := rel_pack h (rel_map _ hf)

variable {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂)
include hs

theorem rel_add3 {a₁ b₁ c₁ d₁ : ℕ → E₁} {a₂ b₂ c₂ d₂ : ℕ → E₂} (ha : ∀ l, R (a₁ l) (a₂ l))
    (hb : ∀ l, R (b₁ l) (b₂ l)) (hc : ∀ l, R (c₁ l) (c₂ l)) (hd : ∀ l, R (d₁ l) (d₂ l)) :
    Q (add3 B₁ s₁ a₁ b₁ c₁ d₁) (add3 B₂ s₂ a₂ b₂ c₂ d₂) := by
  simp only [add3, mul_2exp]
  refine rel_assert_zeros h (.cons ?_ (.cons ?_ .nil)) hs <;> rel_tac

theorem rel_add2 {a₁ b₁ c₁ : ℕ → E₁} {a₂ b₂ c₂ : ℕ → E₂} (ha : ∀ l, R (a₁ l) (a₂ l))
    (hb : ∀ l, R (b₁ l) (b₂ l)) (hc : ∀ l, R (c₁ l) (c₂ l)) :
    Q (add2 B₁ s₁ a₁ b₁ c₁) (add2 B₂ s₂ a₂ b₂ c₂) := by
  simp only [add2, mul_2exp]
  refine rel_assert_zeros h (.cons ?_ (.cons ?_ .nil)) hs <;> rel_tac

theorem rel_xor_32_shift {a₁ b₁ c₁ : ℕ → E₁} {a₂ b₂ c₂ : ℕ → E₂} (ha : ∀ l, R (a₁ l) (a₂ l))
    (hb : ∀ l, R (b₁ l) (b₂ l)) (hc : ∀ l, R (c₁ l) (c₂ l)) (shift : ℕ) :
    Q (xor_32_shift B₁ s₁ a₁ b₁ c₁ shift) (xor_32_shift B₂ s₂ a₂ b₂ c₂ shift) := by
  simp only [xor_32_shift, AirBuilder.assert_bools, AirBuilder.bool_check, List.map_map,
    Function.comp_def, p3_keccak_air.mirror.xor, p3_keccak_air.mirror.double]
  refine rel_assert_zeros h ?_ (rel_assert_zeros h (rel_map _ fun _ => by rel_tac) hs)
  exact .cons (h.sub (ha 0) (rel_pack h (rel_map _ fun _ => by rel_tac)))
    (.cons (h.sub (ha 1) (rel_pack h (rel_map _ fun _ => by rel_tac))) .nil)

/-- Two quarter rounds whose entries are related. -/
structure QRRel (t₁ : QuarterRound E₁ E₁) (t₂ : QuarterRound E₂ E₂) : Prop where
  a : ∀ k, R (t₁.a k) (t₂.a k)
  b : ∀ k, R (t₁.b k) (t₂.b k)
  c : ∀ k, R (t₁.c k) (t₂.c k)
  d : ∀ k, R (t₁.d k) (t₂.d k)
  m : ∀ k, R (t₁.m_two_i k) (t₂.m_two_i k)
  a' : ∀ k, R (t₁.a_prime k) (t₂.a_prime k)
  b' : ∀ k, R (t₁.b_prime k) (t₂.b_prime k)
  c' : ∀ k, R (t₁.c_prime k) (t₂.c_prime k)
  d' : ∀ k, R (t₁.d_prime k) (t₂.d_prime k)
  m' : ∀ k, R (t₁.m_two_i_plus_one k) (t₂.m_two_i_plus_one k)
  a'' : ∀ k, R (t₁.a_output k) (t₂.a_output k)
  b'' : ∀ k, R (t₁.b_output k) (t₂.b_output k)
  c'' : ∀ k, R (t₁.c_output k) (t₂.c_output k)
  d'' : ∀ k, R (t₁.d_output k) (t₂.d_output k)

omit hs in
theorem rel_limbs {f₁ : ℕ → E₁} {f₂ : ℕ → E₂} (hf : ∀ k, R (f₁ k) (f₂ k)) (l : ℕ) :
    R (if l = 0 then low16 B₁.toExprOps f₁ else high16 B₁.toExprOps f₁)
      (if l = 0 then low16 B₂.toExprOps f₂ else high16 B₂.toExprOps f₂) :=
  rel_ite (fun _ => rel_low16 h hf) (fun _ => rel_high16 h hf)

omit hs in
theorem rel_quarter_round {t₁ : QuarterRound E₁ E₁} {t₂ : QuarterRound E₂ E₂} (ht : QRRel (R := R) t₁ t₂)
    {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) :
    Q (quarter_round_function B₁ s₁ t₁) (quarter_round_function B₂ s₂ t₂) := by
  simp only [quarter_round_function]
  exact rel_xor_32_shift h (rel_add2 h (rel_xor_32_shift h (rel_add3 h (rel_xor_32_shift h
    (rel_add2 h (rel_xor_32_shift h (rel_add3 h hs ht.a' ht.a (rel_limbs h ht.b) ht.m) ht.a' ht.d ht.d' _)
    ht.c' ht.c (rel_limbs h ht.d')) ht.c' ht.b ht.b' _) ht.a'' ht.a' (rel_limbs h ht.b') ht.m')
    ht.a'' ht.d' ht.d'' _) ht.c'' ht.c' (rel_limbs h ht.d'')) ht.c'' ht.b' ht.b'' _

/-- Two states whose cells are related. -/
def StRel (x₁ : Blake3State E₁) (x₂ : Blake3State E₂) : Prop :=
  (∀ j k, R (x₁.row0 j k) (x₂.row0 j k)) ∧ (∀ j k, R (x₁.row1 j k) (x₂.row1 j k)) ∧
    (∀ j k, R (x₁.row2 j k) (x₂.row2 j k)) ∧ (∀ j k, R (x₁.row3 j k) (x₂.row3 j k))

omit hs in
theorem rel_verify_round {x₁ : Blake3State E₁} {x₂ : Blake3State E₂} (hx : StRel (R := R) x₁ x₂)
    {loc₁ : ℕ → E₁} {loc₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i)) (r : ℕ)
    {m₁ : ℕ → ℕ → E₁} {m₂ : ℕ → ℕ → E₂} (hm : ∀ i l, R (m₁ i l) (m₂ i l)) {s₁ : S₁} {s₂ : S₂}
    (hs : Q s₁ s₂) :
    Q (verify_round B₁ s₁ x₁ (fullRoundAt loc₁ r) m₁) (verify_round B₂ s₂ x₂ (fullRoundAt loc₂ r) m₂) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  simp only [verify_round]
  refine rel_foldl _ (fun i _ _ hs => rel_quarter_round h ⟨fun _ => hl _, fun _ => hl _, fun _ => hl _,
    fun _ => hl _, hm _, fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _, hm _,
    fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _⟩ hs) ?_
  exact rel_foldl _ (fun i _ _ hs => rel_quarter_round h ⟨h0 _, h1 _, h2 _, h3 _, hm _,
    fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _, hm _, fun _ => hl _, fun _ => hl _,
    fun _ => hl _, fun _ => hl _⟩ hs) hs

omit hs in
theorem rel_stateAt {loc₁ : ℕ → E₁} {loc₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i)) (base : ℕ) :
    StRel (R := R) (stateAt loc₁ base) (stateAt loc₂ base) :=
  ⟨fun _ _ => hl _, fun _ _ => hl _, fun _ _ => hl _, fun _ _ => hl _⟩

end rel

theorem rel_foldl₂ {α₁ α₂ σ₁ σ₂ : Type} {RA : α₁ → α₂ → Prop} {P : σ₁ → σ₂ → Prop}
    {f₁ : σ₁ → α₁ → σ₁} {f₂ : σ₂ → α₂ → σ₂} {l₁ : List α₁} {l₂ : List α₂} (hl : List.Forall₂ RA l₁ l₂)
    (hf : ∀ a₁ a₂ s₁ s₂, RA a₁ a₂ → P s₁ s₂ → P (f₁ s₁ a₁) (f₂ s₂ a₂)) {s₁ : σ₁} {s₂ : σ₂}
    (hs : P s₁ s₂) : P (l₁.foldl f₁ s₁) (l₂.foldl f₂ s₂) := by
  induction hl generalizing s₁ s₂ with
  | nil => exact hs
  | cons ha _ ih => exact ih (hf _ _ _ _ ha hs)

section steps

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
  {loc₁ : ℕ → E₁} {loc₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i)) {s₁ : S₁} {s₂ : S₂}
  (hs : Q s₁ s₂)
include h hl hs

theorem rel_assert_inputs : Q (assert_inputs B₁ loc₁ s₁) (assert_inputs B₂ loc₂ s₂) := by
  unfold assert_inputs
  refine rel_foldl₂ (RA := fun f₁ f₂ => ∀ k, R (f₁ k) (f₂ k)) ?_ (fun w₁ w₂ _ _ hw hs =>
    rel_foldl _ (fun k _ _ hs => by
      simp only [AirBuilder.assert_bool, AirBuilder.bool_check]
      exact h.assert_zero hs (h.mul (hw k) (h.sub (hw k) (h.const 1)))) hs) hs
  refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_ <;>
    exact Plonky3Lean.Proofs.Air.forall₂_map_map fun _ _ _ => hl _

theorem rel_assert_initial_row0 :
    Q (assert_initial_row0 B₁ loc₁ s₁) (assert_initial_row0 B₂ loc₂ s₂) := by
  unfold assert_initial_row0
  refine rel_foldl _ (fun j _ _ hs => ?_) hs
  simp only [AirBuilder.assert_eq]
  exact h.assert_zero (h.assert_zero hs (h.sub (rel_low16 h fun _ => hl _) (hl _)))
    (h.sub (rel_high16 h fun _ => hl _) (hl _))

theorem rel_assert_initial_row2 :
    Q (assert_initial_row2 B₁ loc₁ s₁) (assert_initial_row2 B₂ loc₂ s₂) := by
  unfold assert_initial_row2
  refine rel_foldl _ (fun j _ _ hs => ?_) hs
  simp only [AirBuilder.assert_eq]
  exact h.assert_zero (h.assert_zero hs (h.sub (hl _) (h.const _))) (h.sub (hl _) (h.const _))

theorem rel_verify_rounds : Q (verify_rounds B₁ loc₁ s₁) (verify_rounds B₂ loc₂ s₂) := by
  unfold verify_rounds
  refine rel_foldl _ (fun r _ _ hs => rel_verify_round h ?_ hl r ?_ hs) hs
  · unfold round_input
    split_ifs
    · exact ⟨fun _ _ => hl _, fun _ _ => hl _, fun _ _ => hl _, fun _ _ => hl _⟩
    · exact rel_stateAt h hl _
  · induction r with
    | zero => exact fun i l => rel_limbs h (fun _ => hl _) l
    | succ r ih =>
      intro i l
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ih _ l

theorem rel_assert_helpers : Q (assert_helpers B₁ loc₁ s₁) (assert_helpers B₂ loc₂ s₂) := by
  unfold assert_helpers final
  refine rel_foldl _ (fun j _ _ hs => ?_) hs
  simp only [AirBuilder.assert_eq]
  exact h.assert_zero (h.assert_zero hs (h.sub (rel_low16 h fun _ => hl _) (hl _)))
    (h.sub (rel_high16 h fun _ => hl _) (hl _))

theorem rel_assert_outputs_bool :
    Q (assert_outputs_bool B₁ loc₁ s₁) (assert_outputs_bool B₂ loc₂ s₂) := by
  unfold assert_outputs_bool
  refine rel_foldl _ (fun j _ _ hs => rel_foldl _ (fun k _ _ hs => ?_) hs) hs
  simp only [AirBuilder.assert_bool, AirBuilder.bool_check]
  exact h.assert_zero hs (h.mul (hl _) (h.sub (hl _) (h.const 1)))

theorem rel_assert_output_row0 :
    Q (assert_output_row0 B₁ loc₁ s₁) (assert_output_row0 B₂ loc₂ s₂) := by
  unfold assert_output_row0 final
  refine rel_foldl _ (fun j _ _ hs' => ?_) hs
  exact rel_xor_32_shift h hs' (fun _ => hl _) (fun _ => hl _) (fun _ => hl _) 0

omit hl in
theorem rel_assert_output_xor (q : ℕ) {x₁ y₁ : ℕ → ℕ → E₁} {x₂ y₂ : ℕ → ℕ → E₂}
    (hx : ∀ j k, R (x₁ j k) (x₂ j k)) (hy : ∀ j k, R (y₁ j k) (y₂ j k)) (hl : ∀ i, R (loc₁ i) (loc₂ i)) :
    Q (assert_output_xor B₁ loc₁ q x₁ y₁ s₁) (assert_output_xor B₂ loc₂ q x₂ y₂ s₂) := by
  unfold assert_output_xor
  refine rel_foldl _ (fun j _ _ hs => rel_foldl _ (fun k _ _ hs => ?_) hs) hs
  simp only [AirBuilder.assert_eq, p3_keccak_air.mirror.xor, p3_keccak_air.mirror.double]
  exact h.assert_zero hs (h.sub (hl _) (h.sub (h.add (hx j k) (hy j k))
    (h.mul (hx j k) (h.add (hy j k) (hy j k)))))

end steps

theorem eval_parametric : IsParametric (eval (F := F)) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hl := rel_getD (h.main_current hs) (h.const 0)
  show Q (eval B₁ s₁) (eval B₂ s₂)
  simp only [eval]
  exact rel_assert_output_xor h (rel_assert_output_xor h (rel_assert_output_xor h
    (rel_assert_output_row0 h hl (rel_assert_outputs_bool h hl (rel_assert_helpers h hl
    (rel_verify_rounds h hl (rel_assert_initial_row2 h hl (rel_assert_initial_row0 h hl
    (rel_assert_inputs h hl hs))))))) 1 (fun _ _ => hl _) (fun _ _ => hl _) hl) 2
    (fun _ _ => hl _) (fun _ _ => hl _) hl) 3 (fun _ _ => hl _) (fun _ _ => hl _) hl

/-- The BLAKE3 AIR over a prime field: 9168 main columns, the degree hint 3 and the transcribed evaluation. -/
def blake3Air : Air F where
  width := NUM_BLAKE3_COLS
  max_constraint_degree := some 3
  eval := eval
  parametric := eval_parametric

end Plonky3Lean.Proofs.Blake3Air
