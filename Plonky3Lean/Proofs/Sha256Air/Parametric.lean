module

public import P3Sha256Air
public import Plonky3Lean.Proofs.KeccakAir.Parametric

@[expose] public section

/-!
# The SHA-256 AIRs are parametric

Both transcribed evaluations are programs over any builder.

Related builders and related states give related states, as for every Rust evaluation generic in the builder.

That makes each an AIR of the p3-air model.

- Over a prime field: 7728 main columns, and the declared degree bound 3.
- Over a field of characteristic 2: 23712 main columns, with or without the input booleanity.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror
open Plonky3Lean.Proofs.KeccakAir (rel_foldl rel_assert_zeros rel_map rel_getD rel_ite)

variable {F : Type} [Field F]

theorem rel_foldl₂ {α β σ₁ σ₂ : Type} {P : σ₁ → σ₂ → Prop} {T : α → β → Prop}
    {f₁ : σ₁ → α → σ₁} {f₂ : σ₂ → β → σ₂} {l₁ : List α} {l₂ : List β} (hl : List.Forall₂ T l₁ l₂)
    (hf : ∀ a b s₁ s₂, T a b → P s₁ s₂ → P (f₁ s₁ a) (f₂ s₂ b)) {s₁ : σ₁} {s₂ : σ₂}
    (hs : P s₁ s₂) : P (l₁.foldl f₁ s₁) (l₂.foldl f₂ s₂) := by
  induction hl generalizing s₁ s₂ with
  | nil => exact hs
  | cons hab _ ih => exact ih (hf _ _ _ _ hab hs)

section rel

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
include h

theorem rel_double {a₁ : E₁} {a₂ : E₂} (ha : R a₁ a₂) :
    R (double B₁.toExprOps a₁) (double B₂.toExprOps a₂) := h.add ha ha

theorem rel_xor {a₁ b₁ : E₁} {a₂ b₂ : E₂} (ha : R a₁ a₂) (hb : R b₁ b₂) :
    R (xor B₁.toExprOps a₁ b₁) (xor B₂.toExprOps a₂ b₂) :=
  h.sub (h.add ha hb) (h.mul ha (rel_double h hb))

theorem rel_xor3 {a₁ b₁ c₁ : E₁} {a₂ b₂ c₂ : E₂} (ha : R a₁ a₂) (hb : R b₁ b₂) (hc : R c₁ c₂) :
    R (xor3 B₁.toExprOps a₁ b₁ c₁) (xor3 B₂.toExprOps a₂ b₂ c₂) :=
  rel_xor h (rel_xor h ha hb) hc

theorem rel_exp_u64 {a₁ : E₁} {a₂ : E₂} (ha : R a₁ a₂) (n : ℕ) :
    R (exp_u64 B₁.toExprOps a₁ n) (exp_u64 B₂.toExprOps a₂ n) := by
  unfold exp_u64
  refine (rel_foldl (P := fun (p : E₁ × E₁) (q : E₂ × E₂) => R p.1 q.1 ∧ R p.2 q.2) _ (fun j p q hpq => ?_)
    ⟨ha, h.const 1⟩).2
  exact ⟨h.mul hpq.1 hpq.1, rel_ite (fun _ => h.mul hpq.2 hpq.1) (fun _ => hpq.2)⟩

theorem rel_mul_2exp_u64 {a₁ : E₁} {a₂ : E₂} (ha : R a₁ a₂) (n : ℕ) :
    R (mul_2exp_u64 B₁.toExprOps a₁ n) (mul_2exp_u64 B₂.toExprOps a₂ n) :=
  h.mul ha (rel_exp_u64 h (h.const 2) n)

theorem rel_pack_bits_le {l₁ : List E₁} {l₂ : List E₂} (hl : List.Forall₂ R l₁ l₂) :
    R (pack_bits_le B₁.toExprOps l₁) (pack_bits_le B₂.toExprOps l₂) := by
  unfold pack_bits_le
  have hr := List.forall₂_reverse_iff.mpr hl
  revert hr
  generalize l₁.reverse = r₁
  generalize l₂.reverse = r₂
  intro hr
  cases hr with
  | nil => exact h.const 0
  | cons hab hr => exact rel_foldl₂ hr (fun _ _ _ _ he hp => h.add (rel_double h hp) he) hab

theorem rel_pair {x₁ y₁ : E₁} {x₂ y₂ : E₂} (hx : R x₁ x₂) (hy : R y₁ y₂) :
    List.Forall₂ R [x₁, y₁] [x₂, y₂] := .cons hx (.cons hy .nil)

end rel

/-- Close a relation goal between two runs of one transcribed program, step by step. -/
macro "sha_rel" : tactic => `(tactic| repeat' (first
  | (with_reducible apply rel_foldl <;> intros <;> try beta_reduce)
  | with_reducible apply rel_assert_zeros
  | apply List.Forall₂.cons
  | apply List.Forall₂.nil
  | (with_reducible apply rel_map <;> intros)
  | (with_reducible apply rel_ite <;> intros)
  | with_reducible apply rel_getD
  | with_reducible apply rel_pack_bits_le
  | with_reducible apply rel_mul_2exp_u64
  | with_reducible apply rel_xor3
  | with_reducible apply rel_xor
  | with_reducible apply rel_double
  | with_reducible apply BuilderRel.add
  | with_reducible apply BuilderRel.sub
  | with_reducible apply BuilderRel.mul
  | with_reducible apply BuilderRel.const
  | with_reducible apply BuilderRel.main_current
  | with_reducible apply BuilderRel.assert_zero
  | with_reducible apply_assumption))

section helpers

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
  {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂)
  {a₁ b₁ c₁ d₁ : ℕ → E₁} {a₂ b₂ c₂ d₂ : ℕ → E₂} (ha : ∀ i, R (a₁ i) (a₂ i))
  (hb : ∀ i, R (b₁ i) (b₂ i)) (hc : ∀ i, R (c₁ i) (c₂ i)) (hd : ∀ i, R (d₁ i) (d₂ i))
include h hs ha hb hc

theorem rel_add2 : Q (add2 B₁ s₁ a₁ b₁ c₁) (add2 B₂ s₂ a₂ b₂ c₂) := by
  simp only [add2]; sha_rel

theorem rel_add2_expr_out : Q (add2_expr_out B₁ s₁ a₁ b₁ c₁) (add2_expr_out B₂ s₂ a₂ b₂ c₂) := by
  simp only [add2_expr_out]; sha_rel

include hd

theorem rel_add3 : Q (add3 B₁ s₁ a₁ b₁ c₁ d₁) (add3 B₂ s₂ a₂ b₂ c₂ d₂) := by
  simp only [add3]; sha_rel

theorem rel_add3_expr_out :
    Q (add3_expr_out B₁ s₁ a₁ b₁ c₁ d₁) (add3_expr_out B₂ s₂ a₂ b₂ c₂ d₂) := by
  simp only [add3_expr_out]; sha_rel


theorem rel_ch : Q (assert_ch_matches B₁ s₁ a₁ b₁ c₁ d₁) (assert_ch_matches B₂ s₂ a₂ b₂ c₂ d₂) := by
  simp only [assert_ch_matches]; sha_rel

theorem rel_maj : Q (assert_maj_matches B₁ s₁ a₁ b₁ c₁ d₁) (assert_maj_matches B₂ s₂ a₂ b₂ c₂ d₂) := by
  simp only [assert_maj_matches]; sha_rel

omit hc hd in
theorem rel_packed : Q (assert_packed_equals_bits B₁ s₁ a₁ b₁)
    (assert_packed_equals_bits B₂ s₂ a₂ b₂) := by
  simp only [assert_packed_equals_bits, pack_word]; sha_rel

omit hc hd in
theorem rel_sigma (spec : SigmaSpec) :
    Q (assert_sigma_matches B₁ s₁ a₁ spec b₁) (assert_sigma_matches B₂ s₂ a₂ spec b₂) := by
  cases spec <;> simp only [assert_sigma_matches, sigma_params] <;> sha_rel <;>
    exact rel_ite (fun _ => ha _) (fun _ => h.const 0)

end helpers

omit [Field F] in
theorem rel_pack_word [Field F] {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁}
    {B₂ : AirBuilder F E₂ S₂} {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
    {a₁ : ℕ → E₁} {a₂ : ℕ → E₂} (ha : ∀ i, R (a₁ i) (a₂ i)) (limb : ℕ) :
    R (pack_word B₁.toExprOps a₁ limb) (pack_word B₂.toExprOps a₂ limb) := by
  simp only [pack_word]; sha_rel

section steps

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
  {loc₁ : ℕ → E₁} {loc₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i)) {s₁ : S₁} {s₂ : S₂}
  (hs : Q s₁ s₂)
include h hl hs

theorem rel_bit_range_checks :
    Q (eval_bit_range_checks B₁ loc₁ s₁) (eval_bit_range_checks B₂ loc₂ s₂) := by
  simp only [eval_bit_range_checks, AirBuilder.assert_bools, AirBuilder.bool_check, List.map_map,
    Function.comp_def]
  sha_rel

theorem rel_initial_state : Q (eval_initial_state B₁ loc₁ s₁) (eval_initial_state B₂ loc₂ s₂) := by
  simp only [eval_initial_state]
  refine rel_foldl (P := Q) _ (fun _ _ _ hq => ?_) (rel_foldl (P := Q) _ (fun _ _ _ hq => ?_) hs) <;>
    exact rel_packed h hq (fun _ => hl _) (fun _ => hl _)

theorem rel_message_schedule :
    Q (eval_message_schedule B₁ loc₁ s₁) (eval_message_schedule B₂ loc₂ s₂) := by
  simp only [eval_message_schedule]
  refine rel_foldl (P := Q) _ (fun _ _ _ hq => ?_) hs
  have hw := fun t => rel_pack_word h (fun b => hl (col.w t b))
  exact rel_add3_expr_out h (rel_add2 h (rel_sigma h (rel_sigma h hq (fun _ => hl _) (fun _ => hl _) _)
    (fun _ => hl _) (fun _ => hl _) _) (fun _ => hl _) (fun _ => hl _) (hw _)) (hw _) (fun _ => hl _)
    (fun _ => hl _) (hw _)

theorem rel_compression : Q (eval_compression B₁ loc₁ s₁) (eval_compression B₂ loc₂ s₂) := by
  simp only [eval_compression]
  refine rel_foldl (P := Q) _ (fun t _ _ hq => ?_) hs
  have ha := fun k => rel_pack_word h (fun b => hl (col.a_chain k b))
  have he := fun k => rel_pack_word h (fun b => hl (col.e_chain k b))
  have hw := rel_pack_word h (fun b => hl (col.w t b))
  have hk := fun limb => rel_ite (R := R) (p := limb = 0)
    (fun _ => h.const ((kOf t &&& 0xFFFF : ℕ) : F)) (fun _ => h.const ((kOf t >>> BITS_PER_LIMB : ℕ) : F))
  exact rel_add2_expr_out h (rel_add3_expr_out h (rel_maj h (rel_sigma h (rel_add3 h (rel_add3 h
    (rel_ch h (rel_sigma h hq (fun _ => hl _) (fun _ => hl _) _) (fun _ => hl _) (fun _ => hl _)
    (fun _ => hl _) (fun _ => hl _)) (fun _ => hl _) (fun _ => hl _) (fun _ => hl _) (he _))
    (fun _ => hl _) (fun _ => hl _) hk hw) (fun _ => hl _) (fun _ => hl _) _) (fun _ => hl _)
    (fun _ => hl _) (fun _ => hl _) (fun _ => hl _)) (ha _) (fun _ => hl _) (fun _ => hl _)
    (fun _ => hl _)) (he _) (fun _ => hl _) (ha _)

theorem rel_finalization : Q (eval_finalization B₁ loc₁ s₁) (eval_finalization B₂ loc₂ s₂) := by
  simp only [eval_finalization]
  refine rel_foldl (P := Q) _ (fun _ _ _ hq => ?_) (rel_foldl (P := Q) _ (fun _ _ _ hq => ?_) hs) <;>
    exact rel_add2_expr_out h hq (rel_pack_word h (fun _ => hl _)) (fun _ => hl _)
      (rel_pack_word h (fun _ => hl _))

end steps

theorem eval_parametric : IsParametric (eval (F := F)) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hl := rel_getD (h.main_current hs) (h.const 0)
  simp only [eval]
  exact rel_finalization h hl (rel_compression h hl (rel_message_schedule h hl
    (rel_initial_state h hl (rel_bit_range_checks h hl hs))))

/-- The SHA-256 AIR over a prime field.

It has 7728 main columns and the declared degree bound 3. -/
def sha256Air : Air F where
  width := NUM_SHA256_COLS
  max_constraint_degree := some 3
  eval := eval
  parametric := eval_parametric

/-! ## The AIR over a field of characteristic 2 -/

section binary

open p3_sha256_air.mirror.binary

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
include h

/-- Two maps of bits related entrywise. -/
abbrev RF (R : E₁ → E₂ → Prop) (f₁ : ℕ → E₁) (f₂ : ℕ → E₂) : Prop := ∀ i, R (f₁ i) (f₂ i)

theorem rel_bmaj {x₁ y₁ z₁ : E₁} {x₂ y₂ z₂ : E₂} (hx : R x₁ x₂) (hy : R y₁ y₂) (hz : R z₁ z₂) :
    R (maj B₁.toExprOps x₁ y₁ z₁) (maj B₂.toExprOps x₂ y₂ z₂) :=
  h.add (h.mul (h.add hx hz) (h.add hy hz)) hz

theorem rel_xor3_rot {x₁ : ℕ → E₁} {x₂ : ℕ → E₂} (hx : RF R x₁ x₂) (r0 r1 r2 : ℕ) :
    RF R (xor3_rot B₁.toExprOps x₁ r0 r1 r2) (xor3_rot B₂.toExprOps x₂ r0 r1 r2) := fun _ =>
  h.add (h.add (hx _) (hx _)) (hx _)

theorem rel_xor3_shift {x₁ : ℕ → E₁} {x₂ : ℕ → E₂} (hx : RF R x₁ x₂) (r0 r1 s : ℕ) :
    RF R (xor3_shift B₁.toExprOps x₁ r0 r1 s) (xor3_shift B₂.toExprOps x₂ r0 r1 s) := fun _ =>
  rel_ite (fun _ => h.add (h.add (hx _) (hx _)) (hx _)) (fun _ => h.add (hx _) (hx _))

theorem rel_add_many {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) {w₁ c₁ : List (ℕ → E₁)}
    {w₂ c₂ : List (ℕ → E₂)} (hw : List.Forall₂ (RF R) w₁ w₂) (hc : List.Forall₂ (RF R) c₁ c₂)
    {u₁ : ℕ → E₁} {u₂ : ℕ → E₂} (hu : RF R u₁ u₂) :
    Q (add_many B₁ s₁ w₁ c₁ u₁) (add_many B₂ s₂ w₂ c₂ u₂) := by
  unfold add_many
  rw [hc.length_eq]
  have hz : List.Forall₂ (fun a b => RF R a.1 b.1 ∧ RF R a.2 b.2)
      (((w₁.drop 1).take c₂.length).zip c₁) (((w₂.drop 1).take c₂.length).zip c₂) := by
    have h1 : List.Forall₂ (RF R) ((w₁.drop 1).take c₂.length) ((w₂.drop 1).take c₂.length) :=
      List.forall₂_take _ (List.forall₂_drop _ hw)
    clear hu hs
    revert h1
    generalize (w₁.drop 1).take c₂.length = a₁
    generalize (w₂.drop 1).take c₂.length = a₂
    intro h1
    induction h1 generalizing c₁ c₂ with
    | nil => cases hc <;> exact .nil
    | cons hab _ ih => cases hc with
      | nil => exact .nil
      | cons hcd hc' => exact .cons ⟨hab, hcd⟩ (ih hc')
  obtain ⟨hs', hp⟩ := rel_foldl₂ (P := fun (a : S₁ × (ℕ → E₁)) (b : S₂ × (ℕ → E₂)) =>
      Q a.1 b.1 ∧ RF R a.2 b.2) (f₁ := add_many_step B₁) (f₂ := add_many_step B₂) hz
    (fun a b x y hab hxy => by
      simp only [add_many_step]
      exact ⟨rel_foldl (P := Q) _ (fun i _ _ hq => h.assert_zero hq (h.add (rel_bmaj h (hxy.2 i)
        (hab.1 i) (hab.2 (i - 1))) (hab.2 i))) (h.assert_zero hxy.1 (h.add (h.mul (hxy.2 0) (hab.1 0))
        (hab.2 0))), fun i => rel_ite (fun _ => h.add (hxy.2 0) (hab.1 0))
        (fun _ => h.add (h.add (hxy.2 i) (hab.1 i)) (hab.2 (i - 1)))⟩)
    (show Q (s₁, w₁.getD 0 fun _ => B₁.const 0).1 (s₂, w₂.getD 0 fun _ => B₂.const 0).1 ∧ _ from
      ⟨hs, rel_getD hw (fun _ => h.const 0) 0⟩)
  have hl := rel_getD hw (fun _ => h.const 0) (c₂.length + 1)
  simp only []
  have hcar := fun i => h.add (h.add (hu i) (hp i)) (hl i)
  exact rel_foldl (P := Q) _ (fun i _ _ hq => h.assert_zero hq (h.add (rel_bmaj h (hp i) (hl i)
    (hcar i)) (hcar (i + 1)))) (h.assert_zero hs' (hcar 0))

omit h in
theorem binary_eval_parametric (cb : Bool) : IsParametric (binary.eval (F := F) cb) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hl := rel_getD (h.main_current hs) (h.const 0)
  simp only [binary.eval]
  refine rel_foldl (P := Q) _ (fun i _ _ hq => ?_) ?_
  · by_cases hi : i < 4 <;> simp only [hi, ite_true, ite_false] <;>
      exact rel_add_many h hq (.cons (fun _ => hl _) (.cons (fun _ => hl _) .nil)) .nil (fun _ => hl _)
  refine rel_foldl (P := Q) _ (fun t _ _ hq => ?_) ?_
  · refine rel_add_many h (rel_add_many h (rel_add_many h ?_ (.cons (fun _ => hl _) (.cons
      (rel_xor3_rot h (fun _ => hl _) _ _ _) (.cons (fun _ => hl _) (.cons (fun _ => h.const _)
      (.cons (fun _ => hl _) .nil))))) (rel_map _ fun _ _ => hl _) (fun _ => hl _))
      (.cons (fun _ => hl _) (.cons (fun _ => hl _) .nil)) .nil (fun _ => hl _))
      (.cons (fun _ => hl _) (.cons (rel_xor3_rot h (fun _ => hl _) _ _ _) (.cons (fun _ => hl _) .nil)))
      (.cons (fun _ => hl _) .nil) (fun _ => hl _)
    refine rel_foldl (P := Q) _ (fun i _ _ hq' => ?_) (rel_foldl (P := Q) _ (fun i _ _ hq' => ?_) hq)
    · exact h.assert_zero hq' (h.add (rel_bmaj h (hl _) (hl _) (hl _)) (hl _))
    · exact h.assert_zero hq' (h.add (h.add (h.mul (hl _) (h.add (hl _) (hl _))) (hl _)) (hl _))
  refine rel_foldl (P := Q) _ (fun i _ _ hq => rel_add_many h hq
    (.cons (rel_xor3_shift h (fun _ => hl _) _ _ _) (.cons (fun _ => hl _)
      (.cons (rel_xor3_shift h (fun _ => hl _) _ _ _) (.cons (fun _ => hl _) .nil))))
    (rel_map _ fun _ _ => hl _) (fun _ => hl _)) ?_
  split
  · refine rel_foldl₂ (P := Q) (T := RF R) ?_ (fun a b _ _ hab hq => ?_) hs
    · exact List.rel_append (List.rel_append (rel_map _ fun _ _ => hl _) (rel_map _ fun _ _ => hl _))
        (rel_map _ fun _ _ => hl _)
    · simp only [AirBuilder.assert_bools, List.map_map, Function.comp_def, AirBuilder.bool_check]
      exact rel_assert_zeros h (rel_map _ fun i => h.mul (hab i) (h.sub (hab i) (h.const 1))) hq
  · exact hs

/-- The SHA-256 AIR over a field of characteristic 2, with or without the input booleanity. -/
def binaryAir (cb : Bool) : Air F where
  width := p3_sha256_air.mirror.binary.NUM_SHA256_BINARY_COLS
  max_constraint_degree := some 2
  eval := binary.eval cb
  parametric := binary_eval_parametric cb

end binary

end Plonky3Lean.Proofs.Sha256Air
