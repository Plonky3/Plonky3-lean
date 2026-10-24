module

public import Plonky3Lean.Proofs.Blake3Air.Parametric

@[expose] public section

/-!
# The characteristic-2 BLAKE3 AIR is parametric

The transcribed evaluation maps related builders and related states to related states.

That makes it an AIR in the sense of the p3-air model, with 11536 main columns and the degree hint 2.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F]

section rel

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)
include h

/-- Two maps from an index and a bit whose entries are related. -/
abbrev Rel2 (f₁ : ℕ → ℕ → E₁) (f₂ : ℕ → ℕ → E₂) : Prop := ∀ i k, R (f₁ i k) (f₂ i k)

/-- Two states whose bits are related. -/
def StateRel (x₁ : State E₁) (x₂ : State E₂) : Prop :=
  Rel2 (R := R) x₁.a x₂.a ∧ Rel2 (R := R) x₁.b x₂.b ∧ Rel2 (R := R) x₁.c x₂.c ∧ Rel2 (R := R) x₁.d x₂.d

theorem rel_maj {x₁ y₁ z₁ : E₁} {x₂ y₂ z₂ : E₂} (hx : R x₁ x₂) (hy : R y₁ y₂) (hz : R z₁ z₂) :
    R (maj B₁.toExprOps x₁ y₁ z₁) (maj B₂.toExprOps x₂ y₂ z₂) :=
  h.add (h.mul (h.add hx hz) (h.add hy hz)) hz

theorem rel_xor_rotl {x₁ y₁ : ℕ → E₁} {x₂ y₂ : ℕ → E₂} (hx : ∀ k, R (x₁ k) (x₂ k))
    (hy : ∀ k, R (y₁ k) (y₂ k)) (shift k : ℕ) :
    R (xor_rotl B₁.toExprOps x₁ y₁ shift k) (xor_rotl B₂.toExprOps x₂ y₂ shift k) :=
  h.add (hx k) (hy _)

theorem rel_add2 {x₁ y₁ z₁ : ℕ → E₁} {x₂ y₂ z₂ : ℕ → E₂} (hx : ∀ k, R (x₁ k) (x₂ k))
    (hy : ∀ k, R (y₁ k) (y₂ k)) (hz : ∀ k, R (z₁ k) (z₂ k)) {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) :
    Q (binary.add2 B₁ s₁ x₁ y₁ z₁) (binary.add2 B₂ s₂ x₂ y₂ z₂) := by
  have hc : ∀ i, R _ _ := fun i => h.add (h.add (hz i) (hx i)) (hy i)
  unfold binary.add2
  refine rel_foldl _ (fun i _ _ hs' => ?_) (h.assert_zero hs (hc 0))
  exact h.assert_zero hs' (h.add (rel_maj h (hx i) (hy i) (hc i)) (hc (i + 1)))

theorem rel_add3 {x₁ y₁ z₁ c₁ w₁ : ℕ → E₁} {x₂ y₂ z₂ c₂ w₂ : ℕ → E₂} (hx : ∀ k, R (x₁ k) (x₂ k))
    (hy : ∀ k, R (y₁ k) (y₂ k)) (hz : ∀ k, R (z₁ k) (z₂ k)) (hc : ∀ k, R (c₁ k) (c₂ k))
    (hw : ∀ k, R (w₁ k) (w₂ k)) {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) :
    Q (binary.add3 B₁ s₁ x₁ y₁ z₁ c₁ w₁) (binary.add3 B₂ s₂ x₂ y₂ z₂ c₂ w₂) := by
  unfold binary.add3
  refine rel_add2 h (fun i => rel_ite (fun _ => h.add (hx 0) (hy 0))
    (fun _ => h.add (h.add (hx i) (hy i)) (hc _))) hz hw ?_
  refine rel_foldl _ (fun i _ _ hs' => ?_) (h.assert_zero hs (h.add (h.mul (hx 0) (hy 0)) (hc 0)))
  exact h.assert_zero hs' (h.add (rel_maj h (hx (i + 1)) (hy (i + 1)) (hc i)) (hc (i + 1)))

theorem rel_update {f₁ : ℕ → ℕ → E₁} {f₂ : ℕ → ℕ → E₂} (hf : Rel2 (R := R) f₁ f₂) (i : ℕ)
    {g₁ : ℕ → E₁} {g₂ : ℕ → E₂} (hg : ∀ k, R (g₁ k) (g₂ k)) :
    Rel2 (R := R) (Function.update f₁ i g₁) (Function.update f₂ i g₂) := by
  intro j k
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact hg k
  · simp only [Function.update_of_ne hj]; exact hf j k

theorem rel_eval_g {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) {x₁ : State E₁} {x₂ : State E₂}
    (hx : StateRel (R := R) x₁ x₂) (ia ib ic id : ℕ) {mx₁ my₁ c₁ d₁ b₁ c₁' d₁' b₁' : ℕ → E₁}
    {mx₂ my₂ c₂ d₂ b₂ c₂' d₂' b₂' : ℕ → E₂} (hmx : ∀ k, R (mx₁ k) (mx₂ k))
    (hmy : ∀ k, R (my₁ k) (my₂ k)) (hc : ∀ k, R (c₁ k) (c₂ k)) (hd : ∀ k, R (d₁ k) (d₂ k))
    (hb : ∀ k, R (b₁ k) (b₂ k)) (hc' : ∀ k, R (c₁' k) (c₂' k)) (hd' : ∀ k, R (d₁' k) (d₂' k))
    (hb' : ∀ k, R (b₁' k) (b₂' k)) :
    Q (eval_g B₁ s₁ x₁ ia ib ic id mx₁ my₁ c₁ d₁ b₁ c₁' d₁' b₁').1
        (eval_g B₂ s₂ x₂ ia ib ic id mx₂ my₂ c₂ d₂ b₂ c₂' d₂' b₂').1 ∧
      StateRel (R := R) (eval_g B₁ s₁ x₁ ia ib ic id mx₁ my₁ c₁ d₁ b₁ c₁' d₁' b₁').2
        (eval_g B₂ s₂ x₂ ia ib ic id mx₂ my₂ c₂ d₂ b₂ c₂' d₂' b₂').2 := by
  obtain ⟨ha, hb0, hc0, hd0⟩ := hx
  have ha1 := rel_xor_rotl h (hd0 id) hd 16
  have hc1 := rel_xor_rotl h (hb0 ib) hb 12
  have ha2 := rel_xor_rotl h hd hd' 8
  have hc2 := rel_xor_rotl h hb hb' 7
  exact ⟨rel_add2 h hc1 hd' hc2 (rel_add3 h ha1 hb hmy hc' ha2 (rel_add2 h (hc0 ic) hd hc1
      (rel_add3 h (ha ia) (hb0 ib) hmx hc ha1 hs))),
    rel_update h ha ia ha2, rel_update h hb0 ib hb', rel_update h hc0 ic hc2, rel_update h hd0 id hd'⟩

theorem rel_g_step {loc₁ : ℕ → E₁} {loc₂ : ℕ → E₂} (hl : ∀ i, R (loc₁ i) (loc₂ i)) (r g : ℕ)
    {a₁ : S₁ × State E₁} {a₂ : S₂ × State E₂} (ha : Q a₁.1 a₂.1 ∧ StateRel (R := R) a₁.2 a₂.2) :
    Q (g_step B₁ loc₁ r g a₁).1 (g_step B₂ loc₂ r g a₂).1 ∧
      StateRel (R := R) (g_step B₁ loc₁ r g a₁).2 (g_step B₂ loc₂ r g a₂).2 :=
  rel_eval_g h ha.1 ha.2 _ _ _ _ (fun _ => hl _) (fun _ => hl _) (fun _ => hl _) (fun _ => hl _)
    (fun _ => hl _) (fun _ => hl _) (fun _ => hl _) (fun _ => hl _)

end rel

theorem eval_parametric (cb : Bool) : IsParametric (binary.eval (F := F) cb) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hl := rel_getD (h.main_current hs) (h.const 0)
  show Q (binary.eval cb B₁ s₁) (binary.eval cb B₂ s₂)
  simp only [binary.eval, rounds]
  have hs' : Q (if cb then binary.assert_inputs B₁ (fun i => (B₁.main s₁).current.getD i (B₁.const 0)) s₁ else s₁) (if cb then binary.assert_inputs B₂ (fun i => (B₂.main s₂).current.getD i (B₂.const 0)) s₂ else s₂) := by
    split_ifs
    · unfold binary.assert_inputs
      refine rel_foldl₂ (RA := fun (f₁ : ℕ → E₁) (f₂ : ℕ → E₂) => ∀ k, R (f₁ k) (f₂ k)) ?_
        (fun w₁ w₂ _ _ hw hs => ?_) hs
      · refine List.rel_append (List.rel_append ?_ ?_) ?_ <;>
          exact Plonky3Lean.Proofs.Air.forall₂_map_map fun _ _ _ => hl _
      · simp only [AirBuilder.assert_bools, List.map_map]
        exact rel_assert_zeros h (Plonky3Lean.Proofs.Air.forall₂_map_map fun k _ =>
          h.mul (hw k) (h.sub (hw k) (h.const 1))) hs
    · exact hs
  refine (rel_foldl (P := fun (a : S₁ × State E₁) (b : S₂ × State E₂) => Q a.1 b.1 ∧ StateRel (R := R) a.2 b.2) _
    (fun r _ _ hp => rel_foldl (P := fun (a : S₁ × State E₁) (b : S₂ × State E₂) => Q a.1 b.1 ∧
      StateRel (R := R) a.2 b.2) _ (fun g _ _ hp => ?_) hp) ⟨hs', ?_⟩).1
  · exact rel_g_step h hl r g hp
  · exact ⟨fun _ _ => hl _, fun _ _ => hl _, fun _ _ => h.const _, fun _ _ => hl _⟩

/-- The characteristic-2 BLAKE3 AIR, with or without the input booleanity. -/
def binaryAir (cb : Bool) : Air F where
  width := NUM_BLAKE3_BINARY_COLS
  max_constraint_degree := some 2
  eval := binary.eval cb
  parametric := eval_parametric cb

end Plonky3Lean.Proofs.Blake3Air.Binary
