module

public import P3Blake2sAir
public import Plonky3Lean.Proofs.Sha256Air.Parametric

@[expose] public section

/-!
# The BLAKE2s AIR is parametric

The transcribed evaluation is a program over any builder.

Related builders and related states give related states, as for every Rust evaluation generic in the builder.

That makes it an AIR of the p3-air model, with 16033 main columns and the declared degree bound 2.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror
open Plonky3Lean.Proofs.KeccakAir (rel_foldl rel_assert_zeros rel_map rel_getD rel_ite)

variable {F : Type} [Field F]

section rel

variable {E₁ S₁ E₂ S₂ : Type} {B₁ : AirBuilder F E₁ S₁} {B₂ : AirBuilder F E₂ S₂}
  {R : E₁ → E₂ → Prop} {Q : S₁ → S₂ → Prop} (h : BuilderRel B₁ B₂ R Q)

/-- Two maps of bits related entrywise. -/
abbrev RF (R : E₁ → E₂ → Prop) (f₁ : ℕ → E₁) (f₂ : ℕ → E₂) : Prop := ∀ i, R (f₁ i) (f₂ i)

/-- Two working states related word by word. -/
def RS (R : E₁ → E₂ → Prop) (s₁ : State E₁) (s₂ : State E₂) : Prop :=
  ∀ i, RF R (s₁.a i) (s₂.a i) ∧ RF R (s₁.b i) (s₂.b i) ∧ RF R (s₁.c i) (s₂.c i) ∧
    RF R (s₁.d i) (s₂.d i)

theorem rf_update {f₁ : ℕ → ℕ → E₁} {f₂ : ℕ → ℕ → E₂} (hf : ∀ i, RF R (f₁ i) (f₂ i)) (j : ℕ)
    {w₁ : ℕ → E₁} {w₂ : ℕ → E₂} (hw : RF R w₁ w₂) (i : ℕ) :
    RF R (Function.update f₁ j w₁ i) (Function.update f₂ j w₂ i) := by
  by_cases hi : i = j
  · subst hi; simpa using hw
  · simpa [Function.update_of_ne hi] using hf i

include h

theorem rel_maj {x₁ y₁ z₁ : E₁} {x₂ y₂ z₂ : E₂} (hx : R x₁ x₂) (hy : R y₁ y₂) (hz : R z₁ z₂) :
    R (maj B₁.toExprOps x₁ y₁ z₁) (maj B₂.toExprOps x₂ y₂ z₂) :=
  h.add (h.mul (h.add hx hz) (h.add hy hz)) hz

theorem rel_xor_rotl {x₁ y₁ : ℕ → E₁} {x₂ y₂ : ℕ → E₂} (hx : RF R x₁ x₂) (hy : RF R y₁ y₂) (n : ℕ) :
    RF R (xor_rotl B₁.toExprOps x₁ y₁ n) (xor_rotl B₂.toExprOps x₂ y₂ n) := fun _ =>
  h.add (hx _) (hy _)

theorem rel_add2 {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) {x₁ y₁ u₁ : ℕ → E₁} {x₂ y₂ u₂ : ℕ → E₂}
    (hx : RF R x₁ x₂) (hy : RF R y₁ y₂) (hu : RF R u₁ u₂) :
    Q (add2 B₁ s₁ x₁ y₁ u₁) (add2 B₂ s₂ x₂ y₂ u₂) := by
  unfold add2
  have hc := fun i => h.add (h.add (hu i) (hx i)) (hy i)
  exact rel_foldl (P := Q) _ (fun i _ _ hq => h.assert_zero hq (h.add (rel_maj h (hx i) (hy i) (hc i))
    (hc (i + 1)))) (h.assert_zero hs (hc 0))

theorem rel_add3 {s₁ : S₁} {s₂ : S₂} (hs : Q s₁ s₂) {x₁ y₁ z₁ c₁ u₁ : ℕ → E₁}
    {x₂ y₂ z₂ c₂ u₂ : ℕ → E₂} (hx : RF R x₁ x₂) (hy : RF R y₁ y₂) (hz : RF R z₁ z₂)
    (hc : RF R c₁ c₂) (hu : RF R u₁ u₂) :
    Q (add3 B₁ s₁ x₁ y₁ z₁ c₁ u₁) (add3 B₂ s₂ x₂ y₂ z₂ c₂ u₂) := by
  unfold add3
  refine rel_add2 h ?_ (fun _ => rel_ite (fun _ => h.add (hx 0) (hy 0))
    (fun _ => h.add (h.add (hx _) (hy _)) (hc _))) hz hu
  exact rel_foldl (P := Q) _ (fun i _ _ hq => h.assert_zero hq (h.add (rel_maj h (hx i) (hy i) (hc (i - 1)))
    (hc i))) (h.assert_zero hs (h.add (h.mul (hx 0) (hy 0)) (hc 0)))

theorem rel_eval_g {s₁ : S₁} {s₂ : S₂} {st₁ : State E₁} {st₂ : State E₂}
    (hs : Q s₁ s₂ ∧ RS R st₁ st₂) (slots : List ℕ) {mx₁ my₁ : ℕ → E₁} {mx₂ my₂ : ℕ → E₂}
    (hmx : RF R mx₁ mx₂) (hmy : RF R my₁ my₂) {g₁ : Blake2sBinaryGCols E₁} {g₂ : Blake2sBinaryGCols E₂}
    (hg : RF R g₁.add1_carries g₂.add1_carries ∧ RF R g₁.d1 g₂.d1 ∧ RF R g₁.b1 g₂.b1 ∧
      RF R g₁.add2_carries g₂.add2_carries ∧ RF R g₁.d2 g₂.d2 ∧ RF R g₁.b2 g₂.b2) :
    Q (eval_g B₁ s₁ st₁ slots mx₁ my₁ g₁).1 (eval_g B₂ s₂ st₂ slots mx₂ my₂ g₂).1 ∧
      RS R (eval_g B₁ s₁ st₁ slots mx₁ my₁ g₁).2 (eval_g B₂ s₂ st₂ slots mx₂ my₂ g₂).2 := by
  obtain ⟨hq, hst⟩ := hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  unfold eval_g
  have ha1 := rel_xor_rotl h (hst (slots.getD 3 0)).2.2.2 h2 16
  have hc1 := rel_xor_rotl h (hst (slots.getD 1 0)).2.1 h3 12
  have ha2 := rel_xor_rotl h h2 h5 8
  have hc2 := rel_xor_rotl h h3 h6 7
  refine ⟨rel_add2 h (rel_add3 h (rel_add2 h (rel_add3 h hq (hst (slots.getD 0 0)).1
    (hst (slots.getD 1 0)).2.1 hmx h1 ha1) (hst (slots.getD 2 0)).2.2.1 h2 hc1) ha1 h3 hmy h4 ha2) hc1 h5
    hc2, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact rf_update (fun i => (hst i).1) _ ha2 i
  · exact rf_update (fun i => (hst i).2.1) _ h6 i
  · exact rf_update (fun i => (hst i).2.2.1) _ hc2 i
  · exact rf_update (fun i => (hst i).2.2.2) _ h5 i

end rel

theorem eval_parametric (cb : Bool) : IsParametric (eval (F := F) cb) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hl := rel_getD (h.main_current hs) (h.const 0)
  simp only [eval]
  refine (rel_foldl (P := fun (a : S₁ × State E₁) (b : S₂ × State E₂) => Q a.1 b.1 ∧ RS R a.2 b.2) _
    (fun r _ _ hq =>
    rel_foldl (P := fun (a : S₁ × State E₁) (b : S₂ × State E₂) => Q a.1 b.1 ∧ RS R a.2 b.2) _ (fun g _ _ hq' =>
      rel_eval_g h hq' _ (fun _ => hl _) (fun _ => hl _)
        ⟨fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _, fun _ => hl _⟩) hq)
    ⟨?_, fun i => ⟨fun _ => hl _, fun _ => hl _, fun _ => h.const _, ?_⟩⟩).1
  · split
    · refine h.assert_zero (Plonky3Lean.Proofs.Sha256Air.rel_foldl₂ (T := RF R) ?_
        (fun a b _ _ hab hq => ?_) hs) (h.mul (hl _) (h.sub (hl _) (h.const 1)))
      · exact List.rel_append (List.rel_append (rel_map _ fun _ _ => hl _) (rel_map _ fun _ _ => hl _))
          (.cons (fun _ => hl _) (.cons (fun _ => hl _) .nil))
      · simp only [AirBuilder.assert_bools, List.map_map, Function.comp_def, AirBuilder.bool_check]
        exact rel_assert_zeros h (rel_map _ fun i => h.mul (hab i) (h.sub (hab i) (h.const 1))) hq
    · exact hs
  · dsimp only
    rcases i with _ | _ | _ | i <;> intro bit <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
    all_goals first | exact h.add (h.const _) (hl _) | exact h.const _

/-- The BLAKE2s AIR over a field of characteristic 2, with or without the input booleanity. -/
def blake2sAir (cb : Bool) : Air F where
  width := NUM_BLAKE2S_BINARY_COLS
  max_constraint_degree := some 2
  eval := eval cb
  parametric := eval_parametric cb

end Plonky3Lean.Proofs.Blake2sAir
