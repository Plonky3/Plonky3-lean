import Plonky3Lean.Proofs.Field.BabyBear

/-!
# BabyBear: what the constructors produce, as field elements

`BabyBear::new`, `new_array` and `new_2d_array`, read through
`Plonky3Lean.Spec.BabyBear.toField`: each input `x` becomes the field element
`x mod p`, stored canonically. Every constant of `baby-bear/src/baby_bear.rs` is
built by one of these, so every claim about a constant's value starts here.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.BabyBear

theorem two_pow_32_ne_zero : (2 ^ 32 : BabyBear.Field) ≠ 0 := by decide

/-- A stored value `n · 2^32 mod p` stands for the field element `n`. -/
theorem toField_eq_of_value {x : Element} {n : ℕ}
    (h : x.value.val = n * 2 ^ 32 % BabyBear.fieldSize) : toField x = n := by
  unfold toField
  rw [h, ZMod.natCast_mod]
  push_cast
  field_simp [two_pow_32_ne_zero]
  norm_num

/-- A stored value reduced mod `p` is canonical. -/
theorem canonical_of_value {x : Element} {n : ℕ}
    (h : x.value.val = n * 2 ^ 32 % BabyBear.fieldSize) : Canonical x := by
  unfold Canonical; rw [h]; exact Nat.mod_lt _ (by decide)

/-- `BabyBear::new x` stands for `x mod p` and is canonical. -/
theorem baby_bear.BabyBear.new.toField (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => Canonical r ∧ toField r = (x.val : BabyBear.Field) ⦄ :=
  Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.montgomery_form x)
    (fun _ hr => ⟨canonical_of_value hr, toField_eq_of_value hr⟩)

/-- What `new` does to one input, as a relation between input and output. -/
def NewRel (x : Std.U32) (r : Element) : Prop :=
  Canonical r ∧ toField r = (x.val : BabyBear.Field)

theorem forall₂_newRel {l : List Std.U32} {l' : List Element}
    (h : List.Forall₂ NewRel l l') :
    (∀ y ∈ l', Canonical y) ∧
      l'.map Spec.BabyBear.toField = l.map (fun x => (x.val : BabyBear.Field)) := by
  induction h with
  | nil => simp
  | cons hxy _ ih =>
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxy.1
      · exact ih.1 y hy
    · simp [hxy.2, ih.2]

/-- `BabyBear::new_array` applies `new` elementwise: every output is canonical,
and the outputs stand for the inputs mod `p`. About the hand-written
transcription of `new_array`. -/
theorem baby_bear.BabyBear.new_array.toField {N : Std.Usize} (input : Array Std.U32 N) :
    p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      ⦃ r => (∀ y ∈ r.val, Canonical y) ∧
        r.val.map Spec.BabyBear.toField = input.val.map (fun x => (x.val : BabyBear.Field)) ⦄ := by
  obtain ⟨l', hl', hall⟩ := mapM_forall₂ _ NewRel baby_bear.BabyBear.new.toField input.val
  have hlen : l'.length = N.val := by rw [← hall.length_eq]; exact input.property
  unfold p3_monty_31.monty_31.MontyField31.new_array
  rw [hl']
  simp only [bind_tc_ok, hlen, _root_.dite_true]
  exact (Aeneas.Std.WP.spec_ok _).mpr (forall₂_newRel hall)

/-- What `new_array` does to one row, as a relation between input and output. -/
def NewArrayRel {N : Std.Usize} (x : Array Std.U32 N) (r : Array Element N) : Prop :=
  (∀ y ∈ r.val, Canonical y) ∧
    r.val.map Spec.BabyBear.toField = x.val.map (fun x => (x.val : BabyBear.Field))

theorem forall₂_newArrayRel {N : Std.Usize} {l : List (Array Std.U32 N)}
    {l' : List (Array Element N)} (h : List.Forall₂ NewArrayRel l l') :
    (∀ row ∈ l', ∀ y ∈ row.val, Canonical y) ∧
      l'.map (fun row => row.val.map Spec.BabyBear.toField) =
        l.map (fun row => row.val.map (fun x => (x.val : BabyBear.Field))) := by
  induction h with
  | nil => simp
  | cons hxy _ ih =>
    refine ⟨?_, ?_⟩
    · intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · exact hxy.1
      · exact ih.1 row hrow
    · simp [hxy.2, ih.2]

/-- `BabyBear::new_2d_array` applies `new_array` to each row: every output is
canonical, and the outputs stand for the inputs mod `p`. About the hand-written
transcription of `new_2d_array`. -/
theorem baby_bear.BabyBear.new_2d_array.toField {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input
      ⦃ r => (∀ row ∈ r.val, ∀ y ∈ row.val, Canonical y) ∧
        r.val.map (fun row => row.val.map Spec.BabyBear.toField) =
          input.val.map (fun row => row.val.map (fun x => (x.val : BabyBear.Field))) ⦄ := by
  obtain ⟨l', hl', hall⟩ :=
    mapM_forall₂ _ NewArrayRel baby_bear.BabyBear.new_array.toField input.val
  have hlen : l'.length = M.val := by rw [← hall.length_eq]; exact input.property
  unfold p3_monty_31.monty_31.MontyField31.new_2d_array
  rw [hl']
  simp only [bind_tc_ok, hlen, _root_.dite_true]
  exact (Aeneas.Std.WP.spec_ok _).mpr (forall₂_newArrayRel hall)

end Plonky3Lean.Proofs.BabyBear
