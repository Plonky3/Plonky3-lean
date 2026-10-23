module

public import Plonky3Lean.Proofs.Commit.Selectors
public import Plonky3Lean.Proofs.Dft.Fields

@[expose] public section

/-!
# p3-commit at BabyBear and its extensions

The domain theorems need three facts about the field, all true for BabyBear:

* the table of two-adic generators is primitive and nested;
* 2 is invertible;
* the multiplicative generator lies outside the largest two-adic subgroup.

The generator 31 has order p - 1 = 2^27 * 15, so its 2^27-th power is not one.

Every field extension inherits the three facts through the embedding, the quartic extension included.
-/

open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

/-- A generator table read through a ring map. -/
def Gen.map {K E : Type _} [Field K] [Field E] (G : Gen K) (f : K →+* E) : Gen E :=
  ⟨G.adicity, fun b => f (G.gen b)⟩

theorem genValid_map {K E : Type _} [Field K] [Field E] {G : Gen K} (hV : GenValid G) (f : K →+* E) :
    GenValid (Gen.map G f) := fun b hb => (hV b hb).map_of_injective f.injective

theorem genNested_map {K E : Type _} [Field K] [Field E] {G : Gen K} (hN : GenNested G) (f : K →+* E) :
    GenNested (Gen.map G f) := fun b hb => by simp [Gen.map, ← map_pow, hN b hb]

/-- An element of order p - 1 lies outside the subgroup of order 2^27. -/
theorem babyBear_outside {x : BabyBear.Field} (hx : orderOf x = BabyBear.fieldSize - 1) :
    x ^ 2 ^ 27 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hx] at this
  revert this
  decide

/-- BabyBear's tables: the generators are primitive and nested up to 27, and the generator lies outside the subgroup of order 2^27. -/
theorem babyBear_facts :
    ∃ t g, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      Plonky3Lean.Spec.BabyBear.FieldParams.MONTY_GEN = .ok g ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)).adicity = 27 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      Plonky3Lean.Spec.BabyBear.toField g ^ 2 ^ 27 ≠ 1 := by
  obtain ⟨t, ht, ha, hV, hN⟩ := babyBear_generators
  obtain ⟨g, hg, -, hord⟩ := Plonky3Lean.Lib.spec_imp_exists
    Proofs.P3BabyBear.FieldParams.MONTY_GEN.generator
  exact ⟨t, g, ht, hg, ha, hV, hN, babyBear_outside hord⟩

theorem babyBear_two_ne_zero : (2 : BabyBear.Field) ≠ 0 := by decide

end Plonky3Lean.Proofs.Commit
