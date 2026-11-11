module

public import Plonky3Lean.Proofs.Dft.Glue
public import Plonky3Lean.Proofs.Field.BabyBear.Constants
public import Plonky3Lean.Proofs.Field.KoalaBear.Constants
public import Plonky3Lean.Proofs.Field.Goldilocks.Constants
public import Plonky3Lean.Proofs.Field.Mersenne31.Constants

@[expose] public section

/-!
# The generators of the fields

Each field's table of two-adic generators, read in the field, gives generators that are primitive and nested.
-/

namespace Plonky3Lean.Proofs.Dft

open p3_dft.mirror Aeneas Aeneas.Std

/-- The generators a table holds: entry b, for b up to the last index. -/
def genOfTable {K : Type _} [Field K] (l : List K) : Gen K := ⟨l.length - 1, fun b => l.getD b 0⟩

theorem genOfTable_valid {K : Type _} [Field K] (l : List K) (hl : 0 < l.length)
    (h : ∀ i (hi : i < l.length), orderOf l[i] = 2 ^ i) : GenValid (genOfTable l) := by
  intro b hb
  have hb' : b < l.length := by simp [genOfTable] at hb; omega
  simp only [genOfTable, List.getD_eq_getElem _ _ hb']
  rw [← h b hb']
  exact IsPrimitiveRoot.orderOf _

theorem genOfTable_nested {K : Type _} [Field K] (l : List K)
    (h : ∀ i (hi : i + 1 < l.length), l[i + 1] ^ 2 = l[i]) : GenNested (genOfTable l) := by
  intro b hb
  have hb' : b + 1 < l.length := by simp [genOfTable] at hb; omega
  simp only [genOfTable, List.getD_eq_getElem _ _ hb', List.getD_eq_getElem _ _ (by omega : b < l.length)]
  exact h b hb'

theorem spec_and {α : Type} {m : RustM α} {p q : α → Prop} (hp : m ⦃ a => p a ⦄)
    (hq : m ⦃ a => q a ⦄) : m ⦃ a => p a ∧ q a ⦄ := by
  obtain ⟨a, ha, hpa⟩ := Plonky3Lean.Lib.spec_imp_exists hp
  rw [ha] at hq ⊢
  exact (WP.spec_ok a).mpr ⟨hpa, (WP.spec_ok a).mp hq⟩

/-- BabyBear's table: 28 nested generators, entry b of order 2^b. -/
theorem babyBear_generators :
    ∃ t, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)).adicity = 27 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) := by
  obtain ⟨t, ht, ⟨hlen, hord⟩, hsq⟩ := Plonky3Lean.Lib.spec_imp_exists (spec_and
    Proofs.P3BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS.order
    Proofs.P3BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ)
  refine ⟨t, ht, ?_, genOfTable_valid _ (by simp_all) (fun i hi => ?_), genOfTable_nested _ (fun i hi => ?_)⟩
  · simp [genOfTable, hlen, Proofs.P3BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  · simpa using hord i (by simpa using hi)
  · simpa using hsq i (by simpa using hi)

/-- KoalaBear's table: 25 nested generators, entry b of order 2^b. -/
theorem koalaBear_generators :
    ∃ t, Plonky3Lean.Spec.KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)).adicity = 24 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)) := by
  obtain ⟨t, ht, ⟨hlen, hord⟩, hsq⟩ := Plonky3Lean.Lib.spec_imp_exists (spec_and
    Proofs.P3KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS.order
    Proofs.P3KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ)
  refine ⟨t, ht, ?_, genOfTable_valid _ (by simp_all) (fun i hi => ?_), genOfTable_nested _ (fun i hi => ?_)⟩
  · simp [genOfTable, hlen, Proofs.P3KoalaBear.koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
  · simpa using hord i (by simpa using hi)
  · simpa using hsq i (by simpa using hi)

/-- Goldilocks's table: 33 nested generators, entry b of order 2^b. -/
theorem goldilocks_generators :
    ∃ t, p3_goldilocks.goldilocks.Goldilocks.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)).adicity = 32 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)) := by
  obtain ⟨t, ht, hlen, hord, hsq⟩ := Plonky3Lean.Lib.spec_imp_exists Proofs.P3Goldilocks.TWO_ADIC_GENERATORS.order
  refine ⟨t, ht, ?_, genOfTable_valid _ (by simp_all) (fun i hi => ?_), genOfTable_nested _ (fun i hi => ?_)⟩
  · simp [genOfTable, hlen]
  · simpa using hord i (by simpa using hi)
  · simpa using hsq i (by simpa using hi)

/-- The complex extension of Mersenne31: 33 nested generators, entry b of order 2^b. -/
theorem mersenne31Complex_generators :
    ∃ t, p3_mersenne_31.mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)).adicity = 32 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)) := by
  refine ⟨_, Proofs.P3Mersenne31.EXT_TWO_ADIC_GENERATORS.eq, ?_, genOfTable_valid _ (by simp_all) (fun i hi => ?_),
    genOfTable_nested _ (fun i hi => ?_)⟩
  · simp [genOfTable, Proofs.P3Mersenne31.extTable.property]
  · have hi' : i < 33 := by simpa [Proofs.P3Mersenne31.extTable.property] using hi
    simpa using Proofs.P3Mersenne31.extTable_order i hi'
  · have hi' : i + 1 < 33 := by simpa [Proofs.P3Mersenne31.extTable.property] using hi
    have hc := fun k (hk : k < 33) => Proofs.P3Mersenne31.toComplex_of_vals
      Proofs.P3Mersenne31.extTable _ Proofs.P3Mersenne31.extTable_vals k hk
      (by rw [Proofs.P3Mersenne31.coeffs_length]; exact hk)
    simp only [List.getElem_map]
    rw [hc (i + 1) hi', hc i (by omega)]
    have := Mersenne31.twoAdicGenerators_sq_succ i
      (by rw [Mersenne31.twoAdicGenerators_length]; exact hi')
    simpa [Mersenne31.twoAdicGenerators] using this

end Plonky3Lean.Proofs.Dft
