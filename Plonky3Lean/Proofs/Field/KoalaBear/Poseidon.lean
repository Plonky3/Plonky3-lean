module

public import Plonky3Lean.Proofs.Field.KoalaBear

@[expose] public section

/-!
# KoalaBear: the Poseidon round-constant length assertions

The eleven `const _: () = assert!(..)` of `koala-bear/src/poseidon{1,2}.rs`.

aeneas names the first in each module `_` and the rest `__N`.
Post-extraction patch 030 renames those to `const_check_N`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear

namespace Plonky3Lean.Proofs.P3KoalaBear

/-- Closes a length assertion on a round-constant table `t`, given that the table builds (`ht`). -/
macro "poseidon_length " ht:ident : tactic =>
  `(tactic| (
    rw [$ht:ident, bind_ok]
    simp only [CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
      CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_ok]
    step*))

/-- `koala-bear/src/poseidon1.rs:65`, on `KOALABEAR_POSEIDON1_RC_16`. -/
theorem poseidon1._.holds : poseidon1._ ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon1.KOALABEAR_POSEIDON1_RC_16 = .ok t := by
    unfold poseidon1.KOALABEAR_POSEIDON1_RC_16; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon1._ poseidon1.KOALABEAR_POSEIDON_HALF_FULL_ROUNDS poseidon1.KOALABEAR_POSEIDON_PARTIAL_ROUNDS_16
  poseidon_length ht

/-- `koala-bear/src/poseidon1.rs:69`, on `KOALABEAR_POSEIDON1_RC_24`. -/
theorem poseidon1.const_check_1.holds : poseidon1.const_check_1 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon1.KOALABEAR_POSEIDON1_RC_24 = .ok t := by
    unfold poseidon1.KOALABEAR_POSEIDON1_RC_24; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon1.const_check_1 poseidon1.KOALABEAR_POSEIDON_HALF_FULL_ROUNDS poseidon1.KOALABEAR_POSEIDON_PARTIAL_ROUNDS_24
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:69`, on `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`. -/
theorem poseidon2._.holds : poseidon2._ ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2._ poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:72`, on `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_1.holds : poseidon2.const_check_1 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2.const_check_1 poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:74`, on `KOALABEAR_POSEIDON2_RC_16_INTERNAL`. -/
theorem poseidon2.const_check_2.holds : poseidon2.const_check_2 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_16_INTERNAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_16_INTERNAL; exact koala_bear.KoalaBear.new_array.never_panics _
  unfold poseidon2.const_check_2 poseidon2.KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_16
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:76`, on `KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_3.holds : poseidon2.const_check_3 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2.const_check_3 poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:79`, on `KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_4.holds : poseidon2.const_check_4 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2.const_check_4 poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:81`, on `KOALABEAR_POSEIDON2_RC_24_INTERNAL`. -/
theorem poseidon2.const_check_5.holds : poseidon2.const_check_5 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_24_INTERNAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_24_INTERNAL; exact koala_bear.KoalaBear.new_array.never_panics _
  unfold poseidon2.const_check_5 poseidon2.KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_24
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:83`, on `KOALABEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_6.holds : poseidon2.const_check_6 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2.const_check_6 poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:86`, on `KOALABEAR_POSEIDON2_RC_32_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_7.holds : poseidon2.const_check_7 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_32_EXTERNAL_FINAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_32_EXTERNAL_FINAL; exact koala_bear.KoalaBear.new_2d_array.never_panics _
  unfold poseidon2.const_check_7 poseidon2.KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS
  poseidon_length ht

/-- `koala-bear/src/poseidon2.rs:88`, on `KOALABEAR_POSEIDON2_RC_32_INTERNAL`. -/
theorem poseidon2.const_check_8.holds : poseidon2.const_check_8 ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.KOALABEAR_POSEIDON2_RC_32_INTERNAL = .ok t := by
    unfold poseidon2.KOALABEAR_POSEIDON2_RC_32_INTERNAL; exact koala_bear.KoalaBear.new_array.never_panics _
  unfold poseidon2.const_check_8 poseidon2.KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_32
  poseidon_length ht

end Plonky3Lean.Proofs.P3KoalaBear
