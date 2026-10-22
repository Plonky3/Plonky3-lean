import Plonky3Lean.Proofs.Field.Mersenne31.Field

/-!
# Mersenne31: `Sum::sum` and `sum_array`

`Sum::sum` adds the stored values in a `u64` and reduces once, with `from_u62`.

It is correct exactly while that sum stays below `2^62`, which holds for at most `2^31 + 1` valid items.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-- The sum of the stored values. -/
def valSum (l : List Element) : ℕ := (l.map fun x => x.value.val).sum

theorem foldl_add_spec (l : List Element) (acc : Std.U64) (h : acc.val + valSum l < 2 ^ 64) :
    l.foldlM (fun acc x => acc + UScalar.cast .U64 x.value) acc ⦃ r =>
      r.val = acc.val + valSum l ⦄ := by
  induction l generalizing acc with
  | nil => simp only [valSum, List.map_nil, List.sum_nil, add_zero, List.foldlM_nil]; exact rfl
  | cons x l ih =>
    simp only [valSum, List.map_cons, List.sum_cons] at h ⊢
    simp only [List.foldlM_cons]
    have hx : acc.val + x.value.val ≤ U64.max := by
      have := Nat.le_add_right (acc.val + x.value.val) (valSum l)
      simp only [valSum] at this; scalar_tac
    step*
    all_goals simp only [valSum] at *
    all_goals rw [init_post, cast_u32_u64_val] at *
    all_goals omega

/-- `Sum::sum` is the field sum while the stored values add up to less than `2^62`. -/
theorem sum.toField (l : List Element) (hs : valSum l < 2 ^ 62) :
    mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum l ⦃ r =>
      Valid r ∧ Spec.Mersenne31.toField r = (l.map Spec.Mersenne31.toField).sum ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum
  step with foldl_add_spec l 0#u64 (by simp; omega) as ⟨s, hs'⟩
  simp only [zero_add] at hs'
  refine WP.spec_mono (from_u62.spec s (by omega)) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [(natCast_eq_iff _ _).mpr (hr.trans (by rw [hs'])), valSum, Nat.cast_list_sum, List.map_map]
  rfl

/-- At most `2^31 + 1` valid items always add up to less than `2^62`. -/
theorem valSum_lt (l : List Element) (hl : ∀ x ∈ l, Valid x) (hn : l.length ≤ 2 ^ 31 + 1) :
    valSum l < 2 ^ 62 := by
  have : valSum l ≤ l.length * (2 ^ 31 - 1) := by
    unfold valSum
    have := List.sum_le_card_nsmul (l.map fun x => x.value.val) (2 ^ 31 - 1) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      have := hl x hx; unfold Valid at this; omega)
    simpa using this
  calc valSum l ≤ l.length * (2 ^ 31 - 1) := this
    _ ≤ (2 ^ 31 + 1) * (2 ^ 31 - 1) := Nat.mul_le_mul_right _ hn
    _ < 2 ^ 62 := by norm_num

/-- `from_u62(x)` panics in a debug build for `x ≥ 2^62`. -/
theorem from_u62.panics (x : Std.U64) (hx : 2 ^ 62 ≤ x.val) :
    mersenne_31.from_u62 x = .fail .panic := by
  unfold mersenne_31.from_u62
  have h1 : (1#u64 <<< 62#i32 : RustM Std.U64) = .ok 4611686018427387904#u64 := by rfl
  have : ¬ x < 4611686018427387904#u64 := by scalar_tac
  rw [h1]
  simp only [bind_tc_ok, massert, this]
  rfl

/-- `Sum::sum` panics, in a debug build, once the stored values add up to `2^62`. -/
theorem sum.panics (l : List Element) (hs : 2 ^ 62 ≤ valSum l) (hs' : valSum l < 2 ^ 64) :
    mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum l = .fail .panic := by
  unfold mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum
  obtain ⟨s, h1, h2⟩ := WP.spec_imp_exists (foldl_add_spec l 0#u64 (by simp; omega))
  rw [h1]
  simp only [show (0#u64).val = 0 from rfl, zero_add] at h2
  simp only [bind_tc_ok]
  exact from_u62.panics s (by omega)

end Plonky3Lean.Proofs.Mersenne31
