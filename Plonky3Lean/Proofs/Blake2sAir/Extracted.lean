module

public import P3Blake2sAir
public import Plonky3Lean.Lib.Scalar.Words
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Lib.Array
public import Mathlib.Tactic.IntervalCases
public import Plonky3Lean.Proofs.Blake2sAir.Spec

@[expose] public section

/-!
# The extracted integer code of p3-blake2s-air

- The extracted initialization vector and message schedule are the transcribed ones, and those of RFC 7693.
- The extracted schedule of G positions is the transcribed one.
- The extracted carry word never panics, and is `(sum ^ x ^ y) >> 1`.
-/

namespace Plonky3Lean.Proofs.Blake2sAir

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib

/-- The extracted initialization vector is the transcribed one. -/
theorem IV_extracted : p3_blake2s_air.constants.IV.val.map UScalar.bv = p3_blake2s_air.mirror.IV := by
  unfold p3_blake2s_air.constants.IV
  decide +kernel

/-- The extracted initialization vector is that of RFC 7693, section 2.6. -/
theorem IV_rfc : p3_blake2s_air.constants.IV.val.map UScalar.bv = Plonky3Lean.Spec.Blake2s.IV := by
  unfold p3_blake2s_air.constants.IV
  decide +kernel

/-- The extracted message schedule is the transcribed one. -/
theorem SIGMA_extracted :
    p3_blake2s_air.constants.SIGMA.val.map (fun row => row.val.map (·.val)) = p3_blake2s_air.mirror.SIGMA := by
  unfold p3_blake2s_air.constants.SIGMA
  decide +kernel

/-- The extracted message schedule is that of RFC 7693, section 2.7. -/
theorem SIGMA_rfc :
    p3_blake2s_air.constants.SIGMA.val.map (fun row => row.val.map (·.val)) = Plonky3Lean.Spec.Blake2s.SIGMA := by
  unfold p3_blake2s_air.constants.SIGMA
  decide +kernel

/-- The extracted schedule of G positions never panics, and is the transcribed one. -/
theorem G_SCHEDULE_extracted : ∃ s, p3_blake2s_air.binary.G_SCHEDULE = .ok s ∧
    s.val.map (fun row => row.val.map (·.val)) = p3_blake2s_air.mirror.G_SCHEDULE := by
  have rep : ∀ k : Std.Usize, ∃ a : Std.Array Std.Usize 4#usize, core.array.repeat 4#usize core.Usize.Insts.CoreCloneClone k = .ok a ∧
      a.val.map (·.val) = [k.val, k.val, k.val, k.val] := fun k => by
    obtain ⟨a, ha, he⟩ := array_repeat_eq 4#usize core.Usize.Insts.CoreCloneClone (fun _ => rfl) k
    refine ⟨a, ha, ?_⟩
    have hl : a.val.length = 4 := a.property
    rw [List.eq_replicate_iff.mpr ⟨hl, he⟩]
    rfl
  obtain ⟨a0, h0, e0⟩ := rep 0#usize
  obtain ⟨a1, h1, e1⟩ := rep 1#usize
  obtain ⟨a2, h2, e2⟩ := rep 2#usize
  obtain ⟨a3, h3, e3⟩ := rep 3#usize
  unfold p3_blake2s_air.binary.G_SCHEDULE
  simp only [h0, h1, h2, h3, bind_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [Array.make, Std.Array.from_val, List.map_cons, List.map_nil, e0, e1, e2, e3]
  rfl

/-- The extracted carry word never panics, and is the transcribed one. -/
theorem carries_word_eq (x y s : Std.U32) :
    p3_blake2s_air.binary.generation.carries_word x y s =
      .ok ⟨p3_blake2s_air.mirror.carries_word x.bv y.bv s.bv⟩ := by
  simp only [p3_blake2s_air.binary.generation.carries_word, lift, bind_ok,
    u32_shiftRight_i32_eq _ 1#i32 (by decide) (by decide)]
  rfl

/-! ## The G step on words -/

section array

variable {α : Type} {n : Std.Usize} (v : Std.Array α n) {i : Std.Usize} (hi : i.val < v.val.length)
include hi

theorem index_usize_eq : v.index_usize i = .ok v.val[i.val] := by
  simp only [Std.Array.index_usize]
  simp [List.getElem?_eq_getElem hi]

theorem update_eq (x : α) : v.update i x = .ok (v.set i x) := by
  simp only [Std.Array.update, Std.Array.set]
  simp [List.getElem?_eq_getElem hi]

omit hi in
theorem index_usize_fail (h : v.val.length ≤ i.val) : v.index_usize i = .fail .panic := by
  simp only [Std.Array.index_usize]
  simp [List.getElem?_eq_none h]

theorem index_mut_usize_eq : v.index_mut_usize i = .ok (v.val[i.val], v.set i) := by
  simp [Std.Array.index_mut_usize, index_usize_eq v hi]

end array

/-- The word a state of four rows of four words holds at a row and a position. -/
def cellOf (state : Std.Array (Std.Array Std.U32 4#usize) 4#usize) (r i : ℕ) : p3_blake2s_air.mirror.Word :=
  ((state.val[r]!).val[i]!).bv

theorem cellOf_set (st : Std.Array (Std.Array Std.U32 4#usize) 4#usize) (k : Std.Usize) (hk : k.val < 4)
    (row : Std.Array Std.U32 4#usize) (r i : ℕ) :
    cellOf (st.set k row) r i = if r = k.val then (row.val[i]!).bv else cellOf st r i := by
  unfold cellOf
  have hl : st.val.length = 4 := st.property
  split_ifs with h
  · subst h; simp [Std.Array.set_val_eq, hl, hk]
  · simp [Std.Array.set_val_eq, getElem!_def, Ne.symm h]

theorem row_set_get (row : Std.Array Std.U32 4#usize) (j : Std.Usize) (hj : j.val < 4) (x : Std.U32) (i : ℕ) :
    ((row.set j x).val[i]!).bv = if i = j.val then x.bv else (row.val[i]!).bv := by
  have hl : row.val.length = 4 := row.property
  split_ifs with h
  · subst h; simp [Std.Array.set_val_eq, hl, hj]
  · simp [Std.Array.set_val_eq, getElem!_def, Ne.symm h]

theorem state_set_get (st : Std.Array (Std.Array Std.U32 4#usize) 4#usize) (k j : Std.Usize)
    (row : Std.Array Std.U32 4#usize) (h : j.val < (st.set k row).val.length) (hjk : j.val ≠ k.val) :
    (st.set k row).val[j.val] = st.val[j.val]'(by simpa using h) := by
  simp [Std.Array.set_val_eq, Ne.symm hjk]

/-- When every position is below 4, the extracted G step on words never panics.

It returns the transcribed words, and leaves the transcribed state. -/
theorem g_words_extracted (state : Std.Array (Std.Array Std.U32 4#usize) 4#usize)
    (a : Std.Array Std.Usize 4#usize) (mx my : Std.U32) (ha : ∀ j < 4, (a.val[j]!).val < 4) :
    ∃ r, p3_blake2s_air.binary.generation.g_words state a mx my = .ok r ∧
      let m := p3_blake2s_air.mirror.g_words (cellOf state) (a.val.map (·.val)) mx.bv my.bv
      (r.1.add1_carries.bv = m.1.add1_carries ∧ r.1.d1.bv = m.1.d1 ∧ r.1.b1.bv = m.1.b1 ∧
        r.1.add2_carries.bv = m.1.add2_carries ∧ r.1.d2.bv = m.1.d2 ∧ r.1.b2.bv = m.1.b2) ∧
      ∀ row < 4, ∀ i < 4, cellOf r.2 row i = m.2 row i := by
  have hal : a.val.length = 4 := a.property
  have hsl : state.val.length = 4 := state.property
  have hrl : ∀ x : Std.Array Std.U32 4#usize, x.val.length = 4 := fun x => x.property
  have h0 : (a.val[0]'(by omega)).val < 4 := by simpa [hal] using ha 0 (by norm_num)
  have h1 : (a.val[1]'(by omega)).val < 4 := by simpa [hal] using ha 1 (by norm_num)
  have h2 : (a.val[2]'(by omega)).val < 4 := by simpa [hal] using ha 2 (by norm_num)
  have h3 : (a.val[3]'(by omega)).val < 4 := by simpa [hal] using ha 3 (by norm_num)
  simp (disch := first | simp [hal, hsl, hrl, h0, h1, h2, h3] | omega) only
    [p3_blake2s_air.binary.generation.g_words, index_usize_eq, index_mut_usize_eq, update_eq,
      u32_wrapping_add_eq, u32_rotate_right_eq, lift, bind_ok, carries_word_eq]
  have hget : ∀ k (hk : k < 4), (a.val.map (·.val)).getD k 0 = (a.val[k]'(by omega)).val := by
    intro k hk; simp [List.getD_eq_getElem?_getD, hal, hk]
  have hcell : ∀ r (hr : r < 4) (j : Std.Usize) (hj : j.val < 4),
      cellOf state r j.val = ((state.val[r]'(by omega)).val[j.val]'(by rw [hrl]; exact hj)).bv := by
    intro r hr j hj
    simp [cellOf, getElem!_pos, hsl, hr, hrl, hj]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [p3_blake2s_air.mirror.g_words, p3_blake2s_air.mirror.carries_word, hget 0 (by norm_num),
      hget 1 (by norm_num), hget 2 (by norm_num), hget 3 (by norm_num), hcell 0 (by norm_num) _ h0,
      hcell 1 (by norm_num) _ h1, hcell 2 (by norm_num) _ h2, hcell 3 (by norm_num) _ h3]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro row hr i hi
    simp only [p3_blake2s_air.mirror.g_words, hget 0 (by norm_num),
      hget 1 (by norm_num), hget 2 (by norm_num), hget 3 (by norm_num), hcell 0 (by norm_num) _ h0,
      hcell 1 (by norm_num) _ h1, hcell 2 (by norm_num) _ h2, hcell 3 (by norm_num) _ h3,
      Function.update_apply]
    simp (disch := first | assumption | (simp [h0, h1, h2, h3]; done) | omega) only [cellOf_set,
      row_set_get, state_set_get]
    interval_cases row <;>
    · simp only [show ((3#usize : Std.Usize) : ℕ) = 3 from rfl, show ((2#usize : Std.Usize) : ℕ) = 2 from rfl,
        show ((1#usize : Std.Usize) : ℕ) = 1 from rfl, show ((0#usize : Std.Usize) : ℕ) = 0 from rfl,
        ↓reduceIte, Nat.reduceEqDiff, Function.update_apply]
      split_ifs <;> first | rfl | simp [cellOf, getElem!_pos, hsl]

/-- The extracted G step on words panics when a position is not below 4. -/
theorem g_words_panics (state : Std.Array (Std.Array Std.U32 4#usize) 4#usize)
    (a : Std.Array Std.Usize 4#usize) (mx my : Std.U32) (ha : ∃ j < 4, 4 ≤ (a.val[j]!).val) :
    p3_blake2s_air.binary.generation.g_words state a mx my = .fail .panic := by
  have hal : a.val.length = 4 := a.property
  have hsl : state.val.length = 4 := state.property
  have hrl : ∀ x : Std.Array Std.U32 4#usize, x.val.length = 4 := fun x => x.property
  have hj : ∀ j (hj : j < 4), (a.val[j]!) = a.val[j]'(by omega) := fun j hj => by
    simp [getElem!_pos, hal, hj]
  obtain ⟨j, hj4, hge⟩ := ha
  rw [hj j hj4] at hge
  unfold p3_blake2s_air.binary.generation.g_words
  by_cases h0 : (a.val[0]'(by omega)).val < 4 <;> by_cases h1 : (a.val[1]'(by omega)).val < 4 <;>
    by_cases h2 : (a.val[2]'(by omega)).val < 4 <;> by_cases h3 : (a.val[3]'(by omega)).val < 4
  · interval_cases j <;> omega
  all_goals simp (disch := first | simp [hal, hsl, hrl]; done | simp [hrl]; omega)
    only [index_usize_eq, index_usize_fail, bind_ok, bind_fail, u32_wrapping_add_eq,
      u32_rotate_right_eq, lift]

end Plonky3Lean.Proofs.Blake2sAir
