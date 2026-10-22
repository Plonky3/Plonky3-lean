module

public import P3Blake2s
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Slice

@[expose] public section

/-!
# p3-blake2s: hashing many messages one at a time

With `n` digests requested and an input of `n · L` bytes, digest `i` is the hash of bytes `[i L, (i + 1) L)`.

No digests requested returns at once; an input that `n` does not divide panics.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake2s

/-- The digests after the first `k` messages: the first `k` hashes, then what `out` held. -/
def digestsAt (out : Slice (Std.Array Std.U8 32#usize)) (d : ℕ → Std.Array Std.U8 32#usize)
    (k : ℕ) : Slice (Std.Array Std.U8 32#usize) :=
  Slice.from ((List.range out.val.length).map fun j => if j < k then d j else out.val[j]!)
    (by simp)

theorem digestsAt_val (out : Slice (Std.Array Std.U8 32#usize)) (d : ℕ → Std.Array Std.U8 32#usize)
    (k : ℕ) : (digestsAt out d k).val =
      (List.range out.val.length).map fun j => if j < k then d j else out.val[j]! := by
  simp [digestsAt]

variable (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize)) (len : Std.Usize)
  (d : ℕ → Std.Array Std.U8 32#usize)

theorem loop_body (hlen : input.val.length = out.val.length * len.val)
    (hd : ∀ i < out.val.length, ∀ s : Slice Std.U8,
      s.val = (input.val.drop (i * len.val)).take len.val → p3_blake2s.Blake2s256.hash s = .ok (d i))
    (k : ℕ) (hk : k < out.val.length) :
    p3_blake2s.hax_reshaped.hash_many_loop.body input len
      { start := usz k, «end» := Slice.len out } (digestsAt out d k) =
      .ok (.cont ({ start := usz (k + 1), «end» := Slice.len out }, digestsAt out d (k + 1))) := by
  have hn : (Slice.len out).val = out.val.length := by simp
  obtain ⟨i', e, hi'⟩ := range_next_some (usz k) (Slice.len out)
    (by rw [usz_val_le (Slice.len out) (by omega), hn]; exact hk)
  rw [show i' = usz (k + 1) from eq_usz_le (Slice.len out) (by omega)
    (by rw [hi', usz_val_le (Slice.len out) (by omega)])] at e
  unfold p3_blake2s.hax_reshaped.hash_many_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok,
    Aeneas.Std.uncurry_apply_pair]
  have hkL : k * len.val + len.val ≤ input.val.length := by
    rw [hlen]; nlinarith
  have hmax : (usz k).val * len.val ≤ UScalar.max .Usize := by
    rw [usz_val_le (Slice.len out) (by omega)]
    have := input.property; scalar_tac
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [usz_val_le (Slice.len out) (by omega)] at hzv
  rw [hz, bind_ok, slice_index_rangeFrom_eq _ _ (by rw [hzv]; omega), bind_ok,
    index_rangeTo_eq _ _ (by simp [List.slice_length, hzv]; omega), bind_ok,
    hd k hk _ (by
      simp only [Slice.from_val, List.slice, hzv, Nat.sub_zero, List.drop_zero]
      rw [List.take_take, Nat.min_eq_left (by omega)]), bind_ok,
    slice_update_eq _ _ _ (by rw [usz_val_le (Slice.len out) (by omega), digestsAt_val]; simpa using hk), bind_ok]
  apply congrArg RustM.ok
  apply congrArg ControlFlow.cont
  congr 1
  apply Slice.ext
  simp only [Slice.from_val, digestsAt_val, usz_val_le (Slice.len out) (show k ≤ (Slice.len out).val by omega)]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem loop_done (o : Slice (Std.Array Std.U8 32#usize)) :
    p3_blake2s.hax_reshaped.hash_many_loop.body input len
      { start := usz out.val.length, «end» := Slice.len out } o = .ok (.done o) := by
  unfold p3_blake2s.hax_reshaped.hash_many_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz out.val.length) (Slice.len out)
      (by rw [usz_val_le (Slice.len out) (by simp)]; simp), bind_ok,
    Aeneas.Std.uncurry_apply_pair]

theorem digestsAt_zero : digestsAt out d 0 = out := by
  apply Slice.ext
  rw [digestsAt_val]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem digestsAt_full : (digestsAt out d out.val.length).val = (List.range out.val.length).map d := by
  rw [digestsAt_val]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  simp [hj]

theorem loop_eq (hlen : input.val.length = out.val.length * len.val)
    (hd : ∀ i < out.val.length, ∀ s : Slice Std.U8,
      s.val = (input.val.drop (i * len.val)).take len.val → p3_blake2s.Blake2s256.hash s = .ok (d i)) :
    p3_blake2s.hax_reshaped.hash_many_loop { start := 0#usize, «end» := Slice.len out } input out len =
      .ok (digestsAt out d out.val.length) := by
  unfold p3_blake2s.hax_reshaped.hash_many_loop
  rw [show (0#usize : Std.Usize) = usz 0 from eq_usz_le (Slice.len out) (by simp) rfl]
  have h := loop_of_steps (fun x => match x with
      | (iter1, out1) => p3_blake2s.hax_reshaped.hash_many_loop.body input len iter1 out1)
    (fun k => (({ start := usz k, «end» := Slice.len out } : CoreModels.core.ops.range.Range Std.Usize),
      digestsAt out d k)) out.val.length _
    (fun k hk => loop_body input out len d hlen hd k hk) (loop_done input out len _)
  rw [digestsAt_zero] at h
  exact h

/-- `n` digests of messages of `L` bytes each: digest `i` is the hash of bytes `[i L, (i + 1) L)`. -/
theorem hash_many_eq (hn : 0 < out.val.length) (hlen : input.val.length = out.val.length * len.val)
    (hd : ∀ i < out.val.length, ∀ s : Slice Std.U8,
      s.val = (input.val.drop (i * len.val)).take len.val → p3_blake2s.Blake2s256.hash s = .ok (d i)) :
    ∃ r, p3_blake2s.batch.hash_many input out = .ok r ∧ r.val = (List.range out.val.length).map d := by
  unfold p3_blake2s.batch.hash_many p3_blake2s.hax_reshaped.hash_many
  have hlv : (Slice.len out).val = out.val.length := by simp
  have hli : (Slice.len input).val = input.val.length := by simp
  have h0 : (Slice.len out).val ≠ 0 := by rw [hlv]; omega
  have hne : ¬ Slice.len out = 0#usize := fun e => h0 (by rw [e]; rfl)
  obtain ⟨m, hm, hmv⟩ := spec_imp_exists (UScalar.rem_spec (Slice.len input) h0)
  have hm0 : m = 0#usize := UScalar.eq_of_val_eq (by
    rw [hmv, hli, hlv, hlen]; simp)
  obtain ⟨q, hq, hqv⟩ := UScalar.div_spec (Slice.len input) h0
  have hql : q = len := UScalar.eq_of_val_eq (by
    rw [hqv, hli, hlv, hlen]; exact Nat.mul_div_cancel_left _ hn)
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, hne, decide_false, ite_false,
    CoreModels.core.num.Usize.is_multiple_of]
  simp only [Bool.false_eq_true, ite_false, hm, bind_ok, hm0, decide_true, ite_true, hq, hql]
  exact ⟨_, loop_eq input out len d hlen hd, digestsAt_full out d⟩

/-- No digests requested: `out` comes back unchanged, whatever the input. -/
theorem hash_many_empty (h : out.val = []) : p3_blake2s.batch.hash_many input out = .ok out := by
  unfold p3_blake2s.batch.hash_many p3_blake2s.hax_reshaped.hash_many
  have he : Slice.len out = 0#usize := UScalar.eq_of_val_eq (by simp [h])
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, he, decide_true, ite_true]

/-- An input whose length the digest count does not divide panics. -/
theorem hash_many_ragged (hn : 0 < out.val.length) (h : input.val.length % out.val.length ≠ 0) :
    p3_blake2s.batch.hash_many input out = .fail .panic := by
  unfold p3_blake2s.batch.hash_many p3_blake2s.hax_reshaped.hash_many
  have hlv : (Slice.len out).val = out.val.length := by simp
  have hli : (Slice.len input).val = input.val.length := by simp
  have h0 : (Slice.len out).val ≠ 0 := by rw [hlv]; omega
  have hne : ¬ Slice.len out = 0#usize := fun e => h0 (by rw [e]; rfl)
  obtain ⟨m, hm, hmv⟩ := spec_imp_exists (UScalar.rem_spec (Slice.len input) h0)
  have hm0 : ¬ m = 0#usize := fun e => h (by
    have := congrArg UScalar.val e; rw [hmv, hli, hlv] at this; simpa using this)
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, hne, decide_false, ite_false,
    CoreModels.core.num.Usize.is_multiple_of, Bool.false_eq_true, hm, hm0,
    CoreModels.core.fmt.rt.Argument.new_display, CoreModels.core.fmt.Arguments.new]

end Plonky3Lean.Proofs.Blake2s
