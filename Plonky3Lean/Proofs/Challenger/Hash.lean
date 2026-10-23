module

public import Plonky3Lean.Proofs.Challenger.Duplex

@[expose] public section

/-!
# The extracted hash challenger

The hash challenger keeps a list of pending inputs and a list of buffered outputs.

A flush hashes the pending inputs, keeps the digest as the only pending input (the chaining value), and buffers the digest as the outputs.

Observing appends to the inputs and clears the outputs.

Sampling flushes when no output is left and pops the last one.

The hasher is abstract: it computes a function `H` of the items its iterator yields and never panics.

```text
    inputs [c], observe a b, sample:   flush: d = H(c, a, b)
                                       inputs [d_0 ... d_(n-1)], outputs the same
                                       sample = d_(n-1)
```
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Proofs.Symmetric

namespace Plonky3Lean.Proofs.Challenger

/-- The hasher, through its dictionary, returns `H xs` for any iterable that yields `xs`. -/
def HasherComputes {Hs T : Type} {N : Std.Usize}
    (inst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N)) (h : Hs)
    (H : List T → Std.Array T N) : Prop :=
  ∀ {I J : Type} (iterInst : core.iter.traits.collect.IntoIterator I T J) (input : I) (xs : List T),
    (∃ it, iterInst.into_iter input = .ok it ∧ Yields iterInst.iteratorIteratorInst it xs) →
      inst.hash_iter iterInst h input = .ok (H xs)

/-- A drain yields the items it holds. -/
theorem drain_yields {T A : Type} :
    ∀ (xs : List T) (d : alloc.vec.drain.Drain T A), d.1.val = xs →
      Yields (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator T A) d xs := by
  intro xs
  induction xs with
  | nil => intro d hd; exact ⟨d, drain_next_nil d hd⟩
  | cons x xs ih =>
    intro d hd
    obtain ⟨d', e, hd'⟩ := drain_next_cons d x xs hd
    exact ⟨d', e, ih d' hd'⟩

/-- The list machine of the hash challenger: pending inputs and buffered outputs. -/
structure HSt (T : Type) where
  inb : List T
  outb : List T

/-- The extracted challenger's view as the list machine. -/
def toHSt {T Hs : Type} {N : Std.Usize} (c : p3_challenger.hash_challenger.HashChallenger T Hs N) : HSt T :=
  ⟨c.input_buffer.val, c.output_buffer.val⟩

theorem vec_extend_from_slice_eq {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x)
    (v : alloc.vec.Vec T) (s : Slice T) (hl : v.val.length + s.val.length ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.extend_from_slice cl v s = .ok v' ∧ v'.val = v.val ++ s.val := by
  have hm : s.val.mapM cl.clone = .ok s.val := Lib.mapM_ok _ hcl _
  refine ⟨Slice.from (v.val ++ s.val) (by simpa using hl), ?_, by simp⟩
  simp only [alloc.vec.Vec.extend_from_slice, rust_primitives.sequence.seq_extend, hm]
  simp [hl]

set_option allowUnsafeReducibility true in
attribute [local reducible] alloc.vec.Vec rust_primitives.sequence.Seq in
/-- A flush hashes the pending inputs.

The digest becomes both the only pending input and the outputs. -/
theorem flush_eq {T Hs : Type} {N : Std.Usize} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x)
    (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N)) (H : List T → Std.Array T N)
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (hH : HasherComputes hashInst c.hasher H) :
    ∃ c', p3_challenger.hash_challenger.HashChallenger.flush cl hashInst c = .ok c' ∧
      toHSt c' = ⟨(H c.input_buffer.val).val, (H c.input_buffer.val).val⟩ ∧ c'.hasher = c.hasher := by
  obtain ⟨d, ed, hd⟩ := vec_drain_full c.input_buffer
  have hlenN : (H c.input_buffer.val).val.length ≤ Usize.max := by
    have := (H c.input_buffer.val).property; simp only [this]; scalar_tac
  have hhash := hH (core.iter.traits.collect.IntoIterator.Blanket
    (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator T alloc.alloc.Global)) d c.input_buffer.val
    ⟨d, rfl, drain_yields _ d hd⟩
  obtain ⟨v1, ev1, hv1⟩ := vec_extend_from_slice_eq cl hcl (Slice.from [] (Nat.zero_le _))
    (Std.Array.to_slice (H c.input_buffer.val)) (by simpa [Std.Array.to_slice] using hlenN)
  obtain ⟨it, eit, hit⟩ := array_into_iter_yields (H c.input_buffer.val)
  obtain ⟨v3, ev3, hv3⟩ := extend_loop_eq
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N) (H c.input_buffer.val).val
    (vnil T) it hit (by simpa using hlenN)
  have hclear : alloc.vec.Vec.clear c.output_buffer = .ok (vnil T) := by
    simp [alloc.vec.Vec.clear, rust_primitives.sequence.seq_empty, vnil]
  refine ⟨⟨v1, v3, c.hasher⟩, ?_, ?_, rfl⟩
  · unfold p3_challenger.hash_challenger.HashChallenger.flush
    show (do
      let p ← alloc.vec.Vec.drain alloc.alloc.Global
        (core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds Std.Usize) c.input_buffer ()
      let output ← hashInst.hash_iter (core.iter.traits.collect.IntoIterator.Blanket
        (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator T alloc.alloc.Global)) c.hasher p.1
      let s ← core.array.Array.as_slice output
      let v1 ← alloc.vec.Vec.extend_from_slice cl p.2 s
      let v2 ← alloc.vec.Vec.clear c.output_buffer
      let v3 ← alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend
        (core.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter T N) v2 output
      RustM.ok (p3_challenger.hash_challenger.HashChallenger.mk v1 v3 c.hasher)) = _
    simp only [ed, bind_tc_ok, bind_ok, hhash, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, ev1,
      hclear, alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend, eit, ev3]
  · simp [toHSt, hv1, hv3, Std.Array.to_slice]

/-- Observing appends the value to the pending inputs and clears the outputs. -/
theorem hash_observe_eq {T Hs : Type} {N : Std.Usize} (cl : core.clone.Clone T)
    (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N))
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (x : T)
    (hl : c.input_buffer.val.length + 1 ≤ Usize.max) :
    ∃ c', p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanObserve.observe cl hashInst c x =
      .ok c' ∧ toHSt c' = ⟨c.input_buffer.val ++ [x], []⟩ ∧ c'.hasher = c.hasher := by
  obtain ⟨v1, ev1, hv1⟩ := vec_push_eq c.input_buffer x hl
  have hclear : alloc.vec.Vec.clear c.output_buffer = .ok (vnil T) := by
    simp [alloc.vec.Vec.clear, rust_primitives.sequence.seq_empty, vnil]
  refine ⟨⟨v1, vnil T, c.hasher⟩, ?_, by simp [toHSt, hv1], rfl⟩
  simp [p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanObserve.observe, hclear, ev1]

set_option allowUnsafeReducibility true in
attribute [local reducible] alloc.vec.Vec rust_primitives.sequence.Seq in
/-- After an observation, a sample flushes and returns the last cell of the digest of every pending input. -/
theorem hash_sample_after_observe {T Hs : Type} [Inhabited T] {N : Std.Usize} (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = .ok x)
    (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N)) (H : List T → Std.Array T N)
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (hH : HasherComputes hashInst c.hasher H)
    (x : T) (hl : c.input_buffer.val.length + 1 ≤ Usize.max) (hN : 0 < N.val) :
    ∃ c', (do
        let c1 ← p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanObserve.observe cl
          hashInst c x
        p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanSample.sample cl hashInst c1) =
      .ok ((H (c.input_buffer.val ++ [x])).val.getLastD default, c') ∧
      toHSt c' = ⟨(H (c.input_buffer.val ++ [x])).val, (H (c.input_buffer.val ++ [x])).val.dropLast⟩ := by
  obtain ⟨c1, e1, h1, hh1⟩ := hash_observe_eq cl hashInst c x hl
  have hH1 : HasherComputes hashInst c1.hasher H := hh1 ▸ hH
  obtain ⟨c2, e2, h2, hh2⟩ := flush_eq cl hcl hashInst H c1 hH1
  have hin1 : c1.input_buffer.val = c.input_buffer.val ++ [x] := congrArg HSt.inb h1
  have hout1 : c1.output_buffer.val = [] := congrArg HSt.outb h1
  have hout2 : c2.output_buffer.val = (H (c.input_buffer.val ++ [x])).val := by
    have := congrArg HSt.outb h2; simpa [toHSt, hin1] using this
  have hne : c2.output_buffer.val ≠ [] := by
    rw [hout2]; exact List.ne_nil_of_length_pos (by simp; omega)
  obtain ⟨v, ev, hv⟩ := vec_pop_eq default c2.output_buffer hne
  refine ⟨⟨c2.input_buffer, v, c2.hasher⟩, ?_, ?_⟩
  · rw [e1]
    simp only [bind_tc_ok, p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanSample.sample,
      vec_is_empty_eq, hout1, decide_true, ↓reduceIte, bind_ok, e2, ev, core.option.Option.expect, hout2]
    show (do
      let t ← RustM.ok ((H (c.input_buffer.val ++ [x])).val.getLastD default)
      RustM.ok (t, (⟨c2.input_buffer, v, c2.hasher⟩ : p3_challenger.hash_challenger.HashChallenger T Hs N))) = _
    simp only [bind_tc_ok]
  · have hin2 := congrArg HSt.inb h2
    simp [toHSt, hin1] at hin2
    simp [toHSt, hin2, hv, hout2]

end Plonky3Lean.Proofs.Challenger
