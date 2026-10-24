module

public import P3MultiStark
public import Plonky3Lean.Lib.Yields

@[expose] public section

/-!
# The extracted verifier arithmetic

hax extracts the boundary selectors, the successor row and the zerocheck's free coordinates.

Their theorems assume one thing of the field instance: each member they call computes the operation it names.

Under that assumption each returns what its transcription computes.

So every theorem about the transcriptions holds for the shipped code.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.MultiStark.Extracted

variable {K : Type} [Field K]

/-- The members of the field instance that the extracted code calls compute:

- one, the sum, the difference and the product;
- the product assigned in place;
- the field element of a boolean;
- a vector of zeros of a given length. -/
structure FieldComputes (inst : p3_field.field.Field K) : Prop where
  one : inst.AlgebraInst.PrimeCharacteristicRingInst.ONE = .ok 1
  add : ∀ a b : K, inst.AlgebraInst.coreopsarithAddInst.add a b = .ok (a + b)
  sub : ∀ a b : K, inst.AlgebraInst.coreopsarithSubInst.sub a b = .ok (a - b)
  mul : ∀ a b : K, inst.AlgebraInst.coreopsarithMulInst.mul a b = .ok (a * b)
  mul_assign : ∀ a b : K, inst.AlgebraInst.coreopsarithMulAssignInst.mul_assign a b = .ok (a * b)
  from_bool : ∀ b : Bool, inst.AlgebraInst.PrimeCharacteristicRingInst.from_bool b = .ok (if b then 1 else 0)
  zero_vec : ∀ n : Std.Usize, ∃ v,
    inst.AlgebraInst.PrimeCharacteristicRingInst.zero_vec n = .ok v ∧ Slice.val v = List.replicate n.val 0

/-- The shipped selectors that hold a transcription's values. -/
def ofMirror (b : p3_multi_stark.selectors.mirror.BoundaryEvals K) :
    p3_multi_stark.selectors.BoundaryEvals K :=
  ⟨b.first, b.last, b.transition⟩

variable {inst : p3_field.field.Field K} (h : FieldComputes inst)
include h

omit h in
/-- The row after a row below the largest usize. -/
theorem add_one_ok (row : Std.Usize) (hrow : row.val < Usize.max) :
    ∃ i : Std.Usize, (row + 1#usize : RustM Std.Usize) = .ok i ∧ i.val = row.val + 1 := by
  have hs := @Usize.add_spec row 1#usize
  generalize (row + 1#usize : RustM Std.Usize) = m at hs ⊢
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using hs⟩
  | vis i k => cases i with | fail e => (cases e <;> simp [WP.partialSpec] at hs; omega)
  | div => simp at hs

omit h in
/-- The row after the largest usize overflows. -/
theorem add_one_max (row : Std.Usize) (hrow : row.val = Usize.max) :
    (row + 1#usize : RustM Std.Usize) = .fail .panic := by
  have hs := @Usize.add_spec row 1#usize
  generalize (row + 1#usize : RustM Std.Usize) = m at hs ⊢
  cases m with
  | ret r => simp at hs; scalar_tac
  | vis i k =>
    cases i with
    | fail e =>
      cases e <;> simp [WP.partialSpec] at hs
      exact congrArg _ (funext fun x => nomatch x)
  | div => simp at hs

/-! ## The boundary selectors -/

theorem at_loop {it : core.slice.iter.Iter K} {rs : List K}
    (hy : Yields (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT K) it rs)
    (acc : K × K) :
    p3_multi_stark.selectors.BoundaryEvals.at_loop inst 1 it acc.1 acc.2 =
      .ok (rs.foldl p3_multi_stark.selectors.mirror.atStep acc) := by
  induction hy generalizing acc with
  | nil e =>
    simp only at e
    unfold p3_multi_stark.selectors.BoundaryEvals.at_loop
    rw [loop]
    simp [p3_multi_stark.selectors.BoundaryEvals.at_loop.body, e]
  | @cons _ _ r _ e _ ih =>
    simp only at e
    have ih' := ih (acc.1 * (1 - r), acc.2 * r)
    unfold p3_multi_stark.selectors.BoundaryEvals.at_loop at ih' ⊢
    rw [loop]
    simp only [p3_multi_stark.selectors.BoundaryEvals.at_loop.body, h.sub, h.mul_assign, bind_ok] at ih'
    simpa [p3_multi_stark.selectors.BoundaryEvals.at_loop.body, e, h.sub, h.mul_assign,
      p3_multi_stark.selectors.mirror.atStep] using ih'

/-- The extracted selectors at a point compute their transcription. -/
theorem at_eq (rs : Slice K) :
    p3_multi_stark.selectors.BoundaryEvals.at inst rs =
      .ok (ofMirror (p3_multi_stark.selectors.mirror.BoundaryEvals.at rs.val)) := by
  unfold p3_multi_stark.selectors.BoundaryEvals.at
  simp only [h.one, Std.bind_ok,
    core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice]
  repeat erw [Std.bind_ok]
  rw [at_loop h (yields_slice _ rs rfl) (1, 1)]
  simp only [h.sub, bind_ok, ofMirror, p3_multi_stark.selectors.mirror.BoundaryEvals.at]
  generalize rs.val.foldl p3_multi_stark.selectors.mirror.atStep (1, 1) = p
  cases p
  rfl

/-- The extracted fold of one more coordinate computes its transcription. -/
theorem apply_eq (b : p3_multi_stark.selectors.mirror.BoundaryEvals K) (r : K) :
    p3_multi_stark.selectors.BoundaryEvals.apply inst (ofMirror b) r = .ok (ofMirror (b.apply r)) := by
  simp [p3_multi_stark.selectors.BoundaryEvals.apply, h.one, h.sub, h.mul_assign, ofMirror,
    p3_multi_stark.selectors.mirror.BoundaryEvals.apply]

/-- The extracted indicators of one row compute their transcription, for every row but the largest.

That row panics, since the row after it overflows. -/
theorem from_row_eq (row height : Std.Usize) (hrow : row.val < Usize.max) :
    p3_multi_stark.selectors.BoundaryEvals.from_row inst row height =
      .ok (ofMirror (p3_multi_stark.selectors.mirror.BoundaryEvals.from_row row.val height.val)) := by
  obtain ⟨i, hi, hiv⟩ := add_one_ok row hrow
  have h0 : (row = 0#usize) ↔ row.val = 0 := ⟨fun e => by simp [e], fun e => UScalar.eq_of_val_eq (by simp [e])⟩
  have h1 : (i = height) ↔ row.val + 1 = height.val := ⟨fun e => by simp [← e, hiv],
    fun e => UScalar.eq_of_val_eq (by simp [hiv, e])⟩
  simp [p3_multi_stark.selectors.BoundaryEvals.from_row, h.from_bool, hi, h0, h1, hiv,
    p3_multi_stark.selectors.BoundaryEvals.new, ofMirror, p3_multi_stark.selectors.mirror.BoundaryEvals.from_row]

/-- The extracted indicators of the largest row panic. -/
theorem from_row_max (row height : Std.Usize) (hrow : row.val = Usize.max) :
    p3_multi_stark.selectors.BoundaryEvals.from_row inst row height = .fail .panic := by
  simp [p3_multi_stark.selectors.BoundaryEvals.from_row, h.from_bool, add_one_max row hrow]

/-- The extracted indicators behind a prefix compute their transcription, for every row but the largest. -/
theorem from_row_with_prefix_eq (row height : Std.Usize) (hrow : row.val < Usize.max)
    (pre : p3_multi_stark.selectors.mirror.BoundaryEvals K) :
    p3_multi_stark.selectors.BoundaryEvals.from_row_with_prefix inst row height (ofMirror pre) =
      .ok (ofMirror (p3_multi_stark.selectors.mirror.BoundaryEvals.from_row_with_prefix row.val height.val pre)) := by
  simp [p3_multi_stark.selectors.BoundaryEvals.from_row_with_prefix, from_row_eq h row height hrow, h.mul, h.add,
    p3_multi_stark.selectors.BoundaryEvals.new, ofMirror,
    p3_multi_stark.selectors.mirror.BoundaryEvals.from_row_with_prefix]

/-! ## The zerocheck's free coordinates -/

omit h in
/-- The extracted free coordinates are the cube's variables minus the lookup's, clamped at 0. -/
theorem free_coordinates_eq (s : p3_multi_stark.zerocheck.transcript.ZerocheckShape) :
    ∃ n : Std.Usize, p3_multi_stark.zerocheck.transcript.ZerocheckShape.free_coordinates s = .ok n ∧
      n.val = s.log_height.val - s.lookup_point_len.val := by
  refine ⟨_, rfl, ?_⟩
  show (BitVec.ofNat _ (s.log_height.val - s.lookup_point_len.val)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) s.log_height.hBounds)]

/-! ## The successor row -/

omit h in
/-- Writing through a vector's mutable index sets one entry, and panics past the end. -/
theorem index_mut_eq {T : Type} (v : Slice T) (c : Std.Usize) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) v c =
      if hc : c.val < v.val.length then .ok (v.val[c.val], Slice.set v c) else .fail .panic := by
  unfold alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut
  simp only [rust_primitives.sequence.seq_to_slice_mut, Std.bind_ok]
  show (do let (t, b) ← Slice.index_mut_usize v c; .ok (t, fun t1 => b t1)) = _
  split <;> rename_i hc <;> simp [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq, hc] <;> rfl

/-- A vector computation agrees with a transcription that returns a list or panics. -/
def Agrees {T : Type} (m : RustM (alloc.vec.Vec T)) : Option (List T) → Prop
  | none => m = .fail .panic
  | some l => ∃ v, m = .ok v ∧ Slice.val v = l

/-- The column-value pairs of the claims, as the transcription reads them. -/
def pairs (l : List (Std.Usize × K)) : List (ℕ × K) := l.map fun cv => (cv.1.val, cv.2)

omit h [Field K] in
theorem scatter_none (l : List (ℕ × K)) : l.foldl p3_multi_stark.opening.mirror.scatterStep none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

omit h [Field K] in
theorem next_row_loop {it : core.slice.iter.Iter (Std.Usize × K)} {l : List (Std.Usize × K)}
    (hy : Yields (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT _) it l)
    (row : Slice K) :
    Agrees (p3_multi_stark.opening.OpeningClaims.next_row_loop it row)
      ((pairs l).foldl p3_multi_stark.opening.mirror.scatterStep (some (Slice.val row))) := by
  induction hy generalizing row with
  | nil e =>
    simp only at e
    unfold p3_multi_stark.opening.OpeningClaims.next_row_loop
    rw [loop]
    exact ⟨row, by simp [p3_multi_stark.opening.OpeningClaims.next_row_loop.body, e], rfl⟩
  | @cons _ _ cv rest e _ ih =>
    simp only at e
    obtain ⟨c, x⟩ := cv
    unfold p3_multi_stark.opening.OpeningClaims.next_row_loop at ih ⊢
    rw [loop]
    simp only [p3_multi_stark.opening.OpeningClaims.next_row_loop.body, e, Std.bind_ok,
      Aeneas.Std.uncurry_apply_pair]
    by_cases hc : c.val < (Slice.val row).length
    · have hstep : p3_multi_stark.opening.mirror.scatterStep (some (Slice.val row)) (c.val, x) =
          some (Slice.val (Slice.set row c x)) := by
        simp [p3_multi_stark.opening.mirror.scatterStep, hc, Slice.set_val_eq]
      rw [index_mut_eq row c, dite_eq_left hc, pairs, List.map_cons, List.foldl_cons]
      erw [hstep, Std.bind_ok, Std.bind_ok]
      exact ih (Slice.set row c x)
    · have hstep : p3_multi_stark.opening.mirror.scatterStep (some (Slice.val row)) (c.val, x) = none := by
        simp [p3_multi_stark.opening.mirror.scatterStep, hc]
      rw [index_mut_eq row c, dite_eq_right hc, pairs, List.map_cons, List.foldl_cons]
      erw [hstep, scatter_none, Std.bind_fail, Std.bind_fail]
      rfl

/-- The extracted successor row scatters the claimed values into a zero row of the given width.

It panics when a column lies past the width. -/
theorem next_row_eq (claims : p3_multi_stark.opening.OpeningClaims K) (width : Std.Usize) :
    Agrees (p3_multi_stark.opening.OpeningClaims.next_row inst claims width)
      ((pairs (Slice.val claims.next)).foldl p3_multi_stark.opening.mirror.scatterStep
        (some (List.replicate width.val 0))) := by
  obtain ⟨z, hz, hzv⟩ := h.zero_vec width
  unfold p3_multi_stark.opening.OpeningClaims.next_row
  rw [hz, Std.bind_ok]
  simp only [alloc.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    alloc.vec.Vec.as_slice, core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice]
  repeat erw [Std.bind_ok]
  rw [← hzv]
  exact next_row_loop (yields_slice _ claims.next rfl) z

end Plonky3Lean.Proofs.MultiStark.Extracted
