module

public import Plonky3Lean.Proofs.Word.Ops

@[expose] public section

/-!
# Shifts: construction and application

A shift applies to a word exactly as the bit-vector model says, or panics.

It panics only when it was not built by the checked constructor.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

/-- The word instance at 32 bits. -/
abbrev I32w := word.Word32.Insts.P3_wordWordWord

/-- The word instance at 64 bits. -/
abbrev I64w := word.Word64.Insts.P3_wordWordWord

theorem amount_cast_val (a : Std.U8) : (UScalar.cast .U32 a).val = a.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by decide)

theorem apply32_eq (s : shift.Shift word.Word32) (x : word.Word32) :
    shift.Shift.apply I32w s x =
      if panics32 s.kind s.amount.val then RustM.fail .panic
      else RustM.ok ⟨sem32 s.kind s.amount.val x.bv⟩ := by
  obtain ⟨k, a, _⟩ := s
  cases k <;>
    simp [shift.Shift.apply, core.U32.Insts.CoreConvertFromU8.from,
      W32.logical_left_eq, W32.logical_right_eq, W32.arithmetic_right_eq, W32.rotate_right_eq,
      W32.lane32_left_eq, W32.lane32_right_eq, W32.lane32_arithmetic_right_eq,
      W32.lane32_rotate_right_eq, panics32, sem32, base, isLane, isRotate,
      CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic] <;>
    split_ifs <;> first | rfl | omega

theorem apply64_eq (s : shift.Shift word.Word64) (x : word.Word64) :
    shift.Shift.apply I64w s x =
      if panics64 s.kind s.amount.val then RustM.fail .panic
      else RustM.ok ⟨sem64 s.kind s.amount.val x.bv⟩ := by
  obtain ⟨k, a, _⟩ := s
  cases k <;>
    simp [shift.Shift.apply, core.U32.Insts.CoreConvertFromU8.from,
      W64.logical_left_eq, W64.logical_right_eq, W64.arithmetic_right_eq, W64.rotate_right_eq,
      W64.lane32_left_eq, W64.lane32_right_eq, W64.lane32_arithmetic_right_eq,
      W64.lane32_rotate_right_eq, panics64, opWidth, sem64, base, isLane, isRotate,
      CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic] <;>
    (try split_ifs) <;> first | rfl | omega | simp

theorem bits32 : word.Word32.Insts.P3_wordWordWord.BITS = 32#u32 := by
  unfold word.Word32.Insts.P3_wordWordWord.BITS; rfl

theorem bits64 : word.Word64.Insts.P3_wordWordWord.BITS = 64#u32 := by
  unfold word.Word64.Insts.P3_wordWordWord.BITS; rfl

/-- The checked constructor at 32 bits.

- A lane movement is refused, since a 32-bit word has no lanes.
- A distance of 32 or more is refused.
- Otherwise the shift is built, with a zero distance spelled as a left shift. -/
theorem new32_eq (k : shift.ShiftKind) (amt : Std.Usize) :
    shift.Shift.new I32w k amt = RustM.ok
      (if isLane k then .Err .Lane32RequiresWord64
       else if 32 ≤ amt.val then .Err (.AmountOutOfRange amt 32#u32)
       else .Ok ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩) := by
  have hz : (amt = 0#usize) ↔ amt.val = 0 :=
    ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩
  cases k <;> simp [shift.Shift.new, shift.ShiftKind.is_lane32, isLane, bits32, lift_eq, hz] <;>
    split_ifs <;> simp_all

/-- The checked constructor at 64 bits.

- A distance at or past the movement's width is refused: 32 for a lane, 64 otherwise.
- Otherwise the shift is built, with a zero distance spelled as a left shift. -/
theorem new64_eq (k : shift.ShiftKind) (amt : Std.Usize) :
    shift.Shift.new I64w k amt = RustM.ok
      (if opWidth 64 k ≤ amt.val then
         .Err (.AmountOutOfRange amt (if isLane k then 32#u32 else 64#u32))
       else .Ok ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩) := by
  have hz : (amt = 0#usize) ↔ amt.val = 0 :=
    ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩
  cases k <;> simp [shift.Shift.new, shift.ShiftKind.is_lane32, isLane, opWidth, bits64,
    lift_eq, hz] <;> split_ifs <;> simp_all

theorem cast_u8_val (amt : Std.Usize) (h : amt.val < 256) : (UScalar.cast .U8 amt).val = amt.val :=
  UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simpa using h)

/-- Every movement by zero is the identity. -/
theorem base_zero {n : Nat} (k : shift.ShiftKind) (x : BitVec n) : base k 0 x = x := by
  cases k <;> simp [base, BitVec.rotateRight, BitVec.rotateRightAux]

/-- A 32-bit shift from the checked constructor applies without panicking, as the model says. -/
theorem apply32_of_new {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word32}
    (h : shift.Shift.new I32w k amt = RustM.ok (.Ok s)) (x : word.Word32) :
    shift.Shift.apply I32w s x = RustM.ok ⟨sem32 k amt.val x.bv⟩ := by
  rw [new32_eq, RustM.ok.injEq] at h
  split_ifs at h with h1 h2 h0 <;> cases h <;> rw [apply32_eq, cast_u8_val _ (by omega)]
  · simp [h0, panics32, isLane, isRotate, sem32, base_zero]
  · simp [panics32, h1, show amt.val < 32 by omega]

theorem lanes_id (x : BitVec 64) : lanes (fun y => y) x = x := by
  ext i hi
  simp only [lanes, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp [h, hi]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega, hi]

/-- A 64-bit shift from the checked constructor applies without panicking, as the model says. -/
theorem apply64_of_new {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word64}
    (h : shift.Shift.new I64w k amt = RustM.ok (.Ok s)) (x : word.Word64) :
    shift.Shift.apply I64w s x = RustM.ok ⟨sem64 k amt.val x.bv⟩ := by
  rw [new64_eq, RustM.ok.injEq] at h
  have hw : opWidth 64 k ≤ 64 := by unfold opWidth; split <;> omega
  split_ifs at h with h1 h0 <;> cases h <;> rw [apply64_eq, cast_u8_val _ (by omega)]
  · simp only [h0, panics64, isRotate, opWidth, isLane]
    simp [sem64, base_zero, lanes_id]
  · simp [panics64, show amt.val < opWidth 64 k by omega]

/-! ## Terms with two shifts -/

/-- The identity shift, spelled as the constructor normalizes it. -/
def idShift {W : Type} : shift.Shift W := ⟨.LogicalLeft, 0#u8, ()⟩

/-- The movement a term applies first. -/
def svInner {W : Type} (t : shift.ShiftedValue W) : shift.Shift W := t.shifts.val.getD 0 idShift

/-- The movement a term applies second. -/
def svOuter {W : Type} (t : shift.ShiftedValue W) : shift.Shift W := t.shifts.val.getD 1 idShift

theorem sv_index {W : Type} (t : shift.ShiftedValue W) :
    Std.Array.index_usize t.shifts 0#usize = .ok (svInner t) ∧
      Std.Array.index_usize t.shifts 1#usize = .ok (svOuter t) := by
  have hl : t.shifts.val.length = 2 := t.shifts.property
  refine ⟨?_, ?_⟩ <;> rw [index_usize_eq _ _ (by simp [hl])] <;>
    simp [svInner, svOuter, List.getD_eq_getElem?_getD, hl]

/-- A 32-bit term applies its inner movement, then its outer one, or panics if either does. -/
theorem sv_apply32_eq (t : shift.ShiftedValue word.Word32) (x : word.Word32) :
    shift.ShiftedValue.apply I32w t x =
      if panics32 (svInner t).kind (svInner t).amount.val ∨
          panics32 (svOuter t).kind (svOuter t).amount.val then RustM.fail .panic
      else RustM.ok ⟨sem32 (svOuter t).kind (svOuter t).amount.val
        (sem32 (svInner t).kind (svInner t).amount.val x.bv)⟩ := by
  obtain ⟨h0, h1⟩ := sv_index t
  simp only [shift.ShiftedValue.apply, h0, h1, bind_ok, apply32_eq]
  by_cases a : panics32 (svInner t).kind (svInner t).amount.val
  · simp [a]
  · by_cases b : panics32 (svOuter t).kind (svOuter t).amount.val <;> simp [a, b]

/-- A 64-bit term applies its inner movement, then its outer one, or panics if either does. -/
theorem sv_apply64_eq (t : shift.ShiftedValue word.Word64) (x : word.Word64) :
    shift.ShiftedValue.apply I64w t x =
      if panics64 (svInner t).kind (svInner t).amount.val ∨
          panics64 (svOuter t).kind (svOuter t).amount.val then RustM.fail .panic
      else RustM.ok ⟨sem64 (svOuter t).kind (svOuter t).amount.val
        (sem64 (svInner t).kind (svInner t).amount.val x.bv)⟩ := by
  obtain ⟨h0, h1⟩ := sv_index t
  simp only [shift.ShiftedValue.apply, h0, h1, bind_ok, apply64_eq]
  by_cases a : panics64 (svInner t).kind (svInner t).amount.val
  · simp [a]
  · by_cases b : panics64 (svOuter t).kind (svOuter t).amount.val <;> simp [a, b]

end Plonky3Lean.Proofs.Word
