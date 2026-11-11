module

public import Plonky3Lean.Proofs.Word.System

@[expose] public section

/-!
# Compact word positions

A position is stored in 32 bits.

A position that does not fit is refused with an error, never truncated.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

/-- Converting a platform word to 32 bits keeps its value when it fits.

Otherwise it reports an error. -/
theorem u32_try_from_eq (x : Std.Usize) :
    CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from x =
      .ok (if x.val < 2 ^ 32 then .Ok (UScalar.cast .U32 x) else .Err ()) := by
  unfold CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  have hmax : (UScalar.cast .Usize CoreModels.core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])]
    simp [CoreModels.core.num.U32.MAX, U32.rMax]
  have hmin : (UScalar.cast .Usize CoreModels.core.num.U32.MIN).val = 0 := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])]
    simp [CoreModels.core.num.U32.MIN]
  simp only [lift_eq, bind_ok, GT.gt, UScalar.lt_equiv, hmax, hmin]
  simp only [Nat.not_lt_zero, ite_false]
  split_ifs <;> first | rfl | omega

/-- A position becomes an index exactly when it fits in 32 bits, and keeps its value. -/
theorem value_index_new_eq (seg : index.Segment) (pos : Std.Usize) :
    index.ValueIndex.new seg pos =
      .ok (if pos.val < 2 ^ 32 then .Ok ⟨seg, UScalar.cast .U32 pos⟩
        else .Err (.PositionTooLarge pos)) := by
  unfold index.ValueIndex.new
  rw [u32_try_from_eq]
  split_ifs <;>
    simp [CoreModels.core.result.Result.map_err,
      index.ValueIndex.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorIndexError.call_once,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]

theorem cast_u32_val (pos : Std.Usize) (h : pos.val < 2 ^ 32) : (UScalar.cast .U32 pos).val = pos.val :=
  UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simpa using h)

/-! ## Movement codes -/

theorem small_mod_platform {k : ℕ} (h : k < 2 ^ 32) : k % 2 ^ System.Platform.numBits = k := by
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

/-- Every movement round-trips through its three-bit code. -/
theorem shift_code_round_trip (k : shift.ShiftKind) :
    (do let c ← shift.ShiftKind.code k; shift.ShiftKind.from_code c) = .ok (.Some k) := by
  cases k <;> simp [shift.ShiftKind.code, shift.ShiftKind.from_code, shift.ShiftKind.ALL,
    CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, lift_eq,
    Std.Array.to_slice, shift.ShiftKind.read_discriminant] <;>
    rw [index_make _ _ _ (by simp [UScalar.cast_val_eq, small_mod_platform])] <;>
    simp [UScalar.cast_val_eq, small_mod_platform]

/-- A code of 8 or more names no movement. -/
theorem shift_from_code_none (c : Std.U8) (h : 8 ≤ c.val) :
    shift.ShiftKind.from_code c = .ok .None := by
  simp [shift.ShiftKind.from_code, shift.ShiftKind.ALL, lift_eq,
    CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Std.Array.to_slice]
  omega

end Plonky3Lean.Proofs.Word
