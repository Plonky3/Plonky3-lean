module

public import Plonky3Lean.Proofs.BinaryDft.ExtractedLch

@[expose] public section

/-!
# The extracted transform

The extracted schedule, tile pass and blocked run are the transcribed ones.

So the extracted forward and inverse transforms return what the transcribed transform returns.

They panic exactly when it does.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

/-! ## Iterating a range backwards -/

theorem range_next_back_lt (i : Std.Usize) {K : ℕ} (hK : K ≤ Usize.max) (h : i.val < K) :
    core.IteratorRange.next_back core.Usize.Insts.CoreIterRangeStep { start := i, «end» := uz K } =
      .ok (core.option.Option.Some (uz (K - 1)), { start := i, «end» := uz (K - 1) }) := by
  unfold core.IteratorRange.next_back
  have h1 : (1#usize : Std.Usize).val = 1 := rfl
  have hu : uoverflowing_sub (uz K) 1#usize = (uz (K - 1), false) := by
    have hKv := uz_val hK
    have hle : (1#usize : Std.Usize).bv ≤ (uz K).bv := by
      rw [BitVec.le_def, UScalar.bv_toNat, UScalar.bv_toNat, h1, hKv]; omega
    refine Prod.ext (UScalar.eq_of_val_eq ?_) (by simp [uoverflowing_sub, uz_val hK, h1]; omega)
    rw [uz_val (show K - 1 ≤ Usize.max by omega)]
    calc (uoverflowing_sub (uz K) 1#usize).1.val
        = (@HSub.hSub (BitVec UScalarTy.Usize.numBits) _ _ _ (uz K).bv (1#usize : Std.Usize).bv).toNat := rfl
      _ = (uz K).bv.toNat - (1#usize : Std.Usize).bv.toNat := BitVec.toNat_sub_of_le hle
      _ = K - 1 := by rw [UScalar.bv_toNat, UScalar.bv_toNat, hKv, h1]
  simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, uz_val hK, compare_lt_iff_lt.mpr h,
    core.Usize.Insts.CoreIterRangeStep.backward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_sub, core.num.Usize.overflowing_sub,
    rust_primitives.arithmetic.overflowing_sub_usize, hu]

/-! ## Base-two logarithms -/

theorem u32_sub_ok (x y : Std.U32) (h : y.val ≤ x.val) :
    ∃ z : Std.U32, (x - y : RustM Std.U32) = .ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.sub_bv_spec (x := x) (y := y) h)
  exact ⟨z, hz, hv.1⟩

theorem numBits_le64 : UScalarTy.Usize.numBits ≤ 64 := by
  rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> omega

theorem log_lt_numBits (x : Std.Usize) (hx : x.val ≠ 0) : Nat.log 2 x.val < UScalarTy.Usize.numBits :=
  (Nat.log_lt_iff_lt_pow one_lt_two hx).mpr x.hBounds

theorem lz_eq (x : Std.Usize) (hx : x.val ≠ 0) :
    ∃ v : Std.U32, core.num.Usize.leading_zeros x = .ok v ∧
      v.val = UScalarTy.Usize.numBits - Nat.log 2 x.val - 1 := by
  have h0 : x.bv ≠ 0 := fun h => hx (by simp [UScalar.val, h])
  refine ⟨_, rfl, ?_⟩
  simp only [Aeneas.Std.core.num.Usize.leading_zeros, BitVec.leadingZeros, h0, ↓reduceIte]
  show (BitVec.ofNat 32 (System.Platform.numBits - Nat.log 2 x.bv.toNat - 1)).toNat = _
  have := numBits_le64
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat, ← UScalarTy.Usize_numBits_eq, Nat.mod_eq_of_lt (by omega)]

theorem lz_zero (x : Std.Usize) (hx : x.val = 0) :
    ∃ v : Std.U32, core.num.Usize.leading_zeros x = .ok v ∧ v.val = UScalarTy.Usize.numBits := by
  have h0 : x.bv = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [UScalar.bv_toNat, hx]; rfl
  refine ⟨_, rfl, ?_⟩
  simp only [Aeneas.Std.core.num.Usize.leading_zeros, BitVec.leadingZeros, h0, ↓reduceIte]
  show (BitVec.ofNat 32 System.Platform.numBits).toNat = _
  have := numBits_le64
  rw [BitVec.toNat_ofNat, ← UScalarTy.Usize_numBits_eq, Nat.mod_eq_of_lt (by omega)]

theorem bits_val : (core.num.Usize.BITS : Std.U32).val = UScalarTy.Usize.numBits := by
  simp [core.num.Usize.BITS]

theorem cast_u32_usize (v : Std.U32) (h : v.val ≤ 64) : (UScalar.cast .Usize v) = uz v.val :=
  UScalar.eq_of_val_eq (by
    rw [uz_val (by have := usize_max_ge (n := 64) (by norm_num); rw [UScalar.max_USize_eq] at this; omega),
      UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
        rcases System.Platform.numBits_eq with e | e <;> simp [UScalarTy.numBits, e])])

/-- The floor of log_2, with log_2 0 taken as 0. -/
theorem log2_floor_eq (n : Std.Usize) : p3_util.log2_floor_usize n = .ok (uz (Nat.log 2 n.val)) := by
  unfold p3_util.log2_floor_usize
  by_cases h0 : n.val = 0
  · have : n = 0#usize := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst this
    simp only [ite_true, Nat.log_zero_right, h0]
    exact congrArg RustM.ok (UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl))
  · rw [ite_of_neg (fun h => h0 (by rw [h]; rfl))]
    have hl := log_lt_numBits n h0
    have h64 := numBits_le64
    have h1 : (1#u32 : Std.U32).val = 1 := rfl
    obtain ⟨z, hz, hzv⟩ := u32_sub_ok core.num.Usize.BITS 1#u32 (by rw [bits_val, h1]; omega)
    obtain ⟨v, hv, hvv⟩ := lz_eq n h0
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok z v (by rw [hzv, hvv, bits_val, h1]; omega)
    rw [hz, bind_ok, hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hzv, hvv, bits_val, h1]; omega),
      hyv, hzv, hvv, bits_val, h1]
    congr 2; omega

theorem clog_eq_log_pred {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow one_lt_two]
    have := Nat.lt_pow_succ_log_self one_lt_two (n - 1)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt one_lt_two]
    have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
    omega

/-- The ceiling of log_2, with log_2 0 taken as 0. -/
theorem log2_ceil_eq (n : Std.Usize) : p3_util.log2_ceil_usize n = .ok (uz (Nat.clog 2 n.val)) := by
  unfold p3_util.log2_ceil_usize
  have h64 := numBits_le64
  rw [show core.num.Usize.saturating_sub_exposed n 1#usize = .ok (uz (n.val - 1)) from rfl, bind_ok]
  have hum : n.val - 1 ≤ Usize.max := by scalar_tac
  by_cases h1 : n.val ≤ 1
  · obtain ⟨v, hv, hvv⟩ := lz_zero (uz (n.val - 1)) (by rw [uz_val hum]; omega)
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok core.num.Usize.BITS v (by rw [hvv, bits_val])
    rw [hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hvv, bits_val]; omega), hyv, hvv, bits_val,
      Nat.sub_self, Nat.clog_of_right_le_one h1]
  · have hn0 : (uz (n.val - 1)).val ≠ 0 := by rw [uz_val hum]; omega
    obtain ⟨v, hv, hvv⟩ := lz_eq (uz (n.val - 1)) hn0
    have hl := log_lt_numBits _ hn0
    rw [uz_val hum] at hvv hl
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok core.num.Usize.BITS v (by rw [hvv, bits_val]; omega)
    rw [hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hvv, bits_val]; omega), hyv, hvv, bits_val,
      clog_eq_log_pred (by omega)]
    congr 2; omega

end Plonky3Lean.Proofs.BinaryDft
