module

public import P3WordBackend
public import Plonky3Lean.Proofs.Word.Index
public import Plonky3Lean.Proofs.Word.Shift

@[expose] public section

/-!
# The compact key codes round-trip

A shift code holds the kind in three bits above a six-bit amount.

A key code holds the family tag above two shift codes of nine bits each:

```text
    key code   [ family : 2 | outer shift : 9 | inner shift : 9 ]
    shift code [ kind : 3 | amount : 6 ]
```

Every shift the constructor builds decodes back to itself, and so does every key.

So the code is injective, and decoding a code built here never panics.
-/

open Aeneas Aeneas.Std CoreModels p3_word Plonky3Lean.Proofs.Word
open p3_word_backend.keys.code.mirror Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.WordBackend

variable {W : Type}

theorem or_eq_add {x a k : ℕ} (ha : a < 2 ^ k) : (x <<< k) ||| a = x * 2 ^ k + a := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]

theorem shift_code_spec (k : shift.ShiftKind) :
    ∃ c : Std.U8, shift.ShiftKind.code k = .ok c ∧ c.val < 8 ∧
      shift.ShiftKind.from_code ⟨BitVec.ofNat _ c.val⟩ = .ok (.Some k) := by
  have h := shift_code_round_trip k
  cases k <;> simp [shift.ShiftKind.code, shift.ShiftKind.read_discriminant] at h ⊢ <;>
    exact h

theorem u8_mk_val (c : Std.U8) : (⟨BitVec.ofNat _ c.val⟩ : Std.U8) = c := by
  obtain ⟨b⟩ := c
  show (⟨BitVec.ofNat 8 b.toNat⟩ : Std.U8) = ⟨b⟩
  rw [BitVec.ofNat_toNat]
  exact congrArg _ (BitVec.setWidth_eq b)

theorem usize_mk_val {a : ℕ} (h : a < 2 ^ 32) : (⟨BitVec.ofNat _ a⟩ : Std.Usize).val = a := by
  show (BitVec.ofNat _ a).toNat = a
  rw [BitVec.toNat_ofNat]; exact small_mod_platform h

theorem kind_from_code_lit (k : system.ConstraintKind) :
    system.ConstraintKind.from_code
      (match k with | .Zero => 0#u8 | .And => 1#u8 | .IntegerMul => 2#u8) = .ok (.Some k) := by
  cases k <;> simp [system.ConstraintKind.from_code, system.ConstraintKind.ALL, lift_eq,
    CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Std.Array.to_slice] <;>
    rw [index_make _ _ _ (by simp)] <;> simp

theorem kind_code_spec (k : system.ConstraintKind) :
    system.ConstraintKind.code k = .ok ⟨BitVec.ofNat _ k.ctorIdx⟩ ∧ k.ctorIdx < 3 ∧
      system.ConstraintKind.from_code ⟨BitVec.ofNat _ k.ctorIdx⟩ = .ok (.Some k) := by
  have := kind_from_code_lit k
  cases k <;> exact ⟨rfl, by decide, this⟩

/-- A shift the constructor rebuilds from its own kind and amount. -/
def Fixed (inst : word.Word W) (s : shift.Shift W) : Prop :=
  s.amount.val < 64 ∧ shift.Shift.new inst s.kind ⟨BitVec.ofNat _ s.amount.val⟩ = .ok (.Ok s)

/-- Every shift the 32-bit constructor builds is fixed. -/
theorem fixed32 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word32}
    (h : shift.Shift.new I32w k amt = .ok (.Ok s)) : Fixed I32w s := by
  rw [new32_eq] at h
  have key : isLane k = false ∧ amt.val < 32 ∧
      s = ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩ := by
    split_ifs at h with h1 h2 <;> simp_all
  obtain ⟨h1, h2, rfl⟩ := key
  have hc : (UScalar.cast .U8 amt).val = amt.val := cast_u8_val amt (by omega)
  refine ⟨by simp only [hc]; omega, ?_⟩
  rw [new32_eq]
  simp only [hc, usize_mk_val (show amt.val < 2 ^ 32 by omega)]
  have hl : isLane (if amt.val = 0 then .LogicalLeft else k) = false := by
    split
    · rfl
    · exact h1
  have hu : UScalar.cast .U8 (⟨BitVec.ofNat _ amt.val⟩ : Std.Usize) = UScalar.cast .U8 amt :=
    UScalar.eq_of_val_eq (by
      rw [UScalar.cast_val_eq, UScalar.cast_val_eq, usize_mk_val (show amt.val < 2 ^ 32 by omega)])
  rw [hl, hu]
  split_ifs <;> simp_all

/-- Every shift the 64-bit constructor builds is fixed. -/
theorem fixed64 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word64}
    (h : shift.Shift.new I64w k amt = .ok (.Ok s)) : Fixed I64w s := by
  rw [new64_eq] at h
  have key : amt.val < opWidth 64 k ∧
      s = ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩ := by
    split_ifs at h with h1 <;> simp_all; omega
  obtain ⟨h1, rfl⟩ := key
  have hw : opWidth 64 k ≤ 64 := by unfold opWidth; split <;> omega
  have hc : (UScalar.cast .U8 amt).val = amt.val := cast_u8_val amt (by omega)
  refine ⟨by simp only [hc]; omega, ?_⟩
  rw [new64_eq]
  simp only [hc, usize_mk_val (show amt.val < 2 ^ 32 by omega)]
  have hl : amt.val < opWidth 64 (if amt.val = 0 then .LogicalLeft else k) := by
    split
    · simp [opWidth, isLane]; omega
    · exact h1
  have hu : UScalar.cast .U8 (⟨BitVec.ofNat _ amt.val⟩ : Std.Usize) = UScalar.cast .U8 amt :=
    UScalar.eq_of_val_eq (by
      rw [UScalar.cast_val_eq, UScalar.cast_val_eq, usize_mk_val (show amt.val < 2 ^ 32 by omega)])
  rw [hu, ite_eq_right_of_eq_false _ _ (by simp; omega)]
  split_ifs <;> simp_all

/-- The code of a fixed shift is below $2^9$, and decodes back to the shift. -/
theorem shift_code_round (inst : word.Word W) {s : shift.Shift W} (hs : Fixed inst s) :
    ∃ c, ShiftCode.new s = .ok c ∧ c < 2 ^ 9 ∧ ShiftCode.shift inst c = .ok s := by
  obtain ⟨hlt, hnew⟩ := hs
  obtain ⟨k, hk, hk8, hfrom⟩ := shift_code_spec s.kind
  refine ⟨k.val * 64 + s.amount.val, ?_, by omega, ?_⟩
  · simp only [ShiftCode.new, hk, bind_ok]
    rw [or_eq_add (by simpa using hlt)]
    rfl
  · have h1 : (k.val * 64 + s.amount.val) &&& (2 ^ SHIFT_BITS - 1) = k.val * 64 + s.amount.val := by
      rw [Nat.and_two_pow_sub_one_eq_mod, SHIFT_BITS, Nat.mod_eq_of_lt (by omega)]
    have h2 : (k.val * 64 + s.amount.val) >>> 6 = k.val := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    have h3 : (k.val * 64 + s.amount.val) &&& 0x3f = s.amount.val := by
      rw [show (0x3f : ℕ) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
    simp only [ShiftCode.shift, h1, h2, h3, hfrom, bind_ok, hnew]

theorem shift_mod (inst : word.Word W) (c : ℕ) :
    ShiftCode.shift inst c = ShiftCode.shift inst (c % 2 ^ 9) := by
  unfold ShiftCode.shift
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, SHIFT_BITS, Nat.mod_mod]

theorem key_layout {o co ci : ℕ} (hco : co < 2 ^ 9) (hci : ci < 2 ^ 9) :
    (o <<< SEQUENCE_BITS) ||| (co <<< SHIFT_BITS) ||| ci = (o * 2 ^ 9 + co) * 2 ^ 9 + ci := by
  have : (o <<< SEQUENCE_BITS) ||| (co <<< SHIFT_BITS) = ((o <<< 9) ||| co) <<< 9 := by
    rw [SEQUENCE_BITS, SHIFT_BITS, show 2 * 9 = 9 + 9 from rfl, Nat.shiftLeft_add,
      Nat.shiftLeft_or_distrib]
  rw [this, or_eq_add hco, or_eq_add hci]

/-- A key code decodes to its family and its two shifts. -/
theorem key_code_round (inst : word.Word W) (op : system.ConstraintKind)
    (shifts : Array (shift.Shift W) 2#usize) {inner outer : shift.Shift W}
    (h : shifts.val = [inner, outer]) (hi : Fixed inst inner) (ho : Fixed inst outer) :
    ∃ c, KeyCode.new op shifts = .ok c ∧ KeyCode.operation c = .ok op ∧
      ShiftSequenceCode.shifts inst (KeyCode.sequence c) = .ok shifts := by
  obtain ⟨ci, hci, hci2, hdi⟩ := shift_code_round inst hi
  obtain ⟨co, hco, hco2, hdo⟩ := shift_code_round inst ho
  obtain ⟨hk, hk3, hkf⟩ := kind_code_spec op
  have h0 : Array.index_usize shifts 0#usize = .ok inner := by simp [Array.index_usize, h]
  have h1 : Array.index_usize shifts 1#usize = .ok outer := by simp [Array.index_usize, h]
  refine ⟨(op.ctorIdx * 2 ^ 9 + co) * 2 ^ 9 + ci, ?_, ?_, ?_⟩
  · simp only [KeyCode.new, hk, h0, h1, hci, hco, bind_ok]
    rw [show (⟨BitVec.ofNat _ op.ctorIdx⟩ : Std.U8).val = op.ctorIdx by
      show (BitVec.ofNat 8 _).toNat = _; rw [BitVec.toNat_ofNat]; omega, key_layout hco2 hci2]
  · have : ((op.ctorIdx * 2 ^ 9 + co) * 2 ^ 9 + ci) >>> SEQUENCE_BITS = op.ctorIdx := by
      rw [Nat.shiftRight_eq_div_pow, SEQUENCE_BITS, SHIFT_BITS]; omega
    simp only [KeyCode.operation, this, hkf, bind_ok]
  · have hs : KeyCode.sequence ((op.ctorIdx * 2 ^ 9 + co) * 2 ^ 9 + ci) = co * 2 ^ 9 + ci := by
      rw [KeyCode.sequence, SEQUENCE_MASK, Nat.and_two_pow_sub_one_eq_mod, SEQUENCE_BITS, SHIFT_BITS]
      omega
    have e1 : (co * 2 ^ 9 + ci) % 2 ^ 16 % 2 ^ 9 = ci := by omega
    have e2 : ((co * 2 ^ 9 + ci) >>> SHIFT_BITS) % 2 ^ 16 % 2 ^ 9 = co := by
      rw [Nat.shiftRight_eq_div_pow, SHIFT_BITS]; omega
    simp only [ShiftSequenceCode.shifts, hs]
    rw [shift_mod inst, e1, hdi, bind_ok, shift_mod inst, e2, hdo, bind_ok]
    congr 1
    exact Std.Array.ext _ _ (by simp [h])

end Plonky3Lean.Proofs.WordBackend
