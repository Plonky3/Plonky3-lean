module

public import Plonky3Lean.Proofs.WordBackend.ShiftLinear

@[expose] public section

/-!
# The transcribed transpose, at 32 and at 64 bits

For a shift that does not panic, the transcribed transpose is the transpose of the shift's meaning.

The identity shortcut returns the same table as the general formula.

The two-slot transpose applies the outer shift first, so it is the transpose of the composed shift.
-/

open Finset Aeneas Aeneas.Std p3_word Plonky3Lean.Proofs.Word
open p3_word_backend.shift.wiring.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.WordBackend

variable {R : Type _} [CommRing R] [CharP R 2]

/-- The weight table read as a function, zero past its end. -/
def wt (out : List R) (b : ℕ) : R := out.getD b 0

theorem foldlM_at (out : List R) (L : List ℕ) (hL : ∀ b ∈ L, b < out.length) (acc : R) :
    L.foldlM (fun acc bit => do let w ← at? out bit; RustM.ok (acc + w)) acc =
      RustM.ok (acc + (L.map (wt out)).sum) := by
  induction L generalizing acc with
  | nil => simp; rfl
  | cons b L ih =>
    have hb := hL b (by simp)
    have hat : at? out b = RustM.ok out[b] := by simp [at?, List.getElem?_eq_getElem hb]
    simp only [List.foldlM_cons, hat, bind_ok, Aeneas.Std.bind_tc_ok]
    rw [ih (fun c hc => hL c (by simp [hc]))]
    simp [wt, add_assoc, List.getElem?_eq_getElem hb]

omit [CharP R 2] in
theorem sum_filter_range (n : ℕ) (p : ℕ → Bool) (f : ℕ → R) :
    (((List.range n).filter p).map f).sum = ∑ b ∈ range n, if p b then f b else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      sum_range_succ]
    cases h : p n <;> simp [List.filter, h]

theorem setBitsSum_eq (n pattern : ℕ) (out : List R) (h : n ≤ out.length) :
    setBitsSum n pattern out = RustM.ok (ev n pattern (wt out)) := by
  unfold setBitsSum
  rw [foldlM_at out _ (fun b hb => by simp at hb; omega), zero_add, sum_filter_range]
  unfold ev
  congr 1
  refine sum_congr rfl fun b _ => ?_
  simp

/-- A 32-bit shift's meaning on bit patterns. -/
def S32 (s : shift.Shift word.Word32) (x : ℕ) : ℕ :=
  (sem32 s.kind s.amount.val (BitVec.ofNat 32 x)).toNat

theorem S32_xor (s : shift.Shift word.Word32) (x y : ℕ) : S32 s (x ^^^ y) = S32 s x ^^^ S32 s y := by
  simp [S32, BitVec.ofNat_xor, sem32_xor, BitVec.toNat_xor]

theorem basis32 (j : ℕ) : word.Word32.Insts.P3_wordWordWord.from_low_bits ⟨BitVec.ofNat _ (2 ^ j)⟩ =
    RustM.ok ⟨BitVec.ofNat 32 (2 ^ j)⟩ := by
  simp only [word.Word32.Insts.P3_wordWordWord.from_low_bits, lift, bind_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by decide))

theorem to_u64_32 (x : word.Word32) :
    word.Word32.Insts.P3_wordWordWord.to_u64 x = RustM.ok (UScalar.cast .U64 x) := rfl

theorem cast64_val (x : word.Word32) : (UScalar.cast .U64 x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by decide)

/-- For a 32-bit shift that does not panic, the transcribed transpose is the transpose of its meaning. -/
theorem shift_transpose32 (s : shift.Shift word.Word32) (hs : ¬ panics32 s.kind s.amount.val)
    (out : List R) (hout : out.length = 32) :
    shift_transpose I32w s out = RustM.ok (transposeSpec 32 (S32 s) (wt out)) := by
  unfold shift_transpose
  simp only [shift.Shift.is_identity, bind_ok, bits32]
  split
  · rename_i h0
    have ha : s.amount.val = 0 := by simpa using congrArg UScalar.val (of_decide_eq_true h0)
    congr 1
    apply List.ext_getElem (by simp [transposeSpec, hout])
    intro j h₁ h₂
    have hj : j < 32 := by omega
    simp only [transposeSpec, List.getElem_map, List.getElem_range, S32, ha, sem32, base_zero,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj), ev_two_pow hj]
    simp [wt, List.getElem?_eq_getElem h₁]
  · unfold transposeSpec
    apply mapM_ok
    intro j hj
    rw [List.mem_range] at hj
    simp only [basis32, apply32_eq, hs, ite_false, bind_ok, to_u64_32]
    rw [setBitsSum_eq _ _ _ (by simp [hout]), cast64_val]
    rfl

/-- A 64-bit shift's meaning on bit patterns. -/
def S64 (s : shift.Shift word.Word64) (x : ℕ) : ℕ :=
  (sem64 s.kind s.amount.val (BitVec.ofNat 64 x)).toNat

theorem S64_xor (s : shift.Shift word.Word64) (x y : ℕ) : S64 s (x ^^^ y) = S64 s x ^^^ S64 s y := by
  simp [S64, BitVec.ofNat_xor, sem64_xor, BitVec.toNat_xor]

theorem lanes_id' (x : BitVec 64) : lanes (fun y => base .LogicalLeft 0 y) x = x := by
  simpa [base_zero] using lanes_id x

/-- For a 64-bit shift that does not panic, the transcribed transpose is the transpose of its meaning. -/
theorem shift_transpose64 (s : shift.Shift word.Word64) (hs : ¬ panics64 s.kind s.amount.val)
    (out : List R) (hout : out.length = 64) :
    shift_transpose I64w s out = RustM.ok (transposeSpec 64 (S64 s) (wt out)) := by
  unfold shift_transpose
  simp only [shift.Shift.is_identity, bind_ok, bits64]
  split
  · rename_i h0
    have ha : s.amount.val = 0 := by simpa using congrArg UScalar.val (of_decide_eq_true h0)
    congr 1
    apply List.ext_getElem (by simp [transposeSpec, hout])
    intro j h₁ h₂
    have hj : j < 64 := by omega
    have hsem : ∀ x : BitVec 64, sem64 s.kind 0 x = x := by
      intro x; unfold sem64; split
      · simpa [base_zero] using lanes_id x
      · exact base_zero _ x
    simp only [transposeSpec, List.getElem_map, List.getElem_range, S64, ha, hsem,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj), ev_two_pow hj]
    simp [wt, List.getElem?_eq_getElem h₁]
  · unfold transposeSpec
    apply mapM_ok
    intro j hj
    rw [List.mem_range] at hj
    simp only [word.Word64.Insts.P3_wordWordWord.from_low_bits, apply64_eq, hs, ite_false,
      bind_ok, word.Word64.Insts.P3_wordWordWord.to_u64]
    rw [setBitsSum_eq _ _ _ (by simp [hout])]
    rfl

theorem S32_lt (s : shift.Shift word.Word32) (x : ℕ) : S32 s x < 2 ^ 32 := BitVec.isLt _

theorem S64_lt (s : shift.Shift word.Word64) (x : ℕ) : S64 s x < 2 ^ 64 := BitVec.isLt _

theorem length_transposeSpec (n : ℕ) (S : ℕ → ℕ) (out : ℕ → R) :
    (transposeSpec n S out).length = n := by simp [transposeSpec]

/-- Transposing twice, the outer map first, is the transpose of the composed map. -/
theorem transpose_comp (n : ℕ) (Si So : ℕ → ℕ) (hSo : ∀ x y, So (x ^^^ y) = So x ^^^ So y)
    (hSi : ∀ x, Si x < 2 ^ n) (out : ℕ → R) :
    transposeSpec n Si (wt (transposeSpec n So out)) = transposeSpec n (So ∘ Si) out := by
  unfold transposeSpec
  refine List.map_congr_left fun j _ => ?_
  exact pair_transpose n So hSo out (hSi _)

theorem index01 {T : Type} (shifts : Array T 2#usize) {inner outer : T}
    (h : shifts.val = [inner, outer]) :
    Array.index_usize shifts 0#usize = RustM.ok inner ∧
      Array.index_usize shifts 1#usize = RustM.ok outer := by
  simp [Array.index_usize, h]

/-- The two-slot transpose at 32 bits is the transpose of the outer shift after the inner one. -/
theorem shift_weights32 (shifts : Array (shift.Shift word.Word32) 2#usize)
    {inner outer : shift.Shift word.Word32} (h : shifts.val = [inner, outer])
    (hi : ¬ panics32 inner.kind inner.amount.val) (ho : ¬ panics32 outer.kind outer.amount.val)
    (out : List R) (hout : out.length = 32) :
    shift_weights I32w shifts out =
      RustM.ok (transposeSpec 32 (S32 outer ∘ S32 inner) (wt out)) := by
  obtain ⟨h0, h1⟩ := index01 shifts h
  simp only [shift_weights, h0, h1, bind_ok, shift_transpose32 outer ho out hout,
    shift_transpose32 inner hi _ (length_transposeSpec _ _ _)]
  rw [transpose_comp 32 _ _ (S32_xor outer) (S32_lt inner)]

/-- The two-slot transpose at 64 bits is the transpose of the outer shift after the inner one. -/
theorem shift_weights64 (shifts : Array (shift.Shift word.Word64) 2#usize)
    {inner outer : shift.Shift word.Word64} (h : shifts.val = [inner, outer])
    (hi : ¬ panics64 inner.kind inner.amount.val) (ho : ¬ panics64 outer.kind outer.amount.val)
    (out : List R) (hout : out.length = 64) :
    shift_weights I64w shifts out =
      RustM.ok (transposeSpec 64 (S64 outer ∘ S64 inner) (wt out)) := by
  obtain ⟨h0, h1⟩ := index01 shifts h
  simp only [shift_weights, h0, h1, bind_ok, shift_transpose64 outer ho out hout,
    shift_transpose64 inner hi _ (length_transposeSpec _ _ _)]
  rw [transpose_comp 64 _ _ (S64_xor outer) (S64_lt inner)]

end Plonky3Lean.Proofs.WordBackend
