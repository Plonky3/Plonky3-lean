module

public import Plonky3Lean.Proofs.Blake3Air.Round
public import Plonky3Lean.Proofs.Hash.Blake3.Round

@[expose] public section

/-!
# Soundness of the prime-field BLAKE3 AIR

Let a trace satisfy the AIR, over a field of characteristic above 3 * 2^16.

On every row, the input cells hold the bits of a chaining value, a block, a counter, a block length and flags.

The output cells then hold the bits of the 16 words the BLAKE3 compression function returns on them.

Nothing ties a row to another row, or to public values.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

/-! ## The message schedule -/

/-- After r permutations, message word i is word `permPow r i` of the original. -/
theorem permute_iter_apply {T : Type _} (f : ℕ → T) (r i : ℕ) :
    (permute^[r] f) i = f (Plonky3Lean.Proofs.Blake3.permPow r i) := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih, Plonky3Lean.Proofs.Blake3.permPow_succ']
    rfl

open Plonky3Lean.Spec.Blake3 in
theorem length_round' (s m : List (BitVec 32)) (hs : s.length = 16) : (round s m).length = 16 := by
  simp [round, length_g', hs]

open Plonky3Lean.Spec.Blake3 in
/-- Round r + 1 is a round of round r's state, with the message permuted r times. -/
theorem rounds_succ (r : ℕ) (s m : List (BitVec 32)) :
    rounds (r + 1) s m = round (rounds r s m) (Spec.Blake3.permute^[r] m) := by
  induction r generalizing s m with
  | zero => rfl
  | succ r ih =>
    rw [rounds, ih, rounds, Function.iterate_succ_apply]

open Plonky3Lean.Spec.Blake3 in
theorem length_rounds (r : ℕ) (s m : List (BitVec 32)) (hs : s.length = 16) :
    (rounds r s m).length = 16 := by
  induction r with
  | zero => exact hs
  | succ r ih => rw [rounds_succ]; exact length_round' _ _ ih

/-! ## One row -/

variable {F : Type} [Field F] [DecidableEq F]

section row

variable (loc : ℕ → F)

/-- Message word i, decoded from its bits. -/
def blockOf : List Word := (List.range 16).map fun i => decodeWord fun k => loc (col.inputs i k)

/-- The eight chaining words, decoded from their bits. -/
def cvOf : List Word :=
  (List.range 8).map fun i => decodeWord fun k => loc (col.chaining_values (i / 4) (i % 4) k)

/-- Word j of row 3 of the initial state: the counter halves, the block length and the flags. -/
def row3Of (j : ℕ) : Word := decodeWord (initial_row_3 loc j)

/-- The initial state of the compression. -/
def initOf : List Word :=
  cvOf loc ++ Plonky3Lean.Spec.Blake3.IV.take 4 ++ [row3Of loc 0, row3Of loc 1, row3Of loc 2, row3Of loc 3]

theorem length_initOf : (initOf loc).length = 16 := by simp [initOf, cvOf, Plonky3Lean.Spec.Blake3.IV]

end row

theorem rowSpec_bool {loc : ℕ → F} (h : RowSpec loc) :
    (∀ i < 16, ∀ k < 32, loc (col.inputs i k) * (loc (col.inputs i k) - 1) = 0) ∧
    (∀ hh < 2, ∀ j < 4, ∀ k < 32,
      loc (col.chaining_values hh j k) * (loc (col.chaining_values hh j k) - 1) = 0) ∧
    (∀ j < 4, ∀ k < 32, initial_row_3 loc j k * (initial_row_3 loc j k - 1) = 0) := by
  have hb := h.inputs
  simp only [List.mem_append, List.mem_map, List.mem_range] at hb
  refine ⟨fun i hi k hk => hb _ (.inl (.inl (.inl ⟨i, hi, rfl⟩))) k hk, fun hh hhh j hj k hk => ?_,
    fun j hj k hk => hb _ (.inr ⟨j, hj, rfl⟩) k hk⟩
  interval_cases hh
  · exact hb _ (.inl (.inl (.inr ⟨j, hj, rfl⟩))) k hk
  · exact hb _ (.inl (.inr ⟨j, hj, rfl⟩)) k hk

/-- Limb cells equal to the packing of bit cells hold the word the bits decode to. -/
theorem limbsRep_of_pack {bits a : ℕ → F} (hb : ∀ k < 32, bits k * (bits k - 1) = 0)
    (h0 : low16 fieldOps bits - a 0 = 0) (h1 : high16 fieldOps bits - a 1 = 0) :
    LimbsRep a (decodeWord bits) := by
  have hL := limbsRep_limbs (bitsRep_decode hb)
  exact ⟨(sub_eq_zero.mp h0).symm.trans hL.1, (sub_eq_zero.mp h1).symm.trans hL.2⟩

theorem iv_limbs : ∀ j < 4, (Plonky3Lean.Spec.Blake3.IV.getD j 0).toNat % 2 ^ 16 = ivHalf j 0 ∧
    (Plonky3Lean.Spec.Blake3.IV.getD j 0).toNat / 2 ^ 16 = ivHalf j 1 := by decide

section initOf

variable (loc : ℕ → F) {j : ℕ} (hj : j < 4)
include hj

theorem initOf_cv {h : ℕ} (hh : h < 2) :
    (initOf loc).getD (4 * h + j) 0 = decodeWord fun k => loc (col.chaining_values h j k) := by
  rw [initOf, List.append_assoc, List.getD_append _ _ _ _ (by simp [cvOf]; omega), cvOf,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show (4 * h + j) / 4 = h by omega, show (4 * h + j) % 4 = j by omega]

theorem initOf_iv : (initOf loc).getD (8 + j) 0 = Plonky3Lean.Spec.Blake3.IV.getD j 0 := by
  rw [initOf, List.append_assoc, List.getD_append_right _ _ _ _ (by simp [cvOf])]
  simp only [cvOf, List.length_map, List.length_range]
  rw [List.getD_append _ _ _ _ (by simp [Plonky3Lean.Spec.Blake3.IV]; omega)]
  interval_cases j <;> rfl

theorem initOf_row3 : (initOf loc).getD (12 + j) 0 = row3Of loc j := by
  rw [initOf, List.append_assoc, List.getD_append_right _ _ _ _ (by simp [cvOf]; omega)]
  simp only [cvOf, List.length_map, List.length_range]
  rw [List.getD_append_right _ _ _ _ (by simp [Plonky3Lean.Spec.Blake3.IV]; omega)]
  interval_cases j <;> rfl

end initOf

/-- The initial state's cells hold the state the input cells and the IV give. -/
theorem init_rep {loc : ℕ → F} (h : RowSpec loc) :
    Rep (initial_state loc) (fun i => (initOf loc).getD i 0) := by
  obtain ⟨_, hcv, h3⟩ := rowSpec_bool h
  intro j hj
  have hr0 := h.row0 j (List.mem_range.mpr hj)
  have hr2 := h.row2 j (List.mem_range.mpr hj)
  obtain ⟨hiv0, hiv1⟩ := iv_limbs j hj
  refine ⟨?_, ?_, ?_, ?_⟩ <;> beta_reduce
  · have := initOf_cv loc hj (h := 0) (by norm_num)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [this]
    exact limbsRep_of_pack (a := fun l => loc (col.initial_row0 j l)) (hcv 0 (by norm_num) j hj) hr0.1
      hr0.2
  · have := initOf_cv loc hj (h := 1) (by norm_num)
    rw [Nat.mul_one] at this
    rw [this]
    exact bitsRep_decode (hcv 1 (by norm_num) j hj)
  · rw [initOf_iv loc hj]
    exact ⟨(sub_eq_zero.mp hr2.1).trans (by rw [hiv0]), (sub_eq_zero.mp hr2.2).trans (by rw [hiv1])⟩
  · rw [initOf_row3 loc hj]
    exact bitsRep_decode (h3 j hj)

theorem blockOf_getD (loc : ℕ → F) {i : ℕ} (hi : i < 16) :
    (blockOf loc).getD i 0 = decodeWord fun k => loc (col.inputs i k) := by
  simp [blockOf, List.getD_eq_getElem?_getD, hi]

theorem length_blockOf (loc : ℕ → F) : (blockOf loc).length = 16 := by simp [blockOf]

/-- Output cells equal to the xor of two bit words hold the xor of the words. -/
theorem bitsRep_xor {o x y : ℕ → F} {wx wy : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (h : ∀ k ∈ List.range 32, o k - p3_keccak_air.mirror.xor fieldOps (x k) (y k) = 0) :
    BitsRep o (wx ^^^ wy) := by
  intro k hk
  rw [sub_eq_zero.mp (h k (List.mem_range.mpr hk)), hx k hk, hy k hk, xor_bit, BitVec.getLsbD_xor]

open Plonky3Lean.Spec.Blake3 in
/-- Output word p of the compression.

It is the xor of the two halves of the final state, then of its second half and the chaining value. -/
theorem compress_getD (cv block : List (BitVec 32)) (counter : ℕ) (bl fl : BitVec 32) {p : ℕ}
    (hp : p < 16) :
    (compress cv block counter bl fl).getD p 0 =
      let s := rounds 7 (cv ++ Plonky3Lean.Spec.Blake3.IV.take 4 ++
        [BitVec.ofNat 32 counter, BitVec.ofNat 32 (counter / 2 ^ 32), bl, fl]) block
      if p < 8 then s.getD p 0 ^^^ s.getD (p + 8) 0 else s.getD p 0 ^^^ cv.getD (p - 8) 0 := by
  simp only [compress]
  split_ifs with h8
  · rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, h8]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show p - 8 < 8 by omega), Option.map_some, Option.getD_some]
    rw [show p - 8 + 8 = p by omega]

theorem rotateLeft_zero' (w : Word) : w.rotateLeft 0 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotateLeft' w (by norm_num) hi]
  congr 1; omega

theorem counter_words (lo hi : Word) :
    BitVec.ofNat 32 (lo.toNat + 2 ^ 32 * hi.toNat) = lo ∧
      BitVec.ofNat 32 ((lo.toNat + 2 ^ 32 * hi.toNat) / 2 ^ 32) = hi := by
  have := lo.isLt
  have := hi.isLt
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega

variable (hp : 3 * 2 ^ 16 < ringChar F)
include hp

/-- The input of round r holds the state after r rounds of the specification. -/
theorem rounds_rep {loc : ℕ → F} (h : RowSpec loc) :
    ∀ r ≤ 7, Rep (round_input loc r)
      (fun i => (Plonky3Lean.Spec.Blake3.rounds r (initOf loc) (blockOf loc)).getD i 0) := by
  obtain ⟨hin, _, _⟩ := rowSpec_bool h
  intro r hr
  induction r with
  | zero => exact init_rep h
  | succ r ih =>
    have hround := h.rounds r (List.mem_range.mpr (by omega))
    have hm : MRep (permute^[r] fun i => limbs fun k => loc (col.inputs i k))
        (fun i => (Plonky3Lean.Spec.Blake3.permute^[r] (blockOf loc)).getD i 0) := by
      intro i hi
      have hpi := Plonky3Lean.Proofs.Blake3.permPow_lt r i hi
      beta_reduce
      rw [permute_iter_apply, Plonky3Lean.Proofs.Blake3.permute_iter_getD _ _ _ hi, blockOf_getD _ hpi]
      exact limbsRep_limbs (bitsRep_decode (hin _ hpi))
    have := (round_sound hp (ih (by omega)) hm hround.1 hround.2).2
    have e : roundF (fun i => (Plonky3Lean.Spec.Blake3.rounds r (initOf loc) (blockOf loc)).getD i 0)
        (fun i => (Plonky3Lean.Spec.Blake3.permute^[r] (blockOf loc)).getD i 0) =
        fun i => (Plonky3Lean.Spec.Blake3.rounds (r + 1) (initOf loc) (blockOf loc)).getD i 0 := by
      funext i
      rw [rounds_succ, round_getD _ _ (length_rounds _ _ _ (length_initOf loc))]
    rw [e] at this
    simpa [round_input] using this

omit hp in
theorem decodeWord_congr {f g : ℕ → F} (h : ∀ k < 32, f k = g k) : decodeWord f = decodeWord g := by
  unfold decodeWord
  rw [bitsum_congr (g' := fun k => decide (g k = 1)) fun k hk => by rw [h k hk]]

/-- On a row whose constraints hold, the output cells hold the compression of the words the input cells hold. -/
theorem row_sound {loc : ℕ → F} (h : RowSpec loc) : ∀ q < 4, ∀ j < 4,
    BitsRep (fun k => loc (col.outputs q j k))
      ((Plonky3Lean.Spec.Blake3.compress (cvOf loc) (blockOf loc)
        ((row3Of loc 0).toNat + 2 ^ 32 * (row3Of loc 1).toNat) (row3Of loc 2) (row3Of loc 3)).getD
        (4 * q + j) 0) := by
  obtain ⟨_, hcv, _⟩ := rowSpec_bool h
  have hfin := rounds_rep hp h 7 le_rfl
  have hinit : cvOf loc ++ Plonky3Lean.Spec.Blake3.IV.take 4 ++
      [BitVec.ofNat 32 ((row3Of loc 0).toNat + 2 ^ 32 * (row3Of loc 1).toNat),
        BitVec.ofNat 32 (((row3Of loc 0).toNat + 2 ^ 32 * (row3Of loc 1).toNat) / 2 ^ 32),
        row3Of loc 2, row3Of loc 3] = initOf loc := by
    rw [(counter_words _ _).1, (counter_words _ _).2]; rfl
  simp only [round_input, OfNat.ofNat_ne_zero, ite_false, Nat.add_one_sub_one] at hfin
  intro q hq j hj
  rw [compress_getD _ _ _ _ _ (by omega)]
  dsimp only
  rw [hinit]
  obtain ⟨h0, h1, h2, h3⟩ := hfin j hj
  beta_reduce at h0 h1 h2 h3
  have hcv0 := bitsRep_decode (hcv 0 (by norm_num) j hj)
  have hcv1 := bitsRep_decode (hcv 1 (by norm_num) j hj)
  have hc0 : (cvOf loc).getD j 0 = decodeWord fun k => loc (col.chaining_values 0 j k) := by
    have := initOf_cv loc hj (h := 0) (by norm_num)
    rw [Nat.mul_zero, Nat.zero_add, initOf, List.append_assoc,
      List.getD_append _ _ _ _ (by simp [cvOf]; omega)] at this
    exact this
  have hc1 : (cvOf loc).getD (4 + j) 0 = decodeWord fun k => loc (col.chaining_values 1 j k) := by
    have := initOf_cv loc hj (h := 1) (by norm_num)
    rw [Nat.mul_one, initOf, List.append_assoc,
      List.getD_append _ _ _ _ (by simp [cvOf]; omega)] at this
    exact this
  -- The helpers hold row 2 of the final state.
  obtain ⟨hhb, -, -⟩ := h.output_row0 j (List.mem_range.mpr hj)
  have hhelp := h.helpers j (List.mem_range.mpr hj)
  have hw := LimbsRep.unique hp (limbsRep_of_pack hhb hhelp.1 hhelp.2) h2
  have hH : BitsRep (fun k => loc (col.final_round_helpers j k))
      ((Plonky3Lean.Spec.Blake3.rounds 7 (initOf loc) (blockOf loc)).getD (8 + j) 0) := hw ▸ bitsRep_decode hhb
  interval_cases q
  · -- Row 0 of the final state is the first output word xor the helper word.
    have hob := fun k (hk : k < 32) => h.outputs_bool j (List.mem_range.mpr hj) k (List.mem_range.mpr hk)
    have ho := bitsRep_decode hob
    obtain ⟨wc, hwc, hl⟩ := xorC_sound (by norm_num) ho (h.output_row0 j (List.mem_range.mpr hj))
    rw [BitsRep.unique hwc hH, rotateLeft_zero'] at hl
    have e := LimbsRep.unique hp hl h0
    rw [show 4 * 0 + j = j by omega, ite_eq_left_of_eq_true _ _ (eq_true (by omega : j < 8)), show j + 8 = 8 + j by omega, ← e,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact ho
  · rw [show 4 * 1 + j = 4 + j by omega, ite_eq_left_of_eq_true _ _ (eq_true (by omega : 4 + j < 8)), show 4 + j + 8 = 12 + j by omega]
    exact bitsRep_xor h1 h3 (h.output1 j (List.mem_range.mpr hj))
  · rw [show 4 * 2 + j = 8 + j by omega, ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ 8 + j < 8)), show 8 + j - 8 = j by omega, hc0]
    rw [BitVec.xor_comm]
    exact bitsRep_xor hcv0 hH (h.output2 j (List.mem_range.mpr hj))
  · rw [show 4 * 3 + j = 12 + j by omega, ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ 12 + j < 8)),
      show 12 + j - 8 = 4 + j by omega, hc1]
    rw [BitVec.xor_comm]
    exact bitsRep_xor hcv1 h3 (h.output3 j (List.mem_range.mpr hj))

/-! ## A trace -/

omit hp in
/-- Row i of a trace, as the row builder reads it: 0 past the AIR's width. -/
def cur (T : Instance F) (i : ℕ) : ℕ → F := rowOf (rowEnv T i) (AirLayout.from_air (blake3Air (F := F))) 0

omit hp in
theorem cur_eq (T : Instance F) (i : ℕ) {c : ℕ} (hc : c < NUM_BLAKE3_COLS) : cur T i c = T.main i c := by
  simp [cur, rowOf, AirLayout.from_air, blake3Air, hc, rowEnv]

omit hp in
theorem rowSpec_of_satisfies {T : Instance F} (hT : Satisfies (constraints blake3Air) T) {i : ℕ}
    (hi : i < T.height) : RowSpec (cur T i) :=
  (eval_iff _ _).mp ((satisfies_iff_rows blake3Air T).mp hT i hi)

omit hp in
theorem bitsRep_congr {f g : ℕ → F} {w : Word} (h : ∀ k < 32, f k = g k) (hf : BitsRep f w) :
    BitsRep g w := fun k hk => (h k hk).symm.trans (hf k hk)

section curEq

variable (T : Instance F) (i : ℕ)

omit hp

theorem blockOf_cur : blockOf (cur T i) = blockOf (T.main i) :=
  List.map_congr_left fun j hj => decodeWord_congr fun k hk => cur_eq T i (by
    simp only [List.mem_range] at hj; simp only [col.inputs, NUM_BLAKE3_COLS]; omega)

theorem cvOf_cur : cvOf (cur T i) = cvOf (T.main i) :=
  List.map_congr_left fun j hj => decodeWord_congr fun k hk => cur_eq T i (by
    simp only [List.mem_range] at hj; simp only [col.chaining_values, NUM_BLAKE3_COLS]; omega)

theorem row3Of_cur {j : ℕ} (hj : j < 4) : row3Of (cur T i) j = row3Of (T.main i) j :=
  decodeWord_congr fun k hk => cur_eq T i (by simp only [col.counter_low, NUM_BLAKE3_COLS]; omega)

end curEq

/-- Soundness on every row of a satisfying trace.

- The input cells hold the bits of a block, a chaining value, a counter, a block length and flags.
- The output cells hold the bits of their compression. -/
theorem trace_sound {T : Instance F} (hT : Satisfies (constraints blake3Air) T) {i : ℕ}
    (hi : i < T.height) :
    (∀ j < 16, BitsRep (fun k => T.main i (col.inputs j k)) ((blockOf (T.main i)).getD j 0)) ∧
    (∀ hh < 2, ∀ j < 4, BitsRep (fun k => T.main i (col.chaining_values hh j k))
      ((cvOf (T.main i)).getD (4 * hh + j) 0)) ∧
    (∀ j < 4, BitsRep (fun k => T.main i (col.counter_low (32 * j + k))) (row3Of (T.main i) j)) ∧
    ∀ q < 4, ∀ j < 4, BitsRep (fun k => T.main i (col.outputs q j k))
      ((Plonky3Lean.Spec.Blake3.compress (cvOf (T.main i)) (blockOf (T.main i))
        ((row3Of (T.main i) 0).toNat + 2 ^ 32 * (row3Of (T.main i) 1).toNat) (row3Of (T.main i) 2)
        (row3Of (T.main i) 3)).getD (4 * q + j) 0) := by
  have h := rowSpec_of_satisfies hT hi
  obtain ⟨hin, hcv, h3⟩ := rowSpec_bool h
  have hout := row_sound hp h
  rw [blockOf_cur, cvOf_cur, row3Of_cur T i (by norm_num : 0 < 4), row3Of_cur T i (by norm_num : 1 < 4),
    row3Of_cur T i (by norm_num : 2 < 4), row3Of_cur T i (by norm_num : 3 < 4)] at hout
  refine ⟨fun j hj => ?_, fun hh hhh j hj => ?_, fun j hj => ?_, fun q hq j hj => ?_⟩
  · rw [← blockOf_cur, blockOf_getD _ hj]
    exact bitsRep_congr (fun k hk => cur_eq T i (by simp only [col.inputs, NUM_BLAKE3_COLS]; omega))
      (bitsRep_decode (hin j hj))
  · have e := initOf_cv (cur T i) hj hhh
    rw [initOf, List.append_assoc, List.getD_append _ _ _ _ (by simp [cvOf]; omega), cvOf_cur] at e
    rw [e]
    exact bitsRep_congr (fun k hk => cur_eq T i (by simp only [col.chaining_values, NUM_BLAKE3_COLS]; omega))
      (bitsRep_decode (hcv hh hhh j hj))
  · rw [← row3Of_cur T i hj]
    exact bitsRep_congr (fun k hk => cur_eq T i (by simp only [col.counter_low, NUM_BLAKE3_COLS]; omega))
      (bitsRep_decode (h3 j hj))
  · exact bitsRep_congr (fun k hk => cur_eq T i (by simp only [col.outputs, NUM_BLAKE3_COLS]; omega))
      (hout q hq j hj)

end Plonky3Lean.Proofs.Blake3Air
