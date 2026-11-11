module

public import Plonky3Lean.Proofs.Blake2sAir.TransposeExtracted
public import Plonky3Lean.Proofs.Blake2sAir.Step
public import Plonky3Lean.Proofs.Blake2sAir.Trace
public import Plonky3Lean.Proofs.Air.Pack

@[expose] public section

/-!
# The packed generator of the characteristic-2 BLAKE2s AIR

The packed generator fills 64 rows at once, one per bit lane.

A 32-bit word of the 64 rows is held as 32 bit planes:

```text
    plane i   = [ bit i of lane 0, bit i of lane 1, ..., bit i of lane 63 ]
```

Every operation on planes acts on each lane as the scalar operation on the lane's word.

So, in each lane that holds an input, the packed row is the row the scalar generator fills.

The lanes past the last input stay zero.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (bitsum bitsum_lt bitsum_testBit bitF)

/-! ## Lanes of planes -/

/-- The word of lane `k` of 32 planes. -/
def laneW (p : Planes) (k : ℕ) : Word := BitVec.ofNat 32 (bitsum (fun i => (p i).getLsbD k) 32)

theorem laneW_bit (p : Planes) (k : ℕ) {i : ℕ} (hi : i < 32) : (laneW p k).getLsbD i = (p i).getLsbD k := by
  rw [laneW, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bitsum_lt _ _), bitsum_testBit]
  simp [hi]

theorem laneW_eq {p : Planes} {k : ℕ} {w : Word} (h : ∀ i < 32, (p i).getLsbD k = w.getLsbD i) : laneW p k = w :=
  BitVec.eq_of_getLsbD_eq fun i hi => by rw [laneW_bit _ _ hi, h i hi]

/-! ## The adder on planes -/

/-- The plane of the carry into bit `j`. -/
def carryP (x y : Planes) : ℕ → BitVec 64
  | 0 => 0
  | j + 1 => (x j &&& y j) ||| (carryP x y j &&& (x j ^^^ y j))

theorem carryP_lane (x y : Planes) (k : ℕ) : ∀ j ≤ 32,
    (carryP x y j).getLsbD k = BitVec.carry j (laneW x k) (laneW y k) false
  | 0, _ => by simp [carryP, BitVec.carry_zero]
  | j + 1, hj => by
    rw [carryP, BitVec.carry_succ, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and,
      BitVec.getLsbD_xor, carryP_lane x y k j (by omega), laneW_bit x k (by omega), laneW_bit y k (by omega)]
    cases (x j).getLsbD k <;> cases (y j).getLsbD k <;> cases BitVec.carry j (laneW x k) (laneW y k) false <;> rfl

theorem add_planes_fold (x y : Planes) (c : ℕ → BitVec 64) : ∀ n ≤ 31,
    (List.range n).foldl (fun (acc : Planes × (ℕ → BitVec 64) × BitVec 64) bit =>
      let (sum, carries, carry) := acc
      let half := x bit ^^^ y bit
      let sum := Function.update sum bit (half ^^^ carry)
      let carry := (x bit &&& y bit) ||| (carry &&& half)
      (sum, Function.update carries bit carry, carry)) (fun _ => 0, c, 0) =
      (fun i => if i < n then x i ^^^ y i ^^^ carryP x y i else 0,
        fun i => if i < n then carryP x y (i + 1) else c i, carryP x y n)
  | 0, _ => by simp [carryP]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, add_planes_fold x y c n (by omega), List.foldl_cons, List.foldl_nil]
    simp only [Prod.mk.injEq]
    refine ⟨funext fun i => ?_, funext fun i => ?_, by rw [carryP]⟩
    · by_cases h : i = n
      · subst h; simp
      · have : i < n + 1 ↔ i < n := by omega
        simp [Function.update, h, this]
    · by_cases h : i = n
      · subst h; simp [carryP]
      · have : i < n + 1 ↔ i < n := by omega
        simp [Function.update, h, this]

/-- In each lane, the adder on planes returns the sum of the lane words modulo `2^32`. -/
theorem add_planes_sum (x y : Planes) (c : ℕ → BitVec 64) (k : ℕ) :
    laneW (add_planes x y c).1 k = laneW x k + laneW y k := by
  apply laneW_eq
  intro i hi
  simp only [add_planes, add_planes_fold x y c 31 le_rfl]
  rw [BitVec.getLsbD_add hi, laneW_bit x k hi, laneW_bit y k hi, ← carryP_lane x y k i (by omega)]
  by_cases h : i = 31
  · subst h; simp
  · simp [Function.update, h, show i < 31 by omega]

/-- In each lane, the adder on planes returns the ripple carries into bits 1 to 31. -/
theorem add_planes_carries (x y : Planes) (c : ℕ → BitVec 64) (k : ℕ) {i : ℕ} (hi : i < 31) :
    ((add_planes x y c).2 i).getLsbD k = BitVec.carry (i + 1) (laneW x k) (laneW y k) false := by
  simp only [add_planes, add_planes_fold x y c 31 le_rfl, hi, ↓reduceIte]
  exact carryP_lane x y k (i + 1) (by omega)

/-- In each lane, the rotation on planes returns `(x ^ y) >>> n`. -/
theorem xor_rotate_right_lane (x y : Planes) {n : ℕ} (hn : n < 32) (k : ℕ) :
    laneW (xor_rotate_right x y n) k = (laneW x k ^^^ laneW y k).rotateRight n := by
  apply laneW_eq
  intro i hi
  rw [Plonky3Lean.Proofs.Sha256Air.rotr_bit _ hn hi, BitVec.getLsbD_xor,
    laneW_bit x k (Nat.mod_lt _ (by norm_num)), laneW_bit y k (Nat.mod_lt _ (by norm_num))]
  simp [xor_rotate_right]

/-! ## One G step on planes -/

/-- In lane `k`, the planes of the state hold the words of a scalar state. -/
def StRel (k : ℕ) (P : ℕ → ℕ → Planes) (S : ℕ → ℕ → Word) : Prop := ∀ r < 4, ∀ i < 4, laneW (P r i) k = S r i

variable {F : Type} [Field F] [DecidableEq F]

/-- In lane `k`, the witness planes of a G step hold the bits of a row's witness cells. -/
def GRel (k : ℕ) (P : Blake2sBinaryGCols (BitVec 64)) (W : Blake2sBinaryGCols F) : Prop :=
  (∀ i < 31, (P.add1_carries i).getLsbD k = decide (W.add1_carries i = 1)) ∧
  (∀ b < 32, (P.d1 b).getLsbD k = decide (W.d1 b = 1)) ∧
  (∀ b < 32, (P.b1 b).getLsbD k = decide (W.b1 b = 1)) ∧
  (∀ i < 31, (P.add2_carries i).getLsbD k = decide (W.add2_carries i = 1)) ∧
  (∀ b < 32, (P.d2 b).getLsbD k = decide (W.d2 b = 1)) ∧
  (∀ b < 32, (P.b2 b).getLsbD k = decide (W.b2 b = 1))

theorem bitF_one (b : Bool) : decide ((bitF b : F) = 1) = b := by
  cases b <;> simp [bitF]

theorem stRel_update {k : ℕ} {P : ℕ → ℕ → Planes} {S : ℕ → ℕ → Word} (h : StRel k P S) (r0 i0 : ℕ)
    {v : Planes} {w : Word} (hv : laneW v k = w) :
    StRel k (Function.update P r0 (Function.update (P r0) i0 v)) (Function.update S r0 (Function.update (S r0) i0 w)) := by
  intro r hr i hi
  by_cases e1 : r = r0
  · subst e1
    by_cases e2 : i = i0
    · subst e2; simpa using hv
    · simpa [Function.update, e2] using h r hr i hi
  · simpa [Function.update, e1] using h r hr i hi

theorem plane_bit {p : Planes} {k : ℕ} {w : Word} (h : laneW p k = w) {b : ℕ} (hb : b < 32) :
    (p b).getLsbD k = decide ((u32_to_bits_le w b : F) = 1) := by
  rw [Blake2sAir.u32_bits w hb, bitF_one, ← h, laneW_bit _ _ hb]

theorem carry_plane_bit {x y : Planes} {k : ℕ} {X Y : Word} (hx : laneW x k = X) (hy : laneW y k = Y)
    (c : ℕ → BitVec 64) {i : ℕ} (hi : i < 31) :
    ((add_planes x y c).2 i).getLsbD k = decide ((word_to_bits_le (carries_word X Y (X + Y)) i : F) = 1) := by
  rw [carries_bits X Y hi, bitF_one, add_planes_carries _ _ _ _ hi, hx, hy]

/-- A G step on planes is, in lane `k`, the G step on the lane's words. -/
theorem g_planes_sim {k : ℕ} {P : ℕ → ℕ → Planes} {S : ℕ → ℕ → Word} (h : StRel k P S) {slots : List ℕ}
    (hs : ∀ j < 4, slots.getD j 0 < 4) (mx my : Planes) :
    StRel k (g_planes P slots mx my).2 (g_words S slots (laneW mx k) (laneW my k)).2 ∧
      GRel k (g_planes P slots mx my).1 (generate_g (F := F) S slots (laneW mx k) (laneW my k)).1 := by
  have hA := h 0 (by norm_num) _ (hs 0 (by norm_num))
  have hB := h 1 (by norm_num) _ (hs 1 (by norm_num))
  have hC := h 2 (by norm_num) _ (hs 2 (by norm_num))
  have hD := h 3 (by norm_num) _ (hs 3 (by norm_num))
  -- The lane words of every intermediate plane.
  have e1 := add_planes_sum (P 0 (slots.getD 0 0)) (P 1 (slots.getD 1 0)) (fun _ => 0) k
  rw [hA, hB] at e1
  have e2 := add_planes_sum (add_planes (P 0 (slots.getD 0 0)) (P 1 (slots.getD 1 0)) (fun _ => 0)).1 mx
    (fun _ => 0) k
  rw [e1] at e2
  set a1 := (add_planes (add_planes (P 0 (slots.getD 0 0)) (P 1 (slots.getD 1 0)) (fun _ => 0)).1 mx
    (fun _ => 0)).1 with ha1
  have e3 := xor_rotate_right_lane (P 3 (slots.getD 3 0)) a1 (n := 16) (by norm_num) k
  rw [hD, e2] at e3
  set d1 := xor_rotate_right (P 3 (slots.getD 3 0)) a1 16 with hd1
  have e4 := add_planes_sum (P 2 (slots.getD 2 0)) d1 (fun _ => 0) k
  rw [hC, e3] at e4
  set c1 := (add_planes (P 2 (slots.getD 2 0)) d1 (fun _ => 0)).1 with hc1
  have e5 := xor_rotate_right_lane (P 1 (slots.getD 1 0)) c1 (n := 12) (by norm_num) k
  rw [hB, e4] at e5
  set b1 := xor_rotate_right (P 1 (slots.getD 1 0)) c1 12 with hb1
  have e6 := add_planes_sum a1 b1 (fun _ => 0) k
  rw [e2, e5] at e6
  have e7 := add_planes_sum (add_planes a1 b1 (fun _ => 0)).1 my (fun _ => 0) k
  rw [e6] at e7
  set a2 := (add_planes (add_planes a1 b1 (fun _ => 0)).1 my (fun _ => 0)).1 with ha2
  have e8 := xor_rotate_right_lane d1 a2 (n := 8) (by norm_num) k
  rw [e3, e7] at e8
  set d2 := xor_rotate_right d1 a2 8 with hd2
  have e9 := add_planes_sum c1 d2 (fun _ => 0) k
  rw [e4, e8] at e9
  set c2 := (add_planes c1 d2 (fun _ => 0)).1 with hc2
  have e10 := xor_rotate_right_lane b1 c2 (n := 7) (by norm_num) k
  rw [e5, e9] at e10
  set b2 := xor_rotate_right b1 c2 7 with hb2
  simp only [g_planes, g_words, generate_g, GRel]
  refine ⟨stRel_update (stRel_update (stRel_update (stRel_update h 0 _ e7) 1 _ e10) 2 _ e9) 3 _ e8,
    fun i hi => carry_plane_bit hA hB _ hi, fun b hb => plane_bit e3 hb, fun b hb => plane_bit e5 hb,
    fun i hi => carry_plane_bit e2 e5 _ hi, fun b hb => plane_bit e8 hb, fun b hb => plane_bit e10 hb⟩

/-! ## The ten rounds on planes -/

/-- One step of the packed generator's inner loop. -/
abbrev gStepP (m : ℕ → Planes) (r : ℕ)
    (acc : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)) (g : ℕ) :
    (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes) :=
  let schedule := SIGMA.getD r []
  let (cols, state) := g_planes acc.2 (G_SCHEDULE.getD g []) (m (schedule.getD (2 * g) 0))
    (m (schedule.getD (2 * g + 1) 0))
  (Function.update acc.1 r (Function.update (acc.1 r) g cols), state)

/-- One round of the packed generator's outer loop. -/
abbrev roundP (m : ℕ → Planes) (acc : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes))
    (r : ℕ) : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes) :=
  (List.range G_PER_ROUND).foldl (gStepP m r) acc

/-- In lane `k`, the packed loops' state and witness hold the scalar loops' state and witness. -/
def RR (k : ℕ) (P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes))
    (S : Blake2sBinaryCols F × (ℕ → ℕ → Word)) : Prop :=
  StRel k P.2 S.2 ∧ ∀ r < 10, ∀ g < 8, GRel k (P.1 r g) (S.1.rounds r g)

theorem gStep_sim {k : ℕ} {m : ℕ → Planes} {blk : List Word} (hm : ∀ j < 16, laneW (m j) k = blk.getD j 0)
    {r : ℕ} {P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)}
    {S : Blake2sBinaryCols F × (ℕ → ℕ → Word)} (h : RR k P S) (g : ℕ) :
    RR k (gStepP m r P g) (genStep blk r S g) := by
  obtain ⟨hst, hw⟩ := h
  have hx := hm _ (sigma_lt r (2 * g))
  have hy := hm _ (sigma_lt r (2 * g + 1))
  obtain ⟨e1, e2⟩ := g_planes_sim (F := F) hst (fun j hj => g_schedule_lt g hj)
    (m ((SIGMA.getD r []).getD (2 * g) 0)) (m ((SIGMA.getD r []).getD (2 * g + 1) 0))
  rw [hx, hy] at e1 e2
  refine ⟨e1, fun r' hr' g' hg' => ?_⟩
  simp only [genStep]
  by_cases er : r' = r
  · subst er
    by_cases eg : g' = g
    · subst eg; simpa using e2
    · simpa [Function.update, eg] using hw r' hr' g' hg'
  · simpa [Function.update, er] using hw r' hr' g' hg'

theorem rounds_sim {k : ℕ} {m : ℕ → Planes} {blk : List Word} (hm : ∀ j < 16, laneW (m j) k = blk.getD j 0)
    (n : ℕ) {P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)}
    {S : Blake2sBinaryCols F × (ℕ → ℕ → Word)} (h : RR k P S) :
    RR k ((List.range n).foldl (roundP m) P) ((List.range n).foldl (genRound blk) S) := by
  induction n generalizing P S with
  | zero => exact h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil]
    have inner : ∀ (r j : ℕ) (P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes))
        (S : Blake2sBinaryCols F × (ℕ → ℕ → Word)), RR k P S →
        RR k ((List.range j).foldl (gStepP m r) P) ((List.range j).foldl (genStep blk r) S) := by
      intro r j
      induction j with
      | zero => intro P S h; exact h
      | succ j ihj =>
        intro P S h
        rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
          List.foldl_nil, List.foldl_nil]
        exact gStep_sim hm (ihj P S h) j
    exact inner n G_PER_ROUND _ _ (ih h)

/-! ## Rows of planes and their cells -/

/-- In lane `k`, a packed row holds the bits of a row's cells. -/
def CRel (k : ℕ) (P : Blake2sBinaryCols (BitVec 64)) (S : Blake2sBinaryCols F) : Prop :=
  (∀ i < 8, ∀ b < 32, (P.chaining_value i b).getLsbD k = decide (S.chaining_value i b = 1)) ∧
  (∀ i < 16, ∀ b < 32, (P.block i b).getLsbD k = decide (S.block i b = 1)) ∧
  (∀ b < 32, (P.counter_low b).getLsbD k = decide (S.counter_low b = 1)) ∧
  (∀ b < 32, (P.counter_high b).getLsbD k = decide (S.counter_high b = 1)) ∧
  P.last_block.getLsbD k = decide (S.last_block = 1) ∧
  ∀ r < 10, ∀ g < 8, GRel k (P.rounds r g) (S.rounds r g)

theorem cells_rel {k : ℕ} {P : Blake2sBinaryCols (BitVec 64)} {S : Blake2sBinaryCols F} (h : CRel k P S) :
    P.cells.map (·.getLsbD k) = S.cells.map fun x => decide (x = 1) := by
  obtain ⟨hcv, hbl, hlo, hhi, hlast, hr⟩ := h
  simp only [Blake2sBinaryCols.cells, Blake2sBinaryCols.cellBlock, Blake2sBinaryCols.gCells, List.map_append,
    List.map_flatMap, List.map_map, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) (by rw [hlast])) ?_
  · exact List.flatMap_congr fun i hi => List.map_congr_left fun b hb =>
      hcv i (List.mem_range.mp hi) b (List.mem_range.mp hb)
  · exact List.flatMap_congr fun i hi => List.map_congr_left fun b hb =>
      hbl i (List.mem_range.mp hi) b (List.mem_range.mp hb)
  · exact List.map_congr_left fun b hb' => hlo b (List.mem_range.mp hb')
  · exact List.map_congr_left fun b hb' => hhi b (List.mem_range.mp hb')
  · refine List.flatMap_congr fun r hr' => List.flatMap_congr fun g hg => ?_
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hr r (List.mem_range.mp hr') g (List.mem_range.mp hg)
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
      (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_) ?_ <;>
      refine List.map_congr_left fun b hb' => ?_ <;> have := List.mem_range.mp hb'
    · exact g1 b this
    · exact g2 b this
    · exact g3 b this
    · exact g4 b this
    · exact g5 b this
    · exact g6 b this

/-! ## The input planes -/

/-- The input words of each lane, zero past the last input. -/
def wordsOf (inputs : List Blake2sCompressionInput) : ℕ → ℕ → Word := fun lane =>
  (inputs[lane]?.map input_words).getD fun _ => 0

/-- Input plane `c`: plane `c mod 64` of the transpose of word pair `c / 64`. -/
def inPlane (inputs : List Blake2sCompressionInput) (c : ℕ) : BitVec 64 :=
  transpose_bits (fun row => (wordsOf inputs row (2 * (c / 64))).setWidth 64 |||
    (wordsOf inputs row (2 * (c / 64) + 1)).setWidth 64 <<< 32) (c % 64)

/-- In lane `k`, input plane `c` holds bit `c mod 32` of input word `c / 32`. -/
theorem inPlane_bit (inputs : List Blake2sCompressionInput) (c : ℕ) {k : ℕ} (hk : k < 64) :
    (inPlane inputs c).getLsbD k = (wordsOf inputs k (c / 32)).getLsbD (c % 32) := by
  rw [inPlane, transpose_bit _ (Nat.mod_lt _ (by norm_num)) hk]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h : c % 64 < 32
  · have e1 : c / 32 = 2 * (c / 64) := by omega
    have e2 : c % 32 = c % 64 := by omega
    simp [h, e1, e2, show c % 64 < 64 by omega]
  · have e1 : c / 32 = 2 * (c / 64) + 1 := by omega
    have e2 : c % 32 = c % 64 - 32 := by omega
    have e3 : ¬ c % 64 < 32 := h
    simp only [e1, e2, show c % 64 < 64 by omega, decide_true, Bool.true_and, e3, decide_false,
      Bool.not_false]
    simp only [BitVec.getLsbD_of_ge _ (c % 64) (by omega : 32 ≤ c % 64), Bool.false_or,
      show c % 64 - 32 < 64 by omega, decide_true, Bool.true_and]

theorem wordsOf_lt {inputs : List Blake2sCompressionInput} {k : ℕ} (hk : k < inputs.length) :
    wordsOf inputs k = input_words inputs[k] := by
  simp [wordsOf, List.getElem?_eq_getElem hk]

theorem wordsOf_ge {inputs : List Blake2sCompressionInput} {k : ℕ} (hk : inputs.length ≤ k) :
    wordsOf inputs k = fun _ => 0 := by
  simp [wordsOf, List.getElem?_eq_none hk]

/-- The lane mask of a flag sets bit `k` when input `k` sets the flag. -/
theorem lane_mask_bit (inputs : List Blake2sCompressionInput) (f : Blake2sCompressionInput → Bool) {k : ℕ}
    (hk : k < 64) : (lane_mask inputs f).getLsbD k = (decide (k < inputs.length) && (inputs[k]?.map f).getD false) := by
  have key : ∀ (l : List Blake2sCompressionInput) (s : ℕ) (mask : BitVec 64),
      ((l.zipIdx s).foldl (fun mask (input, lane) => mask ||| (BitVec.ofBool (f input)).setWidth 64 <<< lane)
        mask).getLsbD k =
        (mask.getLsbD k || (decide (s ≤ k) && decide (k < s + l.length) && (l[k - s]?.map f).getD false)) := by
    intro l
    induction l with
    | nil => intro s mask; simp
    | cons a l ih =>
      intro s mask
      rw [List.zipIdx_cons, List.foldl_cons, ih]
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool,
        hk, decide_true, Bool.true_and, List.length_cons]
      by_cases e : k = s
      · subst e; simp
      · rcases Nat.lt_or_gt_of_ne e with h | h
        · simp [show ¬ s ≤ k by omega, show ¬ s + 1 ≤ k by omega]
        · have e2 : k - s = (k - (s + 1)) + 1 := by omega
          simp [show s ≤ k by omega, show s + 1 ≤ k by omega, e2, show ¬ k < s by omega, show (k < s + 1 + l.length) = (k < s + (l.length + 1)) by
              apply propext; omega]
  rw [lane_mask, key]
  simp

/-! ## The packed row -/

/-- The plane mask of the lanes that hold an input. -/
def lanesMask (n : ℕ) : BitVec 64 := BitVec.allOnes 64 >>> (64 - n)

/-- The planes of a constant word, set only in the lanes that hold an input. -/
def ivP (n : ℕ) (word : Word) : Planes := fun bit => if (word >>> bit) &&& 1 = 1 then lanesMask n else 0

/-- The planes of the chaining value. -/
def cvP (inputs : List Blake2sCompressionInput) (i : ℕ) : Planes := fun b => inPlane inputs (32 * i + b)

/-- The planes of the message block. -/
def mP (inputs : List Blake2sCompressionInput) (i : ℕ) : Planes := fun b => inPlane inputs (256 + 32 * i + b)

/-- The initial state planes. -/
def stateP (inputs : List Blake2sCompressionInput) : ℕ → ℕ → Planes := fun r i =>
  if r = 0 then cvP inputs i
  else if r = 1 then cvP inputs (4 + i)
  else if r = 2 then ivP inputs.length (IV.getD i 0)
  else if r = 3 then
    (if i < 3 then fun bit => ivP inputs.length (IV.getD (4 + i) 0) bit ^^^
      ([fun b => inPlane inputs (768 + b), fun b => inPlane inputs (800 + b),
        fun _ => lane_mask inputs (·.last_block)].getD i (fun _ => 0)) bit
    else ivP inputs.length (IV.getD (4 + i) 0))
  else fun _ => 0

theorem generate_block_eq (inputs : List Blake2sCompressionInput) :
    generate_block inputs =
      ⟨cvP inputs, mP inputs, fun b => inPlane inputs (768 + b), fun b => inPlane inputs (800 + b),
        lane_mask inputs (·.last_block),
        ((List.range NUM_ROUNDS).foldl (roundP (mP inputs))
          ((Blake2sBinaryCols.zero : Blake2sBinaryCols (BitVec 64)).rounds, stateP inputs)).1⟩ := by
  simp only [generate_block, Blake2sBinaryCols.mk.injEq]
  refine ⟨rfl, rfl, rfl, rfl, trivial, ?_⟩
  delta roundP gStepP mP inPlane wordsOf stateP cvP ivP lanesMask
  rfl

/-! ## The initial state -/

theorem laneW_xor (p q : Planes) (k : ℕ) : laneW (fun b => p b ^^^ q b) k = laneW p k ^^^ laneW q k :=
  laneW_eq fun i hi => by rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, laneW_bit _ _ hi, laneW_bit _ _ hi]

theorem lanesMask_bit (n : ℕ) {k : ℕ} (hk : k < 64) : (lanesMask n).getLsbD k = decide (k < n) := by
  rw [lanesMask, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  by_cases h : k < n <;> simp [h] <;> omega

theorem ivP_lane (n : ℕ) (w : Word) {k : ℕ} (hk : k < 64) : laneW (ivP n w) k = if k < n then w else 0 := by
  apply laneW_eq
  intro b hb
  simp only [ivP]
  split
  · rename_i hw
    have := (Plonky3Lean.Proofs.Sha256Air.Binary.shift_and_one w b).mp hw
    by_cases h : k < n <;> simp [lanesMask_bit n hk, h, this]
  · rename_i hw
    have : w.getLsbD b = false := by
      cases e : w.getLsbD b
      · rfl
      · exact absurd ((Plonky3Lean.Proofs.Sha256Air.Binary.shift_and_one w b).mpr e) hw
    by_cases h : k < n <;> simp [h, this]

theorem inPlane_lane (inputs : List Blake2sCompressionInput) (base : ℕ) {k : ℕ} (hk : k < 64) (i : ℕ) :
    laneW (fun b => inPlane inputs (32 * (base + i) + b)) k = wordsOf inputs k (base + i) := by
  apply laneW_eq
  intro b hb
  rw [inPlane_bit _ _ hk, show (32 * (base + i) + b) / 32 = base + i by omega,
    show (32 * (base + i) + b) % 32 = b by omega]

theorem cvP_lane (inputs : List Blake2sCompressionInput) {k : ℕ} (hk : k < 64) (i : ℕ) :
    laneW (cvP inputs i) k = wordsOf inputs k i := by
  have := inPlane_lane inputs 0 hk i
  simp only [zero_add] at this
  exact this

theorem mP_lane (inputs : List Blake2sCompressionInput) {k : ℕ} (hk : k < 64) (i : ℕ) :
    laneW (mP inputs i) k = wordsOf inputs k (8 + i) := by
  have := inPlane_lane inputs 8 hk i
  simp only [show ∀ b, 32 * (8 + i) + b = 256 + 32 * i + b by intro b; omega] at this
  exact this

theorem input_words_cv (input : Blake2sCompressionInput) {i : ℕ} (hi : i < 8) :
    input_words input i = input.chaining_value.getD i 0 := by
  simp [input_words, hi]

theorem input_words_block (input : Blake2sCompressionInput) {i : ℕ} (hi : i < 16) :
    input_words input (8 + i) = input.block.getD i 0 := by
  simp [input_words, show ¬ 8 + i < 8 by omega, show 8 + i < 24 by omega]

/-- In a lane that holds an input, the initial planes hold the scalar initial state. -/
theorem stateP_rel {inputs : List Blake2sCompressionInput} {k : ℕ} (hk : k < inputs.length)
    (hlen : inputs.length ≤ 64) : StRel k (stateP inputs) (state0 inputs[k]) := by
  have hk64 : k < 64 := by omega
  intro r hr i hi
  have hw := wordsOf_lt hk
  interval_cases r
  · simp only [stateP, ↓reduceIte, state0, cvP_lane _ hk64, hw, input_words_cv _ (show i < 8 by omega)]
  · simp only [stateP, state0, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, cvP_lane _ hk64, hw,
      input_words_cv _ (show 4 + i < 8 by omega)]
  · simp only [stateP, state0, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
      ivP_lane _ _ hk64, hk]
  · have hlo : laneW (fun b => inPlane inputs (768 + b)) k = inputs[k].counter.setWidth 32 := by
      have := inPlane_lane inputs 24 hk64 0
      simp only [add_zero, show 32 * 24 = 768 from rfl] at this
      rw [this, hw]; rfl
    have hhi : laneW (fun b => inPlane inputs (800 + b)) k = (inputs[k].counter >>> 32).setWidth 32 := by
      have := inPlane_lane inputs 25 hk64 0
      simp only [add_zero, show 32 * 25 = 800 from rfl] at this
      rw [this, hw]; rfl
    have hfl : laneW (fun _ => lane_mask inputs (·.last_block)) k = inputs[k].flag_word := by
      apply laneW_eq
      intro b hb
      rw [lane_mask_bit _ _ hk64, Blake2sCompressionInput.flag_word]
      cases e : inputs[k].last_block
      · simp [hk, e]
      · simp only [hk, e, decide_true, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some,
          Bool.true_and, ↓reduceIte]
        rw [show (-1 : Word) = BitVec.allOnes 32 by decide, BitVec.getLsbD_allOnes]
        simp [hb]
    interval_cases i <;> simp only [stateP, state0, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ↓reduceIte, laneW_xor, ivP_lane _ _ hk64, hk, List.getD_cons_zero,
      List.getD_cons_succ, hlo, hhi, hfl, show ¬ (3 : ℕ) < 3 by decide, show (0 : ℕ) < 3 by decide,
      show (1 : ℕ) < 3 by decide, show (2 : ℕ) < 3 by decide]
    simp

/-- In a lane past the last input, the initial planes are zero. -/
theorem stateP_zero {inputs : List Blake2sCompressionInput} {k : ℕ} (hk : inputs.length ≤ k) (hk64 : k < 64) :
    StRel k (stateP inputs) (fun _ _ => 0) := by
  have hw := wordsOf_ge hk
  have hin : ∀ base i, laneW (fun b => inPlane inputs (32 * (base + i) + b)) k = 0 := by
    intro base i; rw [inPlane_lane _ _ hk64, hw]
  have hlo : laneW (fun b => inPlane inputs (768 + b)) k = 0 := by simpa using hin 24 0
  have hhi : laneW (fun b => inPlane inputs (800 + b)) k = 0 := by simpa using hin 25 0
  have hfl : laneW (fun _ => lane_mask inputs (·.last_block)) k = 0 := by
    apply laneW_eq
    intro b hb
    rw [lane_mask_bit _ _ hk64]
    simp [show ¬ k < inputs.length by omega]
  have hnk : ¬ k < inputs.length := by omega
  intro r hr i hi
  interval_cases r
  · simp only [stateP, ↓reduceIte, cvP_lane _ hk64, hw]
  · simp only [stateP, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, cvP_lane _ hk64, hw]
  · simp only [stateP, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
      ivP_lane _ _ hk64, hnk]
  · interval_cases i <;> simp only [stateP, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ↓reduceIte, laneW_xor, ivP_lane _ _ hk64, hnk, List.getD_cons_zero,
      List.getD_cons_succ, hlo, hhi, hfl, show ¬ (3 : ℕ) < 3 by decide, show (0 : ℕ) < 3 by decide,
      show (1 : ℕ) < 3 by decide, show (2 : ℕ) < 3 by decide, BitVec.xor_self] <;> rfl

/-! ## The packed row of a group of inputs -/

theorem u32_one (w : Word) {b : ℕ} (hb : b < 32) : decide ((u32_to_bits_le w b : F) = 1) = w.getLsbD b := by
  rw [Blake2sAir.u32_bits w hb, bitF_one]

theorem rr_init {k : ℕ} {S : ℕ → ℕ → Word} (h : StRel k (stateP inputs) S) (row : Blake2sBinaryCols F)
    (hrow : row.rounds = (Blake2sBinaryCols.zero : Blake2sBinaryCols F).rounds) :
    RR k ((Blake2sBinaryCols.zero : Blake2sBinaryCols (BitVec 64)).rounds, stateP inputs) (row, S) := by
  refine ⟨h, fun r _ g _ => ?_⟩
  rw [hrow]
  refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_⟩ <;>
    simp [Blake2sBinaryCols.zero]

/-- In a lane that holds an input, the packed row holds the bits of the row the scalar generator fills. -/
theorem block_rel {inputs : List Blake2sCompressionInput} (hlen : inputs.length ≤ 64) {k : ℕ}
    (hk : k < inputs.length) :
    CRel k (generate_block inputs) (generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) inputs[k]) := by
  have hk64 : k < 64 := by omega
  have hw := wordsOf_lt hk
  have hm : ∀ j < 16, laneW (mP inputs j) k = inputs[k].block.getD j 0 := fun j hj => by
    rw [mP_lane _ hk64, hw, input_words_block _ hj]
  obtain ⟨_, hrw⟩ := rounds_sim (F := F) hm NUM_ROUNDS (rr_init (stateP_rel hk hlen) (inputRow inputs[k]) rfl)
  obtain ⟨⟨s1, s2, s3, s4, s5⟩, -⟩ := gen_spec (F := F) inputs[k]
  rw [generate_block_eq]
  refine ⟨fun i hi b hb => ?_, fun i hi b hb => ?_, fun b hb => ?_, fun b hb => ?_, ?_, ?_⟩
  · rw [s1]
    show _ = decide ((u32_to_bits_le (inputs[k].chaining_value.getD i 0) b : F) = 1)
    rw [u32_one _ hb]
    have := inPlane_bit inputs (32 * i + b) hk64
    rw [show (32 * i + b) / 32 = i by omega, show (32 * i + b) % 32 = b by omega, hw,
      input_words_cv _ hi] at this
    exact this
  · rw [s2]
    show _ = decide ((u32_to_bits_le (inputs[k].block.getD i 0) b : F) = 1)
    rw [u32_one _ hb]
    have := inPlane_bit inputs (256 + 32 * i + b) hk64
    rw [show (256 + 32 * i + b) / 32 = 8 + i by omega, show (256 + 32 * i + b) % 32 = b by omega, hw,
      input_words_block _ hi] at this
    exact this
  · rw [s3]
    show _ = decide ((u32_to_bits_le (inputs[k].counter.setWidth 32) b : F) = 1)
    rw [u32_one _ hb]
    have := inPlane_bit inputs (768 + b) hk64
    rw [show (768 + b) / 32 = 24 by omega, show (768 + b) % 32 = b by omega, hw] at this
    exact this
  · rw [s4]
    show _ = decide ((u32_to_bits_le ((inputs[k].counter >>> 32).setWidth 32) b : F) = 1)
    rw [u32_one _ hb]
    have := inPlane_bit inputs (800 + b) hk64
    rw [show (800 + b) / 32 = 25 by omega, show (800 + b) % 32 = b by omega, hw] at this
    exact this
  · rw [s5, lane_mask_bit _ _ hk64]
    show _ = decide ((if inputs[k].last_block then 1 else 0 : F) = 1)
    cases e : inputs[k].last_block <;> simp [hk, e]
  · rw [gen_eq]
    exact hrw

/-! ## The lanes past the last input -/

theorem g_words_zero (slots : List ℕ) :
    g_words (fun _ _ => 0) slots 0 0 = (⟨0, 0, 0, 0, 0, 0⟩, fun _ _ => 0) := by
  simp only [g_words, carries_word, Prod.mk.injEq]
  refine ⟨by simp, funext fun r => funext fun i => ?_⟩
  simp only [Function.update]
  split_ifs <;> simp_all

/-- The zero witness of a G step. -/
abbrev zeroG : Blake2sBinaryGCols F := (Blake2sBinaryCols.zero : Blake2sBinaryCols F).rounds 0 0

/-- A G step on planes with zero lanes leaves the lanes zero, and writes zero witness lanes. -/
theorem g_planes_zero {k : ℕ} {P : ℕ → ℕ → Planes} (h : StRel k P (fun _ _ => 0)) {slots : List ℕ}
    (hs : ∀ j < 4, slots.getD j 0 < 4) {mx my : Planes} (hx : laneW mx k = 0) (hy : laneW my k = 0) :
    StRel k (g_planes P slots mx my).2 (fun _ _ => 0) ∧ GRel k (g_planes P slots mx my).1 (zeroG (F := F)) := by
  obtain ⟨e1, e2⟩ := g_planes_sim (F := F) h hs mx my
  rw [hx, hy] at e1 e2
  rw [g_words_zero] at e1
  rw [generate_g_eq, g_words_zero] at e2
  refine ⟨e1, ?_⟩
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := e2
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [g1 i hi]; simp [witOf, word_to_bits_le, zeroG, Blake2sBinaryCols.zero]
  · rw [g2 i hi]; simp [witOf, u32_to_bits_le, zeroG, Blake2sBinaryCols.zero]
  · rw [g3 i hi]; simp [witOf, u32_to_bits_le, zeroG, Blake2sBinaryCols.zero]
  · rw [g4 i hi]; simp [witOf, word_to_bits_le, zeroG, Blake2sBinaryCols.zero]
  · rw [g5 i hi]; simp [witOf, u32_to_bits_le, zeroG, Blake2sBinaryCols.zero]
  · rw [g6 i hi]; simp [witOf, u32_to_bits_le, zeroG, Blake2sBinaryCols.zero]

/-- The packed loops keep a zero lane zero, state and witness. -/
theorem rounds_zero {k : ℕ} {m : ℕ → Planes} (hm : ∀ j, laneW (m j) k = 0) (n : ℕ)
    {P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)}
    (h : StRel k P.2 (fun _ _ => 0) ∧ ∀ r < 10, ∀ g < 8, GRel k (P.1 r g) (zeroG (F := F))) :
    StRel k ((List.range n).foldl (roundP m) P).2 (fun _ _ => 0) ∧
      ∀ r < 10, ∀ g < 8, GRel k (((List.range n).foldl (roundP m) P).1 r g) (zeroG (F := F)) := by
  have step : ∀ (r g : ℕ) (P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)),
      (StRel k P.2 (fun _ _ => 0) ∧ ∀ r < 10, ∀ g < 8, GRel k (P.1 r g) (zeroG (F := F))) →
      (StRel k (gStepP m r P g).2 (fun _ _ => 0) ∧
        ∀ r' < 10, ∀ g' < 8, GRel k ((gStepP m r P g).1 r' g') (zeroG (F := F))) := by
    intro r g P ⟨hst, hw⟩
    obtain ⟨e1, e2⟩ := g_planes_zero (F := F) hst (fun j hj => g_schedule_lt g hj) (hm _) (hm _)
    refine ⟨e1, fun r' hr' g' hg' => ?_⟩
    by_cases er : r' = r
    · subst er
      by_cases eg : g' = g
      · subst eg; simpa using e2
      · simpa [Function.update, eg] using hw r' hr' g' hg'
    · simpa [Function.update, er] using hw r' hr' g' hg'
  induction n generalizing P with
  | zero => exact h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have inner : ∀ (r j : ℕ) (P : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)),
        (StRel k P.2 (fun _ _ => 0) ∧ ∀ r < 10, ∀ g < 8, GRel k (P.1 r g) (zeroG (F := F))) →
        (StRel k ((List.range j).foldl (gStepP m r) P).2 (fun _ _ => 0) ∧
          ∀ r' < 10, ∀ g' < 8, GRel k (((List.range j).foldl (gStepP m r) P).1 r' g') (zeroG (F := F))) := by
      intro r j
      induction j with
      | zero => intro P h; exact h
      | succ j ihj =>
        intro P h
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact step r j _ (ihj P h)
    exact inner n G_PER_ROUND _ (ih h)

/-- In a lane past the last input, every cell of the packed row is zero. -/
theorem block_zero {inputs : List Blake2sCompressionInput} {k : ℕ} (hk : inputs.length ≤ k) (hk64 : k < 64) :
    CRel k (generate_block inputs) (Blake2sBinaryCols.zero : Blake2sBinaryCols F) := by
  have hw := wordsOf_ge hk
  have hin : ∀ c, (inPlane inputs c).getLsbD k = false := fun c => by rw [inPlane_bit _ _ hk64, hw]; simp
  have hm : ∀ j, laneW (mP inputs j) k = 0 := fun j => by rw [mP_lane _ hk64, hw]
  obtain ⟨-, hr⟩ := rounds_zero (F := F) hm NUM_ROUNDS (P := ((Blake2sBinaryCols.zero : Blake2sBinaryCols (BitVec 64)).rounds, stateP inputs))
    ⟨stateP_zero hk hk64, fun r _ g _ => ⟨fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero],
      fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero], fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero],
      fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero], fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero],
      fun _ _ => by simp [zeroG, Blake2sBinaryCols.zero]⟩⟩
  rw [generate_block_eq]
  refine ⟨fun i _ b _ => ?_, fun i _ b _ => ?_, fun b _ => ?_, fun b _ => ?_, ?_, fun r hr' g hg => ?_⟩
  · simp [cvP, hin, Blake2sBinaryCols.zero]
  · simp [mP, hin, Blake2sBinaryCols.zero]
  · simp [hin, Blake2sBinaryCols.zero]
  · simp [hin, Blake2sBinaryCols.zero]
  · rw [lane_mask_bit _ _ hk64]
    simp [Blake2sBinaryCols.zero, show ¬ k < inputs.length by omega]
  · exact hr r hr' g hg

/-! ## The packed trace -/

theorem getD_bit_of_rel {k : ℕ} {P : Blake2sBinaryCols (BitVec 64)} {S : Blake2sBinaryCols F} (h : CRel k P S)
    (j : ℕ) : (P.cells.getD j 0).getLsbD k = decide (S.cells.getD j 0 = 1) := by
  have e := congrArg (fun l => l.getD j false) (cells_rel h)
  rw [show false = (0 : BitVec 64).getLsbD k by simp, List.getD_map] at e
  rw [e, show (0 : BitVec 64).getLsbD k = decide ((0 : F) = 1) by simp, List.getD_map]

/-- Bit `k` of word `j` of a packed row: cell `j` of the row of input `k`, or zero past the last input. -/
theorem block_bit {inputs : List Blake2sCompressionInput} (hlen : inputs.length ≤ 64) (j : ℕ) {k : ℕ}
    (hk : k < 64) (d : Blake2sBinaryCols F) :
    ((generate_block inputs).cells.getD j 0).getLsbD k =
      (decide (k < inputs.length) && decide
        (((inputs.map (generate_trace_row Blake2sBinaryCols.zero)).getD k d).cells.getD j 0 = 1)) := by
  by_cases h : k < inputs.length
  · rw [getD_bit_of_rel (block_rel (F := F) hlen h),
      List.getD_eq_getElem (inputs.map (generate_trace_row Blake2sBinaryCols.zero)) d (by simpa using h),
      List.getElem_map]
    simp [h]
  · rw [getD_bit_of_rel (block_zero (F := F) (Nat.le_of_not_lt h) hk)]
    have hall : ∀ x ∈ (Blake2sBinaryCols.zero : Blake2sBinaryCols F).cells, x = 0 := by
      intro x hx
      simp only [Blake2sBinaryCols.cells, Blake2sBinaryCols.zero, Blake2sBinaryCols.cellBlock,
        Blake2sBinaryCols.gCells, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton] at hx
      aesop
    have : (Blake2sBinaryCols.zero : Blake2sBinaryCols F).cells.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases e : (Blake2sBinaryCols.zero : Blake2sBinaryCols F).cells[j]?
      · rfl
      · exact hall _ (List.mem_of_getElem? e)
    rw [this]
    simp [h]

/-- The packed generator returns the packing of the trace, and panics exactly when the trace generator does. -/
theorem packed_eq (inputs : List Blake2sCompressionInput) (e : ℕ) :
    generate_binary_trace_packed (F := F) inputs = (generate_binary_trace_rows (F := F) inputs e).map packMat := by
  rw [generate_eq]
  by_cases hc : (2 : F) = 0 ∧ inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length
  · obtain ⟨h2, hl, hp⟩ := hc
    rw [ite_eq_left ⟨h2, hl, hp⟩, Option.map_some, matOf,
      packMat_flatMap (by decide) _ _ length_cells (Blake2sBinaryCols.zero : Blake2sBinaryCols F)]
    simp only [generate_binary_trace_packed, h2, hl, hp, ne_eq, not_true_eq_false, ↓reduceIte,
      Option.pure_def, Option.some.injEq, Mat.mk.injEq, true_and,
      List.length_map, packRows]
    refine List.flatMap_congr fun w hw => ?_
    have hw' := List.mem_range.mp hw
    apply List.ext_getElem (by simp [length_cells])
    intro j h1 h2'
    rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h1]
    refine eq_wordOf fun k hk => ?_
    rw [block_bit (F := F) (by simp) j hk Blake2sBinaryCols.zero]
    simp only [List.length_take, List.length_drop]
    by_cases hr : 64 * w + k < inputs.length
    · have hk' : k < min 64 (inputs.length - 64 * w) := by omega
      simp only [hk', hr, decide_true, Bool.true_and]
      have hrow : ∀ (L : List (Blake2sBinaryCols F)) (d : Blake2sBinaryCols F),
          (List.take 64 (List.drop (64 * w) L)).getD k d = L.getD (64 * w + k) d := fun L d => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, List.getElem?_drop,
          ← List.getD_eq_getElem?_getD]
      rw [List.map_take, List.map_drop, hrow]
    · have hk' : ¬ k < min 64 (inputs.length - 64 * w) := by omega
      simp [hk', hr]
  · rw [ite_eq_right hc]
    unfold generate_binary_trace_packed
    by_cases h2 : (2 : F) = 0
    · by_cases hl : inputs.length = 0
      · simp [h2, hl]
      · have hp : ¬ 2 ^ Nat.log 2 inputs.length = inputs.length := fun hp => hc ⟨h2, hl, hp⟩
        simp [h2, hl, hp]
    · simp [h2]

/-! ## The extracted helpers are the transcribed ones -/

theorem laneWord_eq (p : Aeneas.Std.Array Aeneas.Std.U64 32#usize) (k : ℕ) :
    laneWord p k = laneW (fun i => (p.val[i]!).bv) k := rfl

/-- The extracted adder on planes returns the transcribed adder's sum and carry planes. -/
theorem add_planes_extracted (x y : Aeneas.Std.Array Aeneas.Std.U64 32#usize) (c : Aeneas.Std.Array Aeneas.Std.U64 31#usize) :
    ∃ s c', p3_blake2s_air.binary.generation.add_planes x y c = .ok (s, c') ∧
      (∀ i < 32, (s.val[i]!).bv =
        (add_planes (fun i => (x.val[i]!).bv) (fun i => (y.val[i]!).bv) (fun i => (c.val[i]!).bv)).1 i) ∧
      ∀ i < 31, (c'.val[i]!).bv =
        (add_planes (fun i => (x.val[i]!).bv) (fun i => (y.val[i]!).bv) (fun i => (c.val[i]!).bv)).2 i := by
  obtain ⟨s, c', h, hs, hc⟩ := add_planes_spec x y c
  refine ⟨s, c', h, fun i hi => BitVec.eq_of_getLsbD_eq fun k _ => ?_, fun i hi => BitVec.eq_of_getLsbD_eq fun k _ => ?_⟩
  · rw [← laneW_bit _ k hi, add_planes_sum, ← laneWord_eq, ← laneWord_eq, ← hs k, laneWord_eq, laneW_bit _ k hi]
  · rw [hc k i hi, add_planes_carries _ _ _ _ hi, laneWord_eq, laneWord_eq]

/-- The extracted rotation on planes returns the transcribed rotation's planes. -/
theorem xor_rotate_right_extracted (x y : Aeneas.Std.Array Aeneas.Std.U64 32#usize) (amount : Aeneas.Std.Usize) (ha : amount.val < 32) :
    ∃ out, p3_blake2s_air.binary.generation.xor_rotate_right x y amount = .ok out ∧
      ∀ i < 32, (out.val[i]!).bv =
        xor_rotate_right (fun i => (x.val[i]!).bv) (fun i => (y.val[i]!).bv) amount.val i := by
  obtain ⟨out, h, ho⟩ := xor_rotate_right_spec x y amount ha
  refine ⟨out, h, fun i hi => BitVec.eq_of_getLsbD_eq fun k _ => ?_⟩
  rw [← laneW_bit _ k hi, xor_rotate_right_lane _ _ ha, ← laneWord_eq, ← laneWord_eq, ← ho k, laneWord_eq,
    laneW_bit _ k hi]

end Plonky3Lean.Proofs.Blake2sAir
