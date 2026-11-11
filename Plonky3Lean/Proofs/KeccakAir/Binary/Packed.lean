module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Complete
public import Plonky3Lean.Proofs.Air.Pack

@[expose] public section

/-!
# The packed generator of the characteristic-2 Keccak-f AIR

The packed generator stores 64 rows of the trace in each of its rows, one per bit.

For each block of 64 rows, it regenerates the permutations that overlap the block.

It then sets one bit per 1 cell of each row of the block, and marks the padding rows.

So the packed trace is the packing of the trace, and both panic on the same inputs.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.air.mirror p3_keccak_air.mirror p3_keccak_air.mirror.binary Plonky3Lean.Proofs.Air

variable {F : Type} [Field F]

/-! ## Setting bits -/

theorem update_or_bit (block : ℕ → BitVec 64) (c : ℕ) (m : BitVec 64) (c' k : ℕ) :
    (Function.update block c (block c ||| m) c').getLsbD k =
      ((block c').getLsbD k || (decide (c' = c) && m.getLsbD k)) := by
  by_cases h : c' = c
  · subst h; simp
  · simp [Function.update, h]

theorem shift_one_bit (s k : ℕ) : (1#64 <<< s).getLsbD k = (decide (k < 64) && decide (k = s)) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hk : k < 64 <;> by_cases hl : k = s <;> simp [hk, hl]
  omega

/-- Setting bit `v i` of column `base + i`, for `i < n`. -/
theorem range_or_bit (base n : ℕ) (v : ℕ → BitVec 64) (block : ℕ → BitVec 64) (c k : ℕ) :
    (((List.range n).foldl (fun block i =>
      Function.update block (base + i) (block (base + i) ||| v i)) block) c).getLsbD k =
      ((block c).getLsbD k || (decide (base ≤ c) && decide (c < base + n) && (v (c - base)).getLsbD k)) := by
  induction n generalizing c with
  | zero => simp; omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, update_or_bit, ih]
    by_cases h : c = base + n
    · subst h; simp
    · have : (c < base + (n + 1)) ↔ c < base + n := by omega
      simp [h, this]

theorem lane_bit (x : BitVec 64) (i s k : ℕ) :
    (((x >>> i) &&& 1) <<< s).getLsbD k = (decide (k < 64) && decide (k = s) && x.getLsbD i) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hk : k < 64
  · by_cases hl : k = s
    · subst hl; simp [hk]
    · by_cases hlt : k < s
      · simp [hk, hl, hlt]
      · have h0 : k - s ≠ 0 := by omega
        simp [hk, hl, hlt, BitVec.getLsbD_one, h0]
  · simp [hk]

theorem trailing_zeros_shift : ∀ m < 25, trailing_zeros (1#32 <<< m) = m := by decide

/-- Cell `c` of a row with kind `m` and state `S` is 1. -/
def rowSpec (m : ℕ) (S : LState) (c : ℕ) : Bool :=
  if c < 25 then decide (c = m) else decide (c < 1625) && (S ((c - 25) / 64)).getLsbD ((c - 25) % 64)

/-- The lanes of a row set bit `s` of the columns of its 1 state cells. -/
theorem lanes_or_bit (S : LState) (s : ℕ) (n : ℕ) (block : ℕ → BitVec 64) (c k : ℕ) :
    (((List.range n).foldl (fun block lane =>
      (List.range 64).foldl (fun block index =>
        Function.update block (25 + 64 * lane + index)
          (block (25 + 64 * lane + index) ||| ((S lane >>> index) &&& 1) <<< s))
        block) block) c).getLsbD k =
      ((block c).getLsbD k || (decide (25 ≤ c) && decide (c < 25 + 64 * n) && decide (k < 64) &&
        decide (k = s) && (S ((c - 25) / 64)).getLsbD ((c - 25) % 64))) := by
  induction n generalizing c with
  | zero => simp; omega
  | succ n ih =>
    rw [List.range_succ (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [range_or_bit, ih, lane_bit]
    by_cases h1 : 25 + 64 * n ≤ c ∧ c < 25 + 64 * n + 64
    · have e1 : (c - 25) / 64 = n := by omega
      have e2 : (c - 25) % 64 = c - (25 + 64 * n) := by omega
      simp [h1, e1, e2, show 25 ≤ c by omega, show c < 25 + 64 * (n + 1) by omega,
        show ¬ c < 25 + 64 * n by omega]
    · have : (c < 25 + 64 * (n + 1)) ↔ c < 25 + 64 * n := by omega
      simp only [this]
      rcases not_and_or.mp h1 with h | h <;> simp [h]

/-- Packing a row sets bit `s` exactly in the columns of its 1 cells. -/
theorem pack_row_bit (block : ℕ → BitVec 64) {m : ℕ} (hm : m < 25) (S : LState) (s c k : ℕ) :
    ((pack_row block ⟨1#32 <<< m, S⟩ s) c).getLsbD k =
      ((block c).getLsbD k || (decide (k < 64) && decide (k = s) && rowSpec m S c)) := by
  simp only [pack_row, trailing_zeros_shift m hm, KECCAK_BINARY_ROWS_PER_PERM]
  rw [lanes_or_bit, update_or_bit, shift_one_bit]
  unfold rowSpec
  by_cases hc : c < 25
  · simp only [hc, show ¬ 25 ≤ c by omega, ↓reduceIte, decide_false, Bool.false_and, Bool.or_false]
    by_cases a : c = m <;> simp [a, Bool.and_comm]
  · have hcm : c ≠ m := by omega
    simp only [hc, hcm, show 25 ≤ c by omega, ↓reduceIte, decide_false, Bool.false_and, Bool.or_false,
      decide_true, Bool.true_and]
    by_cases a : c < 1625 <;> simp [a, Bool.and_assoc]

/-! ## The words of one permutation -/

theorem perm_words_fold (rows : ℕ → RowWords) (input : LState) (n : ℕ) :
    ((List.range n).foldl (fun (acc : (ℕ → RowWords) × LState) round =>
      let (rows, state) := acc
      (Function.update rows round ⟨1#32 <<< round, state⟩, keccak_round state round)) (rows, input)) =
      (fun m => if m < n then ⟨1#32 <<< m, stateAtB input m⟩ else rows m, stateAtB input n) := by
  induction n with
  | zero => simp [stateAtB]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    simp only [Prod.mk.injEq]
    refine ⟨funext fun m => ?_, by simp [stateAtB, List.range_succ]⟩
    by_cases h : m = n
    · subst h; simp
    · have : m < n + 1 ↔ m < n := by omega
      simp [Function.update, h, this]

/-- Row `m` of a regenerated permutation has kind `m` and the state after `m` rounds. -/
theorem perm_words (rows : ℕ → RowWords) (input : LState) {m : ℕ} (hm : m < 25) :
    generate_perm_words rows input m = ⟨1#32 <<< m, stateAtB input m⟩ := by
  simp only [generate_perm_words, NUM_ROUNDS, perm_words_fold]
  by_cases h : m = 24
  · subst h; simp
  · simp [Function.update, h, show m < 24 by omega]

/-- Two sets of bits, each read off its own row, merge into one set read off a common row. -/
theorem or_combine {A X Y Z : Bool} {H T G : Prop} [Decidable H] [Decidable T] [Decidable G]
    (hX : H → X = Z) (hY : T → Y = Z) (hG : G ↔ H ∨ T) :
    ((A || (decide H && X)) || (decide T && Y)) = (A || (decide G && Z)) := by
  by_cases hH : H <;> by_cases hT : T
  · simp [hH, hT, hG.mpr (Or.inl hH), hX hH, hY hT]
  · simp [hH, hT, hG.mpr (Or.inl hH), hX hH]
  · simp [hH, hT, hG.mpr (Or.inr hT), hY hT]
  · have : ¬ G := fun h => (hG.mp h).elim hH hT
    simp [hH, hT, this]

theorem pack_row_bit' (block : ℕ → BitVec 64) {m : ℕ} (hm : m < 25) (S : LState) (s c k : ℕ) :
    ((pack_row block ⟨1#32 <<< m, S⟩ s) c).getLsbD k =
      ((block c).getLsbD k || (decide (k < 64 ∧ k = s) && rowSpec m S c)) := by
  rw [pack_row_bit _ hm, Bool.decide_and]

/-- Packing rows `start` to `start + len - 1` of a permutation that starts at row `ps`. -/
theorem perm_rows_bit (block : ℕ → BitVec 64) (R : ℕ → RowWords) (input : LState)
    (hR : ∀ m < 25, R m = ⟨1#32 <<< m, stateAtB input m⟩) {bs ps start : ℕ} (hb : bs ≤ start)
    (hp : ps ≤ start) (len : ℕ) (hlen : start + len ≤ ps + 25) (c k : ℕ) :
    (((List.range' start len).foldl (fun block row => pack_row block (R (row - ps)) (row - bs)) block) c).getLsbD k =
      ((block c).getLsbD k || (decide (k < 64 ∧ start ≤ bs + k ∧ bs + k < start + len) &&
        rowSpec (bs + k - ps) (stateAtB input (bs + k - ps)) c)) := by
  induction len with
  | zero => simp; omega
  | succ len ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      hR _ (by omega), pack_row_bit' _ (by omega), ih (by omega)]
    exact or_combine (fun _ => rfl) (fun h => by rw [show start + 1 * len - ps = bs + k - ps by omega]) (by omega)

/-! ## One block -/

/-- Cell `c` of row `r` of a permutation row of the trace is 1. -/
def permBit (inputs : List LState) (r c : ℕ) : Bool :=
  rowSpec (r % 25) (stateAtB (inputOfB inputs (r / 25)) (r % 25)) c

/-- The block's step on one permutation: regenerate it, then pack its rows inside the block. -/
abbrev permStep (bs fp pre : ℕ) (acc : (ℕ → BitVec 64) × (ℕ → RowWords)) (x : LState × ℕ) :
    (ℕ → BitVec 64) × (ℕ → RowWords) :=
  let rows := generate_perm_words acc.2 x.1
  let perm_start := (fp + x.2) * KECCAK_BINARY_ROWS_PER_PERM
  let start := max bs perm_start
  let stop := min pre (perm_start + KECCAK_BINARY_ROWS_PER_PERM)
  ((List.range' start (stop - start)).foldl
    (fun block row => pack_row block (rows (row - perm_start)) (row - bs)) acc.1, rows)

/-- The permutations from offset `s` on pack the rows from permutation `fp + s` up to row `pre`. -/
theorem perms_fold (inputs : List LState) (bs fp pre : ℕ) (l : List LState) (s : ℕ)
    (hl : ∀ i < l.length, l.getD i (fun _ => 0) = inputOfB inputs (fp + s + i)) (hbs : bs < 25 * (fp + 1))
    (block : ℕ → BitVec 64) (rows : ℕ → RowWords) (c k : ℕ) :
    (((l.zipIdx s).foldl (permStep bs fp pre) (block, rows)).1 c).getLsbD k =
      ((block c).getLsbD k || (decide (k < 64 ∧ 25 * (fp + s) ≤ bs + k ∧
        bs + k < pre ∧ bs + k < 25 * (fp + s + l.length)) && permBit inputs (bs + k) c)) := by
  induction l generalizing s block rows with
  | nil => simp; omega
  | cons a l ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih (s + 1) (fun i hi => by
      rw [show fp + (s + 1) + i = fp + s + (i + 1) by omega, ← hl (i + 1) (by simp; omega)]; rfl)]
    have ha : a = inputOfB inputs (fp + s) := by simpa using hl 0 (by simp)
    simp only [KECCAK_BINARY_ROWS_PER_PERM]
    rw [perm_rows_bit _ _ a (fun m hm => perm_words _ _ hm) (le_max_left _ _) (le_max_right _ _) _
      (by omega)]
    refine or_combine (fun h => ?_) (fun _ => rfl) (by simp only [List.length_cons]; omega)
    rw [permBit, show (bs + k) / 25 = fp + s by omega, ← ha, show bs + k - (fp + s) * 25 = (bs + k) % 25 by omega]

theorem pad_bit (block : ℕ → BitVec 64) {bs ps : ℕ} (hb : bs ≤ ps) (len c k : ℕ) :
    (((List.range' ps len).foldl (fun block row =>
      Function.update block OUTPUT_FLAG_COLUMN (block OUTPUT_FLAG_COLUMN ||| 1#64 <<< (row - bs))) block) c).getLsbD k =
      ((block c).getLsbD k || decide (c = 24 ∧ k < 64 ∧ ps ≤ bs + k ∧ bs + k < ps + len)) := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, update_or_bit, ih,
      shift_one_bit]
    simp only [OUTPUT_FLAG_COLUMN, NUM_ROUNDS, Nat.one_mul]
    cases (block c).getLsbD k
    · rw [Bool.eq_iff_iff]
      simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hc : c = 24 <;> simp [hc]
      omega
    · simp

/-- Cell `c` of row `r` of the trace is 1: a permutation row, or a padding row with only its output flag set. -/
def traceBit (inputs : List LState) (r c : ℕ) : Bool :=
  if r < inputs.length * 25 then permBit inputs r c else decide (c = 24)

/-- Bit `k` of column `c` of block `b` says whether cell `c` of row `64 b + k` is 1. -/
theorem pack_block_bit (inputs : List LState) (b num_rows : ℕ) (hb : 64 * b < num_rows)
    (hn : inputs.length * 25 ≤ num_rows) (rows : ℕ → RowWords) (c k : ℕ) :
    ((pack_block (fun _ => 0) b inputs num_rows rows).1 c).getLsbD k =
      (decide (k < 64 ∧ 64 * b + k < num_rows) && traceBit inputs (64 * b + k) c) := by
  unfold pack_block
  rw [show BITS_PER_WORD = 64 from rfl, show KECCAK_BINARY_ROWS_PER_PERM = 25 from rfl]
  rw [pad_bit _ (le_max_left _ _)]
  split_ifs with h
  · have hl : ∀ i < ((inputs.drop (b * 64 / 25)).take
        ((min (min (b * 64 + 64) num_rows) (inputs.length * 25) - 1) / 25 + 1 - b * 64 / 25)).length,
        ((inputs.drop (b * 64 / 25)).take
          ((min (min (b * 64 + 64) num_rows) (inputs.length * 25) - 1) / 25 + 1 - b * 64 / 25)).getD i
          (fun _ => 0) = inputOfB inputs (b * 64 / 25 + 0 + i) := by
      intro i hi
      simp only [List.length_take, List.length_drop] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        ← List.getD_eq_getElem?_getD, inputOfB, add_zero]
    have hp := perms_fold inputs (b * 64) (b * 64 / 25) (min (min (b * 64 + 64) num_rows) (inputs.length * 25))
      _ 0 hl (by omega) (fun _ => 0) rows c k
    erw [hp]
    have z : BitVec.getLsbD (0 : BitVec 64) k = false := by simp
    simp only [List.length_take, List.length_drop, traceBit, z, Bool.false_or,
      show 64 * b = b * 64 from Nat.mul_comm _ _]
    by_cases hr : b * 64 + k < inputs.length * 25 <;> simp only [hr, ↓reduceIte] <;>
      cases permBit inputs (b * 64 + k) c <;> by_cases hc : c = 24 <;> simp [hc] <;>
      first
        | omega
        | (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
  · have z : BitVec.getLsbD (0 : BitVec 64) k = false := by simp
    simp only [traceBit, z, Bool.false_or, show 64 * b = b * 64 from Nat.mul_comm _ _]
    have hr : ¬ b * 64 + k < inputs.length * 25 := by omega
    by_cases hc : c = 24 <;> simp [hc, hr]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega

/-! ## The cells of the trace -/

section cells

variable [DecidableEq F]

theorem bitF_eq_one (b : Bool) : decide ((bitF b : F) = 1) = b := by
  cases b <;> simp [bitF]

theorem state_col {c : ℕ} (h1 : ¬ c < 25) (h2 : c < 1625) :
    ∃ y x z, y < 5 ∧ x < 5 ∧ z < 64 ∧ c = binary.col.a y x z :=
  ⟨(c - 25) / 320, (c - 25) / 64 % 5, (c - 25) % 64, by omega, by omega, by omega, by
    simp only [binary.col.a]; omega⟩

theorem flagRow_bit (k : ℕ) (S : LState) (c : ℕ) :
    decide (getcB (flagRow (F := F) k S) c = 1) = rowSpec k S c := by
  unfold rowSpec
  by_cases hc : c < 25
  · have h := flagRow_onehot (F := F) k S c hc
    simp only [col.round_flags] at h
    rw [h]
    by_cases hk : c = k
    · subst hk; simp [hc]
    · simp [hk, hc]
  · by_cases hc2 : c < 1625
    · obtain ⟨y, x, z, hy, hx, hz, rfl⟩ := state_col hc hc2
      rw [flagRow_state _ _ hy hx hz, bitF_eq_one]
      simp only [binary.col.a] at hc hc2 ⊢
      simp only [hc, ↓reduceIte, hc2, decide_true, Bool.true_and,
        show (25 + 320 * y + 64 * x + z - 25) / 64 = 5 * y + x by omega,
        show (25 + 320 * y + 64 * x + z - 25) % 64 = z by omega]
    · rw [getcB_of_le _ (by simp only [NUM_KECCAK_BINARY_COLS]; omega)]
      simp [hc, hc2]

theorem padRow_bit (c : ℕ) : decide (getcB (padRow (F := F)) c = 1) = decide (c = 24) := by
  by_cases hc : c < 25
  · have h := cellB_flag (padRow (F := F)) hc
    simp only [col.round_flags] at h
    rw [h]
    by_cases h24 : c = 24 <;> simp [padRow, NUM_ROUNDS, h24, Function.update]
  · by_cases hc2 : c < 1625
    · obtain ⟨y, x, z, hy, hx, hz, rfl⟩ := state_col hc hc2
      rw [cellB_a _ hy hx hz]
      simp only [binary.col.a] at hc
      have h0 : (padRow (F := F)).a y x z = 0 := rfl
      have hne : binary.col.a y x z ≠ 24 := by simp only [binary.col.a]; omega
      rw [h0]
      simp [hne]
    · rw [getcB_of_le _ (by simp only [NUM_KECCAK_BINARY_COLS]; omega)]
      simp; omega

/-- Cell `c` of row `r` of the generated trace is 1 exactly as the packed generator reads it. -/
theorem rowsB_bit (inputs : List LState) {r : ℕ} (hr : r < (inputs.length * 25).nextPowerOfTwo) (c : ℕ) :
    decide (getcB ((rowsB (F := F) inputs).getD r KeccakBinaryCols.zero) c = 1) = traceBit inputs r c := by
  rw [rowsB_getD _ hr, traceBit]
  split_ifs with h
  · rw [permRowB, show min (r % 25) 24 = r % 25 by omega, flagRow_bit]
    rfl
  · exact padRow_bit c

end cells

/-! ## The packed trace -/

/-- The words of block `b`: bit `k` of column `j` says whether cell `j` of row `64 b + k` is 1. -/
def groupWordsK (inputs : List LState) (num_rows b : ℕ) : List (BitVec 64) :=
  (List.range NUM_KECCAK_BINARY_COLS).map fun j => Plonky3Lean.Proofs.Air.wordOf fun k =>
    decide (64 * b + k < num_rows) && traceBit inputs (64 * b + k) j

/-- The packed generator's step on one block. -/
abbrev blockStepK (inputs : List LState) (num_rows : ℕ) (acc : List (BitVec 64) × (ℕ → RowWords)) (b : ℕ) :
    List (BitVec 64) × (ℕ → RowWords) :=
  ((acc.1 ++ (List.range NUM_KECCAK_BINARY_COLS).map (pack_block (fun _ => 0) b inputs num_rows acc.2).1),
    (pack_block (fun _ => 0) b inputs num_rows acc.2).2)

theorem blocks_foldK (inputs : List LState) (num_rows : ℕ) (hn : inputs.length * 25 ≤ num_rows)
    (rows : ℕ → RowWords) : ∀ B, 64 * (B - 1) < num_rows ∨ B = 0 →
      ((List.range B).foldl (blockStepK inputs num_rows) ([], rows)).1 =
        (List.range B).flatMap (groupWordsK inputs num_rows)
  | 0, _ => rfl
  | B + 1, hB => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.flatMap_append,
      List.flatMap_singleton]
    change (List.foldl (blockStepK inputs num_rows) ([], rows) (List.range B)).1 ++ _ = _
    rw [blocks_foldK inputs num_rows hn rows B (by omega)]
    refine congrArg (_ ++ ·) ?_
    refine List.map_congr_left fun j _ => Plonky3Lean.Proofs.Air.eq_wordOf fun k hk => ?_
    rw [pack_block_bit _ _ _ (by omega) hn]
    simp [hk]

/-- The packed generator returns the packing of the trace, and panics exactly when the trace generator does. -/
theorem packed_eq [DecidableEq F] (inputs : List LState) (e : ℕ) :
    generate_binary_trace_packed (F := F) inputs = (generate_binary_trace_rows (F := F) inputs e).map packMat := by
  by_cases h2 : (2 : F) = 0
  · by_cases hne : inputs = []
    · simp [generate_binary_trace_packed, generate_binary_trace_rows, h2, hne]
    · rw [generate_binary_eq h2 hne, Option.map_some, matB,
        packMat_flatMap (by decide) _ _ length_cellsB KeccakBinaryCols.zero, length_rowsB]
      have hn := Nat.le_nextPowerOfTwo (inputs.length * 25)
      have key := blocks_foldK inputs ((inputs.length * 25).nextPowerOfTwo) hn (fun _ => RowWords.default)
        (((inputs.length * 25).nextPowerOfTwo + 63) / 64) (by omega)
      simp only [generate_binary_trace_packed, h2, ne_eq, not_true_eq_false, ↓reduceIte, hne,
        KECCAK_BINARY_ROWS_PER_PERM, BITS_PER_WORD]
      rw [show (inputs.length * 25).nextPowerOfTwo + 64 - 1 = (inputs.length * 25).nextPowerOfTwo + 63 by omega]
      erw [key]
      rw [packRows_congr
        (bit := fun r c => decide (((rowsB (F := F) inputs).getD r KeccakBinaryCols.zero).cells.getD c 0 = 1))
        (bit' := traceBit inputs) (fun r hr c _ => rowsB_bit (F := F) inputs hr c)]
      rfl
  · simp [generate_binary_trace_packed, generate_binary_trace_rows, h2]

end Plonky3Lean.Proofs.KeccakAir.Binary
