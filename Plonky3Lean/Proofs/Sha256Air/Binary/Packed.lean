module

public import Plonky3Lean.Proofs.Sha256Air.Binary.Complete
public import Plonky3Lean.Proofs.Air.Pack

@[expose] public section

/-!
# The packed generator of the characteristic-2 SHA-256 AIR

The packed generator stores 64 rows of the trace in each of its rows, one per bit.

It fills a scratch row per input, and reuses it from input to input.

The cells of a filled row do not depend on what the scratch row held before.

So the packed trace is the packing of the trace, and both panic on the same inputs.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.air.mirror p3_sha256_air.mirror.binary Plonky3Lean.Proofs.Air
open p3_sha256_air.mirror (u32_to_bits_le BLOCK_WORDS)

variable {F : Type} [Field F]

/-! ## A loop that writes one entry per step -/

/-- A loop step that writes entry `i` of a map from data alone, and moves the data on. -/
abbrev writeStep {X D : Type} (v : D → ℕ → X) (g : D → ℕ → D) (acc : (ℕ → X) × D) (i : ℕ) :
    (ℕ → X) × D :=
  (Function.update acc.1 i (v acc.2 i), g acc.2 i)

theorem writeStep_snd {X D : Type} (v : D → ℕ → X) (g : D → ℕ → D) (L : List ℕ) (S : ℕ → X) (d : D) :
    (L.foldl (writeStep v g) (S, d)).2 = L.foldl g d := by
  induction L generalizing S d with
  | nil => rfl
  | cons a L ih => exact ih _ _

/-- The entries the loop writes do not depend on the map it starts from. -/
theorem writeStep_fst {X D : Type} (v : D → ℕ → X) (g : D → ℕ → D) (L : List ℕ) (S S0 : ℕ → X) (d : D)
    (j : ℕ) : (L.foldl (writeStep v g) (S, d)).1 j =
      if j ∈ L then (L.foldl (writeStep v g) (S0, d)).1 j else S j := by
  induction L generalizing S S0 d with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, writeStep, List.mem_cons]
    rw [ih _ (Function.update S0 a (v d a))]
    by_cases hL : j ∈ L
    · simp [hL]
    · rw [ih (Function.update S0 a (v d a)) S0]
      by_cases ha : j = a
      · subst ha; simp [hL]
      · simp [hL, ha]

/-! ## The generated row does not depend on the scratch row -/

/-- The schedule entry the schedule loop writes at step `i`, from the words so far. -/
abbrev schedVal (w : ℕ → p3_sha256_air.mirror.Word) (i : ℕ) : Sha256BinaryScheduleCols F :=
  let t := BLOCK_WORDS + i
  ⟨fun j => (carriesOf (F := F)
    [small_sigma1 (w (t - 2)), w (t - 7), small_sigma0 (w (t - 15)), w (t - 16)]).getD j (fun _ => 0)⟩

/-- The words after step `i` of the schedule loop. -/
abbrev schedNext (w : ℕ → p3_sha256_air.mirror.Word) (i : ℕ) : ℕ → p3_sha256_air.mirror.Word :=
  (schedStepB (F := F) (Sha256BinaryCols.zero, w) i).2

theorem sched_fold (L : List ℕ) (r : Sha256BinaryCols F) (w : ℕ → p3_sha256_air.mirror.Word) :
    L.foldl schedStepB (r, w) =
      ({ r with schedule := (L.foldl (writeStep (schedVal (F := F)) (schedNext (F := F))) (r.schedule, w)).1 },
        L.foldl (schedNext (F := F)) w) := by
  induction L generalizing r w with
  | nil => rfl
  | cons a L ih => exact ih _ _

/-- The round entry the compression loop writes at step `t`, from the chains so far. -/
abbrev roundVal (w : ℕ → p3_sha256_air.mirror.Word)
    (c : (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word)) (t : ℕ) :
    Sha256BinaryRoundCols F :=
  let e := c.2 (t + 3)
  let f := c.2 (t + 2)
  let g := c.2 (t + 1)
  let h := c.2 t
  let a := c.1 (t + 3)
  let b := c.1 (t + 2)
  let cc := c.1 (t + 1)
  let ch := (e &&& f) ^^^ (~~~e &&& g)
  let mj := (a &&& b) ^^^ (a &&& cc) ^^^ (b &&& cc)
  let t1 := h + big_sigma1 e + ch + BitVec.ofNat 32 (p3_sha256_air.mirror.kOf t) + w t
  ⟨u32_to_bits_le ch, u32_to_bits_le mj,
    fun j => (carriesOf (F := F) [h, big_sigma1 e, ch, BitVec.ofNat 32 (p3_sha256_air.mirror.kOf t), w t]).getD j
      (fun _ => 0),
    u32_to_bits_le t1, (carriesOf (F := F) [t1, big_sigma0 a, mj]).getD 0 (fun _ => 0)⟩

/-- The chains after step `t` of the compression loop. -/
abbrev roundNext (w : ℕ → p3_sha256_air.mirror.Word)
    (c : (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word)) (t : ℕ) :
    (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word) :=
  (roundStepB (F := F) w (Sha256BinaryCols.zero, c.1, c.2) t).2

theorem round_fold (w : ℕ → p3_sha256_air.mirror.Word) (L : List ℕ) (r : Sha256BinaryCols F)
    (a e : ℕ → p3_sha256_air.mirror.Word) :
    L.foldl (roundStepB w) (r, a, e) =
      ({ r with rounds := (L.foldl (writeStep (roundVal w) (roundNext (F := F) w)) (r.rounds, (a, e))).1 },
        L.foldl (roundNext (F := F) w) (a, e)) := by
  induction L generalizing r a e with
  | nil => rfl
  | cons t L ih => exact ih _ _ _

/-- The schedule loop's result, from any row. -/
def schedFrom (r : Sha256BinaryCols F) (input : List p3_sha256_air.mirror.Word) :
    Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) :=
  List.foldl schedStepB (r, fun t => if t < BLOCK_WORDS then input.getD t 0 else 0)
    (List.range p3_sha256_air.mirror.SCHEDULE_EXTENSIONS)

/-- The compression loop's result, from any row. -/
def compFrom (r : Sha256BinaryCols F) (input : List p3_sha256_air.mirror.Word) :
    Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word) :=
  List.foldl (roundStepB (schedFrom r input).2)
    ({ (schedFrom r input).1 with w := fun t => u32_to_bits_le ((schedFrom r input).2 t) },
      chainA input, chainE input)
    (List.range p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS)

/-- The generated row, from any row. -/
def finalFrom (r : Sha256BinaryCols F) (input : List p3_sha256_air.mirror.Word) : Sha256BinaryCols F :=
  let C := compFrom r input
  { C.1 with
    a_chain := fun k => u32_to_bits_le (C.2.1 k)
    e_chain := fun k => u32_to_bits_le (C.2.2 k)
    h_out := fun i => u32_to_bits_le (input.getD (BLOCK_WORDS + i) 0 +
      (if i < 4 then C.2.1 else C.2.2) (p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS + 3 - i % 4)) }

/-- From any row, the generator never panics, and fills the row by its two loops. -/
theorem gen_eq_from (r : Sha256BinaryCols F) (input : List p3_sha256_air.mirror.Word) :
    generate_trace_row r input = some (finalFrom r input) := by
  unfold generate_trace_row
  dsimp only
  rw [foldlM_some schedStepB _ _ (fun acc i => by
    obtain ⟨row, w⟩ := acc
    simp only [SCHEDULE_CARRIES, awc2]
    rfl)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [foldlM_some (roundStepB _) _ _ (fun acc t => by
    simp only [T1_CARRIES, awc3, awc1]
    rfl)]
  simp only [Option.pure_def, Option.bind_some, finalFrom, compFrom, schedFrom]
  unfold chainA chainE
  rfl

/-- The cells of the generated row do not depend on the row the generator starts from. -/
theorem cells_finalFrom (r : Sha256BinaryCols F) (input : List p3_sha256_air.mirror.Word) :
    (finalFrom r input).cells = (finalB input).cells := by
  rw [show finalB input = finalFrom Sha256BinaryCols.zero input by
    unfold finalB finalFrom compOutB compFrom schedOutB schedFrom; rfl]
  simp only [finalFrom, compFrom, schedFrom, sched_fold, round_fold, Sha256BinaryCols.cells]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl ?_) ?_) rfl
  · refine List.flatMap_congr fun i hi => ?_
    rw [writeStep_fst _ _ _ _ Sha256BinaryCols.zero.schedule, ite_eq_left hi]
  · refine List.flatMap_congr fun t ht => ?_
    rw [writeStep_fst _ _ _ _ Sha256BinaryCols.zero.rounds, ite_eq_left ht]

/-! ## Packing the cells -/

/-- Whether cell `c` of the row generated from an input is 1. -/
def cellBit [DecidableEq F] (input : List p3_sha256_air.mirror.Word) (c : ℕ) : Bool :=
  decide ((finalB (F := F) input).cells.getD c 0 = 1)

theorem shift_getLsbD (lane k : ℕ) : (1#64 <<< lane).getLsbD k = (decide (k < 64) && decide (k = lane)) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hk : k < 64 <;> by_cases hl : k = lane <;> simp [hk, hl]
  omega

/-- Setting bit `m` of the columns whose cell is 1 sets it exactly in those columns. -/
theorem or_cells [DecidableEq F] (l : List F) (m : BitVec 64) (block : ℕ → BitVec 64) (s : ℕ) :
    (l.zipIdx s).foldl (fun block (bit, column) =>
      if bit = 1 then Function.update block column (block column ||| m) else block) block =
      fun c => if s ≤ c ∧ c < s + l.length ∧ l.getD (c - s) 0 = 1 then block c ||| m else block c := by
  induction l generalizing s block with
  | nil => funext c; simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih]
    dsimp only
    funext c
    by_cases hc : c = s
    · subst hc
      by_cases ha : a = 1 <;> simp [ha]
    · have hb : (if a = 1 then Function.update block s (block s ||| m) else block) c = block c := by
        split_ifs <;> simp [Function.update, hc]
      rw [hb]
      rcases Nat.lt_or_gt_of_ne hc with h | h
      · simp [show ¬ s + 1 ≤ c by omega, show ¬ s ≤ c by omega]
      · have e : c - s = (c - (s + 1)) + 1 := by omega
        simp only [List.length_cons, e, List.getD_cons_succ, show s + 1 ≤ c by omega, show s ≤ c by omega,
          true_and, show s + (l.length + 1) = s + 1 + l.length by omega]

theorem cells_getD_ne_one_of_le (r : Sha256BinaryCols F) {c : ℕ} (hc : NUM_SHA256_BINARY_COLS ≤ c) :
    r.cells.getD c 0 ≠ 1 := by
  rw [List.getD_eq_default _ _ (by rw [length_cellsB]; exact hc)]
  exact zero_ne_one

/-- The packed generator's step on one lane: fill the scratch row, then set bit `lane` of its 1 cells. -/
abbrev laneStep [DecidableEq F] (acc : (ℕ → BitVec 64) × Sha256BinaryCols F)
    (x : List p3_sha256_air.mirror.Word × ℕ) : Option ((ℕ → BitVec 64) × Sha256BinaryCols F) := do
  let (block, row) := acc
  let row ← generate_trace_row row x.1
  let block := row.cells.zipIdx.foldl (fun block (bit, column) =>
    if bit = 1 then Function.update block column (block column ||| 1#64 <<< x.2) else block) block
  pure (block, row)

theorem laneStep_eq [DecidableEq F] (block : ℕ → BitVec 64) (row : Sha256BinaryCols F)
    (input : List p3_sha256_air.mirror.Word) (lane : ℕ) :
    laneStep (block, row) (input, lane) =
      some (fun c => block c ||| (if cellBit (F := F) input c then 1#64 <<< lane else 0), finalFrom row input) := by
  simp only [laneStep, gen_eq_from, Option.bind_eq_bind, Option.bind_some, Option.pure_def, or_cells,
    cells_finalFrom, Option.some.injEq, Prod.mk.injEq, and_true]
  funext c
  have key : (0 ≤ c ∧ c < 0 + (finalB (F := F) input).cells.length ∧
      (finalB (F := F) input).cells.getD (c - 0) 0 = 1) ↔ cellBit (F := F) input c = true := by
    rw [cellBit, decide_eq_true_iff, Nat.sub_zero, zero_add]
    refine ⟨fun h => h.2.2, fun h => ⟨Nat.zero_le _, ?_, h⟩⟩
    by_contra hc
    exact cells_getD_ne_one_of_le _ (by rw [length_cellsB] at hc; omega) h
  simp only [key]
  split_ifs <;> simp

/-- After the lanes of a group, bit `k` of column `c` says whether cell `c` of input `k` is 1. -/
theorem lanes_fold [DecidableEq F] (l : List (List p3_sha256_air.mirror.Word)) (s : ℕ)
    (block : ℕ → BitVec 64) (row : Sha256BinaryCols F) :
    ∃ row', (l.zipIdx s).foldlM laneStep (block, row) =
      some ((fun c => block c ||| Plonky3Lean.Proofs.Air.wordOf fun k =>
        decide (s ≤ k) && decide (k < s + l.length) && cellBit (F := F) (l.getD (k - s) []) c), row') := by
  induction l generalizing s block row with
  | nil =>
    refine ⟨row, ?_⟩
    simp only [List.zipIdx_nil, List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq, and_true]
    funext c
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_or, Plonky3Lean.Proofs.Air.wordOf_getLsbD, List.length_nil, add_zero]
    by_cases h : s ≤ k <;> simp [h]
  | cons a l ih =>
    obtain ⟨row', h⟩ := ih (s + 1)
      (fun c => block c ||| (if cellBit (F := F) a c then 1#64 <<< s else 0)) (finalFrom row a)
    refine ⟨row', ?_⟩
    rw [List.zipIdx_cons, List.foldlM_cons, laneStep_eq]
    change List.foldlM laneStep _ _ = _
    rw [h]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    funext c
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_or, Plonky3Lean.Proofs.Air.wordOf_getLsbD, hk, decide_true, Bool.true_and, List.length_cons]
    by_cases hks : k = s
    · subst hks
      by_cases hb : cellBit (F := F) a c <;> simp [hb, hk]
    · have hsh : (if cellBit (F := F) a c then 1#64 <<< s else 0).getLsbD k = false := by
        split_ifs
        · simp only [shift_getLsbD, hk, hks, decide_false, Bool.and_false]
        · simp
      rw [hsh, Bool.or_false]
      rcases Nat.lt_or_gt_of_ne hks with h' | h'
      · simp [show ¬ s ≤ k by omega, show ¬ s + 1 ≤ k by omega]
      · simp [show s ≤ k by omega, show s + 1 ≤ k by omega, show k - s = (k - (s + 1)) + 1 by omega,
          show s + (l.length + 1) = s + 1 + l.length by omega]

/-! ## The packed trace -/

/-- The packed generator's step on one group of 64 inputs. -/
abbrev blockStep [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word))
    (acc : List (BitVec 64) × Sha256BinaryCols F) (w : ℕ) : Option (List (BitVec 64) × Sha256BinaryCols F) := do
  let (words, row) := acc
  let input_block := (inputs.drop (64 * w)).take 64
  let (block, row) ← input_block.zipIdx.foldlM laneStep (fun _ => 0, row)
  pure (words ++ (List.range NUM_SHA256_BINARY_COLS).map block, row)

/-- The words of group `w`: bit `k` of column `j` says whether cell `j` of input `64 w + k` is 1. -/
def groupWords [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word)) (w : ℕ) : List (BitVec 64) :=
  (List.range NUM_SHA256_BINARY_COLS).map fun j => Plonky3Lean.Proofs.Air.wordOf fun k =>
    decide (64 * w + k < inputs.length) && cellBit (F := F) (inputs.getD (64 * w + k) []) j

theorem blockStep_eq [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word))
    (words : List (BitVec 64)) (row : Sha256BinaryCols F) (w : ℕ) :
    ∃ row', blockStep inputs (words, row) w = some (words ++ groupWords (F := F) inputs w, row') := by
  obtain ⟨row', h⟩ := lanes_fold (F := F) ((inputs.drop (64 * w)).take 64) 0 (fun _ => 0) row
  refine ⟨row', ?_⟩
  simp only [blockStep, h, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq, and_true, groupWords, List.append_cancel_left_eq]
  refine List.map_congr_left fun j _ => ?_
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_or]
  refine Plonky3Lean.Proofs.Air.wordOf_congr fun k hk => ?_
  simp only [zero_le, decide_true, Bool.true_and, zero_add, Nat.sub_zero, List.length_take,
    List.length_drop]
  by_cases h1 : 64 * w + k < inputs.length
  · have : k < min 64 (inputs.length - 64 * w) := by omega
    simp only [this, h1, decide_true, Bool.true_and]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
  · have : ¬ k < min 64 (inputs.length - 64 * w) := by omega
    simp [this, h1]

theorem blocks_fold [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word)) (B : ℕ) :
    ∃ row, (List.range B).foldlM (blockStep inputs) ([], Sha256BinaryCols.zero (T := F)) =
      some ((List.range B).flatMap (groupWords (F := F) inputs), row) := by
  induction B with
  | zero => exact ⟨_, rfl⟩
  | succ B ih =>
    obtain ⟨row, h⟩ := ih
    obtain ⟨row', h'⟩ := blockStep_eq (F := F) inputs ((List.range B).flatMap (groupWords (F := F) inputs)) row B
    refine ⟨row', ?_⟩
    rw [List.range_succ, List.foldlM_append, h]
    change List.foldlM (blockStep inputs) ((List.range B).flatMap (groupWords (F := F) inputs), row) [B] = _
    rw [List.foldlM_cons, h', List.flatMap_append, List.flatMap_singleton]
    rfl

/-- The packed generator returns the packing of the trace, and panics exactly when the trace generator does. -/
theorem packed_eq [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word)) (e : ℕ) :
    generate_binary_trace_packed (F := F) inputs = (generate_binary_trace_rows (F := F) inputs e).map packMat := by
  rw [generate_eqB]
  by_cases hc : (2 : F) = 0 ∧ inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length
  · obtain ⟨h2, hl, hp⟩ := hc
    have key : generate_binary_trace_packed (F := F) inputs =
        (List.range ((inputs.length + 63) / 64)).foldlM (blockStep (F := F) inputs) ([], Sha256BinaryCols.zero) >>=
          fun x => pure ⟨NUM_SHA256_BINARY_COLS, x.1⟩ := by
      unfold generate_binary_trace_packed
      simp only [h2, hl, hp, ne_eq, not_true_eq_false, ↓reduceIte]
    obtain ⟨row, h⟩ := blocks_fold (F := F) inputs ((inputs.length + 63) / 64)
    rw [key, h, ite_eq_left ⟨h2, hl, hp⟩, Option.map_some, matOfB,
      packMat_flatMap (by decide) _ _ length_cellsB (finalB [])]
    simp only [List.length_map, List.getD_map, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rfl
  · unfold generate_binary_trace_packed
    rw [ite_eq_right hc]
    by_cases h2 : (2 : F) = 0
    · by_cases hl : inputs.length = 0
      · simp [h2, hl]
      · have hp : ¬ 2 ^ Nat.log 2 inputs.length = inputs.length := fun hp => hc ⟨h2, hl, hp⟩
        simp [h2, hl, hp]
    · simp [h2]

end Plonky3Lean.Proofs.Sha256Air.Binary
