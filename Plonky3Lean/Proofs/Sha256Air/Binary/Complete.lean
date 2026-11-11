module

public import Plonky3Lean.Proofs.Sha256Air.Binary.GenRow
public import Plonky3Lean.Proofs.Sha256Air.Binary.Cells
public import Plonky3Lean.Proofs.Air.Check

@[expose] public section

/-!
# Completeness of the characteristic-2 SHA-256 AIR

In characteristic 2, the row the generator fills from any input meets each row constraint.

So, on a power-of-two number of inputs, the generator's trace satisfies the AIR.

This holds with or without the booleanity.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_sha256_air.mirror.binary Plonky3Lean.Spec.Sha256
open p3_sha256_air.mirror (kOf u32_to_bits_le)
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds Ws vs chA chE t1s Ws_ge vs_succ chain_vars holds_bits bool_bits)

variable {F : Type} [Field F]

theorem chain_step {P W : BitVec 32} {w c : ℕ → F} {l : List ((ℕ → F) × (ℕ → F))}
    {Wl : List (BitVec 32)} (hw : Holds w W) (hc : ∀ i < 31, c i = carry_bits P W (P + W) i)
    (hr : Chain (P + W) l Wl) : Chain P ((w, c) :: l) (W :: Wl) :=
  ⟨hw, fun i hi => (hc i hi).trans (carry_bits_eq P W hi), hr⟩

/-- Cell c of a row. -/
def getcB (r : Sha256BinaryCols F) (c : ℕ) : F := r.cells.getD c 0

section row

variable (input : List p3_sha256_air.mirror.Word)

/-- The cells of the generated row. -/
abbrev locB : ℕ → F := getcB (finalB (F := F) input)

theorem gw {t b : ℕ} (ht : t < 64) (hb : b < 32) :
    locB (F := F) input (col.w t b) = u32_to_bits_le (Ws input t) b := by
  rw [locB, getcB, cellB_w _ ht hb, (gen_specB input).w t ht]

theorem ga {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    locB (F := F) input (col.a_chain k b) = u32_to_bits_le (chA input k) b := by
  rw [locB, getcB, cellB_a _ hk hb, (gen_specB input).a k hk]

theorem ge {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    locB (F := F) input (col.e_chain k b) = u32_to_bits_le (chE input k) b := by
  rw [locB, getcB, cellB_e _ hk hb, (gen_specB input).e k hk]

theorem gh {i b : ℕ} (hi : i < 8) (hb : b < 32) :
    locB (F := F) input (col.h_out i b) =
      u32_to_bits_le (input.getD (16 + i) 0 + (vs input 64).toList.getD i 0) b := by
  rw [locB, getcB, cellB_h _ hi hb, (gen_specB input).h_out i hi]

theorem gsc {i j c : ℕ} (hi : i < 48) (hj : j < 2) (hc : c < 31) :
    locB (F := F) input (col.sched_carries i j c) =
      (carriesOf (F := F) (schedWords input i)).getD j (fun _ => 0) c := by
  rw [locB, getcB, cellB_sched _ hi hj hc, (gen_specB input).sc i hi]

theorem gr {t off : ℕ} (ht : t < 64) (ho : off < 220) :
    locB (F := F) input (9376 + 220 * t + off) =
      (Sha256BinaryCols.roundCells (roundSpecB (F := F) input t)).getD off 0 := by
  rw [locB, getcB, cellB_round _ ht ho, (gen_specB input).rounds t ht]

theorem hW (t : ℕ) (ht : t < 64) : Holds (fun b => locB (F := F) input (col.w t b)) (Ws input t) :=
  holds_bits fun _ hb => gw input ht hb

theorem hA (k : ℕ) (hk : k < 68) : Holds (fun b => locB (F := F) input (col.a_chain k b)) (chA input k) :=
  holds_bits fun _ hb => ga input hk hb

theorem hE (k : ℕ) (hk : k < 68) : Holds (fun b => locB (F := F) input (col.e_chain k b)) (chE input k) :=
  holds_bits fun _ hb => ge input hk hb

theorem hH (i : ℕ) (hi : i < 8) : Holds (fun b => locB (F := F) input (col.h_out i b))
    (input.getD (16 + i) 0 + (vs input 64).toList.getD i 0) :=
  holds_bits fun _ hb => gh input hi hb

theorem hCh (t : ℕ) (ht : t < 64) : Holds (fun b => locB (F := F) input (col.ch t b))
    (ch (vs input t).e (vs input t).f (vs input t).g) :=
  holds_bits fun b hb => by
    rw [col.ch, gr input ht (by omega), (getD_roundCellsB _).1 b hb]; rfl

theorem hMaj (t : ℕ) (ht : t < 64) : Holds (fun b => locB (F := F) input (col.maj t b))
    (maj (vs input t).a (vs input t).b (vs input t).c) :=
  holds_bits fun b hb => by
    rw [col.maj, Nat.add_assoc, gr input ht (by omega), (getD_roundCellsB _).2.1 b hb]; rfl

theorem hT1 (t : ℕ) (ht : t < 64) : Holds (fun b => locB (F := F) input (col.t1 t b)) (t1s input t) :=
  holds_bits fun b hb => by
    rw [col.t1, Nat.add_assoc, gr input ht (by omega), (getD_roundCellsB _).2.2.2.1 b hb]; rfl

theorem gT1c {t j c : ℕ} (ht : t < 64) (hj : j < 3) (hc : c < 31) :
    locB (F := F) input (col.t1_carries t j c) = (carriesOf (F := F) (t1Words input t)).getD j (fun _ => 0) c := by
  rw [col.t1_carries, show 9376 + 220 * t + 64 + 31 * j + c = 9376 + 220 * t + (64 + (31 * j + c)) by omega,
    gr input ht (by omega), (getD_roundCellsB _).2.2.1 j hj c hc]; rfl

theorem gNAc {t c : ℕ} (ht : t < 64) (hc : c < 31) :
    locB (F := F) input (col.new_a_carries t c) = (carriesOf (F := F) (naWords input t)).getD 0 (fun _ => 0) c := by
  rw [col.new_a_carries, Nat.add_assoc, gr input ht (by omega), (getD_roundCellsB _).2.2.2.2 c hc]; rfl

variable (h2 : (2 : F) = 0)
include h2

theorem gen_sched {i : ℕ} (hi : i < 48) : add_many (pb0 (F := F)) True
    [xor3_shift fieldOps (fun b => locB input (col.w (16 + i - 2) b)) 17 19 10,
      fun b => locB input (col.w (16 + i - 7) b),
      xor3_shift fieldOps (fun b => locB input (col.w (16 + i - 15) b)) 7 18 3,
      fun b => locB input (col.w (16 + i - 16) b)]
    ((List.range 2).map fun j c => locB input (col.sched_carries i j c)) (fun b => locB input (col.w (16 + i) b)) := by
  rw [show 16 + i - 2 = i + 14 by omega, show 16 + i - 7 = i + 9 by omega,
    show 16 + i - 15 = i + 1 by omega, show 16 + i - 16 = i by omega]
  have hs := hW (F := F) input (16 + i) (by omega)
  rw [Ws_ge input (by omega) (by omega), show 16 + i - 2 = i + 14 by omega, show 16 + i - 7 = i + 9 by omega,
    show 16 + i - 15 = i + 1 by omega, show 16 + i - 16 = i by omega] at hs
  refine add_many_ok h2 (W0 := smallSigma1 (Ws input (i + 14)))
    (Wrest := [Ws input (i + 9), smallSigma0 (Ws input (i + 1)), Ws input i]) (by simp)
    (holds_shift h2 (hW input _ (by omega)) (by norm_num) (by norm_num)) ?_ ?_ hs
  · simp only [List.zip, List.map, List.range, List.range.loop]
    refine chain_step (hW input _ (by omega)) (fun c hc => ?_) (chain_step
      (holds_shift h2 (hW input _ (by omega)) (by norm_num) (by norm_num)) (fun c hc => ?_) trivial)
    · rw [gsc input hi (by norm_num) hc]; simp [carriesOf, schedWords, BitVec.zero_add]
    · rw [gsc input hi (by norm_num) hc]; simp [carriesOf, schedWords, BitVec.zero_add]
  · simpa using hW (F := F) input i (by omega)

theorem gen_round {t : ℕ} (ht : t < 64) :
    (∀ i < 32, locB (F := F) input (col.e_chain (t + 3) i) * (locB (F := F) input (col.e_chain (t + 2) i) +
      locB (F := F) input (col.e_chain (t + 1) i)) + locB (F := F) input (col.e_chain (t + 1) i) + locB (F := F) input (col.ch t i) = 0) ∧
    (∀ i < 32, maj fieldOps (locB (F := F) input (col.a_chain (t + 3) i)) (locB (F := F) input (col.a_chain (t + 2) i))
      (locB (F := F) input (col.a_chain (t + 1) i)) + locB (F := F) input (col.maj t i) = 0) ∧
    add_many (pb0 (F := F)) True
      [fun b => locB (F := F) input (col.e_chain t b), xor3_rot fieldOps (fun b => locB (F := F) input (col.e_chain (t + 3) b)) 6 11 25,
        fun i => locB (F := F) input (col.ch t i), fun i => u32_to_bits_le (F := F) (BitVec.ofNat 32 (kOf t)) i,
        fun b => locB (F := F) input (col.w t b)]
      ((List.range 3).map fun j c => locB (F := F) input (col.t1_carries t j c)) (fun i => locB (F := F) input (col.t1 t i)) ∧
    add_many (pb0 (F := F)) True
      [fun b => locB (F := F) input (col.a_chain t b), fun i => locB (F := F) input (col.t1 t i)] []
      (fun b => locB (F := F) input (col.e_chain (t + 4) b)) ∧
    add_many (pb0 (F := F)) True
      [fun i => locB (F := F) input (col.t1 t i), xor3_rot fieldOps (fun b => locB (F := F) input (col.a_chain (t + 3) b)) 2 13 22,
        fun i => locB (F := F) input (col.maj t i)]
      [fun c => locB (F := F) input (col.new_a_carries t c)] (fun b => locB (F := F) input (col.a_chain (t + 4) b)) := by
  obtain ⟨ca, cb, cc, cd, ce, cf, cg, ch'⟩ := chain_vars input t (by omega)
  have a3 := hA (F := F) input (t + 3) (by omega); rw [ca] at a3
  have a2 := hA (F := F) input (t + 2) (by omega); rw [cb] at a2
  have a1 := hA (F := F) input (t + 1) (by omega); rw [cc] at a1
  have a0 := hA (F := F) input t (by omega); rw [cd] at a0
  have e3 := hE (F := F) input (t + 3) (by omega); rw [ce] at e3
  have e2 := hE (F := F) input (t + 2) (by omega); rw [cf] at e2
  have e1 := hE (F := F) input (t + 1) (by omega); rw [cg] at e1
  have e0 := hE (F := F) input t (by omega); rw [ch'] at e0
  have hc := hCh (F := F) input t ht
  have hm := hMaj (F := F) input t ht
  have ht1 := hT1 (F := F) input t ht
  have hk : Holds (F := F) (fun i => u32_to_bits_le (BitVec.ofNat 32 (kOf t)) i) (BitVec.ofNat 32 (kOf t)) :=
    holds_bits fun _ _ => rfl
  have e1' := vs_succ input ht
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [show locB (F := F) input (col.e_chain (t + 3) i) = _ from e3 i hi,
      show locB (F := F) input (col.e_chain (t + 2) i) = _ from e2 i hi,
      show locB (F := F) input (col.e_chain (t + 1) i) = _ from e1 i hi,
      show locB (F := F) input (col.ch t i) = _ from hc i hi, add_bitF h2, mul_bitF, add_bitF h2,
      add_bitF h2]
    simp only [ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true,
      Bool.true_and]
    cases (vs input t).e.getLsbD i <;> cases (vs input t).f.getLsbD i <;> cases (vs input t).g.getLsbD i <;>
      simp [bitF]
  · rw [show locB (F := F) input (col.a_chain (t + 3) i) = _ from a3 i hi,
      show locB (F := F) input (col.a_chain (t + 2) i) = _ from a2 i hi,
      show locB (F := F) input (col.a_chain (t + 1) i) = _ from a1 i hi,
      show locB (F := F) input (col.maj t i) = _ from hm i hi, maj_bitF h2, add_bitF h2]
    simp only [Plonky3Lean.Spec.Sha256.maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases (vs input t).a.getLsbD i <;> cases (vs input t).b.getLsbD i <;> cases (vs input t).c.getLsbD i <;>
      simp [bitF]
  · refine add_many_ok h2 (W0 := (vs input t).h)
      (Wrest := [bigSigma1 (vs input t).e, ch (vs input t).e (vs input t).f (vs input t).g,
        BitVec.ofNat 32 (kOf t), Ws input t]) (by simp) e0 ?_ ?_ ht1
    · simp only [List.zip, List.map, List.range, List.range.loop]
      refine chain_step (holds_rot h2 e3 (by norm_num) (by norm_num) (by norm_num)) (fun c hc' => ?_)
        (chain_step hc (fun c hc' => ?_) (chain_step hk (fun c hc' => ?_) trivial))
      all_goals rw [gT1c input ht (by norm_num) hc']; simp [carriesOf, t1Words, BitVec.zero_add]
    · simpa using hW (F := F) input t ht
  · refine add_many_ok h2 (W0 := (vs input t).d) (Wrest := [t1s input t]) (by simp) a0 trivial ?_ ?_
    · simpa using ht1
    · have := hE (F := F) input (t + 4) (by omega)
      simp only [chE, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega, e1',
        round] at this
      simpa [Plonky3Lean.Proofs.Sha256Air.Binary.sumW, t1s] using this
  · refine add_many_ok h2 (W0 := t1s input t)
      (Wrest := [bigSigma0 (vs input t).a, maj (vs input t).a (vs input t).b (vs input t).c]) (by simp) ht1 ?_
      ?_ ?_
    · simp only [List.zip]
      refine chain_step (holds_rot h2 a3 (by norm_num) (by norm_num) (by norm_num)) (fun c hc' => ?_) trivial
      rw [gNAc input ht hc']; simp [carriesOf, naWords, BitVec.zero_add]
    · simpa using hm
    · have := hA (F := F) input (t + 4) (by omega)
      simp only [chA, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega, e1',
        round] at this
      simpa [Plonky3Lean.Proofs.Sha256Air.Binary.sumW, t1s, BitVec.add_assoc] using this

theorem gen_out {i : ℕ} (hi : i < 8) :
    add_many (pb0 (F := F)) True
      [fun b => locB input ((if i < 4 then col.a_chain else col.e_chain) (3 - i % 4) b),
        fun b => locB input ((if i < 4 then col.a_chain else col.e_chain) (67 - i % 4) b)] []
      (fun b => locB input (col.h_out i b)) := by
  obtain ⟨ca, cb, cc, cd, ce, cf, cg, ch'⟩ := chain_vars input 64 le_rfl
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · simp only [h4, ↓reduceIte, Nat.mod_eq_of_lt h4]
    have e1 : chA input (3 - i) = input.getD (16 + i) 0 := by
      simp only [chA, show 3 - i < 4 by omega, ↓reduceIte, show 3 - (3 - i) = i by omega]
    have e2 : chA input (67 - i) = (vs input 64).toList.getD i 0 := by
      interval_cases i
      · exact ca
      · exact cb
      · exact cc
      · exact cd
    have h0 := hA (F := F) input (3 - i) (by omega); rw [e1] at h0
    have h1 := hA (F := F) input (67 - i) (by omega); rw [e2] at h1
    exact add_many_ok h2 (Wrest := [_]) (by simp) h0 trivial (by simpa using h1) (hH input i hi)
  · simp only [show ¬ i < 4 by omega, ↓reduceIte]
    obtain ⟨j, rfl⟩ : ∃ j, i = 4 + j := ⟨i - 4, by omega⟩
    have hj : j < 4 := by omega
    rw [show (4 + j) % 4 = j by omega]
    have e1 : chE input (3 - j) = input.getD (16 + (4 + j)) 0 := by
      simp only [chE, show 3 - j < 4 by omega, ↓reduceIte, show 7 - (3 - j) = 4 + j by omega]
    have e2 : chE input (67 - j) = (vs input 64).toList.getD (4 + j) 0 := by
      interval_cases j
      · exact ce
      · exact cf
      · exact cg
      · exact ch'
    have h0 := hE (F := F) input (3 - j) (by omega); rw [e1] at h0
    have h1 := hE (F := F) input (67 - j) (by omega); rw [e2] at h1
    exact add_many_ok h2 (Wrest := [_]) (by simp) h0 trivial (by simpa using h1) (hH input _ hi)

/-- In characteristic 2, the generated row meets its row constraints, with or without the booleanity. -/
theorem gen_rowSpecB (cb : Bool) : RowSpecB (locB (F := F) input) cb := by
  refine ⟨fun _ => ⟨fun k hk b hb => ?_, fun k hk b hb => ?_, fun t ht b hb => ?_⟩, fun i hi => ?_,
    fun t ht => (gen_round input h2 ht).1, fun t ht => (gen_round input h2 ht).2.1,
    fun t ht => (gen_round input h2 ht).2.2.1, fun t ht => (gen_round input h2 ht).2.2.2.1,
    fun t ht => (gen_round input h2 ht).2.2.2.2, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ga input (by omega) hb]; exact bool_bits _ hb
  · rw [ge input (by omega) hb]; exact bool_bits _ hb
  · rw [gw input (by omega) hb]; exact bool_bits _ hb
  · simpa [SCHEDULE_CARRIES, show 16 + i = BLOCK_WORDS + i from rfl] using gen_sched input h2 hi
  · have := gen_out input h2 (i := i) (by omega)
    simpa [show i < 4 from hi, Nat.mod_eq_of_lt hi] using this
  · have := gen_out input h2 (i := 4 + i) (by omega)
    simpa [show ¬ 4 + i < 4 by omega, show (4 + i) % 4 = i by omega] using this

end row

end Plonky3Lean.Proofs.Sha256Air.Binary

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror.binary Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (rowOf satisfies_iff_rows getD_map_range_of)
open Plonky3Lean.Proofs.Sha256Air (binaryAir)

variable {F : Type} [Field F]

/-- The trace of a list of rows. -/
def matOfB (rows : List (Sha256BinaryCols F)) : Mat F :=
  ⟨NUM_SHA256_BINARY_COLS, rows.flatMap Sha256BinaryCols.cells⟩

theorem mapM_some {α β : Type} {f : α → Option β} (g : α → β) (h : ∀ a, f a = some (g a)) (l : List α) :
    l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, h, ih]

/-- The generator panics unless 2 is 0 in the field and the number of inputs is a power of two. -/
theorem generate_eqB [DecidableEq F] (inputs : List (List p3_sha256_air.mirror.Word)) (e : ℕ) :
    generate_binary_trace_rows (F := F) inputs e =
      if (2 : F) = 0 ∧ (inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) then some (matOfB (inputs.map (finalB (F := F)))) else none := by
  unfold generate_binary_trace_rows
  rw [mapM_some finalB (fun a => gen_eqB a)]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  split_ifs <;> simp_all [matOfB]

theorem matOfB_height (rows : List (Sha256BinaryCols F)) : (matOfB rows).height = rows.length := by
  simp only [Mat.height, matOfB, NUM_SHA256_BINARY_COLS, List.length_flatMap, length_cellsB,
    List.map_const', List.sum_replicate, smul_eq_mul]
  simp

theorem matOfB_cell (rows : List (Sha256BinaryCols F)) {i c : ℕ} (hi : i < rows.length)
    (hc : c < NUM_SHA256_BINARY_COLS) :
    ((matOfB rows).row i).getD c 0 = getcB (rows.getD i Sha256BinaryCols.zero) c := by
  have hk : i * NUM_SHA256_BINARY_COLS + c < NUM_SHA256_BINARY_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_SHA256_BINARY_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOfB, getcB]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cellsB r) _ _ _ hk,
    show (i * NUM_SHA256_BINARY_COLS + c) / NUM_SHA256_BINARY_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_SHA256_BINARY_COLS]), Nat.div_eq_of_lt hc, add_zero],
    show (i * NUM_SHA256_BINARY_COLS + c) % NUM_SHA256_BINARY_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem getcB_of_le (r : Sha256BinaryCols F) {c : ℕ} (hc : NUM_SHA256_BINARY_COLS ≤ c) : getcB r c = 0 := by
  rw [getcB, List.getD_eq_default _ _ (by rw [length_cellsB]; exact hc)]

theorem cur_matOfB [Inhabited F] (cb : Bool) (rows : List (Sha256BinaryCols F)) {i : ℕ}
    (hi : i < rows.length) :
    rowOf (rowEnv (instOf (binaryAir cb) (matOfB rows) []) i)
        (AirLayout.from_air (binaryAir (F := F) cb)) 0 = getcB (rows.getD i Sha256BinaryCols.zero) := by
  funext c
  simp only [rowOf, rowEnv, instOf, AirLayout.from_air, binaryAir]
  by_cases hc : c < NUM_SHA256_BINARY_COLS
  · rw [getD_map_range_of _ rfl hc, matOfB_cell rows hi hc]
  · simp [hc, getcB_of_le _ (Nat.le_of_not_lt hc)]

/-- Completeness in characteristic 2: on a power-of-two number of inputs, the generator's trace satisfies the AIR.

This holds with or without the booleanity. -/
theorem binary_complete [Inhabited F] [DecidableEq F] (h2 : (2 : F) = 0) (cb : Bool)
    {inputs : List (List p3_sha256_air.mirror.Word)}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints (binaryAir cb)) (instOf (binaryAir cb) M []) := by
  refine ⟨matOfB (inputs.map (finalB (F := F))), by simp [generate_eqB, h2, h], ?_⟩
  rw [satisfies_iff_rows]
  change ∀ i < (matOfB (inputs.map (finalB (F := F)))).height, _
  rw [matOfB_height]
  intro i hi
  apply (eval_iff_B cb _ _).mpr
  rw [cur_matOfB cb _ hi, List.getD_eq_getElem _ _ hi, List.getElem_map]
  exact gen_rowSpecB _ h2 cb

end Plonky3Lean.Proofs.Sha256Air.Binary
