module

public import Plonky3Lean.Proofs.Sha256Air.Binary.Words
public import Plonky3Lean.Proofs.KeccakAir.Sound

@[expose] public section

/-!
# One row of the characteristic-2 AIR computes the compression function

Let a row meet its constraints in characteristic 2, with its input cells bits.

Then every other cell is a bit.

The output words are the FIPS 180-4 compression of the input chaining value and block.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_sha256_air.mirror.binary Plonky3Lean.Spec.Sha256
open p3_sha256_air.mirror (kOf u32_to_bits_le)
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds wordOf holds_wordOf Ws vs chA chE hv blk t1s Ws_lt Ws_ge
  vs_succ chain_vars holds_bits)

variable {F : Type} [Field F] [DecidableEq F]

/-- The input a row holds: the block from the schedule, then the chaining value from the chains. -/
def inputOf (loc : ℕ → F) : List p3_sha256_air.mirror.Word :=
  (List.range 16).map (fun t => wordOf fun b => loc (col.w t b)) ++
    [wordOf fun b => loc (col.a_chain 3 b), wordOf fun b => loc (col.a_chain 2 b),
      wordOf fun b => loc (col.a_chain 1 b), wordOf fun b => loc (col.a_chain 0 b),
      wordOf fun b => loc (col.e_chain 3 b), wordOf fun b => loc (col.e_chain 2 b),
      wordOf fun b => loc (col.e_chain 1 b), wordOf fun b => loc (col.e_chain 0 b)]

theorem add_many_holds0 (h2 : (2 : F) = 0) {s : Prop} {ws cs : List (ℕ → F)} {sum : ℕ → F}
    {Ws : List (BitVec 32)} (hw : List.Forall₂ Holds ws Ws) (hlen : ws.length = cs.length + 2)
    (h : add_many (pb0 (F := F)) s ws cs sum) : s ∧ Holds sum (sumW Ws) :=
  add_many_holds (fun _ => 0) {} h2 hw hlen h

theorem inputOf_lt (loc : ℕ → F) {t : ℕ} (ht : t < 16) :
    (inputOf loc).getD t 0 = wordOf fun b => loc (col.w t b) := by
  rw [inputOf, List.getD_append _ _ _ _ (by simpa using ht)]
  simp [ht]

theorem inputOf_ge (loc : ℕ → F) {j : ℕ} (hj : j < 8) :
    (inputOf loc).getD (16 + j) 0 = if j < 4 then wordOf (fun b => loc (col.a_chain (3 - j) b))
      else wordOf (fun b => loc (col.e_chain (7 - j) b)) := by
  rw [inputOf, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  interval_cases j <;> rfl

section row

variable (h2 : (2 : F) = 0) {loc : ℕ → F} {cb : Bool} (h : RowSpecB loc cb)
  (hin : (∀ k < 4, ∀ b < 32, loc (col.a_chain k b) * (loc (col.a_chain k b) - 1) = 0) ∧
    (∀ k < 4, ∀ b < 32, loc (col.e_chain k b) * (loc (col.e_chain k b) - 1) = 0) ∧
    (∀ t < 16, ∀ b < 32, loc (col.w t b) * (loc (col.w t b) - 1) = 0))
include h2 h hin

theorem holds_sched : ∀ t < 64, Holds (fun b => loc (col.w t b)) (Ws (inputOf loc) t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.lt_or_ge t 16 with h16 | h16
    · rw [Ws_lt _ h16, inputOf_lt loc h16]
      exact holds_wordOf (hin.2.2 t h16)
    · obtain ⟨i, rfl⟩ : ∃ i, t = 16 + i := ⟨t - 16, by omega⟩
      have hs := h.sched i (by omega)
      rw [Ws_ge _ (by omega) ht]
      have w2 := ih (16 + i - 2) (by omega) (by omega)
      have w7 := ih (16 + i - 7) (by omega) (by omega)
      have w15 := ih (16 + i - 15) (by omega) (by omega)
      have w16 := ih (16 + i - 16) (by omega) (by omega)
      have key := (add_many_holds0 h2
        (.cons (holds_shift h2 w2 (by norm_num) (by norm_num)) (.cons w7
          (.cons (holds_shift h2 w15 (by norm_num) (by norm_num)) (.cons w16 .nil)))) (by simp) hs).2
      exact key

theorem holds_chain : ∀ t ≤ 64, ∀ k < t + 4,
    Holds (fun b => loc (col.a_chain k b)) (chA (inputOf loc) k) ∧
      Holds (fun b => loc (col.e_chain k b)) (chE (inputOf loc) k) := by
  intro t
  induction t with
  | zero =>
    intro _ k hk
    have ea : chA (inputOf loc) k = wordOf fun b => loc (col.a_chain k b) := by
      simp only [chA, hk, ↓reduceIte, inputOf_ge loc (show 3 - k < 8 by omega),
        show 3 - k < 4 by omega, show 3 - (3 - k) = k by omega]
    have ee : chE (inputOf loc) k = wordOf fun b => loc (col.e_chain k b) := by
      simp only [chE, hk, ↓reduceIte, inputOf_ge loc (show 7 - k < 8 by omega),
        show ¬ 7 - k < 4 by omega, show 7 - (7 - k) = k by omega]
    rw [ea, ee]
    exact ⟨holds_wordOf (hin.1 k hk), holds_wordOf (hin.2.1 k hk)⟩
  | succ t ih =>
    intro ht k hk
    rcases Nat.lt_or_ge k (t + 4) with hk' | hk'
    · exact ih (by omega) k hk'
    obtain rfl : k = t + 4 := by omega
    have hi := ih (by omega)
    obtain ⟨ca, cb', cc, cd, ce, cf, cg, ch'⟩ := chain_vars (inputOf loc) t (by omega)
    have a3 := (hi (t + 3) (by omega)).1; rw [ca] at a3
    have a2 := (hi (t + 2) (by omega)).1; rw [cb'] at a2
    have a1 := (hi (t + 1) (by omega)).1; rw [cc] at a1
    have a0 := (hi t (by omega)).1; rw [cd] at a0
    have e3 := (hi (t + 3) (by omega)).2; rw [ce] at e3
    have e2 := (hi (t + 2) (by omega)).2; rw [cf] at e2
    have e1 := (hi (t + 1) (by omega)).2; rw [cg] at e1
    have e0 := (hi t (by omega)).2; rw [ch'] at e0
    have hch := holds_ch h2 e3 e2 e1 (h.ch t (by omega))
    have hmj := holds_maj h2 a3 a2 a1 (h.maj t (by omega))
    have hk : Holds (F := F) (fun i => u32_to_bits_le (BitVec.ofNat 32 (kOf t)) i) (BitVec.ofNat 32 (kOf t)) :=
      holds_bits fun _ _ => rfl
    have ht1 := (add_many_holds0 h2 (.cons e0 (.cons (holds_rot h2 e3 (by norm_num) (by norm_num)
      (by norm_num)) (.cons hch (.cons hk (.cons (holds_sched h2 h hin t (by omega)) .nil)))))
      (by simp) (h.t1 t (by omega))).2
    have hne := (add_many_holds0 h2 (.cons a0 (.cons ht1 .nil)) (by simp) (h.new_e t (by omega))).2
    have hna := (add_many_holds0 h2 (.cons ht1 (.cons (holds_rot h2 a3 (by norm_num) (by norm_num)
      (by norm_num)) (.cons hmj .nil))) (by simp) (h.new_a t (by omega))).2
    have va : chA (inputOf loc) (t + 4) = sumW [t1s (inputOf loc) t, bigSigma0 (vs (inputOf loc) t).a,
        maj (vs (inputOf loc) t).a (vs (inputOf loc) t).b (vs (inputOf loc) t).c] := by
      simp only [chA, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega,
        vs_succ _ (show t < 64 by omega), round, sumW, List.foldl, BitVec.add_assoc, t1s]
    have ve : chE (inputOf loc) (t + 4) = sumW [(vs (inputOf loc) t).d, t1s (inputOf loc) t] := by
      simp only [chE, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega,
        vs_succ _ (show t < 64 by omega), round, sumW, List.foldl, t1s]
    have vt : t1s (inputOf loc) t = sumW [(vs (inputOf loc) t).h, bigSigma1 (vs (inputOf loc) t).e,
        ch (vs (inputOf loc) t).e (vs (inputOf loc) t).f (vs (inputOf loc) t).g,
        BitVec.ofNat 32 (kOf t), Ws (inputOf loc) t] := rfl
    rw [va, ve, vt]
    exact ⟨hna, hne⟩

omit h2 h hin in
theorem compress_getD (input : List p3_sha256_air.mirror.Word) {j : ℕ} (hj : j < 8) :
    (compress (hv input) (blk input)).getD j 0 =
      input.getD (16 + j) 0 + (vs input 64).toList.getD j 0 := by
  rw [compress, show rounds (schedule (blk input)) (Vars.ofList (hv input)) 64 = vs input 64 from rfl]
  generalize vs input 64 = V
  interval_cases j <;> rfl

/-- The output words are the compression of the row's chaining value and block. -/
theorem holds_out : ∀ j < 8, Holds (fun b => loc (col.h_out j b))
    ((compress (hv (inputOf loc)) (blk (inputOf loc))).getD j 0) := by
  intro j hj
  have hc := holds_chain h2 h hin 64 le_rfl
  obtain ⟨ca, cb', cc, cd, ce, cf, cg, ch'⟩ := chain_vars (inputOf loc) 64 le_rfl
  rw [compress_getD _ hj]
  rcases Nat.lt_or_ge j 4 with h4 | h4
  · have e1 : chA (inputOf loc) (3 - j) = (inputOf loc).getD (16 + j) 0 := by
      simp only [chA, show 3 - j < 4 by omega, ↓reduceIte, show 3 - (3 - j) = j by omega]
    have e2 : chA (inputOf loc) (67 - j) = (vs (inputOf loc) 64).toList.getD j 0 := by
      interval_cases j
      · exact ca
      · exact cb'
      · exact cc
      · exact cd
    have := (add_many_holds0 h2 (.cons (hc (3 - j) (by omega)).1 (.cons (hc (67 - j) (by omega)).1 .nil))
      (by simp) (h.out_a j h4)).2
    rw [e1, e2] at this
    exact this
  · obtain ⟨i, rfl⟩ : ∃ i, j = 4 + i := ⟨j - 4, by omega⟩
    have hi4 : i < 4 := by omega
    have e1 : chE (inputOf loc) (3 - i) = (inputOf loc).getD (16 + (4 + i)) 0 := by
      simp only [chE, show 3 - i < 4 by omega, ↓reduceIte, show 7 - (3 - i) = 4 + i by omega]
    have e2 : chE (inputOf loc) (67 - i) = (vs (inputOf loc) 64).toList.getD (4 + i) 0 := by
      interval_cases i
      · exact ce
      · exact cf
      · exact cg
      · exact ch'
    have := (add_many_holds0 h2 (.cons (hc (3 - i) (by omega)).2 (.cons (hc (67 - i) (by omega)).2 .nil))
      (by simp) (h.out_e i (by omega))).2
    rw [e1, e2] at this
    exact this

end row

end Plonky3Lean.Proofs.Sha256Air.Binary

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror.binary Plonky3Lean.Spec.Air
open Plonky3Lean.Spec.Sha256 Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (rowOf satisfies_iff_rows bitF rowOf_getD)
open Plonky3Lean.Proofs.Sha256Air (binaryAir Holds hv blk wordOf holds_wordOf)

variable {F : Type} [Field F] [DecidableEq F]

/-- Row i of a trace, as the row builder of the characteristic-2 AIR reads it. -/
def curB (cb : Bool) (T : Instance F) (i : ℕ) : ℕ → F :=
  rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0

theorem curB_eq (cb : Bool) (T : Instance F) (i : ℕ) {c : ℕ} (hc : c < NUM_SHA256_BINARY_COLS) :
    curB cb T i c = T.main i c :=
  rowOf_getD _ _ 0 hc

/-- The input cells of row i are bits. -/
def InputBits (T : Instance F) (i : ℕ) : Prop :=
  (∀ k < 4, ∀ b < 32, T.main i (col.a_chain k b) = 0 ∨ T.main i (col.a_chain k b) = 1) ∧
  (∀ k < 4, ∀ b < 32, T.main i (col.e_chain k b) = 0 ∨ T.main i (col.e_chain k b) = 1) ∧
  (∀ t < 16, ∀ b < 32, T.main i (col.w t b) = 0 ∨ T.main i (col.w t b) = 1)

theorem bool_of_or {x : F} (h : x = 0 ∨ x = 1) : x * (x - 1) = 0 := by
  rcases h with h | h <;> simp [h]

/-- Soundness in characteristic 2: a row of a satisfying trace computes one compression.

Its input cells must be bits.

- the chains start with a chaining value H, as bits
- the first schedule words hold a block M, as bits
- the output columns hold the bits of the compression of H and M

With the booleanity stated, the input cells are bits by the constraints. -/
theorem binary_sound (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (binaryAir cb)) T) {i : ℕ} (hrow : i < T.height)
    (hbits : cb = true ∨ InputBits T i) :
    ∃ H M : List (BitVec 32), H.length = 8 ∧ M.length = 16 ∧
      (∀ j < 4, ∀ b < 32, T.main i (col.a_chain (3 - j) b) = bitF ((H.getD j 0).getLsbD b)) ∧
      (∀ j < 4, ∀ b < 32, T.main i (col.e_chain (3 - j) b) = bitF ((H.getD (4 + j) 0).getLsbD b)) ∧
      (∀ t < 16, ∀ b < 32, T.main i (col.w t b) = bitF ((M.getD t 0).getLsbD b)) ∧
      (∀ j < 8, ∀ b < 32, T.main i (col.h_out j b) = bitF (((compress H M).getD j 0).getLsbD b)) := by
  have h := (eval_iff_B cb _ _).mp ((satisfies_iff_rows (binaryAir cb) T).mp hT i hrow)
  have hc : ∀ c < NUM_SHA256_BINARY_COLS, rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0 c =
      T.main i c := fun c hc => curB_eq cb T i hc
  have hin : (∀ k < 4, ∀ b < 32, rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.a_chain k b) * (rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.a_chain k b) - 1) = 0) ∧
      (∀ k < 4, ∀ b < 32, rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.e_chain k b) * (rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.e_chain k b) - 1) = 0) ∧
      (∀ t < 16, ∀ b < 32, rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.w t b) * (rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
        (col.w t b) - 1) = 0) := by
    rcases hbits with hcb | ⟨ha, he, hw⟩
    · exact h.bool hcb
    · refine ⟨fun k hk b hb => ?_, fun k hk b hb => ?_, fun t ht b hb => ?_⟩
      · rw [hc _ (by simp [col.a_chain, NUM_SHA256_BINARY_COLS]; omega)]; exact bool_of_or (ha k hk b hb)
      · rw [hc _ (by simp [col.e_chain, NUM_SHA256_BINARY_COLS]; omega)]; exact bool_of_or (he k hk b hb)
      · rw [hc _ (by simp [col.w, NUM_SHA256_BINARY_COLS]; omega)]; exact bool_of_or (hw t ht b hb)
  set loc := rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0
  have hch := holds_chain h2 h hin 0 (by omega)
  refine ⟨hv (inputOf loc), blk (inputOf loc), by simp [hv], by simp [blk], fun j hj b hb => ?_,
    fun j hj b hb => ?_, fun t ht b hb => ?_, fun j hj b hb => ?_⟩
  · rw [← hc _ (by simp [col.a_chain, NUM_SHA256_BINARY_COLS]; omega)]
    refine ((hch (3 - j) (by omega)).1 b hb).trans ?_
    simp only [Plonky3Lean.Proofs.Sha256Air.chA, show 3 - j < 4 by omega, ↓reduceIte,
      show 3 - (3 - j) = j by omega, hv]
    simp [show j < 8 by omega]
  · rw [← hc _ (by simp [col.e_chain, NUM_SHA256_BINARY_COLS]; omega)]
    refine ((hch (3 - j) (by omega)).2 b hb).trans ?_
    simp only [Plonky3Lean.Proofs.Sha256Air.chE, show 3 - j < 4 by omega, ↓reduceIte,
      show 7 - (3 - j) = 4 + j by omega, hv]
    simp [show 4 + j < 8 by omega]
  · rw [← hc _ (by simp [col.w, NUM_SHA256_BINARY_COLS]; omega)]
    refine (holds_sched h2 h hin t (by omega) b hb).trans ?_
    rw [Plonky3Lean.Proofs.Sha256Air.Ws_lt _ ht]
    simp [blk, ht]
  · rw [← hc _ (by simp [col.h_out, NUM_SHA256_BINARY_COLS]; omega)]
    exact holds_out h2 h hin j hj b hb

end Plonky3Lean.Proofs.Sha256Air.Binary
