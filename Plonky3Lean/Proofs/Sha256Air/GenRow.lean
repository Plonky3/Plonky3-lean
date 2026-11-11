module

public import Plonky3Lean.Proofs.Sha256Air.GenAdd
public import Plonky3Lean.Proofs.Sha256Air.Cells
public import Plonky3Lean.Proofs.Sha256Air.RowSound

@[expose] public section

/-!
# The generated row

The generator fills a row from one input: a block of 16 words, then a chaining value of 8 words.

Its two loops compute the FIPS 180-4 schedule and rounds.

```text
    w[t]          bits of W_t, the schedule word t
    a_chain[k]    bits of H_{3-k} for k < 4, then of a after round k - 4
    e_chain[k]    bits of H_{7-k} for k < 4, then of e after round k - 4
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_sha256_air.mirror Plonky3Lean.Spec.Sha256

variable {F : Type} [Field F]

section spec

variable (input : List (p3_sha256_air.mirror.Word))

/-- The block of an input: its first 16 words. -/
def blk : List (p3_sha256_air.mirror.Word) := (List.range 16).map fun i => input.getD i 0

/-- The chaining value of an input: its words 16 to 23. -/
def hv : List (p3_sha256_air.mirror.Word) := (List.range 8).map fun j => input.getD (16 + j) 0

/-- Schedule word t. -/
def Ws (t : ℕ) : p3_sha256_air.mirror.Word := (schedule (blk input)).getD t 0

/-- The working variables after t rounds. -/
def vs (t : ℕ) : Vars := rounds (schedule (blk input)) (Vars.ofList (hv input)) t

/-- Entry k of the `a` chain. -/
def chA (k : ℕ) : p3_sha256_air.mirror.Word := if k < 4 then input.getD (16 + (3 - k)) 0 else (vs input (k - 3)).a

/-- Entry k of the `e` chain. -/
def chE (k : ℕ) : p3_sha256_air.mirror.Word := if k < 4 then input.getD (16 + (7 - k)) 0 else (vs input (k - 3)).e

theorem length_blk : (blk input).length = 16 := by simp [blk]

end spec

/-! ## The schedule loop -/

/-- The schedule loop's body, as the generator writes it. -/
abbrev schedStep (acc : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word)) (t : ℕ) : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word) :=
  let (row, w_words) := acc
  let i := t - BLOCK_WORDS
  let w_m15 := w_words (t - 15)
  let w_m2 := w_words (t - 2)
  let w_m7 := w_words (t - 7)
  let w_m16 := w_words (t - 16)
  let s0 := w_m15.rotateRight 7 ^^^ w_m15.rotateRight 18 ^^^ w_m15 >>> 3
  let s1 := w_m2.rotateRight 17 ^^^ w_m2.rotateRight 19 ^^^ w_m2 >>> 10
  let tmp := s1 + w_m7
  let w_t := tmp + s0 + w_m16
  let w_words := Function.update w_words t w_t
  let row := { row with
    w := Function.update row.w t (u32_to_bits_le w_t)
    sched_sigma0 := Function.update row.sched_sigma0 i (limbsF s0)
    sched_sigma1 := Function.update row.sched_sigma1 i (limbsF s1)
    sched_tmp := Function.update row.sched_tmp i (limbsF tmp) }
  (row, w_words)

/-- What the schedule loop has written after the words below 16 + n. -/
structure SchedInv (input : List (p3_sha256_air.mirror.Word)) (n : ℕ) (r₀ : Sha256Cols F)
    (acc : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word)) : Prop where
  ww : ∀ t < 16 + n, acc.2 t = Ws input t
  w : ∀ t < 16 + n, acc.1.w t = u32_to_bits_le (Ws input t)
  s0 : ∀ i < n, acc.1.sched_sigma0 i = limbsF (smallSigma0 (Ws input (i + 1)))
  s1 : ∀ i < n, acc.1.sched_sigma1 i = limbsF (smallSigma1 (Ws input (i + 14)))
  tmp : ∀ i < n, acc.1.sched_tmp i = limbsF (smallSigma1 (Ws input (i + 14)) + Ws input (i + 9))
  h_in : acc.1.h_in = r₀.h_in

theorem Ws_lt (input : List (p3_sha256_air.mirror.Word)) {t : ℕ} (ht : t < 16) : Ws input t = input.getD t 0 := by
  rw [Ws, Proofs.Sha256.schedule_lt _ _ (length_blk input) ht]
  simp [blk, ht]

theorem Ws_ge (input : List (p3_sha256_air.mirror.Word)) {t : ℕ} (h16 : 16 ≤ t) (h64 : t < 64) :
    Ws input t = smallSigma1 (Ws input (t - 2)) + Ws input (t - 7) + smallSigma0 (Ws input (t - 15)) +
      Ws input (t - 16) :=
  Proofs.Sha256.schedule_ge _ _ (length_blk input) h16 h64

theorem schedInv_succ {input : List (p3_sha256_air.mirror.Word)} {r₀ : Sha256Cols F} {n : ℕ} (hn : n < 48)
    {acc : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word)} (h : SchedInv input n r₀ acc) :
    SchedInv input (n + 1) r₀ (schedStep acc (16 + n)) := by
  obtain ⟨row, ww⟩ := acc
  have e := Ws_ge input (t := 16 + n) (by omega) (by omega)
  simp only [show 16 + n - 2 = n + 14 by omega, show 16 + n - 7 = n + 9 by omega,
    show 16 + n - 15 = n + 1 by omega, show 16 + n - 16 = n by omega] at e
  have hw : ∀ t < 16 + n, ww t = Ws input t := h.ww
  simp only [schedStep, BLOCK_WORDS, show 16 + n - 16 = n by omega, show 16 + n - 2 = n + 14 by omega,
    show 16 + n - 7 = n + 9 by omega, show 16 + n - 15 = n + 1 by omega,
    hw (n + 14) (by omega), hw (n + 9) (by omega), hw (n + 1) (by omega), hw n (by omega)]
  constructor <;> dsimp only
  · intro t ht
    by_cases h' : t = 16 + n
    · subst h'; simp [e, smallSigma0, smallSigma1]
    · rw [Function.update_of_ne h']; exact h.ww t (by omega)
  · intro t ht
    by_cases h' : t = 16 + n
    · subst h'; simp [e, smallSigma0, smallSigma1]
    · rw [Function.update_of_ne h']; exact h.w t (by omega)
  · intro i hi
    by_cases h' : i = n
    · subst h'; simp [smallSigma0]
    · rw [Function.update_of_ne h']; exact h.s0 i (by omega)
  · intro i hi
    by_cases h' : i = n
    · subst h'; simp [smallSigma1]
    · rw [Function.update_of_ne h']; exact h.s1 i (by omega)
  · intro i hi
    by_cases h' : i = n
    · subst h'; simp [smallSigma1]
    · rw [Function.update_of_ne h']; exact h.tmp i (by omega)
  · exact h.h_in

theorem schedInv_fold {input : List (p3_sha256_air.mirror.Word)} {r₀ : Sha256Cols F}
    {acc : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word)} (h : SchedInv input 0 r₀ acc) :
    ∀ n ≤ 48, SchedInv input n r₀ ((List.range' 16 n).foldl schedStep acc) := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih =>
    intro hn
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]
    exact schedInv_succ (by omega) (ih (by omega))

/-! ## The compression loop -/

/-- The compression loop's body, as the generator writes it, reading schedule words from `w_words`. -/
abbrev roundStep (w_words : ℕ → p3_sha256_air.mirror.Word) (acc : Sha256Cols F × WorkVars) (t : ℕ) :
    Sha256Cols F × WorkVars :=
  let (row, v) := acc
  let sigma1_e := v.e.rotateRight 6 ^^^ v.e.rotateRight 11 ^^^ v.e.rotateRight 25
  let ch := (v.e &&& v.f) ^^^ (~~~v.e &&& v.g)
  let tmp1 := v.h + sigma1_e + ch
  let t1 := tmp1 + BitVec.ofNat 32 (kOf t) + w_words t
  let sigma0_a := v.a.rotateRight 2 ^^^ v.a.rotateRight 13 ^^^ v.a.rotateRight 22
  let maj := (v.a &&& v.b) ^^^ (v.a &&& v.c) ^^^ (v.b &&& v.c)
  let new_a := t1 + sigma0_a + maj
  let new_e := v.d + t1
  let round : Sha256RoundCols F :=
    ⟨limbsF sigma1_e, limbsF ch, limbsF tmp1, limbsF t1, limbsF sigma0_a, limbsF maj⟩
  let row := { row with
    rounds := Function.update row.rounds t round
    a_chain := Function.update row.a_chain (t + 4) (u32_to_bits_le new_a)
    e_chain := Function.update row.e_chain (t + 4) (u32_to_bits_le new_e) }
  (row, ⟨new_a, v.a, v.b, v.c, new_e, v.e, v.f, v.g⟩)

/-- The working variables as the generator holds them. -/
def toWV (v : Vars) : WorkVars := ⟨v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h⟩

/-- T1 of round t on the specification's working variables. -/
def t1s (input : List (p3_sha256_air.mirror.Word)) (t : ℕ) : p3_sha256_air.mirror.Word :=
  let v := vs input t
  v.h + bigSigma1 v.e + ch v.e v.f v.g + BitVec.ofNat 32 (kOf t) + Ws input t

/-- The packed intermediates of round t. -/
def roundSpec (input : List (p3_sha256_air.mirror.Word)) (t : ℕ) : Sha256RoundCols F :=
  let v := vs input t
  ⟨limbsF (bigSigma1 v.e), limbsF (ch v.e v.f v.g), limbsF (v.h + bigSigma1 v.e + ch v.e v.f v.g),
    limbsF (t1s input t), limbsF (bigSigma0 v.a), limbsF (maj v.a v.b v.c)⟩

/-- What the compression loop has written after n rounds. -/
structure CompInv (input : List (p3_sha256_air.mirror.Word)) (n : ℕ) (r₁ : Sha256Cols F)
    (acc : Sha256Cols F × WorkVars) : Prop where
  v : acc.2 = toWV (vs input n)
  rounds : ∀ t < n, acc.1.rounds t = roundSpec input t
  a : ∀ k < 4 + n, acc.1.a_chain k = u32_to_bits_le (chA input k)
  e : ∀ k < 4 + n, acc.1.e_chain k = u32_to_bits_le (chE input k)
  w : acc.1.w = r₁.w
  s0 : acc.1.sched_sigma0 = r₁.sched_sigma0
  s1 : acc.1.sched_sigma1 = r₁.sched_sigma1
  tmp : acc.1.sched_tmp = r₁.sched_tmp
  h_in : acc.1.h_in = r₁.h_in

theorem vs_succ (input : List (p3_sha256_air.mirror.Word)) {t : ℕ} (ht : t < 64) :
    vs input (t + 1) = round (vs input t) (BitVec.ofNat 32 (kOf t)) (Ws input t) := by
  rw [vs, Proofs.Sha256.rounds_succ, kOf_eq t ht]; rfl

theorem compInv_succ {input : List (p3_sha256_air.mirror.Word)} {r₁ : Sha256Cols F} {n : ℕ} (hn : n < 64)
    {ww : ℕ → p3_sha256_air.mirror.Word} (hww : ∀ t < 64, ww t = Ws input t) {acc : Sha256Cols F × WorkVars}
    (h : CompInv input n r₁ acc) : CompInv input (n + 1) r₁ (roundStep ww acc n) := by
  obtain ⟨row, v⟩ := acc
  have hv : v = toWV (vs input n) := h.v
  subst hv
  have e := vs_succ input hn
  simp only [roundStep, toWV, hww n hn]
  constructor <;> dsimp only
  · rw [e]; simp only [round, toWV, add_assoc, bigSigma0, bigSigma1, ch, maj]
  · intro t ht
    by_cases h' : t = n
    · subst h'; simp only [Function.update_self]; rfl
    · rw [Function.update_of_ne h']; exact h.rounds t (by omega)
  · intro k hk
    by_cases h' : k = n + 4
    · subst h'
      simp only [Function.update_self, chA, show ¬ n + 4 < 4 by omega, ↓reduceIte,
        show n + 4 - 3 = n + 1 by omega, e, round, add_assoc]
      rfl
    · rw [Function.update_of_ne h']; exact h.a k (by omega)
  · intro k hk
    by_cases h' : k = n + 4
    · subst h'
      simp only [Function.update_self, chE, show ¬ n + 4 < 4 by omega, ↓reduceIte,
        show n + 4 - 3 = n + 1 by omega, e, round]
      rfl
    · rw [Function.update_of_ne h']; exact h.e k (by omega)
  · exact h.w
  · exact h.s0
  · exact h.s1
  · exact h.tmp
  · exact h.h_in

theorem compInv_fold {input : List (p3_sha256_air.mirror.Word)} {r₁ : Sha256Cols F} {ww : ℕ → p3_sha256_air.mirror.Word}
    (hww : ∀ t < 64, ww t = Ws input t) {acc : Sha256Cols F × WorkVars}
    (h : CompInv input 0 r₁ acc) :
    ∀ n ≤ 64, CompInv input n r₁ ((List.range n).foldl (roundStep ww) acc) := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact compInv_succ (by omega) hww (ih (by omega))

/-! ## The whole row -/

/-- The row before the schedule loop: the chaining value as limbs, and the block as bits. -/
abbrev row1 (input : List (p3_sha256_air.mirror.Word)) : Sha256Cols F :=
  { (Sha256Cols.zero (T := F)) with
    h_in := fun i => limbsF (input.getD (BLOCK_WORDS + i) 0)
    w := fun t => if t < BLOCK_WORDS then u32_to_bits_le (input.getD t 0) else (Sha256Cols.zero (T := F)).w t }

/-- The schedule loop's result. -/
abbrev schedOut (input : List (p3_sha256_air.mirror.Word)) : Sha256Cols F × (ℕ → p3_sha256_air.mirror.Word) :=
  (List.range' BLOCK_WORDS SCHEDULE_EXTENSIONS).foldl schedStep
    (row1 input, fun t => if t < BLOCK_WORDS then input.getD t 0 else 0)

/-- The row before the compression loop: the chain prefixes written. -/
abbrev row2 (input : List (p3_sha256_air.mirror.Word)) : Sha256Cols F :=
  let row := (schedOut (F := F) input).1
  let h_in : ℕ → p3_sha256_air.mirror.Word := fun i => input.getD (BLOCK_WORDS + i) 0
  { row with
    a_chain := fun k => if k = 0 then u32_to_bits_le (h_in 3) else if k = 1 then u32_to_bits_le (h_in 2)
      else if k = 2 then u32_to_bits_le (h_in 1) else if k = 3 then u32_to_bits_le (h_in 0)
      else row.a_chain k
    e_chain := fun k => if k = 0 then u32_to_bits_le (h_in 7) else if k = 1 then u32_to_bits_le (h_in 6)
      else if k = 2 then u32_to_bits_le (h_in 5) else if k = 3 then u32_to_bits_le (h_in 4)
      else row.e_chain k }

/-- The compression loop's result. -/
abbrev compOut (input : List (p3_sha256_air.mirror.Word)) : Sha256Cols F × WorkVars :=
  let h_in : ℕ → p3_sha256_air.mirror.Word := fun i => input.getD (BLOCK_WORDS + i) 0
  (List.range NUM_COMPRESSION_ROUNDS).foldl (roundStep (schedOut (F := F) input).2)
    (row2 input, ⟨h_in 0, h_in 1, h_in 2, h_in 3, h_in 4, h_in 5, h_in 6, h_in 7⟩)

/-- The final state's word i, as the generator reads it. -/
def finalOf (v : WorkVars) : ℕ → p3_sha256_air.mirror.Word
  | 0 => v.a | 1 => v.b | 2 => v.c | 3 => v.d | 4 => v.e | 5 => v.f | 6 => v.g | _ => v.h

/-- What the generator writes into a row, field by field. -/
structure GenSpec (input : List (p3_sha256_air.mirror.Word)) (R : Sha256Cols F) : Prop where
  h_in : ∀ i, R.h_in i = limbsF (input.getD (16 + i) 0)
  w : ∀ t < 64, R.w t = u32_to_bits_le (Ws input t)
  s0 : ∀ i < 48, R.sched_sigma0 i = limbsF (smallSigma0 (Ws input (i + 1)))
  s1 : ∀ i < 48, R.sched_sigma1 i = limbsF (smallSigma1 (Ws input (i + 14)))
  tmp : ∀ i < 48, R.sched_tmp i = limbsF (smallSigma1 (Ws input (i + 14)) + Ws input (i + 9))
  a : ∀ k < 68, R.a_chain k = u32_to_bits_le (chA input k)
  e : ∀ k < 68, R.e_chain k = u32_to_bits_le (chE input k)
  rounds : ∀ t < 64, R.rounds t = roundSpec input t
  h_out : ∀ i < 8, R.h_out i = u32_to_bits_le (input.getD (16 + i) 0 + (vs input 64).toList.getD i 0)

theorem gen_spec (input : List (p3_sha256_air.mirror.Word)) :
    GenSpec input (generate_trace_row_for_compression (Sha256Cols.zero (T := F)) input) := by
  have h0 : SchedInv input 0 (row1 (F := F) input)
      (row1 input, fun t => if t < BLOCK_WORDS then input.getD t 0 else 0) :=
    ⟨fun t ht => by simp [BLOCK_WORDS, show t < 16 by omega, Ws_lt input (show t < 16 by omega)],
      fun t ht => by simp [BLOCK_WORDS, show t < 16 by omega, Ws_lt input (show t < 16 by omega)],
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  have hS : SchedInv input 48 (row1 (F := F) input) (schedOut input) := schedInv_fold h0 48 le_rfl
  have hv0 : ∀ j < 8, (hv input).getD j 0 = input.getD (16 + j) 0 := fun j hj => by simp [hv, hj]
  have hC0 : CompInv input 0 (schedOut (F := F) input).1
      (row2 input, ⟨input.getD (BLOCK_WORDS + 0) 0, input.getD (BLOCK_WORDS + 1) 0,
        input.getD (BLOCK_WORDS + 2) 0, input.getD (BLOCK_WORDS + 3) 0, input.getD (BLOCK_WORDS + 4) 0,
        input.getD (BLOCK_WORDS + 5) 0, input.getD (BLOCK_WORDS + 6) 0,
        input.getD (BLOCK_WORDS + 7) 0⟩) := by
    refine ⟨?_, fun _ h => absurd h (Nat.not_lt_zero _), fun k hk => ?_, fun k hk => ?_, rfl, rfl, rfl,
      rfl, rfl⟩
    · simp only [toWV, vs, rounds, List.range_zero, List.foldl_nil, Vars.ofList,
        hv0 0 (by omega), hv0 1 (by omega), hv0 2 (by omega), hv0 3 (by omega), hv0 4 (by omega),
        hv0 5 (by omega), hv0 6 (by omega), hv0 7 (by omega), BLOCK_WORDS]
    · interval_cases k <;> rfl
    · interval_cases k <;> rfl
  have hC : CompInv input 64 (schedOut (F := F) input).1 (compOut (F := F) input) :=
    compInv_fold (fun t ht => hS.ww t (by omega)) hC0 64 le_rfl
  unfold generate_trace_row_for_compression
  dsimp only
  dsimp only [schedOut, row1, row2, compOut] at hS hC
  delta schedStep roundStep at hS hC
  dsimp only at hS hC
  refine ⟨fun i => ?_, fun t ht => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun k hk => ?_, fun k hk => ?_, fun t ht => ?_, fun i hi => ?_⟩
  · rw [hC.h_in, hS.h_in]; rfl
  · rw [hC.w]; exact hS.w t (by omega)
  · rw [hC.s0]; exact hS.s0 i hi
  · rw [hC.s1]; exact hS.s1 i hi
  · rw [hC.tmp]; exact hS.tmp i hi
  · dsimp only; exact hC.a k hk
  · dsimp only; exact hC.e k hk
  · dsimp only; exact hC.rounds t ht
  · dsimp only
    rw [hC.v]
    interval_cases i <;> rfl

end Plonky3Lean.Proofs.Sha256Air
