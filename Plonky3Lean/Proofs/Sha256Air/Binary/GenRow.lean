module

public import Plonky3Lean.Proofs.Sha256Air.Binary.GenAdd

@[expose] public section

/-!
# The generated row of the characteristic-2 AIR

Every addition the generator performs gets the right number of words, so it never panics.

Its two loops compute the FIPS 180-4 schedule and rounds.

They store the carries of every addition but the last of each sum.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_sha256_air.mirror.binary Plonky3Lean.Spec.Sha256
open p3_sha256_air.mirror (kOf u32_to_bits_le BLOCK_WORDS)
open Plonky3Lean.Proofs.Sha256Air (Ws vs chA chE t1s Ws_lt Ws_ge vs_succ chain_vars)

variable {F : Type} [Field F]

/-- The carry words of the stored-carry additions of words, added from the left. -/
def carriesOf (ws : List p3_sha256_air.mirror.Word) : List (ℕ → F) :=
  (List.range (ws.length - 2)).map fun j =>
    let P := (ws.take (j + 1)).foldl (· + ·) 0
    carry_bits P (ws.getD (j + 1) 0) (P + ws.getD (j + 1) 0)

theorem awc2 (a b c d : p3_sha256_air.mirror.Word) :
    add_with_carries (F := F) 2 [a, b, c, d] = some (a + b + c + d, carriesOf [a, b, c, d]) := by
  simp [add_with_carries, carriesOf, List.range_succ, BitVec.zero_add]

theorem awc3 (a b c d e : p3_sha256_air.mirror.Word) :
    add_with_carries (F := F) 3 [a, b, c, d, e] = some (a + b + c + d + e, carriesOf [a, b, c, d, e]) := by
  simp [add_with_carries, carriesOf, List.range_succ, BitVec.zero_add]

theorem awc1 (a b c : p3_sha256_air.mirror.Word) :
    add_with_carries (F := F) 1 [a, b, c] = some (a + b + c, carriesOf [a, b, c]) := by
  simp [add_with_carries, carriesOf, List.range_succ, BitVec.zero_add]

theorem foldlM_some {α β : Type} {f : α → β → Option α} (g : α → β → α) (l : List β) (a : α)
    (h : ∀ a b, f a b = some (g a b)) : l.foldlM f a = some (l.foldl g a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [List.foldlM, h, ih]

end Plonky3Lean.Proofs.Sha256Air.Binary

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_sha256_air.mirror.binary Plonky3Lean.Spec.Sha256
open p3_sha256_air.mirror (kOf u32_to_bits_le BLOCK_WORDS)

variable {F : Type} [Field F]

/-- The schedule loop's body with its additions evaluated. -/
abbrev schedStepB (acc : Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word)) (i : ℕ) :
    Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) :=
  let t := BLOCK_WORDS + i
  let ws := [small_sigma1 (acc.2 (t - 2)), acc.2 (t - 7), small_sigma0 (acc.2 (t - 15)), acc.2 (t - 16)]
  let sc : Sha256BinaryScheduleCols F := ⟨fun j => (carriesOf (F := F) ws).getD j (fun _ => 0)⟩
  ({ acc.1 with schedule := Function.update acc.1.schedule i sc },
    Function.update acc.2 t (ws.getD 0 0 + ws.getD 1 0 + ws.getD 2 0 + ws.getD 3 0))

/-- The compression loop's body with its additions evaluated, reading the schedule from `w`. -/
abbrev roundStepB (w : ℕ → p3_sha256_air.mirror.Word)
    (acc : Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word))
    (t : ℕ) : Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word) :=
  let a := acc.2.1 (t + 3)
  let b := acc.2.1 (t + 2)
  let c := acc.2.1 (t + 1)
  let d := acc.2.1 t
  let e := acc.2.2 (t + 3)
  let f := acc.2.2 (t + 2)
  let g := acc.2.2 (t + 1)
  let h := acc.2.2 t
  let ch := (e &&& f) ^^^ (~~~e &&& g)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let ws1 := [h, big_sigma1 e, ch, BitVec.ofNat 32 (kOf t), w t]
  let t1 := h + big_sigma1 e + ch + BitVec.ofNat 32 (kOf t) + w t
  let ws2 := [t1, big_sigma0 a, mj]
  let round : Sha256BinaryRoundCols F :=
    ⟨u32_to_bits_le ch, u32_to_bits_le mj, fun j => (carriesOf (F := F) ws1).getD j (fun _ => 0),
      u32_to_bits_le t1, (carriesOf (F := F) ws2).getD 0 (fun _ => 0)⟩
  ({ acc.1 with rounds := Function.update acc.1.rounds t round },
    Function.update acc.2.1 (t + 4) (t1 + big_sigma0 a + mj), Function.update acc.2.2 (t + 4) (d + t1))

/-- The schedule loop's result. -/
def schedOutB (input : List p3_sha256_air.mirror.Word) :
    Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) :=
  List.foldl schedStepB (Sha256BinaryCols.zero, fun t => if t < BLOCK_WORDS then input.getD t 0 else 0)
    (List.range p3_sha256_air.mirror.SCHEDULE_EXTENSIONS)

/-- The `a` chain prefix: the chaining value in round-shift order. -/
def chainA (input : List p3_sha256_air.mirror.Word) : ℕ → p3_sha256_air.mirror.Word := fun k =>
  if k = 0 then input.getD (BLOCK_WORDS + 3) 0
  else if k = 1 then input.getD (BLOCK_WORDS + 2) 0
  else if k = 2 then input.getD (BLOCK_WORDS + 1) 0
  else if k = 3 then input.getD (BLOCK_WORDS + 0) 0 else 0

/-- The `e` chain prefix. -/
def chainE (input : List p3_sha256_air.mirror.Word) : ℕ → p3_sha256_air.mirror.Word := fun k =>
  if k = 0 then input.getD (BLOCK_WORDS + 7) 0
  else if k = 1 then input.getD (BLOCK_WORDS + 6) 0
  else if k = 2 then input.getD (BLOCK_WORDS + 5) 0
  else if k = 3 then input.getD (BLOCK_WORDS + 4) 0 else 0

/-- The compression loop's result. -/
def compOutB (input : List p3_sha256_air.mirror.Word) :
    Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word) :=
  List.foldl (roundStepB (schedOutB (F := F) input).2)
    ({ (schedOutB (F := F) input).1 with w := fun t => u32_to_bits_le ((schedOutB (F := F) input).2 t) },
      chainA input, chainE input)
    (List.range p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS)

/-- The generated row. -/
def finalB (input : List p3_sha256_air.mirror.Word) : Sha256BinaryCols F :=
  let C := compOutB (F := F) input
  { C.1 with
    a_chain := fun k => u32_to_bits_le (C.2.1 k)
    e_chain := fun k => u32_to_bits_le (C.2.2 k)
    h_out := fun i => u32_to_bits_le (input.getD (BLOCK_WORDS + i) 0 +
      (if i < 4 then C.2.1 else C.2.2) (p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS + 3 - i % 4)) }

/-- The generator never panics, and fills the row by its two loops. -/
theorem gen_eqB (input : List p3_sha256_air.mirror.Word) :
    generate_trace_row (Sha256BinaryCols.zero (T := F)) input = some (finalB input) := by
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
  simp only [Option.pure_def, Option.bind_some, finalB, compOutB, schedOutB]
  unfold chainA chainE
  rfl

/-! ## The loops compute the specification -/

section spec

variable (input : List p3_sha256_air.mirror.Word)

/-- The four words of schedule addition i, for word i + 16. -/
def schedWords (i : ℕ) : List p3_sha256_air.mirror.Word :=
  [smallSigma1 (Ws input (i + 14)), Ws input (i + 9), smallSigma0 (Ws input (i + 1)), Ws input i]

/-- The five words of T1 in round t. -/
def t1Words (t : ℕ) : List p3_sha256_air.mirror.Word :=
  let v := vs input t
  [v.h, bigSigma1 v.e, ch v.e v.f v.g, BitVec.ofNat 32 (kOf t), Ws input t]

/-- The three words of new a in round t. -/
def naWords (t : ℕ) : List p3_sha256_air.mirror.Word :=
  let v := vs input t
  [t1s input t, bigSigma0 v.a, maj v.a v.b v.c]

/-- The witness of round t. -/
def roundSpecB (t : ℕ) : Sha256BinaryRoundCols F :=
  let v := vs input t
  ⟨u32_to_bits_le (ch v.e v.f v.g), u32_to_bits_le (maj v.a v.b v.c),
    fun j => (carriesOf (F := F) (t1Words input t)).getD j (fun _ => 0), u32_to_bits_le (t1s input t),
    (carriesOf (F := F) (naWords input t)).getD 0 (fun _ => 0)⟩

end spec

/-- What the schedule loop has written after n words. -/
structure SchedInvB (input : List p3_sha256_air.mirror.Word) (n : ℕ)
    (acc : Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word)) : Prop where
  ww : ∀ t < 16 + n, acc.2 t = Ws input t
  sc : ∀ i < n, (acc.1.schedule i).carries = fun j => (carriesOf (F := F) (schedWords input i)).getD j (fun _ => 0)

theorem schedInvB_fold (input : List p3_sha256_air.mirror.Word) :
    ∀ n ≤ 48, SchedInvB (F := F) input n ((List.range n).foldl schedStepB
      (Sha256BinaryCols.zero, fun t => if t < BLOCK_WORDS then input.getD t 0 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨fun t ht => by simp [BLOCK_WORDS, show t < 16 by omega, Ws_lt input (show t < 16 by omega)],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨hw, hs⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (schedStepB (F := F)) _ = acc at hw hs
    have e := Ws_ge input (t := 16 + n) (by omega) (by omega)
    simp only [show 16 + n - 2 = n + 14 by omega, show 16 + n - 7 = n + 9 by omega,
      show 16 + n - 15 = n + 1 by omega, show 16 + n - 16 = n by omega] at e
    have h14 := hw (n + 14) (by omega)
    have h9 := hw (n + 9) (by omega)
    have h1 := hw (n + 1) (by omega)
    have h0 := hw n (by omega)
    obtain ⟨row, ww⟩ := acc
    dsimp only [schedStepB, BLOCK_WORDS]
    simp only [show 16 + n - 2 = n + 14 by omega, show 16 + n - 7 = n + 9 by omega,
      show 16 + n - 15 = n + 1 by omega, show 16 + n - 16 = n by omega]
    dsimp only at h14 h9 h1 h0 hw hs
    rw [h14, h9, h1, h0]
    refine ⟨fun t ht => ?_, fun i hi => ?_⟩ <;> dsimp only
    · by_cases h' : t = 16 + n
      · subst h'
        simp only [Function.update_self, e, List.getD_cons_zero, List.getD_cons_succ]
        rfl
      · rw [Function.update_of_ne h']; exact hw t (by omega)
    · by_cases h' : i = n
      · subst h'
        simp only [Function.update_self]
        rfl
      · rw [Function.update_of_ne h']; exact hs i (by omega)

/-- What the compression loop has written after n rounds. -/
structure CompInvB (input : List p3_sha256_air.mirror.Word) (n : ℕ) (r₀ : Sha256BinaryCols F)
    (acc : Sha256BinaryCols F × (ℕ → p3_sha256_air.mirror.Word) × (ℕ → p3_sha256_air.mirror.Word)) :
    Prop where
  a : ∀ k < n + 4, acc.2.1 k = chA input k
  e : ∀ k < n + 4, acc.2.2 k = chE input k
  rounds : ∀ t < n, acc.1.rounds t = roundSpecB input t
  w : acc.1.w = r₀.w
  sched : acc.1.schedule = r₀.schedule

theorem compInvB_fold (input : List p3_sha256_air.mirror.Word) {w : ℕ → p3_sha256_air.mirror.Word}
    (hw : ∀ t < 64, w t = Ws input t) (r₀ : Sha256BinaryCols F) :
    ∀ n ≤ 64, CompInvB input n r₀ ((List.range n).foldl (roundStepB w) (r₀, chainA input, chainE input)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩ <;>
      interval_cases k <;> rfl
  | succ n ih =>
    intro hn
    obtain ⟨ha, he, hr, hw', hs⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (roundStepB (F := F) w) _ = acc at ha he hr hw' hs
    obtain ⟨ca, cb, cc, cd, ce, cf, cg, ch'⟩ := chain_vars input n (by omega)
    obtain ⟨row, A, E⟩ := acc
    dsimp only at ha he hr hw' hs
    have e1 := vs_succ input (t := n) (by omega)
    dsimp only [roundStepB]
    rw [ha (n + 3) (by omega), ha (n + 2) (by omega), ha (n + 1) (by omega), ha n (by omega),
      he (n + 3) (by omega), he (n + 2) (by omega), he (n + 1) (by omega), he n (by omega),
      hw n (by omega), ca, cb, cc, cd, ce, cf, cg, ch']
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun t ht => ?_, hw', hs⟩ <;> dsimp only
    · by_cases h' : k = n + 4
      · subst h'
        simp only [Function.update_self, chA, show ¬ n + 4 < 4 by omega, ↓reduceIte,
          show n + 4 - 3 = n + 1 by omega, e1, round, BitVec.add_assoc]
        rfl
      · rw [Function.update_of_ne h']; exact ha k (by omega)
    · by_cases h' : k = n + 4
      · subst h'
        simp only [Function.update_self, chE, show ¬ n + 4 < 4 by omega, ↓reduceIte,
          show n + 4 - 3 = n + 1 by omega, e1, round]
        rfl
      · rw [Function.update_of_ne h']; exact he k (by omega)
    · by_cases h' : t = n
      · subst h'; simp only [Function.update_self]; rfl
      · rw [Function.update_of_ne h']; exact hr t (by omega)

/-- What the generator writes into a row, field by field. -/
structure GenSpecB (input : List p3_sha256_air.mirror.Word) (R : Sha256BinaryCols F) : Prop where
  w : ∀ t < 64, R.w t = u32_to_bits_le (Ws input t)
  sc : ∀ i < 48, (R.schedule i).carries = fun j => (carriesOf (F := F) (schedWords input i)).getD j (fun _ => 0)
  a : ∀ k < 68, R.a_chain k = u32_to_bits_le (chA input k)
  e : ∀ k < 68, R.e_chain k = u32_to_bits_le (chE input k)
  rounds : ∀ t < 64, R.rounds t = roundSpecB input t
  h_out : ∀ i < 8, R.h_out i = u32_to_bits_le (input.getD (16 + i) 0 + (vs input 64).toList.getD i 0)

theorem gen_specB (input : List p3_sha256_air.mirror.Word) : GenSpecB (F := F) input (finalB input) := by
  have hS : SchedInvB (F := F) input 48 (schedOutB input) := schedInvB_fold (F := F) input 48 le_rfl
  have hC : CompInvB input 64
      { (schedOutB (F := F) input).1 with w := fun t => u32_to_bits_le ((schedOutB (F := F) input).2 t) }
      (compOutB input) :=
    compInvB_fold input (w := (schedOutB (F := F) input).2) (fun t ht => hS.ww t (by omega)) _ 64 le_rfl
  obtain ⟨ca, cb, cc, cd, ce, cf, cg, ch'⟩ := chain_vars input 64 le_rfl
  refine ⟨fun t ht => ?_, fun i hi => ?_, fun k hk => ?_, fun k hk => ?_, fun t ht => ?_, fun i hi => ?_⟩
  · simp only [finalB]
    rw [hC.w]
    exact congrArg u32_to_bits_le (hS.ww t (by omega))
  · simp only [finalB]
    rw [hC.sched]
    exact hS.sc i hi
  · simp only [finalB]
    rw [hC.a k (by omega)]
  · simp only [finalB]
    rw [hC.e k (by omega)]
  · simp only [finalB]
    exact hC.rounds t ht
  · have key : (if i < 4 then (compOutB (F := F) input).2.1 else (compOutB (F := F) input).2.2)
        (p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS + 3 - i % 4) = (vs input 64).toList.getD i 0 := by
      simp only [p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS]
      interval_cases i
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.a _ (by norm_num)]; exact ca
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.a _ (by norm_num)]; exact cb
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.a _ (by norm_num)]; exact cc
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.a _ (by norm_num)]; exact cd
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.e _ (by norm_num)]; exact ce
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.e _ (by norm_num)]; exact cf
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.e _ (by norm_num)]; exact cg
      · simp only [Nat.reduceLT, ↓reduceIte]; rw [hC.e _ (by norm_num)]; exact ch'
    simp only [finalB]
    rw [key]
    rfl

end Plonky3Lean.Proofs.Sha256Air.Binary
