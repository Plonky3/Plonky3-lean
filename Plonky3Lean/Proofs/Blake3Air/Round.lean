module

public import Plonky3Lean.Proofs.Blake3Air.Quarter
public import Plonky3Lean.Spec.Blake3
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# A round of the compression function

The specification holds the 16-word state as a list and updates it in place.

Here a state is a map from the word index to the word.

The quarter round of the specification is two half rounds of the generator.

It writes the four words it mixes.

A trace state holds a state when its rows hold the state's words.

- Rows 0 and 2 hold words 0 to 3 and 8 to 11 as limbs.
- Rows 1 and 3 hold words 4 to 7 and 12 to 15 as bits.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

/-- The quarter round on the words a, b, c and d of a state, with message words mx and my. -/
def gF (σ : ℕ → Word) (a b c d : ℕ) (mx my : Word) : ℕ → Word :=
  let r := verifiable_half_round (σ a) (σ b) (σ c) (σ d) mx false
  let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 my true
  Function.update (Function.update (Function.update (Function.update σ a r'.1) b r'.2.1) c r'.2.2.1) d
    r'.2.2.2

/-- The four column quarter rounds. -/
def colsF (σ : ℕ → Word) (m : ℕ → Word) : ℕ → Word :=
  let σ := gF σ 0 4 8 12 (m 0) (m 1)
  let σ := gF σ 1 5 9 13 (m 2) (m 3)
  let σ := gF σ 2 6 10 14 (m 4) (m 5)
  gF σ 3 7 11 15 (m 6) (m 7)

/-- The four diagonal quarter rounds. -/
def diagsF (σ : ℕ → Word) (m : ℕ → Word) : ℕ → Word :=
  let σ := gF σ 0 5 10 15 (m 8) (m 9)
  let σ := gF σ 1 6 11 12 (m 10) (m 11)
  let σ := gF σ 2 7 8 13 (m 12) (m 13)
  gF σ 3 4 9 14 (m 14) (m 15)

/-- One round: the four columns, then the four diagonals. -/
def roundF (σ : ℕ → Word) (m : ℕ → Word) : ℕ → Word := diagsF (colsF σ m) m

/-! ## The specification's round, as a map -/

open Plonky3Lean.Spec.Blake3 in
/-- The specification's quarter round on distinct words of a 16-word state. -/
theorem g_getD (s : List (BitVec 32)) {a b c d : ℕ} (ha : a < s.length) (hb : b < s.length)
    (hc : c < s.length) (hd : d < s.length) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (mx my : BitVec 32) (i : ℕ) :
    (g s a b c d mx my).getD i 0 = gF (fun j => s.getD j 0) a b c d mx my i := by
  simp only [g, gF, verifiable_half_round, List.getD_eq_getElem?_getD, List.getElem?_set,
    List.length_set, Function.update_apply, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, hab.symm,
    hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, ite_true, ite_false, Option.getD_some]
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> subst_vars <;> simp_all

open Plonky3Lean.Spec.Blake3 in
theorem length_g' (s : List (BitVec 32)) (a b c d : ℕ) (mx my : BitVec 32) :
    (g s a b c d mx my).length = s.length := by
  simp [g]

open Plonky3Lean.Spec.Blake3 in
/-- The specification's round, read at word i, is the round on maps. -/
theorem round_getD (s m : List (BitVec 32)) (hs : s.length = 16) (i : ℕ) :
    (round s m).getD i 0 = roundF (fun j => s.getD j 0) (fun j => m.getD j 0) i := by
  simp (disch := first | decide | simp only [length_g', hs]; decide) only [round, g_getD]
  rfl

/-! ## A round of the trace -/

variable {F : Type} [Field F]

/-- A trace state holds a 16-word state. -/
def Rep (st : Blake3State F) (σ : ℕ → Word) : Prop :=
  ∀ j < 4, LimbsRep (st.row0 j) (σ j) ∧ BitsRep (st.row1 j) (σ (4 + j)) ∧
    LimbsRep (st.row2 j) (σ (8 + j)) ∧ BitsRep (st.row3 j) (σ (12 + j))

/-- Message limbs hold 16 message words. -/
def MRep (m : ℕ → ℕ → F) (μ : ℕ → Word) : Prop := ∀ i < 16, LimbsRep (m i) (μ i)

variable [DecidableEq F] (hp : 3 * 2 ^ 16 < ringChar F)
include hp

/-- The constraints of a round fix the state after its columns and the state after the round. -/
theorem round_sound {input : Blake3State F} {rd : FullRound F} {m : ℕ → ℕ → F} {σ μ : ℕ → Word}
    (hin : Rep input σ) (hm : MRep m μ)
    (hc : ∀ i ∈ List.range 4, QRC (full_round_to_column_quarter_round input rd m i))
    (hd : ∀ i ∈ List.range 4, QRC (full_round_to_diagonal_quarter_round rd m i)) :
    Rep rd.state_middle (colsF σ μ) ∧ Rep rd.state_output (roundF σ μ) := by
  have hcol : Rep rd.state_middle (colsF σ μ) := by
    intro j hj
    obtain ⟨h0, h1, h2, h3⟩ := hin j hj
    have := qrc_sound hp (t := full_round_to_column_quarter_round input rd m j) h0 h1 h2 h3
      (hm _ (by omega)) (hm _ (by omega)) (hc j (List.mem_range.mpr hj))
    interval_cases j <;>
      simpa [colsF, gF, Function.update_apply, full_round_to_column_quarter_round] using this
  refine ⟨hcol, ?_⟩
  have hD : ∀ j < 4, _ := fun j hj => qrc_sound hp (t := full_round_to_diagonal_quarter_round rd m j)
    (hcol j hj).1 (hcol ((j + 1) % 4) (Nat.mod_lt _ (by norm_num))).2.1
    (hcol ((j + 2) % 4) (Nat.mod_lt _ (by norm_num))).2.2.1
    (hcol ((j + 3) % 4) (Nat.mod_lt _ (by norm_num))).2.2.2 (hm _ (by omega)) (hm _ (by omega))
    (hd j (List.mem_range.mpr hj))
  have d0 := hD 0 (by norm_num)
  have d1 := hD 1 (by norm_num)
  have d2 := hD 2 (by norm_num)
  have d3 := hD 3 (by norm_num)
  simp only [full_round_to_diagonal_quarter_round, Nat.reduceAdd, Nat.reduceMod, Nat.reduceMul]
    at d0 d1 d2 d3
  intro w hw
  interval_cases w <;> simp only [roundF, diagsF, gF, Function.update_apply, Nat.reduceAdd,
    Nat.reduceEqDiff, ite_true, ite_false, OfNat.ofNat_ne_zero, zero_ne_one]
  · exact ⟨d0.1, d3.2.1, d2.2.2.1, d1.2.2.2⟩
  · exact ⟨d1.1, d0.2.1, d3.2.2.1, d2.2.2.2⟩
  · exact ⟨d2.1, d1.2.1, d0.2.2.1, d3.2.2.2⟩
  · exact ⟨d3.1, d2.2.1, d1.2.2.1, d0.2.2.2⟩

end Plonky3Lean.Proofs.Blake3Air
