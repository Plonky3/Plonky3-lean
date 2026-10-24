module

public import Plonky3Lean.Proofs.Blake3Air.Cells
public import Plonky3Lean.Proofs.Blake3Air.Round

@[expose] public section

/-!
# The generator's words

The generator writes a word as its 32 bits, or as its two 16-bit limbs.

Its half rounds on the columns, or on the diagonals, touch each word once.

So word i of a column half round is the generator's half quarter round on column i.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

theorem u32_bits_eq (w : Word) {i : ℕ} (hi : i < 32) : (u32_to_bits_le w i : F) = bitF (w.getLsbD i) := by
  unfold u32_to_bits_le
  have : (w &&& 1#32 <<< i ≠ 0) ↔ w.getLsbD i = true := by
    constructor
    · intro h
      by_contra hb
      apply h
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
      by_cases hki : k = i
      · subst hki; simp_all
      · simp; omega
    · intro h h0
      have := congrArg (fun v => v.getLsbD i) h0
      rw [BitVec.getLsbD_eq_getElem hi] at h
      simp [hi] at this
      simp_all
  by_cases hb : w.getLsbD i <;> simp_all [bitF]

theorem bitsRep_u32 (w : Word) : BitsRep (u32_to_bits_le w : ℕ → F) w := fun _ hk => u32_bits_eq w hk

theorem limbsRep_save (w : Word) :
    LimbsRep (fun l => if l = 0 then (lowLimb w : F) else highLimb w) w := by
  refine ⟨by simp [lowLimb], ?_⟩
  simp only [one_ne_zero, ite_false, highLimb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  congr 1
  have := w.isLt
  omega

/-- A trace state holds a generator state: rows 0 and 2 as limbs, rows 1 and 3 as bits. -/
def GRep (st : Blake3State F) (σ : WState) : Prop :=
  ∀ j < 4, LimbsRep (st.row0 j) (σ 0 j) ∧ BitsRep (st.row1 j) (σ 1 j) ∧ LimbsRep (st.row2 j) (σ 2 j) ∧
    BitsRep (st.row3 j) (σ 3 j)

theorem gRep_save (σ : WState) : GRep (save_state_to_trace (F := F) σ) σ :=
  fun _ _ => ⟨limbsRep_save _, bitsRep_u32 _, limbsRep_save _, bitsRep_u32 _⟩

/-! ## The half rounds -/

section half

variable (σ : WState) (m : ℕ → Word) (fl : Bool) (off : ℕ)

/-- Word i of a column half round is the half quarter round on column i. -/
theorem halfRounds_col {i : ℕ} (hi : i < 4) :
    let r := verifiable_half_round (σ 0 i) (σ 1 i) (σ 2 i) (σ 3 i) (m (off + 2 * i)) fl
    halfRounds σ m false fl off 0 i = r.1 ∧ halfRounds σ m false fl off 1 i = r.2.1 ∧
      halfRounds σ m false fl off 2 i = r.2.2.1 ∧ halfRounds σ m false fl off 3 i = r.2.2.2 := by
  interval_cases i <;> simp [halfRounds, setWords, List.range_succ]

/-- A diagonal half round writes diagonal i with the half quarter round on that diagonal. -/
theorem halfRounds_diag {i : ℕ} (hi : i < 4) :
    let r := verifiable_half_round (σ 0 i) (σ 1 ((i + 1) % 4)) (σ 2 ((i + 2) % 4)) (σ 3 ((i + 3) % 4))
      (m (off + 2 * i)) fl
    halfRounds σ m true fl off 0 i = r.1 ∧ halfRounds σ m true fl off 1 ((i + 1) % 4) = r.2.1 ∧
      halfRounds σ m true fl off 2 ((i + 2) % 4) = r.2.2.1 ∧
      halfRounds σ m true fl off 3 ((i + 3) % 4) = r.2.2.2 := by
  interval_cases i <;> simp [halfRounds, setWords, List.range_succ]

end half

/-! ## A generated round satisfies its constraints -/

variable [DecidableEq F]

/-- A round whose four trace states hold the generator's four states satisfies its constraints, in every field. -/
theorem round_complete {input : Blake3State F} {rd : FullRound F} {mv : ℕ → ℕ → F} {σ : WState}
    {m : ℕ → Word} (hin : GRep input σ) (hm : ∀ i < 16, LimbsRep (mv i) (m i))
    (h1 : GRep rd.state_prime (halfRounds σ m false false 0))
    (h2 : GRep rd.state_middle (halfRounds (halfRounds σ m false false 0) m false true 1))
    (h3 : GRep rd.state_middle_prime
      (halfRounds (halfRounds (halfRounds σ m false false 0) m false true 1) m true false 8))
    (h4 : GRep rd.state_output (halfRounds (halfRounds (halfRounds (halfRounds σ m false false 0) m
      false true 1) m true false 8) m true true 9)) :
    (∀ i ∈ List.range 4, QRC (full_round_to_column_quarter_round input rd mv i)) ∧
      ∀ i ∈ List.range 4, QRC (full_round_to_diagonal_quarter_round rd mv i) := by
  constructor
  · intro i hi
    rw [List.mem_range] at hi
    obtain ⟨a, b, c, d⟩ := hin i hi
    obtain ⟨a1, b1, c1, d1⟩ := h1 i hi
    obtain ⟨a2, b2, c2, d2⟩ := h2 i hi
    obtain ⟨e1, f1, g1, k1⟩ := halfRounds_col σ m false 0 hi
    obtain ⟨e2, f2, g2, k2⟩ := halfRounds_col (halfRounds σ m false false 0) m true 1 hi
    simp only [Nat.zero_add] at e1 f1 g1 k1
    rw [show 1 + 2 * i = 2 * i + 1 by omega] at e2 f2 g2 k2
    simp only [e1, f1, g1, k1, e2, f2, g2, k2] at a1 b1 c1 d1 a2 b2 c2 d2
    exact qrc_complete a b c d (hm _ (by omega)) (hm _ (by omega)) ⟨a1, b1, c1, d1⟩ ⟨a2, b2, c2, d2⟩
  · intro i hi
    rw [List.mem_range] at hi
    have m1 := Nat.mod_lt (i + 1) (show 0 < 4 by norm_num)
    have m2 := Nat.mod_lt (i + 2) (show 0 < 4 by norm_num)
    have m3 := Nat.mod_lt (i + 3) (show 0 < 4 by norm_num)
    have a := (h2 i hi).1
    have b := (h2 _ m1).2.1
    have c := (h2 _ m2).2.2.1
    have d := (h2 _ m3).2.2.2
    have a1 := (h3 i hi).1
    have b1 := (h3 _ m1).2.1
    have c1 := (h3 _ m2).2.2.1
    have d1 := (h3 _ m3).2.2.2
    have a2 := (h4 i hi).1
    have b2 := (h4 _ m1).2.1
    have c2 := (h4 _ m2).2.2.1
    have d2 := (h4 _ m3).2.2.2
    obtain ⟨e1, f1, g1, k1⟩ := halfRounds_diag (halfRounds (halfRounds σ m false false 0) m false true 1)
      m false 8 hi
    obtain ⟨e2, f2, g2, k2⟩ := halfRounds_diag (halfRounds (halfRounds (halfRounds σ m false false 0) m
      false true 1) m true false 8) m true 9 hi
    rw [show 8 + 2 * i = 2 * i + 8 by omega] at e1 f1 g1 k1
    rw [show 9 + 2 * i = 2 * i + 9 by omega] at e2 f2 g2 k2
    simp only [e1, f1, g1, k1, e2, f2, g2, k2] at a1 b1 c1 d1 a2 b2 c2 d2
    exact qrc_complete a b c d (hm _ (by omega)) (hm _ (by omega)) ⟨a1, b1, c1, d1⟩ ⟨a2, b2, c2, d2⟩

end Plonky3Lean.Proofs.Blake3Air
