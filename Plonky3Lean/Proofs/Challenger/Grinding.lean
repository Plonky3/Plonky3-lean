module

public import P3Challenger
public import Plonky3Lean.Proofs.Challenger.Machine

@[expose] public section

/-!
# The proof-of-work search of the duplex challenger

A proof-of-work witness `w` passes at difficulty `b` when, after observing `w`, the next sample has `b` low zero bits.

`DuplexChallenger::grind` does not run that check per candidate.

It builds the pre-permutation state of the absorbing call once, writes each candidate into its slot, permutes, and reads cell `RATE - 1`.

Here that shortcut, read lane by lane, is shown to compute exactly the check.

```text
    inputs pending: [a, b], RATE = 4, WIDTH = 6

    grind state:  [ a, b, w, 0 | s_4 + 3, s_5 ]
    check:        observe w -> pad(s, [a, b, w]) -> permute -> sample pops cell 3
```
-/

namespace Plonky3Lean.Proofs.Challenger

open Plonky3Lean.Spec.Duplex p3_challenger.mirror

variable {F : Type} [AddMonoidWithOne F]

/-- The state the search builds for a candidate is the padded state of the absorbing call that observing it triggers. -/
theorem grindState_eq_pad (r w : ℕ) (s inb : List F) (x : F) (hs : s.length = w) (hr : r < w)
    (hinb : inb.length < r) : grindState r w s inb x = pad r s (inb ++ [x]) := by
  have hpad : pad r s (inb ++ [x]) = inb ++ x :: (List.replicate (r - (inb.length + 1)) 0 ++
      (s.getD r 0 + ((inb.length + 1 : ℕ) : F)) :: s.drop (r + 1)) := by
    simp [pad]
  rw [hpad]
  apply List.ext_getElem
  · simp [grindState]; omega
  intro i h1 h2
  simp only [grindState, List.getElem_map, List.getElem_range]
  rcases Nat.lt_or_ge i inb.length with hi | hi
  · rw [List.getElem_append_left hi]
    simp [hi]
  rw [List.getElem_append_right hi]
  rcases Nat.lt_or_ge i (inb.length + 1) with hi' | hi'
  · have : i = inb.length := by omega
    subst this
    simp
  simp only [List.getElem_cons, show i - inb.length ≠ 0 by omega, ↓reduceDIte]
  rcases Nat.lt_or_ge i r with hr' | hr'
  · rw [List.getElem_append_left (by simp; omega)]
    simp [show ¬ i < inb.length by omega, show i ≠ inb.length by omega, hr']
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rcases Nat.lt_or_ge i (r + 1) with hr'' | hr''
  · have : i = r := by omega
    subst this
    simp [show ¬ i < inb.length by omega, show i ≠ inb.length by omega,
      show i - inb.length - 1 - (i - (inb.length + 1)) = 0 by omega]
  · simp only [List.getElem_cons, show i - inb.length - 1 - (r - (inb.length + 1)) ≠ 0 by omega,
      ↓reduceDIte, List.getElem_drop]
    simp only [show ¬ i < inb.length by omega, show i ≠ inb.length by omega, show ¬ i < r by omega,
      show i ≠ r by omega, ↓reduceIte]
    have : i < s.length := by simp [grindState] at h1; omega
    rw [List.getD_eq_getElem _ _ this]
    congr 1
    omega

/-- `GrindingChallenger::check_witness` on the list machine: difficulty 0 accepts; otherwise observe the witness, sample, and test the low bits of the canonical value. -/
def checkWitness (f : List F → List F) (r : ℕ) (val : F → ℕ) (st : St F) (bits : ℕ) (x : F) : Bool :=
  bits = 0 || val ((st.observe f r x).sample f r).1 % 2 ^ bits = 0

/-- The search accepts a candidate exactly when the check does.

So the witness `grind` returns passes `check_witness`, and the final `assert!` in `grind` never fires on it. -/
theorem grind_accepts_iff_check (f : List F → List F) (r w : ℕ) (val : F → ℕ) (hr : 0 < r) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) (st : St F) (hs : st.s.length = w)
    (hinb : st.inb.length < r) (bits : ℕ) (hb : 0 < bits) (x : F) :
    checkWitness f r val st bits x =
      decide (val ((f (grindState r w st.s st.inb x)).getD (r - 1) 0) % 2 ^ bits = 0) := by
  rw [checkWitness, sample_observe hr hrw hf st hs hinb x, grindState_eq_pad r w st.s st.inb x hs hrw hinb]
  simp [Nat.pos_iff_ne_zero.1 hb]

/-- Difficulty 0 accepts every witness and leaves the transcript where it was. -/
theorem checkWitness_zero (f : List F → List F) (r : ℕ) (val : F → ℕ) (st : St F) (x : F) :
    checkWitness f r val st 0 x = true := by
  simp [checkWitness]

end Plonky3Lean.Proofs.Challenger
