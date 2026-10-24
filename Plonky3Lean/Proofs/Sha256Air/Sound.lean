module

public import Plonky3Lean.Proofs.Sha256Air.RowSound
public import Plonky3Lean.Proofs.KeccakAir.Sound

@[expose] public section

/-!
# Soundness of the SHA-256 AIR over a prime field

Let a trace satisfy the AIR, over a field of characteristic above `7 * 2^16`.

Then every row holds a chaining value H and a block M:

- the packed input columns hold the 16-bit limbs of H
- the first 16 schedule words hold the bits of M
- the output columns hold the bits of the FIPS 180-4 compression of H and M

Rows are independent: nothing relates one row to the next.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Spec.Sha256 Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder rowOf satisfies_iff_rows bitF rowOf_getD)

variable {F : Type} [Field F] [DecidableEq F]

/-- Row i of a trace, as the row builder reads it. -/
def cur (T : Instance F) (i : ℕ) : ℕ → F :=
  rowOf (rowEnv T i) (AirLayout.from_air (sha256Air (F := F))) 0

theorem cur_eq (T : Instance F) (i : ℕ) {c : ℕ} (hc : c < NUM_SHA256_COLS) : cur T i c = T.main i c :=
  rowOf_getD _ _ 0 hc

theorem rowSpec_of_satisfies {T : Instance F} (hT : Satisfies (constraints sha256Air) T) {i : ℕ}
    (hi : i < T.height) : RowSpec (cur T i) :=
  (eval_iff _ _).mp ((satisfies_iff_rows sha256Air T).mp hT i hi)

/-- Limb `limb` of a word: its bits `16 limb` to `16 limb + 15`. -/
def limbOf (w : BitVec 32) (limb : ℕ) : ℕ := w.toNat / 65536 ^ limb % 65536

/-- Soundness: each row of a satisfying trace computes one compression.

- the input columns hold a chaining value H as limbs
- the first schedule words hold a block M as bits
- the output columns hold the bits of the compression of H and M -/
theorem sound (hp : 7 * 65536 < ringChar F) {T : Instance F}
    (hT : Satisfies (constraints sha256Air) T) {i : ℕ} (hrow : i < T.height) :
    ∃ H M : List (BitVec 32), H.length = 8 ∧ M.length = 16 ∧
      (∀ j < 8, ∀ limb < 2, T.main i (col.h_in j limb) = (limbOf (H.getD j 0) limb : F)) ∧
      (∀ t < 16, ∀ b < 32, T.main i (col.w t b) = bitF ((M.getD t 0).getLsbD b)) ∧
      (∀ j < 8, ∀ b < 32, T.main i (col.h_out j b) = bitF (((compress H M).getD j 0).getLsbD b)) := by
  have h := rowSpec_of_satisfies hT hrow
  refine ⟨chainOf (cur T i), blockOf (cur T i), rfl, length_blockOf, ?_, ?_, ?_⟩
  · intro j hj limb hl
    have hlimb : ∀ w : BitVec 32, ((if limb = 0 then lo w else hi w : ℕ) : F) = (limbOf w limb : F) := by
      intro w
      have := w.isLt
      interval_cases limb <;> simp only [lo, hi, limbOf, ↓reduceIte, one_ne_zero] <;> congr 1 <;> omega
    rw [← cur_eq T i (by simp [col.h_in, NUM_SHA256_COLS]; omega)]
    rcases Nat.lt_or_ge j 4 with h4 | h4
    · have e := (h.init_a j h4)
      rw [← hlimb]
      interval_cases limb
      · rw [sub_eq_zero.mp e.1, packF_eq (holds_a h (k := 3 - j) (by omega)) 0 (by omega)]
        interval_cases j <;> rfl
      · rw [sub_eq_zero.mp e.2, packF_eq (holds_a h (k := 3 - j) (by omega)) 1 (by omega)]
        interval_cases j <;> rfl
    · have e := (h.init_e (j - 4) (by omega))
      rw [show 4 + (j - 4) = j by omega] at e
      rw [← hlimb]
      interval_cases limb
      · rw [sub_eq_zero.mp e.1, packF_eq (holds_e h (k := 3 - (j - 4)) (by omega)) 0 (by omega)]
        interval_cases j <;> rfl
      · rw [sub_eq_zero.mp e.2, packF_eq (holds_e h (k := 3 - (j - 4)) (by omega)) 1 (by omega)]
        interval_cases j <;> rfl
  · intro t ht b hb
    rw [← cur_eq T i (by simp [col.w, NUM_SHA256_COLS]; omega)]
    refine (holds_w h (t := t) (by omega) b hb).trans ?_
    simp [blockOf, ht, wW]
  · intro j hj b hb
    rw [← cur_eq T i (by simp [col.h_out, NUM_SHA256_COLS]; omega), ← row_compress h hp]
    refine (holds_h h hj b hb).trans ?_
    simp [hj]

end Plonky3Lean.Proofs.Sha256Air
