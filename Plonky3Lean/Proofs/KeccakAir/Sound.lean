module

public import Plonky3Lean.Proofs.KeccakAir.Round

@[expose] public section

/-!
# Soundness of the Keccak-f AIR

Let a trace of n rows satisfy the AIR, over a field of characteristic at least 2^16.

* Row i has its round flag one-hot at round i mod 24.
* On rows 24 m to 24 m + 23, when they all exist, the input limbs of row 24 m + k are those of Rnd^k(A).

  Here A is the state whose limbs are the preimage, and the preimage is the same on all 24 rows.
* The output limbs of row 24 m + 23 are those of Keccak-f[1600](A).

Nothing relates the preimages of two consecutive permutations.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Air

variable {F : Type} [Field F] [DecidableEq F]

/-- The layout of the Keccak-f AIR. -/
abbrev layout : AirLayout := AirLayout.from_air (keccakAir (F := F))

/-- Row i of a trace, as the row builder reads it: 0 past the AIR's width. -/
def cur (T : Instance F) (i : ℕ) : ℕ → F := rowOf (rowEnv T i) (layout (F := F)) 0

theorem rowOf_getD (env : Var → F) (L : AirLayout) (o : Fin 2) {c : ℕ} (hc : c < L.main_width) :
    rowOf env L o c = env (.main o c) := by
  simp [rowOf, hc]

/-- The next row the row builder reads on row i is row i + 1, below the last row. -/
theorem rowOf_next (T : Instance F) {i : ℕ} (hi : i + 1 < T.height) :
    rowOf (rowEnv T i) (layout (F := F)) 1 = cur T (i + 1) := by
  funext c
  simp only [cur, rowOf, rowEnv, Nat.mod_eq_of_lt hi]

/-- A satisfying trace satisfies the row constraints on every row. -/
theorem rowSpec_of_satisfies {T : Instance F} (hT : Satisfies (constraints keccakAir) T) {i : ℕ}
    (hi : i < T.height) :
    RowSpec (cur T i) (rowOf (rowEnv T i) (layout (F := F)) 1) (if i = 0 then 1 else 0)
      (if i = T.height - 1 then 0 else 1) :=
  (eval_iff _ _).mp ((satisfies_iff_rows keccakAir T).mp hT i hi)

/-- The round flags of row i are one-hot at round i mod 24. -/
theorem flags_eq {T : Instance F} (hT : Satisfies (constraints keccakAir) T) :
    ∀ i < T.height, ∀ r < 24, cur T i (col.step_flags r) = if r = i % 24 then 1 else 0 := by
  intro i
  induction i with
  | zero =>
    intro hi r hr
    have h := rowSpec_of_satisfies hT hi
    rcases r with _ | r
    · simpa [sub_eq_zero] using h.first_flag
    · simpa using h.first_zero r (by omega)
  | succ i ih =>
    intro hi r hr
    have h := rowSpec_of_satisfies hT (by omega : i < T.height)
    have hne : ¬ i = T.height - 1 := by omega
    rw [rowOf_next T hi] at h
    simp only [hne, ↓reduceIte] at h
    have := h.rotate ((r + 23) % 24) (by omega)
    rw [one_mul, sub_eq_zero, ih (by omega) _ (by omega), show ((r + 23) % 24 + 1) % 24 = r by omega] at this
    rw [← this]
    congr 1
    apply propext
    omega

/-- Limb `limb` of lane (x, y) of a state: its bits 16 limb to 16 limb + 15, least significant first. -/
def stateLimb (A : State) (x y : Fin 5) (limb : Fin 4) : ℕ :=
  bitsum (fun j => A x y ⟨(limb.val * 16 + j) % 64, Nat.mod_lt _ (by omega)⟩) 16

theorem stateLimb_toState (f : ℕ → ℕ → ℕ → Bool) (x y : Fin 5) (limb : Fin 4) :
    stateLimb (toState f) x y limb = bitsum (fun j => f x y (limb.val * 16 + j)) 16 :=
  bitsum_congr fun j hj => by
    simp only [toState]; rw [Nat.mod_eq_of_lt (by omega)]

theorem cur_eq (T : Instance F) (i : ℕ) {c : ℕ} (hc : c < NUM_KECCAK_COLS) : cur T i c = T.main i c :=
  rowOf_getD _ _ 0 hc

section block

variable (hp : 2 ^ 16 ≤ ringChar F) {T : Instance F} (hT : Satisfies (constraints keccakAir) T)
include hp hT

/-- Within a permutation, the input of the next row is this row's round of this row's input. -/
theorem next_input {i k : ℕ} (hi : i + 1 < T.height) (hk : k < 23) (hik : i % 24 = k) :
    toState (inB (cur T (i + 1))) = rnd (toState (inB (cur T i))) k := by
  have h := rowSpec_of_satisfies hT (by omega : i < T.height)
  have h' := rowSpec_of_satisfies hT hi
  have hne : ¬ i = T.height - 1 := by omega
  rw [rowOf_next T hi] at h
  simp only [hne, ↓reduceIte] at h
  have hflag : ∀ r < 24, cur T i (col.step_flags r) = if r = k then 1 else 0 := by
    intro r hr; rw [flags_eq hT i (by omega) r hr, hik]
  have hlimb : ∀ x < 5, ∀ y < 5, ∀ limb < 4, ∀ j < 16,
      inB (cur T (i + 1)) x y (limb * 16 + j) = outB (cur T i) k x y (limb * 16 + j) := by
    intro x hx y hy limb hl
    have ho := h.output x hx y hy limb hl
    rw [hflag 23 (by omega), ite_eq_right (by omega), sub_zero, one_mul, one_mul, sub_eq_zero,
      output_eq h hp (by omega) hflag hx hy hl, a_eq h' hx hy hl] at ho
    exact bits_of_limb hp ho.symm
  rw [← round_eq h hp (by omega)]
  funext x y z
  have := hlimb x x.isLt y y.isLt (z / 16) (by omega) (z % 16) (by omega)
  rwa [show z.val / 16 * 16 + z.val % 16 = z.val by omega] at this

/-- The input of row 24 m + k is Rnd^k of the input of row 24 m. -/
theorem input_iter {m k : ℕ} (hm : 24 * m + 24 ≤ T.height) (hk : k < 24) :
    toState (inB (cur T (24 * m + k))) =
      (List.range k).foldl (fun A r => rnd A r) (toState (inB (cur T (24 * m)))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega),
      ← Nat.add_assoc]
    exact next_input hp hT (by omega) (by omega) (by omega)

/-- The preimage is the same on every row of a permutation. -/
theorem preimage_const {m k : ℕ} (hm : 24 * m + 24 ≤ T.height) (hk : k < 24) {x y limb : ℕ}
    (hx : x < 5) (hy : y < 5) (hl : limb < 4) :
    cur T (24 * m + k) (col.preimage y x limb) = cur T (24 * m) (col.preimage y x limb) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi : 24 * m + k + 1 < T.height := by omega
    have h := rowSpec_of_satisfies hT (by omega : 24 * m + k < T.height)
    have hne : ¬ 24 * m + k = T.height - 1 := by omega
    rw [rowOf_next T hi] at h
    simp only [hne, ↓reduceIte] at h
    have hc := h.carry y hy x hx limb hl
    rw [flags_eq hT _ (by omega) 23 (by omega), ite_eq_right (by omega), sub_zero, one_mul,
      one_mul, sub_eq_zero] at hc
    rw [← Nat.add_assoc, ← hc, ih (by omega)]

/-- The preimage of a permutation holds the limbs of its input state. -/
theorem preimage_eq {m : ℕ} (hm : 24 * m + 24 ≤ T.height) (x y : Fin 5) (limb : Fin 4) :
    cur T (24 * m) (col.preimage y x limb) =
      (stateLimb (toState (inB (cur T (24 * m)))) x y limb : F) := by
  have h := rowSpec_of_satisfies hT (by omega : 24 * m < T.height)
  have hf := h.first_step y y.isLt x x.isLt limb limb.isLt
  rw [flags_eq hT _ (by omega) 0 (by omega), ite_eq_left (by omega), one_mul, sub_eq_zero] at hf
  rw [hf, a_eq h x.isLt y.isLt limb.isLt, stateLimb_toState]

/-- The output of a permutation holds the limbs of Keccak-f[1600] of its input state. -/
theorem output_eq_keccakP {m : ℕ} (hm : 24 * m + 24 ≤ T.height) (x y : Fin 5) (limb : Fin 4) :
    a_prime_prime_prime (cur T (24 * m + 23)) y x limb =
      (stateLimb (keccakP 24 (toState (inB (cur T (24 * m))))) x y limb : F) := by
  have h := rowSpec_of_satisfies hT (by omega : 24 * m + 23 < T.height)
  have hflag : ∀ r < 24, cur T (24 * m + 23) (col.step_flags r) = if r = 23 then 1 else 0 := by
    intro r hr; rw [flags_eq hT _ (by omega) r hr, show (24 * m + 23) % 24 = 23 by omega]
  have hround := round_eq h hp (by omega : 23 < 24)
  rw [input_iter hp hT hm (by omega : 23 < 24)] at hround
  have hP : keccakP 24 (toState (inB (cur T (24 * m)))) = toState (outB (cur T (24 * m + 23)) 23) := by
    rw [hround, keccakP, List.range_succ, List.foldl_append]
    simp
  rw [output_eq h hp (by omega) hflag x.isLt y.isLt limb.isLt, hP, stateLimb_toState]

/-- The input limbs of row 24 m + k are those of Rnd^k of the permutation's input state. -/
theorem input_limbs {m k : ℕ} (hm : 24 * m + 24 ≤ T.height) (hk : k < 24) (x y : Fin 5)
    (limb : Fin 4) :
    T.main (24 * m + k) (col.a y x limb) =
      (stateLimb ((List.range k).foldl (fun A r => rnd A r) (toState (inB (cur T (24 * m))))) x y
        limb : F) := by
  have h := rowSpec_of_satisfies hT (by omega : 24 * m + k < T.height)
  rw [← cur_eq T _ (by simp only [col.a, NUM_KECCAK_COLS]; omega), a_eq h x.isLt y.isLt limb.isLt,
    ← input_iter hp hT hm hk, stateLimb_toState]

end block

end Plonky3Lean.Proofs.KeccakAir
