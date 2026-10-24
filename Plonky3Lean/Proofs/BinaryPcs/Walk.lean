module

public import Plonky3Lean.Proofs.BinaryPcs.Fold
import all Init.Data.Nat.Power2.Basic

@[expose] public section

/-!
# The walk of the tower-basis fold

One round of the tower-basis fold splits its outputs into tasks of 2^10 symbols.

Each task evaluates the domain point of its first output, then walks to the next by one addition.

From output c - 1 to output c, point(2 c) adds beta_1 + ... + beta_(t+1).

Here t counts the trailing zeros of c.

So the walk visits exactly the points the plain fold of each pair evaluates.

The round is therefore that fold, pair by pair.
-/

namespace Plonky3Lean.Proofs.BinaryPcs

open Finset Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft p3_binary_dft.mirror
  p3_binary_dft.domain.mirror p3_binary_pcs.fold.mirror

theorem trailingZeros_two_pow (k : ℕ) : trailingZeros (2 ^ k) = k := by
  induction k with
  | zero => simp [trailingZeros]
  | succ k ih =>
    rw [trailingZeros]
    have h1 : 2 ^ (k + 1) ≠ 0 := by positivity
    have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; simp
    simp only [h1, h2, ↓reduceIte, zero_ne_one]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; simp, ih]

/-- Tasks of G consecutive outputs cover the first min N (T G) outputs in order. -/
theorem flatten_tasks {α : Type _} (f : ℕ → α) (G N : ℕ) :
    ∀ T, ((List.range T).map fun t => (List.range (min G (N - t * G))).map fun o => f (t * G + o)).flatten =
      (List.range (min N (T * G))).map f := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    by_cases hN : N ≤ T * G
    · rw [show N - T * G = 0 by omega, show min N (T * G) = N by omega,
        show min N ((T + 1) * G) = N by rw [add_mul]; omega]
      simp
    · rw [show min N (T * G) = T * G by omega,
        show min N ((T + 1) * G) = T * G + min G (N - T * G) by rw [add_mul]; omega,
        List.range_add, List.map_append, List.map_map]
      rfl

variable {F EF : Type _} [Field F] [CharP F 2] [Field EF] [Algebra F EF]

/-- The fold of one pair, with the domain point given. -/
def pairValue (beta : EF) (x lo hi : F) : EF :=
  beta * algebraMap F EF ((lo + x * (lo + hi)) + (lo + hi)) + algebraMap F EF (lo + x * (lo + hi))

/-- The in-task walk.

After the first o outputs, the point is that of the last output.

The outputs are the plain folds. -/
theorem walk_loop (L : Level F) (codeword : List F) (beta : EF) (steps : List F) (start bound : ℕ)
    (f : F × List EF → ℕ → Option (F × List EF))
    (hf : ∀ (x : F) (out : List EF) (offset : ℕ), f (x, out) offset =
      (if offset ≠ 0 then (steps[trailingZeros (start + offset)]?).map (x + ·) else some x).bind fun x =>
        some (x, out ++ [pairValue beta x (codeword.getD (2 * (start + offset)) 0)
          (codeword.getD (2 * (start + offset) + 1) 0)]))
    (hsteps : ∀ c, start < c → c < bound → ∀ h : trailingZeros c < steps.length,
      steps[trailingZeros c] = ∑ q ∈ range (trailingZeros c + 1), L.cantor (q + 1))
    (hlen : ∀ c, start < c → c < bound → trailingZeros c < steps.length) :
    ∀ o, start + o < bound → (List.range (o + 1)).foldlM f (point L.cantor (2 * start), []) =
      some (point L.cantor (2 * (start + o)), (List.range (o + 1)).map fun j =>
        pairValue beta (point L.cantor (2 * (start + j))) (codeword.getD (2 * (start + j)) 0)
          (codeword.getD (2 * (start + j) + 1) 0)) := by
  intro o
  induction o with
  | zero => intro _; simp [hf]
  | succ o ih =>
    intro hb
    rw [List.range_succ, List.foldlM_append, ih (by omega)]
    have hc : start < start + (o + 1) := by omega
    have hstep := point_step L.cantor (show 0 < start + (o + 1) by omega)
    rw [show start + (o + 1) - 1 = start + o by omega] at hstep
    simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, hf, ne_eq,
      show o + 1 ≠ 0 by omega, not_false_eq_true, ite_true,
      List.getElem?_eq_getElem (hlen _ hc hb), Option.map_some, hsteps _ hc hb (hlen _ hc hb), ← hstep,
      List.map_append, List.map_cons, List.map_nil]
    simp [pure, List.range_succ]

/-- One round of the tower-basis fold is the plain fold of every pair, at its own domain point.

It needs the codeword inside the alphabet's domain and inside a word. -/
theorem fold_round_eq (L : Level F) (codeword : List F) (beta : EF) {m : ℕ}
    (hlen : codeword.length ≤ 2 ^ m) (hm : m ≤ 2 ^ L.logBits) (hw : m ≤ 64) :
    fold_round L codeword beta = (List.range (codeword.length / 2)).mapM fun j =>
      fold_pair L j beta (codeword.getD (2 * j) 0) (codeword.getD (2 * j + 1) 0) := by
  set np := codeword.length / 2 with hnp
  have hdom : ∀ j < np, 2 * j < 2 ^ m := fun j hj => by omega
  have hpair : ∀ j < np, fold_pair L j beta (codeword.getD (2 * j) 0) (codeword.getD (2 * j + 1) 0) =
      some (pairValue beta (point L.cantor (2 * j)) (codeword.getD (2 * j) 0)
        (codeword.getD (2 * j + 1) 0)) := fun j hj => by
    have h1 := hdom j hj
    have hmod : 2 * j % 2 ^ 64 = 2 * j :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hw))
    have hin : 2 * j < 2 ^ 2 ^ L.logBits := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hm)
    simp only [fold_pair_eq, hmod, hin, ite_true]
    rfl
  rw [mapM_some _ _ _ fun j hj => hpair j (List.mem_range.1 hj)]
  -- The steps table.
  obtain ⟨k, hk⟩ : ∃ k, np.nextPowerOfTwo = 2 ^ k := Nat.isPowerOfTwo_nextPowerOfTwo np
  have hnpk : np ≤ 2 ^ k := hk ▸ Nat.le_nextPowerOfTwo np
  have hkm : k < 2 ^ L.logBits := by
    by_cases h0 : m = 0
    · subst h0
      have hle : np.nextPowerOfTwo ≤ 1 := Nat.nextPowerOfTwo_le (by simp at hlen; omega) ⟨0, rfl⟩
      rw [hk] at hle
      have : k = 0 := by
        by_contra hk0
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have := Nat.two_pow_pos L.logBits; omega
    · have hle : np.nextPowerOfTwo ≤ 2 ^ (m - 1) :=
        Nat.nextPowerOfTwo_le (by
          have : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
          omega) ⟨m - 1, rfl⟩
      rw [hk] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
      omega
  have hsteps := domain_point_steps_eq L (trailingZeros np.nextPowerOfTwo)
  rw [hk, trailingZeros_two_pow] at hsteps
  simp only [hkm, ↓reduceIte] at hsteps
  unfold fold_round
  dsimp only
  rw [← hnp, hk, trailingZeros_two_pow, hsteps]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hG : 0 < FOLD_GRAIN := by simp [FOLD_GRAIN]
  have htask : ∀ t, t < (np + FOLD_GRAIN - 1) / FOLD_GRAIN → t * FOLD_GRAIN < np := fun t ht => by
    have := (Nat.le_div_iff_mul_le hG).1 (Nat.succ_le_of_lt ht)
    rw [Nat.succ_eq_add_one, add_mul, one_mul] at this
    clear ht; omega
  have hcover : np ≤ (np + FOLD_GRAIN - 1) / FOLD_GRAIN * FOLD_GRAIN := by
    have h1 := Nat.div_add_mod (np + FOLD_GRAIN - 1) FOLD_GRAIN
    have h2 := Nat.mod_lt (np + FOLD_GRAIN - 1) hG
    rw [mul_comm]; omega
  have hlenk : ∀ c, 0 < c → c < np → trailingZeros c < ((List.range k).map
      fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1)).length := fun c hc hcn => by
    simpa using trailingZeros_lt hc (lt_of_lt_of_le hcn hnpk)
  rw [mapM_some _ (fun t => (List.range (min FOLD_GRAIN (np - t * FOLD_GRAIN))).map fun o =>
      pairValue beta (point L.cantor (2 * (t * FOLD_GRAIN + o))) (codeword.getD (2 * (t * FOLD_GRAIN + o)) 0)
        (codeword.getD (2 * (t * FOLD_GRAIN + o) + 1) 0)) _ fun t ht => ?_]
  · simp only [Option.bind_some]
    rw [flatten_tasks (fun j => pairValue beta (point L.cantor (2 * j)) (codeword.getD (2 * j) 0)
      (codeword.getD (2 * j + 1) 0)) FOLD_GRAIN np, show min np _ = np by omega]
    rfl
  have ht := htask t (List.mem_range.1 ht)
  have hd : 2 * (t * FOLD_GRAIN) % 2 ^ 64 = 2 * (t * FOLD_GRAIN) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (hdom _ ht) (Nat.pow_le_pow_right (by norm_num) hw))
  have hin : 2 * (t * FOLD_GRAIN) < 2 ^ 2 ^ L.logBits :=
    lt_of_lt_of_le (hdom _ ht) (Nat.pow_le_pow_right (by norm_num) hm)
  obtain ⟨o, ho⟩ : ∃ o, min FOLD_GRAIN (np - t * FOLD_GRAIN) = o + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [domain_point_eq, hd]
  simp only [hin, ↓reduceIte, Option.bind_some]
  rw [ho, walk_loop L codeword beta _ (t * FOLD_GRAIN) np _ ?hf
      (fun c hc hcn hlt => by simp) (fun c hc hcn => hlenk c (by omega) hcn) o (by omega)]
  · rfl
  · intro x out offset
    by_cases h0 : offset = 0 <;> simp [h0, pairValue, pure]

end Plonky3Lean.Proofs.BinaryPcs
