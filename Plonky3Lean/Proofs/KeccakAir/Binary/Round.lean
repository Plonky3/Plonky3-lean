module

public import Plonky3Lean.Proofs.KeccakAir.Round
public import Plonky3Lean.Proofs.KeccakAir.GenRow

@[expose] public section

/-!
# The characteristic-2 generator's round is Rnd of FIPS 202

The generator's round works on 25 words, lane 5 y + x holding lane (x, y).

On every state and every round k < 24, it computes Rnd(A, k), the round of FIPS 202, 3.3.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_keccak_air.mirror p3_keccak_air.mirror.binary Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.KeccakAir

/-- The state array of 25 words indexed by lane 5 y + x. -/
def lanesState (S : LState) : State := fun x y z => (S (5 * y.val + x.val)).getLsbD z.val

theorem idx_mod {x y : ℕ} (hx : x < 5) : (5 * y + x) % 5 = x := by omega
theorem idx_div {x y : ℕ} (hx : x < 5) : (5 * y + x) / 5 = y := by omega

/-- The column parity C[x] of a state of words. -/
def parW (S : LState) (x : ℕ) : Word := (List.range 5).foldl (fun acc y => acc ^^^ S (5 * y + x)) 0

/-- D[x] = C[x - 1] xor ROT(C[x + 1], 1). -/
def dW (S : LState) (x : ℕ) : Word := parW S ((x + 4) % 5) ^^^ (parW S ((x + 1) % 5)).rotateLeft 1

theorem parW_getLsbD (S : LState) (x : Fin 5) (z : Fin 64) :
    (parW S x.val).getLsbD z.val = (lanesState S x 0 z ^^ lanesState S x 1 z ^^ lanesState S x 2 z ^^
      lanesState S x 3 z ^^ lanesState S x 4 z) := by
  simp [parW, lanesState, List.range_succ]

/-- Theta on words: lane (x, y) xor D[x] is theta of the state. -/
theorem theta_getLsbD (S : LState) (x y : Fin 5) (z : Fin 64) :
    (S (5 * y.val + x.val) ^^^ dW S x.val).getLsbD z.val = theta (lanesState S) x y z := by
  have h4 := parW_getLsbD S (x - 1) z
  have h1 := parW_getLsbD S (x + 1) (z - 1)
  rw [fin5_sub_one] at h4
  rw [fin5_add, Fin.val_one, fin64_sub_one] at h1
  rw [BitVec.getLsbD_xor, dW, BitVec.getLsbD_xor,
    getLsbD_rotateLeft_nat _ (by omega : 1 < 64) z.isLt, show z.val + 64 - 1 = z.val + 63 by omega,
    h4, h1, theta]
  rfl

/-- B[i mod 5, i / 5] as the round computes it. -/
def bW (S : LState) (i : ℕ) : Word :=
  let (source_y, source_x, rot) := rho_pi_source (i % 5) (i / 5)
  (S (5 * source_y + source_x) ^^^ dW S source_x).rotateLeft rot

theorem bW_getLsbD (S : LState) (x y : Fin 5) (z : Fin 64) :
    (bW S (5 * y.val + x.val)).getLsbD z.val = pi (rho (theta (lanesState S))) x y z := by
  rw [pi_rho_apply, ← theta_getLsbD]
  simp only [bW, rho_pi_source, idx_mod x.isLt, idx_div x.isLt]
  rw [getLsbD_rotateLeft_nat _ (rOf_lt _ (Nat.mod_lt _ (by omega)) _ x.isLt) z.isLt]

/-- The generator's round is Rnd(A, k). -/
theorem keccak_round_eq (S : LState) {k : ℕ} (hk : k < 24) :
    lanesState (keccak_round S k) = rnd (lanesState S) k := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hb : ∀ i, (let (source_y, source_x, rot) := rho_pi_source (i % 5) (i / 5)
      (S (5 * source_y + source_x) ^^^
        ((List.range 5).foldl (fun acc y => acc ^^^ S (5 * y + (source_x + 4) % 5)) 0 ^^^
          ((List.range 5).foldl (fun acc y => acc ^^^ S (5 * y + (source_x + 1) % 5)) 0).rotateLeft 1)).rotateLeft
        rot) = bW S i := fun i => rfl
  have hB1 := bW_getLsbD S (x + 1) y z
  have hB2 := bW_getLsbD S (x + 2) y z
  rw [fin5_add, Fin.val_one] at hB1
  rw [fin5_add, Fin.val_two] at hB2
  simp only [lanesState, keccak_round, rnd, iota, chi, Function.update_apply, hb, idx_mod hx,
    idx_div hx, Bool.xor_true, Fin.ext_iff, Fin.val_zero]
  have hB0 := bW_getLsbD S x y z
  by_cases h0 : x.val = 0 ∧ y.val = 0
  · rw [ite_eq_left (show 5 * y.val + x.val = 0 by omega), ite_eq_left h0]
    rw [h0.1, h0.2] at hB0 hB1 hB2
    simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_div, Nat.zero_mod, Nat.reduceMod] at hB0 hB1 hB2 ⊢
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hB0, hB1, hB2,
      rc_getLsbD k hk _ hz]
    simp only [hz, decide_true, Bool.true_and, rcBit_eq hk hz, Fin.ofNat_val_eq_self,
      Bool.decide_eq_true]
  · rw [ite_eq_right (show ¬ 5 * y.val + x.val = 0 by omega), ite_eq_right h0, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hB0,
      hB1, hB2]
    simp only [hz, decide_true, Bool.true_and]

end Plonky3Lean.Proofs.KeccakAir.Binary
