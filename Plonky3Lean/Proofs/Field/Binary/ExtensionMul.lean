module

public import Plonky3Lean.Proofs.Field.Binary.Extension

@[expose] public section

/-!
# Multiplying a level by a lower level

Level `u` is a vector space over level `l`, with the coefficients stored as consecutive
`2^l`-bit chunks. Multiplying by an element `b` of level `l` multiplies every chunk by `b`
(`toNat_mul_embed`): at each quadratic step, `b (lo + hi X) = b lo + (b hi) X`. `Mul<lower>`
computes exactly that, a chunk at a time.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Chunk `j` of `x`, `2^l` bits wide. -/
def chunk (l x j : ℕ) : ℕ := (x >>> (j * 2 ^ l)) % 2 ^ 2 ^ l

/-- The first `n` chunks of `x`, each multiplied by `b` at level `l`. -/
def chunkMul (l : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, b => chunkMul l n x b ||| towerMul l (chunk l x n) b <<< (n * 2 ^ l)

theorem chunkMul_lt {l b : ℕ} (hb : b < 2 ^ 2 ^ l) :
    ∀ (n : ℕ) (x : ℕ), chunkMul l n x b < 2 ^ (n * 2 ^ l)
  | 0, _ => by simp [chunkMul]
  | n + 1, x => by
    rw [chunkMul]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le (chunkMul_lt hb n x) (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    · rw [Nat.shiftLeft_eq, show (n + 1) * 2 ^ l = n * 2 ^ l + 2 ^ l by ring, pow_add, mul_comm]
      exact Nat.mul_lt_mul_of_pos_left (towerMul_lt l (Nat.mod_lt _ (by positivity)) hb)
        (by positivity)

theorem chunk_shiftRight (l x m n : ℕ) : chunk l (x >>> (m * 2 ^ l)) n = chunk l x (m + n) := by
  unfold chunk
  rw [add_mul, Nat.shiftRight_add]

theorem chunkMul_add {l b : ℕ} (x m : ℕ) : ∀ n : ℕ,
    chunkMul l (m + n) x b = chunkMul l m x b ||| chunkMul l n (x >>> (m * 2 ^ l)) b <<< (m * 2 ^ l)
  | 0 => by simp [chunkMul]
  | n + 1 => by
    rw [← Nat.add_assoc, chunkMul, chunkMul_add x m n, chunkMul, Nat.shiftLeft_or_distrib,
      Nat.or_assoc, chunk_shiftRight, ← Nat.shiftLeft_add, add_mul, Nat.add_comm (n * 2 ^ l)]

theorem chunk_mod {l x m j : ℕ} (hj : j < m) : chunk l (x % 2 ^ (m * 2 ^ l)) j = chunk l x j := by
  unfold chunk
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 2 ^ l
  · have : j * 2 ^ l + i < m * 2 ^ l := by
      have := Nat.mul_le_mul_right (2 ^ l) (show j + 1 ≤ m by omega)
      rw [add_mul, one_mul] at this
      omega
    simp [hi, this]
  · simp [hi]

theorem chunkMul_mod {l b x : ℕ} : ∀ (m : ℕ) (n : ℕ), n ≤ m →
    chunkMul l n (x % 2 ^ (m * 2 ^ l)) b = chunkMul l n x b
  | _, 0, _ => rfl
  | m, n + 1, h => by
    rw [chunkMul, chunkMul, chunkMul_mod m n (by omega), chunk_mod (by omega)]

/-- A value of level `k + 1` is its two halves. -/
theorem fromNat_eq_joinSucc {k x : ℕ} (hx : x < 2 ^ 2 ^ (k + 1)) :
    (fromNat x : ConcreteBTField (k + 1)) =
      joinSucc k (fromNat (x % 2 ^ 2 ^ k)) (fromNat (x >>> 2 ^ k)) := by
  apply ConcreteBTField.toNat_injective
  show _ = (join (k := k + 1) (by omega) _ _).toNat
  rw [toNat_join, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
    ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx, Nat.add_sub_cancel,
    Nat.mod_eq_of_lt (shiftRight_lt_of_lt hx), Nat.mod_mod_of_dvd _ (by
      exact Nat.pow_dvd_pow 2 (le_refl _)), Nat.lor_comm, mod_or_shiftRight_shiftLeft]

/-- Scaling by an element of level `k` scales both halves. -/
theorem embed_mul_joinSucc (k : ℕ) (a lo hi : ConcreteBTField k) :
    concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) a * joinSucc k lo hi =
      joinSucc k (a * lo) (a * hi) :=
  smul_joinSucc k a lo hi

/-- Multiplying by an element `b` of level `l` multiplies every `2^l`-bit chunk by `b`. -/
theorem toNat_mul_embed (l : ℕ) : ∀ (d : ℕ) {x b : ℕ}, x < 2 ^ 2 ^ (l + d) → b < 2 ^ 2 ^ l →
    ((fromNat x : ConcreteBTField (l + d)) *
      concreteTowerAlgebraMap l (l + d) (by omega) (fromNat b)).toNat = chunkMul l (2 ^ d) x b
  | 0, x, b, hx, hb => by
    rw [show concreteTowerAlgebraMap l (l + 0) (by omega) = RingHom.id _ from
      concreteTowerAlgebraMap_id l, RingHom.id_apply]
    rw [show (fromNat x : ConcreteBTField (l + 0)) * fromNat b = concrete_mul (fromNat x) (fromNat b)
      from rfl, toNat_concrete_mul, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by simpa using hb)]
    simp [chunkMul, chunk, Nat.mod_eq_of_lt (show x < 2 ^ 2 ^ l by simpa using hx)]
  | d + 1, x, b, hx, hb => by
    have hx' : x < 2 ^ 2 ^ (l + d + 1) := hx
    have hlo : x % 2 ^ 2 ^ (l + d) < 2 ^ 2 ^ (l + d) := Nat.mod_lt _ (by positivity)
    have hhi : x >>> 2 ^ (l + d) < 2 ^ 2 ^ (l + d) := shiftRight_lt_of_lt hx'
    have hsplit : 2 ^ d * 2 ^ l = 2 ^ (l + d) := by rw [← pow_add, Nat.add_comm]
    show ((fromNat x : ConcreteBTField (l + d + 1)) *
      concreteTowerAlgebraMap l (l + d + 1) (by omega) (fromNat b)).toNat = _
    rw [fromNat_eq_joinSucc hx', concreteTowerAlgebraMap_succ l (l + d) (by omega),
      RingHom.comp_apply, mul_comm, embed_mul_joinSucc]
    show (join (k := l + d + 1) (by omega) _ _).toNat = _
    rw [toNat_join]
    simp only [Nat.add_sub_cancel]
    rw [mul_comm, toNat_mul_embed l d hhi hb, mul_comm,
      toNat_mul_embed l d hlo hb, pow_succ, mul_two, chunkMul_add, hsplit,
      ← chunkMul_mod (2 ^ d) (2 ^ d) le_rfl (x := x), hsplit, Nat.lor_comm]

end Plonky3Lean.Proofs.Binary
