module

public import Plonky3Lean.Proofs.BinaryDft.Domain
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The twiddle state

For a Cantor basis, the twiddle of stage j and block b is W_j(shift) + point(2b) (Lin, Chung and Han,
section III, with W_j(beta_i) = beta_(i-j)).

Going from block b to block b + 1 flips the bits 1 .. t + 1 of 2b, where t counts the trailing zeros of b + 1.

So the step is beta_1 + ... + beta_(t+1), entry t of the steps table.
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.lch.mirror

variable {F : Type _} [Field F]

/-! ## Trailing zeros -/

theorem trailingZeros_spec {c : ℕ} (hc : 0 < c) : ∃ a, c = 2 ^ trailingZeros c * (2 * a + 1) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [trailingZeros]
    by_cases hodd : c % 2 = 1
    · simp only [show c ≠ 0 by omega, hodd, ↓reduceIte, pow_zero, one_mul]
      exact ⟨c / 2, by omega⟩
    · simp only [show c ≠ 0 by omega, hodd, ↓reduceIte]
      obtain ⟨a, ha⟩ := ih (c / 2) (by omega) (by omega)
      exact ⟨a, by rw [pow_succ, mul_comm (2 ^ _) 2, mul_assoc, ← ha]; omega⟩

theorem trailingZeros_lt {c n : ℕ} (hc : 0 < c) (hcn : c < 2 ^ n) : trailingZeros c < n := by
  obtain ⟨a, ha⟩ := trailingZeros_spec hc
  by_contra h
  have : 2 ^ n ≤ 2 ^ trailingZeros c := Nat.pow_le_pow_right two_pos (by omega)
  have h' := Nat.le_mul_of_pos_right (2 ^ trailingZeros c) (show 0 < 2 * a + 1 by omega)
  rw [← ha] at h'
  omega

/-! ## The step between block twiddles -/

theorem point_step [CharP F 2] (β : ℕ → F) {c : ℕ} (hc : 0 < c) :
    point β (2 * c) = point β (2 * (c - 1)) + ∑ q ∈ range (trailingZeros c + 1), β (q + 1) := by
  obtain ⟨a, ha⟩ := trailingZeros_spec hc
  set t := trailingZeros c
  have h1 : 2 * c = 2 ^ (t + 2) * a + 2 ^ (t + 1) := by rw [ha]; ring
  have hpos := Nat.two_pow_pos t
  have h2 : 2 * (c - 1) = 2 ^ (t + 2) * a + 2 ^ 1 * (2 ^ t - 1) := by
    rw [ha]; rw [show t + 2 = t + 1 + 1 by rfl, pow_succ, pow_succ] at *
    have : 2 ^ t * (2 * a + 1) - 1 = 2 * 2 ^ t * a + (2 ^ t - 1) := by
      rw [mul_add, mul_one]; ring_nf; omega
    rw [this]; ring
  rw [h1, h2, point_add_mul β a (t + 2) (by rw [pow_succ, pow_succ]; omega),
    point_add_mul β a (t + 2) (by rw [pow_succ, pow_succ]; omega), point_two_pow,
    point_mul_two_pow β (2 ^ t - 1) 1, point_two_pow_sub_one, sum_range_succ]
  simp only [add_comm 1]
  linear_combination (-(∑ q ∈ range t, β (q + 1))) * CharTwo.two_eq_zero (R := F)

/-! ## The twiddle state of a Cantor level -/

/-- A level is Cantor: its table is a Cantor basis of its whole bit width. -/
def Cantor (L : Level F) : Prop := IsCantor L.cantor (2 ^ L.logBits)

theorem bases_eq (log_n : ℕ) (shift : F) :
    ((List.range log_n).foldl (fun (acc : List F × F) _ =>
      (acc.1 ++ [acc.2], acc.2 ^ 2 + acc.2)) ([], shift)) =
      ((List.range log_n).map fun j => sqAddIter j shift, sqAddIter log_n shift) := by
  induction log_n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, sqAddIter_succ]

theorem Twiddles.new_eq (L : Level F) {log_n : ℕ} (hl : log_n ≤ 2 ^ L.logBits) (shift : F) :
    Twiddles.new L log_n shift = some ⟨(List.range log_n).map fun j => sqAddIter j shift,
      (List.range (log_n - 1)).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1)⟩ := by
  have hpos := Nat.two_pow_pos L.logBits
  simp [Twiddles.new, bases_eq, domain_point_steps_eq, show log_n - 1 < 2 ^ L.logBits by omega]

/-- The twiddle of a block is W_j(shift) + point(2b), when 2b is an index of the level. -/
theorem Twiddles.at_eq (L : Level F) (tw : Twiddles F) {j b : ℕ} (hj : j < tw.bases.length)
    (hb : b * 2 < 2 ^ 2 ^ L.logBits) :
    tw.at L j b = some (tw.bases[j] + point L.cantor (2 * b)) := by
  simp [Twiddles.at, domain_point_eq, show 2 * b < 2 ^ 2 ^ L.logBits by omega,
    List.getElem?_eq_getElem hj, mul_comm b 2]

end Plonky3Lean.Proofs.BinaryDft
