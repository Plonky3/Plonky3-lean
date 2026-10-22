module

public import Plonky3Lean.Proofs.Field.Binary.Poly64

@[expose] public section

/-!
# A kernel-friendly product modulo `x^64 + x^4 + x^3 + x + 1`

Four masked integer products of 32-bit halves give the full carry-less product of two 64-bit
polynomials, and `reduce_64`'s two folds reduce it.

Every step is a closed form of integer operations, which the kernel evaluates directly, so
certificates such as `sqrt(X)^2 = X` check by `decide +kernel`.
-/

open Polynomial BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## A kernel-friendly product -/

/-- Operands below `2^32` have a carry-less product below degree `63`, which the masked multiply
computes in full. -/
theorem natPoly_bmulNat_of_lt {x y : ℕ} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    natPoly (bmulNat x y) = natPoly x * natPoly y := by
  ext p
  by_cases hp : p < 64
  · exact coeff_natPoly_bmulNat (by omega) (by omega) hp
  · rw [coeff_natPoly_of_lt (bmulNat_lt _ _) (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have h1 := natDegree_natPoly_le (k := 31) hx
    have h2 := natDegree_natPoly_le (k := 31) hy
    have := natDegree_mul_le (p := natPoly x) (q := natPoly y)
    omega

/-- The carry-less product of two 64-bit numbers, from the products of their 32-bit halves. -/
def clmulHalves (a b : ℕ) : ℕ :=
  let a0 := a % 2 ^ 32
  let a1 := a >>> 32
  let b0 := b % 2 ^ 32
  let b1 := b >>> 32
  bmulNat a0 b0 ^^^ (bmulNat a0 b1 ^^^ bmulNat a1 b0) <<< 32 ^^^ bmulNat a1 b1 <<< 64

theorem shiftRight_32_lt {a : ℕ} (ha : a < 2 ^ 64) : a >>> 32 < 2 ^ 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem clmulHalves_lt (a b : ℕ) : clmulHalves a b < 2 ^ 128 := by
  have h := bmulNat_lt
  unfold clmulHalves
  simp only
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · exact lt_trans (h _ _) (by norm_num)
  · rw [Nat.shiftLeft_eq]
    have := Nat.xor_lt_two_pow (h (a % 2 ^ 32) (b >>> 32)) (h (a >>> 32) (b % 2 ^ 32))
    omega
  · rw [Nat.shiftLeft_eq]
    have := h (a >>> 32) (b >>> 32)
    omega

theorem natPoly_clmulHalves {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    natPoly (clmulHalves a b) = natPoly a * natPoly b := by
  have ha0 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hb0 : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have ha1 := shiftRight_32_lt ha
  have hb1 := shiftRight_32_lt hb
  unfold clmulHalves
  simp only [natPoly_xor, natPoly_shiftLeft, natPoly_bmulNat_of_lt ha0 hb0,
    natPoly_bmulNat_of_lt ha0 hb1, natPoly_bmulNat_of_lt ha1 hb0, natPoly_bmulNat_of_lt ha1 hb1]
  rw [natPoly_split a 32, natPoly_split b 32]
  ring

/-- The product modulo the modulus, on natural numbers. -/
def mulModHalves (a b : ℕ) : ℕ := reduce64Nat (clmulHalves a b)

theorem mulModHalves_lt (a b : ℕ) : mulModHalves a b < 2 ^ 64 := reduce64Nat_lt _

theorem mk_mulModHalves {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    AdjoinRoot.mk BF64.basePoly (natPoly (mulModHalves a b)) =
      AdjoinRoot.mk BF64.basePoly (natPoly a) * AdjoinRoot.mk BF64.basePoly (natPoly b) := by
  rw [mulModHalves, mk_natPoly_reduce64Nat (clmulHalves_lt _ _), natPoly_clmulHalves ha hb,
    map_mul]

end Plonky3Lean.Proofs.Binary
