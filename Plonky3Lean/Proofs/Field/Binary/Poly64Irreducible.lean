import Plonky3Lean.Proofs.Field.Binary.Poly64
import ToCompPoly.ToMathlib.Polynomial.Rabin

/-!
# `x^64 + x^4 + x^3 + x + 1` is irreducible

Rabin's test, with both conditions checked by the kernel.

- Squaring `X` sixty-four times modulo the modulus returns `X`.
- `X^(2^32) + X` has an inverse modulo the modulus.

Every product is a closed form of integer operations that the kernel evaluates directly:

- four masked integer products of 32-bit halves give the full carry-less product,
- `reduce_64`'s two folds reduce it.
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
    AdjoinRoot.mk Poly64.modulus (natPoly (mulModHalves a b)) =
      AdjoinRoot.mk Poly64.modulus (natPoly a) * AdjoinRoot.mk Poly64.modulus (natPoly b) := by
  rw [mulModHalves, mk_natPoly_reduce64Nat (clmulHalves_lt _ _), natPoly_clmulHalves ha hb,
    map_mul]

/-! ## The certificate -/

/-- `X^(2^k)` modulo the modulus, for `k ≤ 64`, as bit patterns. -/
def frobChain : List ℕ := [
    0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101,
    0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e,
    0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13, 0xbaf1bebe1ae4ad02,
    0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527, 0xb6d535c542116f62,
    0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588, 0x180d86953ed141c6,
    0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba, 0x5c62236777028505,
    0xb964dc682c67ddcd, 0xb58ac9a23d208acb, 0xb3fcc2ab3699fc73, 0xb2644136253abfe8,
    0xb37cd8f5f54e22c6, 0xe267d02369c356e5, 0x82c8dc57a143827, 0x13846a66c22c75be,
    0x4b75c5e1cfbc9888, 0xe6e383fc30ec5c40, 0x18db4821d1201031, 0x4cc669b6b7c0691a,
    0xf26221ddce9cb783, 0x57399d3c29092c2f, 0xae86719cd83b743e, 0xfa5ac498d20dd97e,
    0x50a9adfa20f7c8d5, 0xaf06ffc8fb2c50a6, 0xfe42058b1100328e, 0x11cb06c04a986a2,
    0xb5837f7159f74, 0x551507a7ec9563d7, 0xfefb5bba15c4fcc9, 0x10a51a6f8e1e1ac,
    0x555b52acff1ce98c, 0xfffface6ff2beb3b, 0x55550444ff3218d8, 0xffffafaf00f1e0eb,
    0x5500ff01ff03, 0x55550000fffe0005, 0xffffffff0000000a, 0x2]

/-- `X^(2^k)` modulo the modulus. -/
def frobX (k : ℕ) : ℕ := frobChain.getD k 0

/-- Each entry of the chain squares to the next. -/
theorem frobX_succ : ∀ k < 64, mulModHalves (frobX k) (frobX k) = frobX (k + 1) := by
  decide +kernel
theorem frobX_lt : ∀ k < 65, frobX k < 2 ^ 64 := by
  decide +kernel

theorem frobX_spec (k : ℕ) (hk : k ≤ 64) : frobX k < 2 ^ 64 ∧
    AdjoinRoot.mk Poly64.modulus (natPoly (frobX k)) = AdjoinRoot.mk Poly64.modulus X ^ 2 ^ k := by
  induction k with
  | zero =>
    refine ⟨by decide +kernel, ?_⟩
    rw [show frobX 0 = 2 from rfl, natPoly_two, pow_zero, pow_one]
  | succ k ih =>
    have ih := ih (by omega)
    refine ⟨frobX_lt (k + 1) (by omega), ?_⟩
    rw [← frobX_succ k (by omega), mk_mulModHalves ih.1 ih.1, ih.2, ← sq, ← pow_mul, pow_succ]

/-- `0x53cad161bf5a89c7` inverts `X^(2^32) + X` modulo the modulus. -/
theorem coprime_check : mulModHalves 0x53cad161bf5a89c7 (0x5c62236777028505 ^^^ 2) = 1 := by
  decide +kernel

theorem natDegree_modulus : Poly64.modulus.natDegree = 64 := by
  unfold Poly64.modulus
  compute_degree!

/-- `x^64 + x^4 + x^3 + x + 1` is irreducible over `GF(2)`. -/
theorem modulus_irreducible : Irreducible Poly64.modulus := by
  apply irreducible_of_rabin_two_pow_mk Poly64.modulus 5 natDegree_modulus
  · rw [← (frobX_spec (2 ^ (5 + 1)) (by norm_num)).2,
      show frobX (2 ^ (5 + 1)) = 2 by decide +kernel, natPoly_two]
  · have h32 := (frobX_spec (2 ^ 5) (by norm_num)).2
    rw [show frobX (2 ^ 5) = 0x5c62236777028505 by decide +kernel] at h32
    have hc := mk_mulModHalves (a := 0x53cad161bf5a89c7) (b := 0x5c62236777028505 ^^^ 2)
      (by norm_num) (by decide +kernel)
    rw [coprime_check, natPoly_xor, map_add, h32, natPoly_two, natPoly_one, map_one] at hc
    exact ⟨_, hc.symm⟩

end Plonky3Lean.Proofs.Binary
