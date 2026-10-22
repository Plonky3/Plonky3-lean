import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Eval.Defs
import ToCompPoly.Fields.Binary.NatPoly

/-!
# A carry-less product from integer products

An integer product of two operands whose set bits are four apart has digits, in base `16`,
that count pairs of bits.

Below the top digit no count reaches `16`, so no carry crosses into the next digit, and the
low bit of each digit is the parity of its count.

Summing the four residue classes of each operand recovers the low half of the carry-less
product.
-/

namespace Plonky3Lean.Proofs.Binary

open Polynomial BinaryField

/-! ## Bits as sums -/

/-- The low `w` bits of `n`, as a sum of powers of two. -/
theorem mod_two_pow_eq_sum (n w : ℕ) :
    n % 2 ^ w = ∑ k ∈ Finset.range w, (n.testBit k).toNat * 2 ^ k := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [Nat.mod_pow_succ, ih, Finset.sum_range_succ, Nat.toNat_testBit, Nat.mul_comm (2 ^ w)]

/-- A sum over `range (4 n)`, grouped by fours. -/
theorem sum_range_four_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range (4 * n), f k =
      ∑ i ∈ Finset.range n, (f (4 * i) + f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by ring]
    simp only [Finset.sum_range_succ, ih]
    abel

/-! ## Base-16 digits -/

/-- A sum of base-16 digits below `16` stays below the next power. -/
theorem sum_digits_lt (c : ℕ → ℕ) (m : ℕ) (hc : ∀ k < m, c k < 16) :
    ∑ k ∈ Finset.range m, c k * 16 ^ k < 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun k hk => hc k (by omega))
    have h2 : c m * 16 ^ m ≤ 15 * 16 ^ m :=
      Nat.mul_le_mul_right _ (by have := hc m (by omega); omega)
    omega

/-- The parity of digit `m` survives when every lower digit is below `16`. -/
theorem digit_parity (c : ℕ → ℕ) {n m : ℕ} (hm : m < n) (hc : ∀ k < m, c k < 16) :
    (∑ k ∈ Finset.range n, c k * 16 ^ k) / 16 ^ m % 2 = c m % 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + (d + 1) := ⟨n - m - 1, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_succ']
  have hlow := sum_digits_lt c m hc
  have hsplit : ∑ k ∈ Finset.range d, c (m + (k + 1)) * 16 ^ (m + (k + 1)) +
      c (m + 0) * 16 ^ (m + 0) =
      16 ^ m * (c m + 16 * ∑ k ∈ Finset.range d, c (m + (k + 1)) * 16 ^ k) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, add_comm]
    congr 1
    · simp [Nat.mul_comm]
    · apply Finset.sum_congr rfl
      intro k _
      rw [pow_add, pow_succ]
      ring
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, Nat.zero_add]
  omega

/-! ## Polynomials of masked operands -/

/-- Every fourth bit, starting at bit `r`, over 64 bits. -/
def nibbleMask (r : ℕ) : ℕ := 0x1111_1111_1111_1111 <<< r

theorem testBit_nibbleMask {r k : ℕ} (hr : r < 4) (hk : k < 64) :
    (nibbleMask r).testBit k = decide (k % 4 = r) := by
  unfold nibbleMask
  interval_cases r <;> revert k <;> decide

theorem testBit_nibbleMask_of_ge {r k : ℕ} (hr : r < 4) (hk : 64 ≤ k) :
    (nibbleMask r).testBit k = false := by
  apply Nat.testBit_lt_two_pow
  calc nibbleMask r < 2 ^ 64 := by unfold nibbleMask; interval_cases r <;> decide
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- The bits of `x` in residue class `r`, as base-16 digits. -/
noncomputable def digits (x r : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range 16, C (x.testBit (4 * i + r)).toNat * X ^ i

theorem coeff_digits (x r i : ℕ) :
    (digits x r).coeff i = if i < 16 then (x.testBit (4 * i + r)).toNat else 0 := by
  unfold digits
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hi : i < 16
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have : i ≠ j := by have := Finset.mem_range.mp hj; omega
    simp [this]

theorem coeff_digits_le (x r i : ℕ) : (digits x r).coeff i ≤ 1 := by
  rw [coeff_digits]
  split_ifs
  · exact Bool.toNat_le _
  · exact Nat.zero_le _

/-- A masked operand is `2 ^ r` times its digits read in base `16`. -/
theorem and_nibbleMask_eq {x : ℕ} (hx : x < 2 ^ 64) {r : ℕ} (hr : r < 4) :
    x &&& nibbleMask r = 2 ^ r * (digits x r).eval 16 := by
  have hlt : x &&& nibbleMask r < 2 ^ 64 := lt_of_le_of_lt Nat.and_le_left hx
  rw [← Nat.mod_eq_of_lt hlt, mod_two_pow_eq_sum, show 64 = 4 * 16 by rfl, sum_range_four_mul]
  unfold digits
  rw [eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.testBit_and]
  rw [testBit_nibbleMask hr (by omega), testBit_nibbleMask hr (by omega),
    testBit_nibbleMask hr (by omega), testBit_nibbleMask hr (by omega)]
  rw [show (16 : ℕ) ^ i = 2 ^ (4 * i) by rw [pow_mul]; rfl]
  interval_cases r <;> simp [Nat.add_mod, pow_add] <;> ring

/-- The `GF(2)` image of a polynomial over `ℕ`. -/
noncomputable abbrev mod2 (p : ℕ[X]) : (ZMod 2)[X] := p.map (Nat.castRingHom (ZMod 2))

/-- A masked operand is `X ^ r` times its digits, spread four apart. -/
theorem natPoly_and_nibbleMask {x : ℕ} (hx : x < 2 ^ 64) {r : ℕ} (hr : r < 4) :
    natPoly (x &&& nibbleMask r) = X ^ r * expand (ZMod 2) 4 (mod2 (digits x r)) := by
  ext p
  rw [coeff_natPoly, coeff_X_pow_mul', Nat.testBit_and]
  by_cases hp : p < 64
  · rw [testBit_nibbleMask hr hp]
    by_cases hrp : r ≤ p
    · rw [if_pos hrp, coeff_expand (by norm_num), coeff_map, coeff_digits]
      by_cases hd : 4 ∣ p - r
      · have h1 : (p - r) / 4 < 16 := by omega
        have h2 : 4 * ((p - r) / 4) + r = p := by omega
        have h3 : p % 4 = r := by omega
        simp only [hd, h1, h2, h3, if_true, decide_true, Bool.and_true]
        cases x.testBit p <;> simp
      · have h3 : ¬ p % 4 = r := by omega
        simp [hd, h3]
    · have h3 : ¬ p % 4 = r := by omega
      simp [hrp, h3]
  · have hb : x.testBit p = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb, Bool.false_and, if_neg Bool.false_ne_true]
    split_ifs with hrp
    · rw [coeff_expand (by norm_num)]
      split_ifs with hd
      · rw [coeff_map, coeff_digits, if_neg (by omega)]
        simp
      · rfl
    · rfl

/-- An operand is the sum of its four residue classes. -/
theorem natPoly_eq_sum_nibbles {x : ℕ} (hx : x < 2 ^ 64) :
    natPoly x = ∑ r ∈ Finset.range 4, X ^ r * expand (ZMod 2) 4 (mod2 (digits x r)) := by
  have hsplit : x = (x &&& nibbleMask 0) ^^^ (x &&& nibbleMask 1) ^^^ (x &&& nibbleMask 2) ^^^
      (x &&& nibbleMask 3) := by
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_xor, Nat.testBit_and]
    by_cases hk : k < 64
    · rw [testBit_nibbleMask (by norm_num) hk, testBit_nibbleMask (by norm_num) hk,
        testBit_nibbleMask (by norm_num) hk, testBit_nibbleMask (by norm_num) hk]
      have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      cases x.testBit k <;> interval_cases (k % 4) <;> rfl
    · rw [testBit_nibbleMask_of_ge (by norm_num) (by omega),
        testBit_nibbleMask_of_ge (by norm_num) (by omega),
        testBit_nibbleMask_of_ge (by norm_num) (by omega),
        testBit_nibbleMask_of_ge (by norm_num) (by omega),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
  conv_lhs => rw [hsplit]
  simp only [natPoly_xor, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    natPoly_and_nibbleMask hx (by norm_num : (0 : ℕ) < 4),
    natPoly_and_nibbleMask hx (by norm_num : (1 : ℕ) < 4),
    natPoly_and_nibbleMask hx (by norm_num : (2 : ℕ) < 4),
    natPoly_and_nibbleMask hx (by norm_num : (3 : ℕ) < 4)]

/-! ## Products of masked operands -/

/-- The coefficients of a product of digit polynomials count pairs, so stay below `m + 2`. -/
theorem coeff_digits_mul_le (x y r s m : ℕ) : (digits x r * digits y s).coeff m ≤ m + 1 := by
  rw [coeff_mul]
  calc ∑ ij ∈ Finset.antidiagonal m, (digits x r).coeff ij.1 * (digits y s).coeff ij.2
      ≤ ∑ _ij ∈ Finset.antidiagonal m, 1 := by
        apply Finset.sum_le_sum
        intro ij _
        have h1 := coeff_digits_le x r ij.1
        have h2 := coeff_digits_le y s ij.2
        calc (digits x r).coeff ij.1 * (digits y s).coeff ij.2 ≤ 1 * 1 :=
              Nat.mul_le_mul h1 h2
          _ = 1 := rfl
    _ = m + 1 := by simp

/-- A product of digit polynomials has degree at most `30`. -/
theorem coeff_digits_mul_of_ge (x y r s m : ℕ) (hm : 31 ≤ m) :
    (digits x r * digits y s).coeff m = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_digits, coeff_digits]
  by_cases h : ij.1 < 16
  · rw [if_neg (show ¬ ij.2 < 16 by omega)]; simp
  · rw [if_neg h]; simp

/-- A product of masked operands is `2 ^ (r + s)` times a base-16 number. -/
theorem masked_mul_eq {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) {r s : ℕ}
    (hr : r < 4) (hs : s < 4) :
    (x &&& nibbleMask r) * (y &&& nibbleMask s) =
      2 ^ (r + s) * ∑ k ∈ Finset.range 31, (digits x r * digits y s).coeff k * 16 ^ k := by
  rw [and_nibbleMask_eq hx hr, and_nibbleMask_eq hy hs, ← eval_eq_sum_range' (n := 31)]
  · rw [eval_mul, pow_add]; ring
  · have : (digits x r * digits y s).natDegree ≤ 30 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      exact coeff_digits_mul_of_ge x y r s N (by exact_mod_cast hN)
    omega

/-- Bit `p` of a product of masked operands, at a position in its residue class. -/
theorem testBit_masked_mul {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) {r s : ℕ}
    (hr : r < 4) (hs : s < 4) {p : ℕ} (hp : p < 64) (hrs : r + s ≤ p)
    (hd : (p - (r + s)) % 4 = 0) :
    ((x &&& nibbleMask r) * (y &&& nibbleMask s) % 2 ^ 64).testBit p =
      decide ((digits x r * digits y s).coeff ((p - (r + s)) / 4) % 2 = 1) := by
  rw [Nat.testBit_mod_two_pow, decide_eq_true hp, Bool.true_and, masked_mul_eq hx hy hr hs,
    Nat.testBit_two_pow_mul, decide_eq_true hrs, Bool.true_and]
  obtain ⟨m, hm⟩ : ∃ m, p - (r + s) = 4 * m := ⟨(p - (r + s)) / 4, by omega⟩
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num), Nat.testBit_eq_decide_div_mod_eq,
    show (2 : ℕ) ^ (4 * m) = 16 ^ m by rw [pow_mul]; rfl, digit_parity _ (by omega)]
  intro k hk
  have := coeff_digits_mul_le x y r s k
  omega

/-- A product of masked operands has no bit below `r + s`. -/
theorem testBit_masked_mul_of_lt {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) {r s : ℕ}
    (hr : r < 4) (hs : s < 4) {p : ℕ} (hrs : p < r + s) :
    ((x &&& nibbleMask r) * (y &&& nibbleMask s) % 2 ^ 64).testBit p = false := by
  rw [Nat.testBit_mod_two_pow, masked_mul_eq hx hy hr hs, Nat.testBit_two_pow_mul]
  simp [show ¬ r + s ≤ p by omega]

/-! ## The masked multiply -/

/-- The wrapped integer product of residue class `r` of `x` by residue class `s` of `y`. -/
def maskedProduct (x y r s : ℕ) : ℕ := (x &&& nibbleMask r) * (y &&& nibbleMask s) % 2 ^ 64

/-- The low 64 bits of the carry-less product, from sixteen masked integer products. -/
def bmulNat (x y : ℕ) : ℕ :=
  let w := maskedProduct x y
  let z0 := w 0 0 ^^^ w 1 3 ^^^ w 2 2 ^^^ w 3 1
  let z1 := w 0 1 ^^^ w 1 0 ^^^ w 2 3 ^^^ w 3 2
  let z2 := w 0 2 ^^^ w 1 1 ^^^ w 2 0 ^^^ w 3 3
  let z3 := w 0 3 ^^^ w 1 2 ^^^ w 2 1 ^^^ w 3 0
  (z0 &&& nibbleMask 0) ||| (z1 &&& nibbleMask 1) ||| (z2 &&& nibbleMask 2) |||
    (z3 &&& nibbleMask 3)

/-- The contribution of residue classes `r` and `s` to coefficient `p` of the product. -/
noncomputable def term (x y r s p : ℕ) : ZMod 2 :=
  if r + s ≤ p ∧ (p - (r + s)) % 4 = 0 then
    ((digits x r * digits y s).coeff ((p - (r + s)) / 4) : ZMod 2)
  else 0

theorem term_eq_zero {x y r s p : ℕ} (h : (r + s) % 4 ≠ p % 4) : term x y r s p = 0 := by
  unfold term
  rw [if_neg]
  omega

theorem natCast_zmod_two (n : ℕ) : (n : ZMod 2) = if n % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod n 2]
  have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2 <;> simp

theorem ite_xor (a b : Bool) :
    (if (a ^^ b) = true then 1 else 0 : ZMod 2) =
      (if a = true then 1 else 0) + (if b = true then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- A masked product feeding the output residue of `p` contributes its term there. -/
theorem bit_masked_mul {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) {r s p : ℕ}
    (hr : r < 4) (hs : s < 4) (hp : p < 64) (h : (r + s) % 4 = p % 4) :
    (if (maskedProduct x y r s).testBit p = true then 1 else 0 : ZMod 2) = term x y r s p := by
  unfold term maskedProduct
  by_cases hrs : r + s ≤ p
  · have hd : (p - (r + s)) % 4 = 0 := by omega
    rw [testBit_masked_mul hx hy hr hs hp hrs hd, natCast_zmod_two]
    simp [hrs, hd]
  · rw [testBit_masked_mul_of_lt hx hy hr hs (by omega)]
    simp [hrs]

/-- Coefficient `p` of the product is the sum of the sixteen terms. -/
theorem coeff_natPoly_mul {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (p : ℕ) :
    (natPoly x * natPoly y).coeff p =
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4, term x y r s p := by
  rw [natPoly_eq_sum_nibbles hx, natPoly_eq_sum_nibbles hy, Finset.sum_mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro s _
  rw [show X ^ r * expand (ZMod 2) 4 (mod2 (digits x r)) *
        (X ^ s * expand (ZMod 2) 4 (mod2 (digits y s))) =
      X ^ (r + s) * expand (ZMod 2) 4 (mod2 (digits x r * digits y s)) by
    simp only [mod2, Polynomial.map_mul, map_mul, pow_add]; ring]
  rw [coeff_X_pow_mul', term]
  by_cases hrs : r + s ≤ p
  · rw [if_pos hrs, coeff_expand (by norm_num), coeff_map]
    by_cases hd : 4 ∣ p - (r + s)
    · rw [if_pos hd, if_pos ⟨hrs, by omega⟩]
      rfl
    · rw [if_neg hd, if_neg (by omega)]
  · rw [if_neg hrs, if_neg (by omega)]

theorem bmulNat_lt (x y : ℕ) : bmulNat x y < 2 ^ 64 := by
  have hm : ∀ r < 4, nibbleMask r < 2 ^ 64 := by
    intro r hr; unfold nibbleMask; interval_cases r <;> decide
  unfold bmulNat
  simp only
  apply Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_) ?_ <;>
    exact lt_of_le_of_lt Nat.and_le_right (hm _ (by norm_num))

/-- The masked multiply is the carry-less product, below degree `64`. -/
theorem coeff_natPoly_bmulNat {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) {p : ℕ}
    (hp : p < 64) : (natPoly (bmulNat x y)).coeff p = (natPoly x * natPoly y).coeff p := by
  rw [coeff_natPoly, coeff_natPoly_mul hx hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  unfold bmulNat
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    testBit_nibbleMask (by norm_num : (0 : ℕ) < 4) hp,
    testBit_nibbleMask (by norm_num : (1 : ℕ) < 4) hp,
    testBit_nibbleMask (by norm_num : (2 : ℕ) < 4) hp,
    testBit_nibbleMask (by norm_num : (3 : ℕ) < 4) hp]
  have ht : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 4 <;>
    simp only [decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, OfNat.ofNat_ne_zero, OfNat.zero_ne_ofNat, one_ne_zero, zero_ne_one,
      Nat.reduceEqDiff] <;>
    simp only [ite_xor] <;>
    rw [bit_masked_mul hx hy (by norm_num) (by norm_num) hp (by omega),
      bit_masked_mul hx hy (by norm_num) (by norm_num) hp (by omega),
      bit_masked_mul hx hy (by norm_num) (by norm_num) hp (by omega),
      bit_masked_mul hx hy (by norm_num) (by norm_num) hp (by omega)] <;>
    simp (disch := omega) only [term_eq_zero] <;>
    ring

end Plonky3Lean.Proofs.Binary
