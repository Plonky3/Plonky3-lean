module

public import Plonky3Lean.Proofs.Fri.Matrix
public import Plonky3Lean.Proofs.Dft.Algebra
public import P3Fri.Verifier

@[expose] public section

/-!
# The final polynomial

The prover keeps the first 2^L values of the final codeword, un-bit-reverses them and inverse-transforms them.

Suppose the final codeword is the codeword of a polynomial of degree below 2^L.

Then this gives its coefficients, constant term first.

The verifier evaluates them with Horner's rule at G_H^rev_H(i).

That is the point of index i of the final codeword.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_dft.mirror p3_fri.verifier.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

theorem horner_eq_sum (coeffs : List K) (x : K) :
    horner coeffs x = ∑ i ∈ range coeffs.length, coeffs.getD i 0 * x ^ i := by
  induction coeffs with
  | nil => simp [horner]
  | cons c cs ih =>
    rw [horner, List.foldr_cons, ← horner, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Finset.sum_mul]
    simp only [mul_assoc]

theorem getD_map_range' {α : Type _} [Zero α] {f : ℕ → α} {n r : ℕ} (hr : r < n) :
    ((List.range n).map f).getD r 0 = f r := by
  rw [List.getD_eq_getElem _ _ (by simpa using hr)]; simp

variable (G : Gen K) (hV : GenValid G) (hN : GenNested G)
include hV hN

/-- Point i of the subgroup of order 2^F is G_H^rev_H(i), for F <= H. -/
theorem dom_eq_of_le {F H i : ℕ} (hFH : F ≤ H) (hHa : H ≤ G.adicity) (hi : i < 2 ^ F) :
    G.gen H ^ bitRev H i = dom G F i := by
  rw [dom, bitRev_eq, show H = F + (H - F) by omega, Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt hi,
    ← bitRev_eq, mul_comm, pow_mul, ← Plonky3Lean.Proofs.Commit.gen_sub G hN (show F + (H - F) ≤ G.adicity by omega)
      (by omega), show F + (H - F) - (H - F) = F by omega]

/-- The final check passes on an honest final codeword.

Take its first 2^L values, un-bit-reverse them and inverse-transform them.

The result evaluates back to every value of the codeword. -/
theorem final_poly_eval {P : K[X]} {L b : ℕ} (hLb : L + b ≤ G.adicity) {wF : List K}
    (hc : IsCodeword G P (L + b) wF) (hdeg : P.degree < ↑(2 ^ L)) {coeffs : List K}
    (hlen : coeffs.length = 2 ^ L)
    (hco : ∀ i < 2 ^ L, coeffs.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen L) (2 ^ L) (fun j => (revIndex (2 ^ L) (wF.take (2 ^ L))).getD j 0) i)
    {H i : ℕ} (hH : L + b ≤ H) (hHa : H ≤ G.adicity) (hi : i < 2 ^ (L + b)) :
    horner coeffs (G.gen H ^ bitRev H i) = wF.getD i 0 := by
  have hω := hV L (by omega)
  have hnat : P.natDegree < 2 ^ L := by
    rcases eq_or_ne P 0 with rfl | hP
    · simp
    · exact (natDegree_lt_iff_degree_lt hP).2 hdeg
  -- The un-bit-reversed prefix lists P at the powers of G_L.
  have hev : ∀ j < 2 ^ L, (revIndex (2 ^ L) (wF.take (2 ^ L))).getD j 0 =
      Plonky3Lean.Spec.Dft.dft (G.gen L) (2 ^ L) (fun l => P.coeff l) j := by
    intro j hj
    have hbr := bitRev_lt' L j
    simp only [revIndex, Nat.log_pow (by norm_num : 1 < 2)]
    have hbr' : bitRev L j < 2 ^ (L + b) := lt_of_lt_of_le hbr (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [getD_map_range' hj, List.getD_eq_getElem _ _ (by rw [List.length_take, hc.1]; omega), List.getElem_take,
      ← List.getD_eq_getElem _ 0, hc.2 _ hbr',
      dom, bitRev_eq, Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt (by rw [← bitRev_eq]; exact hbr),
      Plonky3Lean.Proofs.Matrix.bitRev_bitRev hj,
      mul_comm, pow_mul, ← Plonky3Lean.Proofs.Commit.gen_sub G hN hLb (by omega),
      show L + b - b = L by omega, eval_eq_sum_range' hnat, Plonky3Lean.Spec.Dft.dft]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, ← pow_mul, mul_comm]
  have hcoef : ∀ k < 2 ^ L, coeffs.getD k 0 = P.coeff k := by
    intro k hk
    rw [hco k hk, ← @idft_dft K _ K _ _ (G.gen L) (2 ^ L) ⟨by positivity⟩ hω (fun l => P.coeff l) k hk]
    simp only [Plonky3Lean.Spec.Dft.idft]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [hev j (Finset.mem_range.1 hj)]
  rw [dom_eq_of_le G hV hN hH hHa hi, hc.2 i hi, horner_eq_sum, hlen, eval_eq_sum_range' hnat]
  exact Finset.sum_congr rfl fun k hk => by rw [hcoef k (Finset.mem_range.1 hk)]

end Plonky3Lean.Proofs.Fri
