module

public import Plonky3Lean.Proofs.Circle.CfftInv
public import Plonky3Lean.Proofs.Circle.Ordering

@[expose] public section

/-!
# p3-circle: the circle FFT on standard domains

On a standard domain no twiddle is zero: every twiddle is a coordinate of a point of order at least 8, or a y-coordinate of a point of order at least 4.

So interpolate never panics there, and it inverts evaluate.

The row order of the transforms is the circle FFT order: row i holds the value at natural point sigma(i).
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft p3_circle.ordering.mirror p3_circle.point.mirror

set_option linter.unusedSectionVars false

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K]

theorem y_ne_zero_of_order {P : C K} (h : ¬ addOrderOf P ∣ 2) : P.y ≠ 0 := by
  intro hy
  apply h
  apply addOrderOf_dvd_of_nsmul_eq_zero
  refine C.ext ?_ ?_
  · rw [C.two_nsmul_x, C.zero_x]; linear_combination 2 * P.eq - 2 * P.y * hy
  · rw [C.two_nsmul_y, C.zero_y, hy, mul_zero]

theorem x_ne_zero_of_order {P : C K} (h : ¬ addOrderOf P ∣ 4) : P.x ≠ 0 := by
  intro hx
  apply h
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul]
  refine C.ext ?_ ?_
  · rw [C.two_nsmul_x, C.two_nsmul_x, C.zero_x, hx]; ring
  · rw [C.two_nsmul_y, C.two_nsmul_x, C.two_nsmul_y, C.zero_y, hx]; ring

theorem le_of_two_pow_dvd {a b c : ℕ} (h : 2 ^ a ∣ 2 ^ b * (2 * c + 1)) : a ≤ b := by
  have hc : Nat.Coprime (2 ^ a) (2 * c + 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_two_mul_add_one c))
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hc.dvd_of_dvd_mul_right h)

variable [DecidableEq K] {G : p3_dft.mirror.Gen (K × K)}

/-- On a standard domain of size 2^n, every twiddle is nonzero. -/
theorem twC_standard_ne_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) {j b : ℕ} (hj : j < n) :
    twC (genPt G (n + 1)) (genPt G (n - 1)) n j b ≠ 0 := by
  set S := genPt G (n + 1)
  have hS : addOrderOf S = 2 ^ (n + 1) := addOrderOf_genPt hV h2 hG
  have hg : genPt G (n - 1) = 4 • S := by
    rw [← genPt_nsmul hV (show n - 1 ≤ n + 1 by omega) hG, show n + 1 - (n - 1) = 2 by omega]; rfl
  have hpt : S + rev (n - 1 - j) b • genPt G (n - 1) = (2 * (2 * rev (n - 1 - j) b) + 1) • S := by
    rw [hg, smul_smul, add_comm, ← succ_nsmul]; ring_nf
  have hpt0 : S + rev (n - 1) b • genPt G (n - 1) = (2 * (2 * rev (n - 1) b) + 1) • S := by
    rw [hg, smul_smul, add_comm, ← succ_nsmul]; ring_nf
  unfold twC
  split_ifs with h0
  · rw [hpt0]
    apply y_ne_zero_of_order
    intro hd
    have := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
    rw [smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hS, show 2 * (2 * (2 * rev (n - 1) b) + 1) =
      2 ^ 1 * (2 * (2 * rev (n - 1) b) + 1) by ring] at this
    have := le_of_two_pow_dvd this
    omega
  · rw [hpt, smul_smul]
    apply x_ne_zero_of_order
    intro hd
    have := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
    rw [smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hS, show 4 * (2 ^ (j - 1) *
      (2 * (2 * rev (n - 1 - j) b) + 1)) = 2 ^ (j + 1) * (2 * (2 * rev (n - 1 - j) b) + 1) by
        rw [show j + 1 = (j - 1) + 2 by omega, pow_add]; ring] at this
    have := le_of_two_pow_dvd this
    omega


omit [DecidableEq K] in
/-- Row i of the transforms holds the natural point sigma(i) of the twin coset. -/
theorem ptAt_eq_twinPoint {n : ℕ} (hn : 1 ≤ n) (S g : C K) (hg : 2 ^ (n - 1) • g = 0) {i : ℕ}
    (hi : i < 2 ^ n) : ptAt S g n i = twinPoint S g (cfft_permute_index i n) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hg
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
  · have ha : a < 2 ^ n := by rw [pow_succ] at hi; omega
    rw [cfft_permute_index_even ha]
    simp [ptAt, twinPoint]
  · have ha : a < 2 ^ n := by rw [pow_succ] at hi; omega
    have hc := Plonky3Lean.Proofs.Matrix.bitRev_lt n a
    rw [cfft_permute_index_odd ha, rev_complement n ha]
    simp only [ptAt, twinPoint, show (2 * a + 1) % 2 = 1 by omega, show (2 * a + 1) / 2 = a by omega,
      one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      show (2 * (2 ^ n - 1 - rev n a) + 1) % 2 = 1 by omega,
      show (2 * (2 ^ n - 1 - rev n a) + 1) / 2 = 2 ^ n - 1 - rev n a by omega]
    rw [show 2 ^ n - 1 - rev n a + 1 = 2 ^ n - rev n a by omega, neg_add, sub_nsmul _ hc.le, hg]
    abel

/-- On the standard domain of size 2^n, evaluate of 2^m coefficients holds at row i the value of their polynomial at the natural point sigma(i), that is at (2 sigma(i) + 1) Q. -/
theorem evaluate_standard {V : Type} [AddCommGroup V] [Module K V] (hV : CircleGenValid G)
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hG : n + 1 ≤ G.adicity) (x : ℕ → V) :
    ∃ y, p3_circle.cfft.mirror.evaluate G ⟨n, ofC (genPt G (n + 1))⟩ (2 ^ m) x = some y ∧
      ∀ i < 2 ^ n, y i = fftEval m x ((2 * cfft_permute_index i n + 1) • genPt G (n + 1)) := by
  obtain ⟨y, hy, hyi⟩ := evaluate_eq hV hm hmn (by omega) (genPt G (n + 1)) x
  refine ⟨y, hy, fun i hi => ?_⟩
  have hg : 2 ^ (n - 1) • genPt G (n - 1) = 0 := by
    rw [← genPt_zero hV, ← genPt_nsmul hV (j := 0) (k := n - 1) (Nat.zero_le _) (by omega), Nat.sub_zero]
  rw [hyi i hi, ptAt_eq_twinPoint (by omega) _ _ hg hi, twinPoint_standard hV (by omega) hG]

/-- On the standard domain of size 2^n, interpolate never panics, and returns coefficients whose polynomial takes value i at the natural point sigma(i). -/
theorem interpolate_standard {V : Type} [AddCommGroup V] [Module K V] (hV : CircleGenValid G)
    (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n) (hG : n + 1 ≤ G.adicity) (v : ℕ → V) :
    ∃ cs, p3_circle.cfft.mirror.interpolate G ⟨n, ofC (genPt G (n + 1))⟩ v = some cs ∧
      ∀ i < 2 ^ n, fftEval n cs ((2 * cfft_permute_index i n + 1) • genPt G (n + 1)) = v i := by
  obtain ⟨cs, hcs, hi⟩ := interpolate_spec hV h2 hn (by omega) (genPt G (n + 1))
    (fun j hj b _ => twC_standard_ne_zero hV h2 hn hG hj) v
  refine ⟨cs, hcs, fun i hi' => ?_⟩
  have hg : 2 ^ (n - 1) • genPt G (n - 1) = 0 := by
    rw [← genPt_zero hV, ← genPt_nsmul hV (j := 0) (k := n - 1) (Nat.zero_le _) (by omega), Nat.sub_zero]
  rw [← hi i hi', ptAt_eq_twinPoint hn _ _ hg hi', twinPoint_standard hV hn hG]


/-! ## The basis -/

omit [DecidableEq K] in
theorem basis_one_list (P : C K) : (List.range (2 ^ 1)).map (fun j => basis 1 j P) = [1, P.y] := by
  simp [basis, bit, List.range_succ]

omit [DecidableEq K] in
theorem basis_list_succ {k : ℕ} (hk : 1 ≤ k) (P : C K) :
    (List.range (2 ^ (k + 1))).map (fun j => basis (k + 1) j P) =
      (List.range (2 ^ k)).map (fun j => basis k j P) ++
        ((List.range (2 ^ k)).map (fun j => basis k j P)).map (· * vn k P) := by
  rw [pow_succ, mul_two, List.range_add, List.map_append, List.map_map, List.map_map]
  congr 1
  · exact List.map_congr_left fun j hj => basis_succ_low hk (by simpa using hj) P
  · exact List.map_congr_left fun j hj => by
      simp only [Function.comp_apply]
      rw [add_comm (2 ^ k) j, basis_succ_high hk (by simpa using hj)]

/-- circle_basis lists the FFT basis of Definition 4 at the point, b_0, ..., b_(2^n - 1), and panics at n = 0. -/
theorem circle_basis_eq (P : C K) {n : ℕ} (hn : 1 ≤ n) :
    p3_circle.cfft.mirror.circle_basis (ofC P) n = some ((List.range (2 ^ n)).map fun j => basis n j P) := by
  have loop : ∀ k, (List.range k).foldl
      (fun (acc : List K × K) _ => (acc.1 ++ acc.1.map (· * acc.2), Point.vnStep acc.2)) ([1, P.y], P.x) =
      ((List.range (2 ^ (k + 1))).map (fun j => basis (k + 1) j P), vn (k + 1) P) := by
    intro k
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, zero_add, vn, Nat.sub_self, pow_zero, one_smul]
      refine Prod.ext ?_ rfl
      simp [basis, bit, List.range_succ]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        basis_list_succ (k := k + 1) (by omega)]
      refine Prod.ext rfl ?_
      simp only [vn, Nat.add_sub_cancel]
      rw [vnStep_x, smul_smul, ← pow_succ']
  unfold p3_circle.cfft.mirror.circle_basis
  simp only [show ¬ n < 1 by omega, ↓reduceIte, ofC_y, ofC_x, loop (n - 1),
    show n - 1 + 1 = n by omega]
  simp

end Plonky3Lean.Proofs.Circle
