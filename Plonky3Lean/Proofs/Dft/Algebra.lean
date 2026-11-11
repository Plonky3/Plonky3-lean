module

public import Plonky3Lean.Spec.Dft
public import Plonky3Lean.Proofs.Matrix.Interpolation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-!
# Facts about the transform

Inversion, the coset transform, and the reading of the transform as polynomial evaluation.

They follow Cormen et al., Introduction to Algorithms, section 30.2.
-/

namespace Plonky3Lean.Proofs.Dft

open Finset Polynomial Plonky3Lean.Spec.Dft

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

/-- Sums over j < n of omega^(i j) omega^(-l j) vanish unless i = l, for i, l < n. -/
theorem sum_pow_mul_inv_pow {ω : K} {n : ℕ} (hω : IsPrimitiveRoot ω n) {i l : ℕ} (hi : i < n)
    (hl : l < n) : ∑ j ∈ range n, ω ^ (i * j) * ω⁻¹ ^ (l * j) = if i = l then (n : K) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hterm : ∀ j, ω ^ (i * j) * ω⁻¹ ^ (l * j) = (ω ^ i * ω⁻¹ ^ l) ^ j := by
    intro j; rw [mul_pow, ← pow_mul, ← pow_mul]
  simp only [hterm]
  split_ifs with h
  · subst h
    rw [← mul_pow, mul_inv_cancel₀ hω0, one_pow]
    simp
  · set ζ := ω ^ i * ω⁻¹ ^ l
    have hζn : ζ ^ n = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm l, pow_mul, pow_mul, hω.pow_eq_one,
        inv_pow, hω.pow_eq_one]
      simp
    have hζ1 : ζ ≠ 1 := by
      intro h1
      have : ω ^ i = ω ^ l := by
        have := congrArg (· * ω ^ l) h1
        simp only [one_mul] at this
        rw [← this, mul_assoc, ← mul_pow, inv_mul_cancel₀ hω0, one_pow, mul_one]
      exact h (hω.pow_inj hi hl this)
    have := geom_sum_mul ζ n
    rw [hζn, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hζ1)

/-- The inverse transform undoes the transform. -/
theorem idft_dft {ω : K} {n : ℕ} [NeZero n] (hω : IsPrimitiveRoot ω n) (x : ℕ → V) {i : ℕ}
    (hi : i < n) : idft ω n (dft ω n x) i = x i := by
  have hn : (n : K) ≠ 0 := (hω.neZero').out
  have key : ∑ j ∈ range n, ω⁻¹ ^ (i * j) • ∑ l ∈ range n, ω ^ (j * l) • x l = (n : K) • x i := by
    simp_rw [smul_sum, smul_smul]
    rw [sum_comm, sum_congr rfl (g := fun l => (if l = i then (n : K) else 0) • x l)]
    · simp [hi]
    · intro l hl
      rw [← sum_smul]
      congr 1
      rw [← sum_pow_mul_inv_pow hω (mem_range.mp hl) hi]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_comm, mul_comm j l]
  unfold idft dft
  rw [key, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- The transform undoes the inverse transform. -/
theorem dft_idft {ω : K} {n : ℕ} [NeZero n] (hω : IsPrimitiveRoot ω n) (x : ℕ → V) {i : ℕ}
    (hi : i < n) : dft ω n (idft ω n x) i = x i := by
  have hn : (n : K) ≠ 0 := (hω.neZero').out
  have key : ∑ j ∈ range n, ω ^ (i * j) • ∑ l ∈ range n, ω⁻¹ ^ (j * l) • x l = (n : K) • x i := by
    simp_rw [smul_sum, smul_smul]
    rw [sum_comm, sum_congr rfl (g := fun l => (if i = l then (n : K) else 0) • x l)]
    · simp [hi]
    · intro l hl
      rw [← sum_smul]
      congr 1
      rw [← sum_pow_mul_inv_pow hω hi (mem_range.mp hl)]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_comm j l]
  unfold idft dft
  simp_rw [smul_comm _ ((n : K)⁻¹)]
  rw [← smul_sum, key, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Entry (n - r) mod n of the transform at omega is entry r of the transform at omega^(-1). -/
theorem dft_neg_index {ω : K} {n : ℕ} (hω : ω ^ n = 1) (x : ℕ → V) {r : ℕ} (hr : r < n) :
    dft ω n x ((n - r) % n) = dft ω⁻¹ n x r := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos n with h | h
    · omega
    · simp [zero_pow (by omega : n ≠ 0)] at hω
  simp only [dft]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    have : ω ^ ((n - r) * j) * ω ^ (r * j) = 1 := by
      rw [← pow_add, ← add_mul, Nat.sub_add_cancel hr.le, pow_mul, hω, one_pow]
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left this

/-- The coset transform is the transform of x_j s^j. -/
theorem cosetDft_eq (s ω : K) (n : ℕ) (x : ℕ → V) (i : ℕ) :
    cosetDft s ω n x i = dft ω n (fun j => (s ^ j) • x j) i := by
  simp only [cosetDft, dft, smul_smul]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rw [mul_pow, ← pow_mul]
  ring

/-- The inverse coset transform undoes the coset transform, for a nonzero shift. -/
theorem cosetIdft_cosetDft {s ω : K} {n : ℕ} [NeZero n] (hs : s ≠ 0) (hω : IsPrimitiveRoot ω n)
    (x : ℕ → V) {i : ℕ} (hi : i < n) : cosetIdft s ω n (cosetDft s ω n x) i = x i := by
  simp only [cosetIdft]
  rw [show cosetDft s ω n x = dft ω n (fun j => (s ^ j) • x j) from funext (cosetDft_eq s ω n x),
    idft_dft hω _ hi, smul_smul, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_smul]

/-- Linear maps commute with the transform. -/
theorem dft_map {U : Type _} [AddCommGroup U] [Module K U] (f : V →ₗ[K] U) (ω : K) (n : ℕ)
    (x : ℕ → V) (i : ℕ) : dft ω n (f ∘ x) i = f (dft ω n x i) := by
  simp [dft, map_sum, map_smul]

/-- For scalar entries, the transform evaluates the polynomial sum_j x_j X^j. -/
theorem eval_poly (n : ℕ) (x : ℕ → K) (z : K) :
    (poly n x).eval z = ∑ j ∈ range n, z ^ j • x j := by
  simp only [poly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
  exact sum_congr rfl fun j _ => mul_comm _ _

theorem degree_poly_lt (n : ℕ) (x : ℕ → K) : (poly n x).degree < n := by
  unfold poly
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j hj
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast mem_range.mp hj

/-- The polynomial of the inverse transform is the interpolant of the values at the powers of omega. -/
theorem poly_idft_eq_interpolant {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → K) :
    poly (2 ^ k) (idft ω (2 ^ k) x) = interpolant ω (2 ^ k) x := by
  unfold interpolant
  have hinj : Function.Injective (fun i : Fin (2 ^ k) => ω ^ i.val) := fun a b h =>
    Plonky3Lean.Proofs.Matrix.Interp.cosetPt_injective (g := 1) hω one_ne_zero
      (by simpa [Plonky3Lean.Proofs.Matrix.Interp.cosetPt] using h)
  refine Lagrange.eq_interpolate_of_eval_eq _ hinj.injOn
    (by rw [card_univ, Fintype.card_fin]; exact degree_poly_lt _ _) (fun i _ => ?_)
  rw [eval_poly]
  have := dft_idft hω x i.isLt
  simp only [dft] at this
  rw [← this]
  refine sum_congr rfl fun j _ => ?_
  rw [← pow_mul]

end Plonky3Lean.Proofs.Dft
