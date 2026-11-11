module

public import P3Commit.Encoder
public import Plonky3Lean.Proofs.Dft.Algebra
public import Plonky3Lean.Proofs.Dft.Basic

@[expose] public section

/-!
# p3-commit: the Reed-Solomon encoder

A message of height h = 2^k, at rate 2^(-r), is padded with zero rows to 2^(k + r) and transformed.

Column c of the codeword lists the message polynomial at the powers of omega = G_(k + r):

```text
    m_c(X) = sum_{j < h} m_(j, c) X^j,      codeword_(i, c) = m_c(omega^i),   0 <= i < 2^(k + r)
```

The padding panics exactly when the padded length leaves the word, or the rate is 64 or more.
-/

open Polynomial Finset
open p3_commit.encoder.mirror p3_commit.pcs.univariate.mirror p3_dft.mirror
open Plonky3Lean.Spec.Dft Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

/-- The padding keeps len 2^r exactly when the rate is below 64 and len 2^r fits the word. -/
theorem paddedLen_eq (len r : ℕ) :
    paddedLen len r = if r < 64 ∧ len * 2 ^ r < 2 ^ 64 then some (len * 2 ^ r) else none := by
  unfold paddedLen
  have hp : 0 < 2 ^ r := by positivity
  have hW : 0 < (2 : ℕ) ^ 64 := by positivity
  generalize (2 : ℕ) ^ 64 = W at *
  dsimp only
  by_cases h1 : 2 ^ 32 ≤ r
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
  by_cases h2 : 64 ≤ r
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
  by_cases hw : len * 2 ^ r < W
  · rw [Nat.mod_eq_of_lt hw, Nat.mul_div_cancel _ hp, ite_eq_left_of_eq_true _ _ (eq_true rfl),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hw⟩)]
  · have hlt : len * 2 ^ r % W / 2 ^ r < len := by
      rw [Nat.div_lt_iff_lt_mul hp]
      exact lt_of_lt_of_le (Nat.mod_lt _ hW) (not_lt.mp hw)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hlt.ne), ite_eq_right_of_eq_false _ _ (eq_false fun h => hw h.2)]

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The backend computes the transform on every power-of-two height the table covers. -/
def DftComputes (dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)) : Prop :=
  ∀ w k, k ≤ G.adicity → ∀ x, Computes (dft w (2 ^ k) x) (2 ^ k) (Spec.Dft.dft (G.gen k) (2 ^ k) x)

/-- The transform of a zero-padded column is its polynomial at the powers of omega. -/
theorem dft_pad_eval {w : ℕ} (ω : K) {k N : ℕ} (hkN : 2 ^ k ≤ N) (x f : ℕ → Fin w → K)
    (hx : ∀ j < N, x j = if j < 2 ^ k then f j else 0) (i : ℕ) (c : Fin w) :
    Spec.Dft.dft ω N x i c = (Spec.Dft.poly (2 ^ k) fun j => f j c).eval (ω ^ i) := by
  rw [eval_poly, Spec.Dft.dft, Finset.sum_apply, ← Finset.sum_range_add_sum_Ico _ hkN]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun j hj => by
    rw [hx j (Finset.mem_Ico.mp hj).2,
      ite_eq_right_of_eq_false _ _ (eq_false (by have := (Finset.mem_Ico.mp hj).1; omega))]; simp]
  rw [add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hx j (by omega), ite_eq_left_of_eq_true _ _ (eq_true hj'), Pi.smul_apply, ← pow_mul]

/-- A message of height 2^k encodes at rate 2^(-r).

The codeword lists the message polynomials at the 2^(k + r) powers of G_(k + r). -/
theorem encode_batch_eq {dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    (hdft : DftComputes G dft) (m : Mat K) {k r : ℕ} (hh : m.height = 2 ^ k) (hw : m.width ≠ 0)
    (hk : k + r ≤ G.adicity) (hr : r < 64) (hword : m.height * m.width * 2 ^ r < 2 ^ 64) :
    ∃ e, encode_batch dft m r = some ⟨2 ^ (k + r), m.width, e⟩ ∧
      ∀ i < 2 ^ (k + r), ∀ c,
        e i c = (Spec.Dft.poly (2 ^ k) fun j => m.entry j c).eval (G.gen (k + r) ^ i) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [add_zero] at hk ⊢
    obtain ⟨y, hy, hspec⟩ := hdft m.width k (by simpa using hk) m.entry
    refine ⟨y, ?_, fun i hi c => ?_⟩
    · simp [encode_batch, hh, hy]
    · rw [hspec i hi, dft_pad_eval _ le_rfl m.entry m.entry
        (fun j hj => by rw [ite_eq_left_of_eq_true _ _ (eq_true hj)])]
  · have hpl : paddedLen (m.height * m.width) r = some (m.height * m.width * 2 ^ r) := by
      rw [paddedLen_eq]; simp only [hr, hword, and_self, ite_true]
    have hht : heightOf (m.height * m.width * 2 ^ r) m.width = 2 ^ (k + r) := by
      rw [heightOf, ite_eq_right_of_eq_false _ _ (eq_false hw), Nat.mul_right_comm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hw), hh,
        pow_add]
    obtain ⟨y, hy, hspec⟩ := hdft m.width (k + r) hk
      fun j c => if j < m.height then m.entry j c else 0
    refine ⟨y, ?_, fun i hi c => ?_⟩
    · simp [encode_batch, hr0, hpl, hht, hy]
    · rw [hspec i hi, dft_pad_eval (k := k) _ (Nat.pow_le_pow_right (by norm_num) (by omega)) _ m.entry
        (fun j _ => by rw [hh]; split_ifs <;> rfl)]

/-- At a positive rate, a padded length that leaves the word, or a rate of 64 or more, panics. -/
theorem encode_batch_overflow (dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (m : Mat K) {r : ℕ} (hr : 0 < r) (h : ¬ (r < 64 ∧ m.height * m.width * 2 ^ r < 2 ^ 64)) :
    encode_batch dft m r = none := by
  rw [encode_batch, paddedLen_eq, ite_eq_right_of_eq_false _ _ (eq_false h)]
  simp [hr]

/-- Zero padding to a larger power of two keeps the polynomial. -/
theorem poly_pad {k N : ℕ} (hkN : 2 ^ k ≤ N) (f : ℕ → K) :
    Spec.Dft.poly N (fun j => if j < 2 ^ k then f j else 0) = Spec.Dft.poly (2 ^ k) f := by
  unfold Spec.Dft.poly
  rw [← Finset.sum_range_add_sum_Ico _ hkN, Finset.sum_eq_zero (s := Finset.Ico _ _) fun j hj => by
    dsimp only
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := (Finset.mem_Ico.mp hj).1; omega))]; simp,
    add_zero]
  exact Finset.sum_congr rfl fun j hj => by
    dsimp only
    rw [ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_range.mp hj))]

/-- The borrowed encoding, through the zero-padded copy and the padded encoding, gives the same codeword. -/
theorem encode_batch_borrowed_eq {dft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    (hdft : DftComputes G dft) (m : Mat K) {k r : ℕ} (hh : m.height = 2 ^ k) (hw : m.width ≠ 0)
    (hk : k + r ≤ G.adicity) (hr : r < 64) (hword : m.height * m.width * 2 ^ r < 2 ^ 64) :
    ∃ e, encode_batch_borrowed dft m r = some ⟨2 ^ (k + r), m.width, e⟩ ∧
      ∀ i < 2 ^ (k + r), ∀ c,
        e i c = (Spec.Dft.poly (2 ^ k) fun j => m.entry j c).eval (G.gen (k + r) ^ i) := by
  set P : Mat K := ⟨2 ^ (k + r), m.width, fun j c => if j < m.height then m.entry j c else 0⟩
  have hz : zero_padded m r = some P := by
    simp only [zero_padded, paddedLen_eq, hr, hword, and_self, ite_true, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq, P, heightOf,
      ite_eq_right_of_eq_false _ _ (eq_false hw)]
    congr 1
    rw [Nat.mul_right_comm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hw), hh, pow_add]
  obtain ⟨e, he, hspec⟩ := encode_batch_eq G hdft P (k := k + r) (r := 0) rfl hw (by simpa using hk)
    (by omega) (by
      show 2 ^ (k + r) * m.width * 2 ^ 0 < 2 ^ 64
      rw [pow_zero, mul_one, pow_add, ← hh, Nat.mul_right_comm]; exact hword)
  refine ⟨e, ?_, fun i hi c => ?_⟩
  · simp only [encode_batch_borrowed, hz, Option.bind_eq_bind, Option.bind_some, encode_batch_padded,
      P, log2Strict_pow, show r ≤ k + r by omega, ite_true]
    simpa using he
  · rw [hspec i (by simpa using hi) c]
    simp only [P, hh, add_zero]
    rw [poly_pad (Nat.pow_le_pow_right (by norm_num) (by omega))]

end Plonky3Lean.Proofs.Commit
