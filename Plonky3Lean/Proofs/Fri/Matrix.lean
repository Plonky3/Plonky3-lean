module

public import Plonky3Lean.Proofs.Fri.Row
public import Plonky3Lean.Proofs.Commit.Coset

@[expose] public section

/-!
# The matrix fold on its scalar paths

A codeword of log height N stores P(G_N^rev_N(i)) at index i.

One arity-2 pass maps it to the codeword of the fold of P by 2, of log height N - 1.

The scalar paths of the matrix fold are such passes.

So they return, row by row, the row fold the verifier computes.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]


theorem length_flatMap_blocks {α : Type _} (f : ℕ → List α) (L : ℕ) :
    ∀ n, (∀ i < n, (f i).length = L) → ((List.range n).flatMap f).length = n * L
  | 0, _ => by simp
  | n + 1, hf => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_blocks f L n (fun i hi => hf i (by omega))]
    simp [hf n (by omega)]; ring

/-- Reading a concatenation of blocks of length L: entry i L + c is entry c of block i. -/
theorem getD_flatMap_blocks {α : Type _} [Zero α] (f : ℕ → List α) (L : ℕ) :
    ∀ (n : ℕ), (∀ i < n, (f i).length = L) → ∀ (i c : ℕ), i < n → c < L →
      ((List.range n).flatMap f).getD (i * L + c) 0 = (f i).getD c 0
  | 0, _, _, _, hi, _ => absurd hi (by omega)
  | n + 1, hf, i, c, hi, hc => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen := length_flatMap_blocks f L n (fun i hi => hf i (by omega))
    simp only [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i n with hin | hin
    · rw [List.getElem?_append_left (by rw [hlen]; nlinarith)]
      have := getD_flatMap_blocks f L n (fun i hi => hf i (by omega)) i c hin hc
      simpa only [List.getD_eq_getElem?_getD] using this
    · obtain rfl : i = n := by omega
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

/-- Point i of the bit-reversed subgroup of order 2^N: G_N^rev_N(i). -/
def dom (G : Gen K) (N i : ℕ) : K := G.gen N ^ bitRev N i

/-- A list is the codeword of Q at log height N. -/
def IsCodeword (G : Gen K) (Q : K[X]) (N : ℕ) (d : List K) : Prop :=
  d.length = 2 ^ N ∧ ∀ i < 2 ^ N, d.getD i 0 = Q.eval (dom G N i)

theorem getD_foldPairs {β : K} {tbl d : List K} {n i : ℕ} (hi : i < n) :
    (foldPairs β tbl d n).getD i 0 = foldPair (d.getD (2 * i) 0) (d.getD (2 * i + 1) 0) β (tbl.getD i 0) := by
  rw [foldPairs, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

variable (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
include hV hN

/-- Row t of a codeword of log height n + k lies on the coset of G_(n + k)^rev_n(t), in bit-reversed order. -/
theorem dom_row {n k t j : ℕ} (hnk : n + k ≤ G.adicity) (hj : j < 2 ^ k) :
    dom G (n + k) (t * 2 ^ k + j) = revCoset (G.gen (n + k) ^ bitRev n t) (G.gen k) k ⟨j, hj⟩ := by
  rw [dom, bitRev_split n k t j hj, revCoset, pow_add, mul_comm, pow_mul, ← pow_mul,
    mul_comm (bitRev k j), pow_mul, ← Plonky3Lean.Proofs.Commit.gen_sub G hN hnk (by omega),
    Nat.add_sub_cancel_left]

/-- The shift of row t, raised to 2^k, is point t of the folded subgroup. -/
theorem rowShift_pow {n k : ℕ} (hnk : n + k ≤ G.adicity) (t : ℕ) :
    (G.gen (n + k) ^ bitRev n t) ^ 2 ^ k = dom G n t := by
  rw [dom, ← pow_mul, mul_comm, pow_mul, ← Plonky3Lean.Proofs.Commit.gen_sub G hN hnk (by omega),
    Nat.add_sub_cancel]

include h2

/-- The fold of row t of the codeword of P is the fold of P by 2^k at point t of the folded subgroup. -/
theorem fold_row_codeword {P : K[X]} {n k : ℕ} (hnk : n + k ≤ G.adicity) {d : List K}
    (hd : IsCodeword G P (n + k) d) {t : ℕ} (ht : t < 2 ^ n) (β : K) :
    foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => d.getD (t * 2 ^ k + j.val) 0) β =
      (polyFold P (2 ^ k) β).eval (dom G n t) := by
  have hs : G.gen (n + k) ^ bitRev n t ≠ 0 := pow_ne_zero _ ((hV _ hnk).ne_zero (by positivity))
  have hrow : (fun j : Fin (2 ^ k) => d.getD (t * 2 ^ k + j.val) 0) =
      fun j => P.eval (revCoset (G.gen (n + k) ^ bitRev n t) (G.gen k) k j) := by
    funext j
    rw [hd.2 _ (by rw [pow_add]; nlinarith [j.2]), dom_row G hV hN hnk j.2]
  rw [hrow, foldValue_eval P (hV k (by omega)) hs, rowShift_pow G hV hN hnk]

/-- A halving table valid up to log height N: entry i at log height M is G_M^(-rev_(M-1)(i)) / 2. -/
def IsHalveTable (N : ℕ) (tbl : List K) : Prop :=
  ∀ M, 1 ≤ M → M ≤ N → ∀ i < 2 ^ (M - 1), tbl.getD i 0 = 1 / 2 * (G.gen M)⁻¹ ^ bitRev (M - 1) i

/-- The bit-reversed table of G_N^(-i) / 2 is valid at every log height up to N.

Its prefixes are the smaller tables. -/
theorem halveTable_full {N : ℕ} (hN1 : 1 ≤ N) (hNa : N ≤ G.adicity) :
    IsHalveTable G N (revIndex (2 ^ (N - 1)) (shiftedPowersList (G.gen N)⁻¹ (1 / 2) (2 ^ (N - 1)))) := by
  intro M hM1 hMN i hi
  have hi' : i < 2 ^ (N - 1) := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hr : bitRev (N - 1) i = bitRev (M - 1) i * 2 ^ (N - M) := by
    rw [show N - 1 = (M - 1) + (N - M) by omega, bitRev_eq,
      Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt hi, ← bitRev_eq]
  simp only [revIndex, Nat.log_pow (by norm_num : 1 < 2), shiftedPowersList]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ (by simpa using bitRev_lt' (N - 1) i), List.getElem_map,
    List.getElem_range, hr, mul_comm (bitRev (M - 1) i), pow_mul, inv_pow,
    ← Plonky3Lean.Proofs.Commit.gen_sub G hN hNa (by omega : N - M ≤ N),
    show N - (N - M) = M by omega]

/-- One arity-2 pass maps the codeword of Q at log height M to the codeword of the fold of Q by 2. -/
theorem foldPairs_codeword {Q : K[X]} {M : ℕ} (hM1 : 1 ≤ M) (hMa : M ≤ G.adicity) {tbl : List K}
    (ht : ∀ i < 2 ^ (M - 1), tbl.getD i 0 = 1 / 2 * (G.gen M)⁻¹ ^ bitRev (M - 1) i) {d : List K}
    (hd : IsCodeword G Q M d) (β : K) :
    IsCodeword G (polyFold Q 2 β) (M - 1) (foldPairs β tbl d (2 ^ (M - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  refine ⟨by simp [foldPairs], fun i hi => ?_⟩
  have hx : G.gen (m + 1) ^ bitRev m i ≠ 0 := pow_ne_zero _ ((hV _ hMa).ne_zero (by positivity))
  have hrow := fold_row_codeword G hV hN h2 (n := m) (k := 1) hMa hd hi β
  have hfun : (fun j : Fin (2 ^ 1) => d.getD (i * 2 ^ 1 + j.val) 0) =
      ![d.getD (2 * i) 0, d.getD (2 * i + 1) 0] := by
    funext j; fin_cases j <;> simp [mul_comm]
  rw [hfun, foldValue_two (hV 1 (by omega)) hx h2, pow_one] at hrow
  rw [← hrow, getD_foldPairs hi, foldPair, ht i hi, ← two_mul, mul_inv, inv_pow, one_div]

/-- The later passes: r more passes, with beta, beta^2, ..., give the codeword of the fold by 2^r. -/
theorem foldRounds_codeword {N : ℕ} (hNa : N ≤ G.adicity) {tbl : List K} (ht : IsHalveTable G N tbl) :
    ∀ (r M : ℕ) (Q : K[X]) (β : K) (d : List K), M ≤ N → r ≤ M → IsCodeword G Q M d →
      IsCodeword G (polyFold Q (2 ^ r) β) (M - r) (foldRounds tbl r β d)
  | 0, M, Q, β, d, _, _, hd => by
    have h1 : polyFold Q 1 β = Q := by ext m; simp [coeff_polyFold]
    simpa [foldRounds, h1] using hd
  | r + 1, M, Q, β, d, hMN, hr, hd => by
    have hp := foldPairs_codeword G hV hN h2 (by omega) (by omega)
      (ht M (by omega) hMN) hd β
    rw [foldRounds, hd.1, show 2 ^ M / 2 = 2 ^ (M - 1) by
      rw [show M = M - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]]
    have := foldRounds_codeword hNa ht r (M - 1) _ (β ^ 2) _ (by omega) (by omega) hp
    rwa [← polyFold_two_pow, show M - 1 - r = M - (r + 1) by omega] at this

/-- The scalar matrix fold maps the codeword of P at log height n + k to the codeword of its fold.

The fold is by 2^k, at log height n. -/
theorem fold_matrix_scalar_codeword {P : K[X]} {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity)
    {v : List K} (hv : IsCodeword G P (n + k) v) (β : K) :
    ∃ L, fold_matrix_scalar G β k v = some L ∧ IsCodeword G (polyFold P (2 ^ k) β) n L := by
  have hg : G.gen (n + k) ≠ 0 := (hV _ hnk).ne_zero (by positivity)
  have hlen : v.length / 2 ^ k = 2 ^ n := by rw [hv.1, pow_add, Nat.mul_div_cancel _ (by positivity)]
  unfold fold_matrix_scalar
  simp only [hlen, Option.bind_eq_bind]
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    simp only [↓reduceIte, log2Strict_pow, Option.bind_some, gen_get_of_le G hnk, inv,
      p3_commit.domain.mirror.inv, hg]
    have := foldPairs_codeword G hV hN h2 (M := n + 1) (by omega) hnk
      (halveTable_full G hV hN h2 (N := n + 1) (by omega) hnk (n + 1) (by omega) le_rfl) hv β
    simp only [Nat.add_sub_cancel] at this
    exact ⟨_, rfl, by simpa using this⟩
  · have hih : 2 ^ n * (2 ^ k / 2) = 2 ^ (n + k - 1) := by
      rw [show n + k - 1 = n + (k - 1) by omega, pow_add, show 2 ^ k = 2 ^ (k - 1) * 2 by
        rw [← pow_succ]; congr 1; omega, Nat.mul_div_cancel _ (by norm_num)]
    have hN1 : n + k - 1 + 1 = n + k := by omega
    simp only [show k ≠ 1 by omega, ↓reduceIte, show 2 ^ k % 2 = 0 by
      rw [show k = k - 1 + 1 by omega, pow_succ]; simp, hih, log2Strict_pow, Option.bind_some, hN1,
      gen_get_of_le G hnk, inv, p3_commit.domain.mirror.inv, hg, ne_eq, not_true_eq_false]
    have ht := halveTable_full G hV hN h2 (N := n + k) (by omega) hnk
    have hp := foldPairs_codeword G hV hN h2 (M := n + k) (by omega) hnk (ht (n + k) (by omega) le_rfl) hv β
    rw [show n + k - 1 = n + k - 1 from rfl] at hp
    have := foldRounds_codeword G hV hN h2 hnk ht (k - 1) (n + k - 1) _ (β ^ 2) _ (by omega) (by omega) hp
    rw [← polyFold_two_pow, show k - 1 + 1 = k by omega, show n + k - 1 - (k - 1) = n by omega] at this
    exact ⟨_, rfl, this⟩

/-- The polynomial of degree below 2^N through a word on the bit-reversed subgroup of order 2^N. -/
noncomputable def wordPoly (N : ℕ) (v : List K) : K[X] :=
  Lagrange.interpolate univ (fun i : Fin (2 ^ N) => dom G N i) (fun i => v.getD i 0)

omit hN h2 in
theorem dom_eq_revCoset (N : ℕ) (i : Fin (2 ^ N)) : dom G N i = revCoset 1 (G.gen N) N i := by
  simp [dom, revCoset]

omit hN h2 in
/-- Every word of length 2^N is the codeword of its polynomial. -/
theorem isCodeword_wordPoly {N : ℕ} (hNa : N ≤ G.adicity) {v : List K} (hv : v.length = 2 ^ N) :
    IsCodeword G (wordPoly G N v) N v := by
  refine ⟨hv, fun i hi => ?_⟩
  have hinj : Function.Injective fun i : Fin (2 ^ N) => dom G N i := by
    intro i j h
    have h' : dom G N i = dom G N j := h
    rw [dom_eq_revCoset G hV, dom_eq_revCoset G hV] at h'
    exact revCoset_injective (hV N hNa) one_ne_zero h'
  have := Lagrange.eval_interpolate_at_node (fun i : Fin (2 ^ N) => v.getD i 0) hinj.injOn
    (mem_univ ⟨i, hi⟩)
  exact this.symm

/-- The prover's matrix fold returns, for each row, the verifier's row fold.

This holds on every word, not only on codewords. -/
theorem fold_matrix_scalar_rows {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K}
    (hv : v.length = 2 ^ (n + k)) (β : K) :
    fold_matrix_scalar G β k v = some ((List.range (2 ^ n)).map fun t =>
      foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => v.getD (t * 2 ^ k + j.val) 0) β) := by
  have hc := isCodeword_wordPoly G hV hnk hv
  obtain ⟨L, hL, hLc⟩ := fold_matrix_scalar_codeword G hV hN h2 hk hnk hc β
  rw [hL]
  congr 1
  apply List.ext_getElem
  · simp [hLc.1]
  · intro t h1 h2'
    have ht : t < 2 ^ n := by simpa [hLc.1] using h1
    rw [List.getElem_map, List.getElem_range, fold_row_codeword G hV hN h2 hnk hc ht β, ← hLc.2 t ht,
      List.getD_eq_getElem]

/-- Fold two codeword values of Q at log height m + 1 with arity 2.

This gives the fold of Q by 2 at point i of log height m. -/
theorem foldPair_dom (Q : K[X]) {m i : ℕ} (hm : m + 1 ≤ G.adicity) (hi : i < 2 ^ m) (β : K) :
    foldPair (Q.eval (dom G (m + 1) (2 * i))) (Q.eval (dom G (m + 1) (2 * i + 1))) β
        (1 / 2 * (G.gen (m + 1))⁻¹ ^ bitRev m i) = (polyFold Q 2 β).eval (dom G m i) := by
  set d := (List.range (2 ^ (m + 1))).map fun j => Q.eval (dom G (m + 1) j)
  have hd : IsCodeword G Q (m + 1) d := ⟨by simp [d], fun j hj => by
    simp [d, List.getD_eq_getElem?_getD, hj]⟩
  have ht := halveTable_full G hV hN h2 (N := m + 1) (by omega) hm (m + 1) (by omega) le_rfl
  have hc := foldPairs_codeword G hV hN h2 (M := m + 1) (by omega) hm ht hd β
  simp only [Nat.add_sub_cancel] at hc ht
  rw [← hc.2 i hi, getD_foldPairs hi, ht i hi]
  have h1 : 2 * i < 2 ^ (m + 1) := by rw [pow_succ]; omega
  have h2' : 2 * i + 1 < 2 ^ (m + 1) := by rw [pow_succ]; omega
  rw [hd.2 _ h1, hd.2 _ h2']

end Plonky3Lean.Proofs.Fri
