module

public import Plonky3Lean.Proofs.Fri.Robust
public import Plonky3Lean.Proofs.Fri.Reduce
public import Plonky3Lean.Proofs.Fri.Final
public import Plonky3Lean.Proofs.Fri.Transcript
public import Plonky3Lean.Proofs.Fri.Hiding
public import Plonky3Lean.Proofs.Fri.Packed
public import Plonky3Lean.Proofs.Commit.BabyBear

@[expose] public section

/-!
# p3-fri: claims

The crate is transcribed over a field K, not extracted.

The specification is the FRI folding operator of Ben-Sasson, Bentov, Horesh and Riabzev, ICALP 2018:

```text
    p(X) = sum_{j < a} X^j p_j(X^a),     fold(p, a, beta) = sum_{j < a} beta^j p_j
```

and the reduced opening of Haböck's summary, eprint 2022/1216:

```text
    R(x) = sum_k sum_i alpha^(off_k + i) (y_(k,i) - c_(k,i)) / (z_k - x)
```

A codeword of log height N stores P(G_N^rev_N(i)) at index i, for the generator table G.

The field facts are hypotheses: the table is primitive and nested, and 2 is invertible.

BabyBear and every extension of it satisfy them, the quartic one included.
-/

open Polynomial Finset
open Plonky3Lean.Spec.Fri Plonky3Lean.Proofs.Fri Plonky3Lean.Proofs.Dft
open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_fri.two_adic_pcs.mirror p3_fri.verifier.mirror
open p3_fri.transcript.mirror p3_fri.hiding_pcs.mirror p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Fri

/-! ## The folding operator -/

section fold

variable {K : Type} [Field K]

/-- The splitting identity: p(x) = sum_j x^j p_j(x^a). -/
theorem fold.split (p : K[X]) {a : ℕ} (ha : 0 < a) (x : K) :
    p.eval x = ∑ j ∈ range a, x ^ j * (split p a j).eval (x ^ a) :=
  eval_eq_sum_split p ha x

/-- Exactness: the fold by a of a polynomial of degree below a d has degree below d. -/
theorem fold.degree {p : K[X]} {a d : ℕ} (hp : p.degree < ↑(a * d)) (β : K) :
    (polyFold p a β).degree < d :=
  degree_polyFold_lt hp β

/-- Folding by 2^(k + 1) with beta is folding by 2 with beta, then by 2^k with beta^2. -/
theorem fold.two_pow (p : K[X]) (k : ℕ) (β : K) :
    polyFold p (2 ^ (k + 1)) β = polyFold (polyFold p 2 β) (2 ^ k) (β ^ 2) :=
  polyFold_two_pow p k β

/-- A polynomial of degree below a folds by a to the constant p(beta). -/
theorem fold.of_degree_lt {p : K[X]} {a : ℕ} (hp : p.degree < a) (β : K) :
    polyFold p a β = C (p.eval β) :=
  polyFold_of_degree_lt hp β

/-- The word of p on the coset s H of order 2^k folds to the fold of p by 2^k at s^(2^k). -/
theorem fold.coset_word (p : K[X]) {s ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) (β : K) :
    foldValue s ω k (fun j => p.eval (revCoset s ω k j)) β = (polyFold p (2 ^ k) β).eval (s ^ 2 ^ k) :=
  foldValue_eval p hω hs β

end fold

/-! ## The row fold and the matrix fold -/

section rows

variable {K : Type} [Field K] [DecidableEq K]

/-- Barycentric interpolation over a coset in bit-reversed order returns the value of the interpolant. -/
theorem lagrange_interpolate_at {s ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    (h2 : (2 : K) ≠ 0) (y : Fin (2 ^ k) → K) (z : K) :
    p3_fri.two_adic_pcs.mirror.lagrange_interpolate_at (List.ofFn (revCoset s ω k)) (List.ofFn y) z =
      some (foldValue s ω k y z) :=
  lagrange_interpolate_at_revCoset hω hs h2 y z

/-- The row fold returns the value at beta of the polynomial through the opened row, on its coset, for every row. -/
theorem fold_row (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) {index h k : ℕ} (hk : 1 ≤ k)
    (hhk : h + k ≤ G.adicity) (evals : Fin (2 ^ k) → K) (β : K) :
    p3_fri.two_adic_pcs.mirror.fold_row G index h k β (List.ofFn evals) =
      some (foldValue (G.gen (h + k) ^ bitRev h index) (G.gen k) k evals β) :=
  fold_row_eq G hV h2 hk hhk evals β

/-- The row fold panics exactly when the table is too short or the row does not hold 2^k values. -/
theorem fold_row.panics (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) {index h k : ℕ} (hk : 1 ≤ k)
    (β : K) (evals : List K) :
    p3_fri.two_adic_pcs.mirror.fold_row G index h k β evals = none ↔
      G.adicity < h + k ∨ evals.length ≠ 2 ^ k :=
  fold_row_eq_none G hV h2 hk β evals

/-- The scalar matrix fold maps the codeword of P to the codeword of its fold by 2^k. -/
theorem fold_matrix_scalar.codeword (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {P : K[X]} {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K}
    (hv : IsCodeword G P (n + k) v) (β : K) :
    ∃ L, fold_matrix_scalar G β k v = some L ∧ IsCodeword G (polyFold P (2 ^ k) β) n L :=
  fold_matrix_scalar_codeword G hV hN h2 hk hnk hv β

/-- The prover's scalar matrix fold returns, row by row, the verifier's row fold, on every word. -/
theorem fold_matrix_scalar.rows (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K} (hv : v.length = 2 ^ (n + k)) (β : K) :
    fold_matrix_scalar G β k v = some ((List.range (2 ^ n)).map fun t =>
      foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => v.getD (t * 2 ^ k + j.val) 0) β) :=
  fold_matrix_scalar_rows G hV hN h2 hk hnk hv β

/-- fold_matrix, on its packed path for every packing width and every scratch buffer, or on its scalar paths, returns the verifier's row fold for every row. -/
theorem fold_matrix.rows (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (W field_bits : ℕ) {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K} (hv : v.length = 2 ^ (n + k))
    (init : List (Fin W → K)) (hinit : init.length = 2 ^ (k - 1)) (β : K) :
    fold_matrix G W field_bits init β k v = some ((List.range (2 ^ n)).map fun t =>
      foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => v.getD (t * 2 ^ k + j.val) 0) β) := by
  rw [fold_matrix_eq_scalar G hV hN h2 W field_bits hk hnk hv init hinit β]
  exact fold_matrix_scalar_rows G hV hN h2 hk hnk hv β

end rows

/-! ## The folding schedule -/

/-- From the tallest height above the final height: every arity lies in [1, cap], they sum to the distance, and the descent stops at every input height at or above the final one. -/
theorem fold_schedule.spec {h0 : ℕ} {rest : List ℕ} (hdec : (h0 :: rest).IsChain (· > ·)) {F A : ℕ}
    (hA : 0 < A) (hF : F < h0) :
    ∃ L, fold_schedule (h0 :: rest) F A = some L ∧ (∀ a ∈ L, 1 ≤ a ∧ a ≤ A) ∧ L.sum = h0 - F ∧
      ∀ h ∈ h0 :: rest, F ≤ h → ∃ r ≤ L.length, h0 - (L.take r).sum = h :=
  fold_schedule_spec hdec hA hF

/-- No round is scheduled when the tallest height is at or below the final height. -/
theorem fold_schedule.nil {hs : List ℕ} (hdec : hs.IsChain (· > ·)) {F A : ℕ}
    (h : ∀ h0 ∈ hs.head?, h0 ≤ F) : fold_schedule hs F A = some [] :=
  fold_schedule_nil hdec h

/-- The schedule panics exactly on heights that are not strictly decreasing, or on a zero cap with a round to schedule. -/
theorem fold_schedule.panics {hs : List ℕ} {F A : ℕ} :
    fold_schedule hs F A = none ↔ ¬ hs.IsChain (· > ·) ∨ (A = 0 ∧ ∃ h0 ∈ hs.head?, F < h0) :=
  fold_schedule_eq_none

/-! ## The query phase -/

section query

variable {K : Type} [Field K] [DecidableEq K]

/-- The siblings the prover sends are its row without the queried position. -/
theorem answer_queries.siblings {α : Type _} (row : List α) (p : ℕ) :
    (row.zipIdx.filter fun x => x.2 ≠ p).map Prod.fst = row.eraseIdx p :=
  siblings_eq_eraseIdx row p

/-- The verifier rebuilds the row from the running value and the siblings. -/
theorem fold_query.rebuild (row : List K) {p : ℕ} (hp : p < row.length) :
    rebuildRow row.length p row[p] (row.eraseIdx p) = row :=
  rebuildRow_eraseIdx row hp

/-- Completeness of one query: on an honest chain, fold_query returns the final word's value at the shifted index, that index, and every round's group index and row. -/
theorem fold_query.complete {ME IE : Type} (G : Gen K) (q idx : ℕ) (rs : List (Rd K)) (wF : List K)
    {H Hf : ℕ} (hc : ChainOK G q H idx rs wF) (h64 : ∀ r ∈ rs, r.a < 64) (hHf : H - totalA rs = Hf) :
    fold_query (ME := ME) (IE := IE) G q idx (rs.map Rd.β) (rs.map Rd.a) (rs.map Rd.sv)
        ((H, (nextWord rs wF).getD idx 0) :: rolls rs H idx) H Hf =
      pure (wF.getD (idx / 2 ^ totalA rs) 0, idx / 2 ^ totalA rs, recordedOf rs idx) :=
  fold_query_complete G q idx rs wF hc h64 hHf

/-- Soundness of one query's checks: an accepted chain records rows that each hold the running value at the queried position and fold to the next running value with any rolled-in opening, and it ends at the returned value at the final height. -/
theorem fold_query.sound {ME IE : Type} (G : Gen K) (q idx : ℕ) (betas : List K) (las : List ℕ)
    (svs : List (List (List K))) (ro : List (ℕ × K)) (H Hf : ℕ) {f : K} {i' : ℕ}
    {recorded : List (ℕ × List K)}
    (h : fold_query (ME := ME) (IE := IE) G q idx betas las svs ro H Hf = pure (f, i', recorded)) :
    ∃ v0 ro', ro = (H, v0) :: ro' ∧
      Consistent G H idx v0 ro' ((List.zip betas (List.zip las svs)).map fun r => (r.1, r.2.1))
        recorded f [] ∧
      H - ((List.zip betas (List.zip las svs)).map fun r => r.2.1).sum = Hf :=
  fold_query_sound G q idx betas las svs ro H Hf h

/-- An honest round: the prover's scalar matrix fold returns, at every row, the verifier's row fold. -/
theorem honest_round (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) {n a : ℕ}
    (ha : 1 ≤ a) (hna : n + a ≤ G.adicity) {w : List K} (hw : w.length = 2 ^ (n + a)) (β : K) :
    ∃ f, fold_matrix_scalar G β a w = some f ∧ f.length = 2 ^ n ∧
      ∀ t < 2 ^ n, p3_fri.two_adic_pcs.mirror.fold_row G t n a β (rowList w a t) = some (f.getD t 0) :=
  Plonky3Lean.Proofs.Fri.honest_round G hV hN h2 ha hna hw β

/-- Honest folding with a rolled-in input keeps the degree below 2^(n - b). -/
theorem honest_round.degree (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {n a b : ℕ} (ha : 1 ≤ a) (hna : n + a ≤ G.adicity) (hbn : b ≤ n) {P R : K[X]} {w u : List K}
    (hw : IsCodeword G P (n + a) w) (hP : P.degree < ↑(2 ^ (n + a - b)))
    (hu : IsCodeword G R n u) (hR : R.degree < ↑(2 ^ (n - b))) (β : K) :
    ∃ f, fold_matrix_scalar G β a w = some f ∧
      IsCodeword G (polyFold P (2 ^ a) β + C (β ^ 2 ^ a) * R) n
        (List.zipWith (fun c x => c + β ^ 2 ^ a * x) f u) ∧
      (polyFold P (2 ^ a) β + C (β ^ 2 ^ a) * R).degree < ↑(2 ^ (n - b)) :=
  honest_round_degree G hV hN h2 ha hna hbn hw hP hu hR β

/-- The final check passes on an honest final codeword: the inverse transform of its first 2^L values, un-bit-reversed, evaluates with Horner's rule at G_H^rev_H(i) to its value at i. -/
theorem final_poly (G : Gen K) (hV : GenValid G) (hN : GenNested G) {P : K[X]} {L b : ℕ}
    (hLb : L + b ≤ G.adicity) {wF : List K} (hc : IsCodeword G P (L + b) wF) (hdeg : P.degree < ↑(2 ^ L))
    {coeffs : List K} (hlen : coeffs.length = 2 ^ L)
    (hco : ∀ i < 2 ^ L, coeffs.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen L) (2 ^ L) (fun j => (revIndex (2 ^ L) (wF.take (2 ^ L))).getD j 0) i)
    {H i : ℕ} (hH : L + b ≤ H) (hHa : H ≤ G.adicity) (hi : i < 2 ^ (L + b)) :
    horner coeffs (G.gen H ^ bitRev H i) = wF.getD i 0 :=
  final_poly_eval G hV hN hLb hc hdeg hlen hco hH hHa hi

/-- An index of the tallest codeword, shifted to a height h, indexes the codeword of height h. -/
theorem shifted_index {H h idx : ℕ} (hh : h ≤ H) (hidx : idx < 2 ^ H) : idx / 2 ^ (H - h) < 2 ^ h :=
  shifted_index_lt hh hidx

end query

/-! ## The reduced openings -/

section reduce

variable {K : Type} [Field K] [DecidableEq K]

/-- The verifier's reduction of one query: at each height present, the reduced opening of the claims at that height, with the opened rows as column values. -/
theorem reduceQuery.spec {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) (ro : List (ℕ × K))
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    (h : reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index = pure ro) :
    ∀ e ∈ ro, e.2 = reducedOpening α (xOfQuery G g H index e.1) 0
      (((matsEntries b (queryMats claims rows)).filter (·.1 = e.1)).map (·.2)) :=
  reduceQuery_spec G g b H α claims rows index ro halign h

/-- The prover's reduced vectors: at each height present, the entry at the row of query idx is the reduced opening of the claims at that height, with the matrices' rows as column values. -/
theorem reduced_openings.spec (G : Gen K) (hN : GenNested G) (g α : K)
    (mats : List (MatToOpen K)) {H : ℕ} (hHmax : (mats.map fun m => Nat.log 2 m.mat.height).max? = some H)
    (hHa : H ≤ G.adicity) (hpow : ∀ m ∈ mats, m.mat.height = 2 ^ Nat.log 2 m.mat.height)
    (h32 : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ 32)
    (hw : ∀ m ∈ mats, ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width)
    (hout : ∀ m ∈ mats, ∀ z ∈ m.points, ∀ r < 2 ^ H, z ≠ rowPoint G g H r)
    {red : List (ℕ × List K)} (h : reduced_openings G g α mats = some red) {idx : ℕ} (hidx : idx < 2 ^ H) :
    ∀ e ∈ red, e.2.length = 2 ^ e.1 ∧ e.2.getD (idx / 2 ^ (H - e.1)) 0 =
      reducedOpening α (xOfQuery G g H idx e.1) 0 (((proverAllEntries H idx mats).filter (·.1 = e.1)).map (·.2)) :=
  reduced_openings_spec G hN g α mats hHmax hHa hpow h32 hw hout h hidx

/-- The verifier recomputes exactly the prover's reduced opening: same claims in the same order, same powers of alpha, same query point. -/
theorem reduced_openings.agree {ME IE : Type} (G : Gen K) (hN : GenNested G) (g α : K) {C : Type} (b : ℕ)
    (claims : List (Claim G C)) (rows : List (List (List K))) (mats : List (MatToOpen K)) {H : ℕ}
    (hHmax : (mats.map fun m => Nat.log 2 m.mat.height).max? = some H)
    (hHa : H ≤ G.adicity) (hpow : ∀ m ∈ mats, m.mat.height = 2 ^ Nat.log 2 m.mat.height)
    (h32 : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ 32)
    (hw : ∀ m ∈ mats, ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width)
    (hout : ∀ m ∈ mats, ∀ z ∈ m.points, ∀ r < 2 ^ H, z ≠ rowPoint G g H r)
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    {idx : ℕ} (hidx : idx < 2 ^ H) (hsame : matsEntries b (queryMats claims rows) = proverAllEntries H idx mats)
    {red : List (ℕ × List K)} (hp : reduced_openings G g α mats = some red)
    {ro : List (ℕ × K)} (hv : reduceQuery (ME := ME) (IE := IE) G g b H α claims rows idx = pure ro)
    {h : ℕ} {u : K} {v : List K} (hu : (h, u) ∈ ro) (hvr : (h, v) ∈ red) :
    u = v.getD (idx / 2 ^ (H - h)) 0 := by
  have h1 := reduceQuery_spec G g b H α claims rows idx ro halign hv _ hu
  have h2 := (reduced_openings_spec G hN g α mats hHmax hHa hpow h32 hw hout hp hidx _ hvr).2
  simp only at h1 h2
  rw [h1, h2, hsame]

end reduce

/-! ## The verifier never panics -/

/-- The verifier never panics: on every proof, transcript, commitment schemes and claims, it accepts or rejects. -/
theorem verify_fri.never_panics {K : Type} [Field K] [DecidableEq K] (G : Gen K) (hV : GenValid G)
    (h2 : (2 : K) ≠ 0) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K) (tx : VerifierTx K fmmcs.Commitment S)
    (params : FriParameters) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) :
    (show Option _ from verify_fri G g fmmcs immcs tx params proof s claims commit_of alpha).isSome :=
  verify_fri_total G hV h2 g fmmcs immcs tx params proof s claims commit_of alpha

/-! ## The transcripts -/

/-- Each commit round carries one grinding step of the configured difficulty, and none at zero difficulty. -/
theorem shape.commit_pow (s : FriShape) (b : ℕ) :
    s.pattern.count (Step.commitPow b) =
      if 0 < s.commit_pow_bits ∧ b = s.commit_pow_bits then s.log_arities.length else 0 :=
  count_commitPow s b

/-- The query grinding step is present exactly at positive difficulty, with that difficulty. -/
theorem shape.query_pow (s : FriShape) (b : ℕ) :
    Step.queryPow b ∈ s.pattern ↔ 0 < s.query_pow_bits ∧ b = s.query_pow_bits :=
  queryPow_mem s b

/-- The query indices are the last step, drawn with the shape's index bits. -/
theorem shape.indices_last (s : FriShape) :
    s.pattern.getLast? = some (Step.queryIndices s.index_bits s.num_queries) :=
  pattern_getLast s

/-- The batching grinding step is present exactly at positive difficulty, with that difficulty. -/
theorem shape.batch_pow (s : PcsShape) (b : ℕ) :
    Step.batchPow b ∈ s.pattern ↔ 0 < s.batch_pow_bits ∧ b = s.batch_pow_bits :=
  batchPow_mem s b

/-! ## The hiding PCS -/

section hidingPcs

variable {K : Type} [Field K]

/-- The randomized commitment keeps the trace on the even rows of the doubled domain. -/
theorem hiding_pcs.even_rows (v : List K) {w r h : ℕ} (hw : 0 < w) (hv : v.length = h * w) (rnd : List K)
    (hrnd : h * (w + 2 * r) ≤ rnd.length) {i c : ℕ} (hi : i < h) (hc : c < w) :
    (randomize v w r rnd).1.getD (2 * i * (w + r) + c) 0 = v.getD (i * w + c) 0 :=
  randomize_even_row v hw hv rnd hrnd hi hc

/-- The quotient mask adds r(X) (p X^h - 1) to every column, r with coefficients g^i r_(i,j). -/
theorem hiding_pcs.mask_column (g p x : K) {h w : ℕ} (rv coeffs : List K) (hlen : 2 * h * w ≤ coeffs.length)
    {j : ℕ} (hj : j < w) :
    ∑ i ∈ range (2 * h), (maskCoeffs g p h w rv coeffs).getD (i * w + j) 0 * x ^ i =
      ∑ i ∈ range (2 * h), coeffs.getD (i * w + j) 0 * x ^ i +
        (∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i) * (p * x ^ h - 1) :=
  maskCoeffs_column g p x rv coeffs hlen hj

/-- The chunk masks cancel in the recombination when the last mask is minus the others scaled by c_i / c_last. -/
theorem hiding_pcs.masks_cancel {d : ℕ} (c v : Fin (d + 1) → K) (R : Fin d → K) (hc : c (Fin.last d) ≠ 0) :
    ∑ i : Fin (d + 1), (c i * ∏ j ∈ univ.erase i, v j) *
      (v i * Fin.lastCases (-∑ i : Fin d, c i.castSucc / c (Fin.last d) * R i) R i) = 0 :=
  Plonky3Lean.Proofs.Fri.masks_cancel c v R hc

/-- The verifier's merge undoes the prover's split. -/
theorem hiding_pcs.merge_split {k : ℕ} (z : K) (vals : List K) (hk : k ≤ vals.length) :
    mergePoint k ⟨z, (splitPoint k vals).1⟩ (splitPoint k vals).2 = some ⟨z, vals⟩ :=
  Plonky3Lean.Proofs.Fri.merge_split z vals hk

/-- The merge rejects exactly a hidden part of the wrong count. -/
theorem hiding_pcs.merge_rejects (k : ℕ) (pt : PointOpening K) (rand : List K) :
    mergePoint k pt rand = none ↔ rand.length ≠ k :=
  mergePoint_eq_none k pt rand

/-- The commit, open and verify budgets read the same mask height N. -/
theorem hiding_pcs.mask_heights (N b : ℕ) (hb : b < 64) :
    lde_mask_height b (2 * N * 2 ^ b) = N ∧ (2 * N) / 2 = N :=
  mask_heights_agree N b hb

end hidingPcs

/-! ## BabyBear and its extensions -/

section babyBear

/-- At every extension E of BabyBear, the quartic one included, the generator table is primitive and nested, and 2 is invertible. -/
theorem babyBear.facts (E : Type) [Field E] [Algebra BabyBear.Field E] :
    ∃ t, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (Plonky3Lean.Proofs.Commit.Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field E)).adicity = 27 ∧
      GenValid (Plonky3Lean.Proofs.Commit.Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field E)) ∧
      GenNested (Plonky3Lean.Proofs.Commit.Gen.map (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField))
        (algebraMap BabyBear.Field E)) ∧
      (2 : E) ≠ 0 := by
  obtain ⟨t, g, ht, -, ha, hV, hN, -⟩ := Plonky3Lean.Proofs.Commit.babyBear_facts
  refine ⟨t, ht, ha, Plonky3Lean.Proofs.Commit.genValid_map hV _,
    Plonky3Lean.Proofs.Commit.genNested_map hN _, ?_⟩
  rw [← map_ofNat (algebraMap BabyBear.Field E) 2, ne_eq,
    map_eq_zero_iff _ (algebraMap BabyBear.Field E).injective]
  exact Plonky3Lean.Proofs.Commit.babyBear_two_ne_zero

end babyBear

end Plonky3Lean.Claims.Fri
