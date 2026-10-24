module

public import Plonky3Lean.Proofs.Fri.Robust
public import Plonky3Lean.Proofs.Fri.Reduce
public import Plonky3Lean.Proofs.Fri.Final
public import Plonky3Lean.Proofs.Fri.Transcript
public import Plonky3Lean.Proofs.Fri.Hiding
public import Plonky3Lean.Proofs.Fri.Packed
public import Plonky3Lean.Proofs.Commit.BabyBear
public import Plonky3Lean.Proofs.Fri.Deep
public import Plonky3Lean.Proofs.Fri.Complete
public import Plonky3Lean.Proofs.Fri.Edge

@[expose] public section

/-!
# p3-fri: claims

The crate is transcribed over a field K, not extracted.

The specification is the FRI folding operator of Ben-Sasson, Bentov, Horesh and Riabzev, ICALP 2018:

```text
    p(X) = sum_{j < a} X^j p_j(X^a),     fold(p, a, beta) = sum_{j < a} beta^j p_j
```

The reduced opening follows Haböck's summary, eprint 2022/1216:

```text
    R(x) = sum_k sum_i alpha^(off_k + i) (y_(k,i) - c_(k,i)) / (z_k - x)
```

A codeword of log height N stores P(G_N^rev_N(i)) at index i, for the generator table G.

The field facts are hypotheses:

- the generator table is primitive and nested
- 2 is invertible

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

/-- For every row, the row fold evaluates at beta the polynomial through the opened row on its coset. -/
theorem fold_row (G : Gen K) (hV : GenValid G) (h2 : (2 : K) ≠ 0) {index h k : ℕ} (hk : 1 ≤ k)
    (hhk : h + k ≤ G.adicity) (evals : Fin (2 ^ k) → K) (β : K) :
    p3_fri.two_adic_pcs.mirror.fold_row G index h k β (List.ofFn evals) =
      some (foldValue (G.gen (h + k) ^ bitRev h index) (G.gen k) k evals β) :=
  fold_row_eq G hV h2 hk hhk evals β

/-- The row fold panics exactly in two cases:

- the table is too short
- the row does not hold 2^k values. -/
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

/-- On every word, the prover's scalar matrix fold returns the verifier's row fold, row by row. -/
theorem fold_matrix_scalar.rows (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K} (hv : v.length = 2 ^ (n + k)) (β : K) :
    fold_matrix_scalar G β k v = some ((List.range (2 ^ n)).map fun t =>
      foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => v.getD (t * 2 ^ k + j.val) 0) β) :=
  fold_matrix_scalar_rows G hV hN h2 hk hnk hv β

/-- The matrix fold returns the verifier's row fold for every row.

This holds on its scalar paths, and on its packed path for every packing width and scratch buffer. -/
theorem fold_matrix.rows (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (W field_bits : ℕ) {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity) {v : List K} (hv : v.length = 2 ^ (n + k))
    (init : List (Fin W → K)) (hinit : init.length = 2 ^ (k - 1)) (β : K) :
    fold_matrix G W field_bits init β k v = some ((List.range (2 ^ n)).map fun t =>
      foldValue (G.gen (n + k) ^ bitRev n t) (G.gen k) k (fun j => v.getD (t * 2 ^ k + j.val) 0) β) := by
  rw [fold_matrix_eq_scalar G hV hN h2 W field_bits hk hnk hv init hinit β]
  exact fold_matrix_scalar_rows G hV hN h2 hk hnk hv β

end rows

/-! ## The folding schedule -/

/-- Start from a tallest height above the final height.

The schedule then satisfies:

- every arity lies in [1, cap]
- the arities sum to the distance
- the descent stops at every input height at or above the final one. -/
theorem fold_schedule.spec {h0 : ℕ} {rest : List ℕ} (hdec : (h0 :: rest).IsChain (· > ·)) {F A : ℕ}
    (hA : 0 < A) (hF : F < h0) :
    ∃ L, fold_schedule (h0 :: rest) F A = some L ∧ (∀ a ∈ L, 1 ≤ a ∧ a ≤ A) ∧ L.sum = h0 - F ∧
      ∀ h ∈ h0 :: rest, F ≤ h → ∃ r ≤ L.length, h0 - (L.take r).sum = h :=
  fold_schedule_spec hdec hA hF

/-- No round is scheduled when the tallest height is at or below the final height. -/
theorem fold_schedule.nil {hs : List ℕ} (hdec : hs.IsChain (· > ·)) {F A : ℕ}
    (h : ∀ h0 ∈ hs.head?, h0 ≤ F) : fold_schedule hs F A = some [] :=
  fold_schedule_nil hdec h

/-- The schedule panics exactly in two cases:

- the heights are not strictly decreasing
- the cap is zero and a round remains to schedule. -/
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

/-- Completeness of one query.

On an honest chain, the query fold returns:

- the final word's value at the shifted index
- that shifted index
- every round's group index and row. -/
theorem fold_query.complete {ME IE : Type} (G : Gen K) (q idx : ℕ) (rs : List (Rd K)) (wF : List K)
    {H Hf : ℕ} (hc : ChainOK G q H idx rs wF) (h64 : ∀ r ∈ rs, r.a < 64) (hHf : H - totalA rs = Hf) :
    fold_query (ME := ME) (IE := IE) G q idx (rs.map Rd.β) (rs.map Rd.a) (rs.map Rd.sv)
        ((H, (nextWord rs wF).getD idx 0) :: rolls rs H idx) H Hf =
      pure (wF.getD (idx / 2 ^ totalA rs) 0, idx / 2 ^ totalA rs, recordedOf rs idx) :=
  fold_query_complete G q idx rs wF hc h64 hHf

/-- Soundness of one query's checks.

An accepted chain records rows that satisfy:

- each row holds the running value at the queried position
- each row folds to the next running value, with any rolled-in opening
- the chain ends at the returned value at the final height. -/
theorem fold_query.sound {ME IE : Type} (G : Gen K) (q idx : ℕ) (betas : List K) (las : List ℕ)
    (svs : List (List (List K))) (ro : List (ℕ × K)) (H Hf : ℕ) {f : K} {i' : ℕ}
    {recorded : List (ℕ × List K)}
    (h : fold_query (ME := ME) (IE := IE) G q idx betas las svs ro H Hf = pure (f, i', recorded)) :
    ∃ v0 ro', ro = (H, v0) :: ro' ∧
      Consistent G H idx v0 ro' ((List.zip betas (List.zip las svs)).map fun r => (r.1, r.2.1))
        recorded f [] ∧
      H - ((List.zip betas (List.zip las svs)).map fun r => r.2.1).sum = Hf :=
  fold_query_sound G q idx betas las svs ro H Hf h

/-- In an honest round, the prover's scalar matrix fold returns the verifier's row fold at every row. -/
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

/-- The final check passes on an honest final codeword.

Take the inverse transform of its first 2^L values, un-bit-reversed.

Evaluated with Horner's rule at G_H^rev_H(i), it gives the codeword's value at i. -/
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

/-- The verifier's reduction of one query.

At each height present, it is the reduced opening of the claims at that height.

The opened rows serve as column values. -/
theorem reduceQuery.spec {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) (ro : List (ℕ × K))
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    (h : reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index = pure ro) :
    ∀ e ∈ ro, e.2 = reducedOpening α (xOfQuery G g H index e.1) 0
      (((matsEntries b (queryMats claims rows)).filter (·.1 = e.1)).map (·.2)) :=
  reduceQuery_spec G g b H α claims rows index ro halign h

/-- The prover's reduced vectors.

At each height present, take the entry at the row of query idx.

It is the reduced opening of the claims at that height, with the matrices' rows as column values. -/
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

/-- The verifier recomputes exactly the prover's reduced opening.

Both use the same claims in the same order, the same powers of alpha and the same query point. -/
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

/-- The verifier never panics on a transcript whose phases never panic at a height within the adicity.

This holds on every proof, commitment schemes and claims. -/
theorem verify_fri.never_panics {K : Type} [Field K] [DecidableEq K] (G : Gen K) (hV : GenValid G)
    (h2 : (2 : K) ≠ 0) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
    (mkTx : FriShape → VerifierTx K fmmcs.Commitment S)
    (params : FriParameters)
    (htx : ∀ L H, H ≤ G.adicity → (∀ s c w, ((mkTx (FriShape.with_schedule params L H)).commit_rounds s c w).run.isSome) ∧
      ∀ s f w, ((mkTx (FriShape.with_schedule params L H)).query_phase s f w).run.isSome)
    (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K) :
    (show Option _ from verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha).isSome :=
  verify_fri_total G hV h2 g fmmcs immcs mkTx params htx proof s claims commit_of alpha

/-! ## The DEEP quotients -/

section deep

variable {K : Type} [Field K]

/-- Off z, the quotient (f - f(z)) / (X - z) takes the value (f(x) - f(z)) / (x - z). -/
theorem deep.eval (f : K[X]) {z x : K} (hx : x ≠ z) :
    (deepQuot f z).eval x = (f.eval x - f.eval z) / (x - z) :=
  eval_deepQuot f hx

/-- The quotient of a non-constant f has degree below that of f. -/
theorem deep.degree {f : K[X]} (hf : 0 < f.degree) (z : K) : (deepQuot f z).degree < f.degree :=
  degree_deepQuot_lt hf z

/-- A constant column has quotient zero, so a one-row matrix contributes nothing. -/
theorem deep.constant (c z : K) : deepQuot (C c) z = 0 := deepQuot_C c z

/-- On honest claims, the reduced opening at x is the batched DEEP polynomial at x:

```text
    R(x) = Q(x),   Q = sum_k sum_i alpha^(off_k + i) (f_(k,i) - f_(k,i)(z_k)) / (X - z_k)
```

This holds when no point z_k equals x. -/
theorem deep.reduced_opening (α x : K) (off : ℕ) (L : List (K × List K[X])) (hz : ∀ e ∈ L, e.1 ≠ x) :
    reducedOpening α x off (L.map fun e => (e.1, e.2.map (·.eval e.1), e.2.map (·.eval x))) =
      (deepPoly α off L).eval x :=
  reducedOpening_eq_deepPoly α x off L hz

/-- The batched DEEP polynomial has degree below d when every column has. -/
theorem deep.batched_degree (α : K) {d : WithBot ℕ} (hd : ⊥ < d) (off : ℕ) (L : List (K × List K[X]))
    (hL : ∀ e ∈ L, ∀ f ∈ e.2, f.degree < d) : (deepPoly α off L).degree < d :=
  degree_deepPoly_lt α hd off L hL

/-- The verifier's reduction of one query is the batched DEEP polynomial at each height, at its query point.

This needs opened rows that are the columns at the query point.

It also needs claimed values that are the columns at each opening point. -/
theorem deep.verifier : type_of% @reduceQuery_deep := @reduceQuery_deep

end deep

/-! ## The fold chain, round by round -/

/-- Row t of the codeword of P folds by 2^a to fold(P, 2^a, beta) at point t of the folded subgroup. -/
theorem fold_chain.row : type_of% @fold_row_rowList := @fold_row_rowList

/-- One round of the verifier's fold chain on an honest codeword.

It returns fold(P, 2^a, beta) at the folded point, for any arity 2^a.

When the next opening sits at the folded height, it adds beta^(2^a) times that opening. -/
theorem fold_chain.step : type_of% @foldStep_codeword := @foldStep_codeword

/-- A chain of codewords, each the fold of the previous one plus beta^(2^a) times any rolled-in codeword,
satisfies every check of the fold chain. -/
theorem fold_chain.honest : type_of% @HonestChain.chainOK := @HonestChain.chainOK

/-- An accepted fold chain has every opening at or above the final height.

So an input below the final height is never rolled in, and its query is rejected. -/
theorem fold_chain.final_le : type_of% @fold_query_final_le := @fold_query_final_le

/-! ## The PCS verifier: panics -/

/-- The grinding check panics exactly when the difficulty b is positive and not both b < 64 and 2^b < p. -/
theorem pcs.check_witness.panics {K Com S : Type} (sp : Sponge K Com S) (s : S) (b : ℕ) (w : K) :
    check_witness sp s b w = none ↔ ¬ (b = 0 ∨ (b < 64 ∧ 2 ^ b < sp.order)) :=
  check_witness_eq_none sp s b w

/-- The commit rounds panic exactly when:

- the commitment and witness counts match the schedule
- some round exists
- the commit difficulty is unsafe. -/
theorem pcs.commit_rounds.panics : type_of% @commit_rounds_run_eq_none := @commit_rounds_run_eq_none

/-- With a safe index width, the query phase panics exactly when:

- the final polynomial has its length
- a witness is given
- the query difficulty is unsafe. -/
theorem pcs.query_phase.panics : type_of% @query_phase_run_eq_none := @query_phase_run_eq_none

/-- The batching phase panics exactly when a witness is given and the batching difficulty is unsafe. -/
theorem pcs.batch_phase.panics : type_of% @batch_phase_run_eq_none := @batch_phase_run_eq_none

/-- The claims replay never rejects and never panics, since its description comes from the same claims. -/
theorem pcs.claims_replay : type_of% @claimed_openings_from_claims := @claimed_openings_from_claims

/-- The FRI verifier panics exactly when its checks pass up to the transcript, and then:

- the commit rounds panic, or
- they return, and the query phase panics. -/
theorem pcs.fri_panics_iff : type_of% @verify_fri_panics_iff := @verify_fri_panics_iff

/-- The PCS verifier never panics when:

- the three difficulties are safe for the field order p
- 2^h < p for the adicity h, with h < 64. -/
theorem pcs.never_panics : type_of% @Plonky3Lean.Proofs.Fri.verify_total := @Plonky3Lean.Proofs.Fri.verify_total

/-- The PCS verifier panics exactly when the zero-difficulty witnesses are zero, and one of these holds:

- the batching difficulty is unsafe, or
- the batching grind passes, the FRI checks before its transcript pass, and either
  - some round exists, the counts match, and the commit difficulty is unsafe, or
  - the commit rounds return and the query difficulty is unsafe. -/
theorem pcs.panics_iff : type_of% @Plonky3Lean.Proofs.Fri.verify_panics_iff :=
  @Plonky3Lean.Proofs.Fri.verify_panics_iff

/-- For BabyBear, a grinding difficulty is safe exactly up to 30 bits. -/
theorem pcs.babyBear_difficulty (b : ℕ) : (b = 0 ∨ (b < 64 ∧ 2 ^ b < 2013265921)) ↔ b ≤ 30 :=
  powSafe_babyBear b

/-! ## The PCS verifier: completeness -/

/-- The FRI verifier accepts when:

- the checks before the transcript pass, and the transcript accepts
- the input checks return each query's first value and rolled-in inputs
- each query sees an honest chain of codewords
- the final polynomial agrees with the final word
- the commit-phase scheme accepts the honest rows. -/
theorem pcs.fri_complete : type_of% @verify_fri_complete := @verify_fri_complete

/-- The PCS verifier accepts when:

- the zero-difficulty witnesses are zero
- the batching grind passes
- the FRI verifier accepts. -/
theorem pcs.complete : type_of% @pcs_verify_complete := @pcs_verify_complete

/-- The input checks pass on honest openings, and leave each query's reduction. -/
theorem pcs.inputs_honest : type_of% @open_inputs_honest := @open_inputs_honest

/-- One batch's checks pass on rows of the right shape that the scheme accepts. -/
theorem pcs.batch_honest : type_of% @checkBatch_honest := @checkBatch_honest

/-- The denominator checks pass when no opening point is a query point. -/
theorem pcs.denominators_honest : type_of% @checkDenominators_honest := @checkDenominators_honest

/-! ## Edge cases -/

/-- Zero queries are rejected. -/
theorem edge.zero_queries : type_of% @verify_fri_zero_queries := @verify_fri_zero_queries

/-- A blowup of 1 is rejected. -/
theorem edge.zero_blowup : type_of% @verify_fri_zero_blowup := @verify_fri_zero_blowup

/-- A tallest claimed height past the adicity is rejected. -/
theorem edge.too_tall : type_of% @verify_fri_too_tall := @verify_fri_too_tall

/-- The prover panics exactly when an opening point is one of the domain points it divides by. -/
theorem edge.point_in_domain : type_of% @compute_inverse_denominators_eq_none :=
  @compute_inverse_denominators_eq_none

/-- A domain shorter than one full arity still folds.

With height 2, final height 1 and arity cap 2^3, the schedule folds once by 2.

The security model's layer count for it is (2 - 0) / 3 = 0. -/
theorem edge.short_round : fold_schedule [2] 1 3 = some [1] ∧ (2 - 0) / 3 = 0 := by decide

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

/-- The quotient mask adds r(X) (p X^h - 1) to every column.

The coefficients of r are g^i r_(i,j). -/
theorem hiding_pcs.mask_column (g p x : K) {h w : ℕ} (rv coeffs : List K) (hlen : 2 * h * w ≤ coeffs.length)
    {j : ℕ} (hj : j < w) :
    ∑ i ∈ range (2 * h), (maskCoeffs g p h w rv coeffs).getD (i * w + j) 0 * x ^ i =
      ∑ i ∈ range (2 * h), coeffs.getD (i * w + j) 0 * x ^ i +
        (∑ i ∈ range h, g ^ i * rv.getD (i * w + j) 0 * x ^ i) * (p * x ^ h - 1) :=
  maskCoeffs_column g p x rv coeffs hlen hj

/-- The chunk masks cancel in the recombination.

This needs the last mask to be minus the others, each scaled by c_i / c_last. -/
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

/-- In every extension E of BabyBear, the quartic one included, the field facts hold:

- the generator table is primitive and nested
- 2 is invertible. -/
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
