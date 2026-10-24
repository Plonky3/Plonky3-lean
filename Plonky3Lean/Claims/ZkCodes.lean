module

public import Plonky3Lean.Proofs.ZkCodes.Properties
public import Plonky3Lean.Proofs.ZkCodes.Batch
public import Plonky3Lean.Proofs.Dft.SmallBatch

@[expose] public section

/-!
# p3-zk-codes: claims

The encoding is transcribed over a field K, not extracted.

The definitions follow Chiesa, Fenzi and Weissenberg, eprint 2026/391, Section 3.2.1.

The code puts the message in the low coefficients and t masks in the next ones.

It evaluates on the subgroup of order m = 2^k:

```text
    p_{f,rho}(X) = sum_{j < l} f_j X^j + sum_{j < t} rho_j X^(l+j)
    codeword_i   = p_{f,rho}(omega^i),      omega = G_k,  0 <= i < m
```

A backend computes the transform when it returns the transform at omega = G_k on all m rows.

A distribution on a finite set is the probability of each outcome, a rational number.

A random generator is the stream of its draws.
-/

open p3_dft.mirror Plonky3Lean.Spec.Dft Plonky3Lean.Spec.ZkCodes Plonky3Lean.Proofs.Dft
open Plonky3Lean.Proofs.ZkCodes p3_zk_codes.reed_solomon.mirror
open p3_dft.radix_2_dit.mirror p3_dft.radix_2_small_batch.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.ZkCodes

/-! ## Proposition 3.19 -/

section spec

variable {K : Type _} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- At distinct nonzero points, the encoding with t masks is t-query zero knowledge with error zero.

The simulator samples each queried symbol uniformly. -/
theorem rs_isZk {l t : ℕ} (L : Fin m → K) (hL : Function.Injective L) (h0 : ∀ i, L i ≠ 0) :
    IsZkEncoding (rsZkEnc (l := l) (t := t) L) t 0 uniformSim :=
  rsZkEnc_isZk L hL h0

/-- Fix a message and a set S of at most t distinct nonzero points.

Each value of the view at S is reached by exactly |K|^(t - |S|) randomness vectors. -/
theorem rs_view_balanced {l t : ℕ} (L : Fin m → K) {S : Finset (Fin m)} (hL : Set.InjOn L S)
    (h0 : ∀ i ∈ S, L i ≠ 0) (hS : S.card ≤ t) (f : Fin l → K) (y : S → K) :
    (Finset.univ.filter fun ρ : Fin t → K => restrict (rsZkEnc L f ρ) S = y).card *
      Fintype.card K ^ S.card = Fintype.card K ^ t := by
  have := card_view_fiber L hL h0 hS f y
  simpa [Fintype.card_fun] using this

/-- At exactly t distinct nonzero points, the view is a bijection of the randomness, for every message. -/
theorem rs_view_bijective {l t : ℕ} (L : Fin m → K) {S : Finset (Fin m)} (hL : Set.InjOn L S)
    (h0 : ∀ i ∈ S, L i ≠ 0) (hS : S.card = t) (f : Fin l → K) :
    Function.Bijective fun ρ : Fin t → K => restrict (rsZkEnc L f ρ) S :=
  view_bijective L hL h0 hS f

/-- The bound t is tight.

Take l >= 1 and at least t + 1 distinct nonzero points.

No simulator achieves (t + 1)-query zero knowledge with error below 1/2. -/
theorem rs_not_isZk_succ {l t : ℕ} (hl : 1 ≤ l) (L : Fin m → K) (hL : Function.Injective L)
    (h0 : ∀ i, L i ≠ 0) (hm : t + 1 ≤ m) {ζ : ℚ} (hζ : ζ < 1 / 2)
    (sim : (S : Finset (Fin m)) → (S → K) → ℚ) :
    ¬ IsZkEncoding (rsZkEnc (l := l) (t := t) L) (t + 1) ζ sim :=
  not_isZk_succ hl L hL h0 hm hζ sim

/-- With the message in the low coefficients, a zero point reveals the constant coefficient.

So with l, t >= 1 and a zero point, the encoding is not t-query zero knowledge. -/
theorem rs_not_isZk_of_zero {l t : ℕ} (hl : 1 ≤ l) (ht : 1 ≤ t) (L : Fin m → K) {i : Fin m}
    (hi : L i = 0) {ζ : ℚ} (hζ : ζ < 1 / 2) (sim : (S : Finset (Fin m)) → (S → K) → ℚ) :
    ¬ IsZkEncoding (rsZkEnc (l := l) (t := t) L) t ζ sim :=
  not_isZk_of_zero hl ht L hi hζ sim

/-- Every codeword lies in the Reed-Solomon code of degree below l + t. -/
theorem rs_mem_code {l t : ℕ} (L : Fin m → K) (f : Fin l → K) (ρ : Fin t → K) :
    rsZkEnc L f ρ ∈ rsCode L (l + t) :=
  rsZkEnc_mem L f ρ

/-- Definition 3.17: the generating matrix.

Its rows are L_i^j for the message and L_i^(l+j) for the randomness. -/
theorem rs_generating {l t : ℕ} (L : Fin m → K) :
    IsGeneratingMatrix (rsZkEnc (l := l) (t := t) L) (rsMsgMatrix L) (rsRandMatrix (l := l) L) :=
  rsZkEnc_generating L

/-- The subgroup of order 2^k is a domain of distinct nonzero points.

So the code's encoding is t-query zero knowledge on it. -/
theorem rs_isZk_subgroup {l t k : ℕ} {ω : K} (hω : IsPrimitiveRoot ω (2 ^ k)) :
    IsZkEncoding (rsZkEnc (l := l) (t := t) fun j : Fin (2 ^ k) => ω ^ (j : ℕ)) t 0 uniformSim :=
  rsZkEnc_isZk _ (fun a b h => Fin.ext (hω.pow_inj a.isLt b.isLt h))
    (fun _ => pow_ne_zero _ (hω.ne_zero (by positivity)))

end spec

/-! ## The transcriptions -/

section rust

variable {K : Type _} [Field K] [DecidableEq K]

/-- The constructor accepts m = 2^k with l + t <= m, for k < 64. -/
theorem new (t l : ℕ) {k : ℕ} (hle : l + t ≤ 2 ^ k) (hk : k < 64) :
    ReedSolomonZkEncoding.new t l (2 ^ k) = some ⟨t, l, 2 ^ k⟩ :=
  new_eq_some hle hk

/-- The constructor returns exactly when all of these hold:

- m is a power of two
- l + t <= m
- l + t fits in a word. -/
theorem new.some_iff {t l m : ℕ} {rs : ReedSolomonZkEncoding} :
    ReedSolomonZkEncoding.new t l m = some rs ↔
      (∃ k, m = 2 ^ k) ∧ l + t ≤ m ∧ l + t < 2 ^ 64 ∧ rs = ⟨t, l, m⟩ :=
  new_eq_some_iff

/-- The query bound and the randomness length are t, and the error is zero. -/
theorem accessors (rs : ReedSolomonZkEncoding) :
    rs.query_bound = rs.t ∧ rs.randomness_len = rs.t ∧ rs.message_len = rs.msg_len ∧
      rs.codeword_len = rs.m ∧ rs.error = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The evaluation point at position p is G_k^p, which repeats with period 2^k. -/
theorem evaluation_point (G : Gen K) (hG : GenValid G) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p = some (G.gen k ^ (p % 2 ^ k)) := by
  rw [evaluation_point_eq G hk, pow_mod_of_primitive (hG k hk)]

/-- Beyond the two-adicity every evaluation point panics. -/
theorem evaluation_point.panics (G : Gen K) {t l k : ℕ} (hk : G.adicity < k) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p = none :=
  evaluation_point_none G hk p

/-- The message row at position p is x^0, ..., x^(l-1), for x = G_k^p. -/
theorem message_row (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).message_row G p =
      some ((List.range l).map fun j => (G.gen k ^ p) ^ j) :=
  message_row_eq G hk p

/-- The randomness row at position p is x^l, ..., x^(l+t-1), for x = G_k^p.

It is empty for t = 0. -/
theorem randomness_row (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).randomness_row G p =
      some ((List.range t).map fun j => (G.gen k ^ p) ^ (l + j)) :=
  randomness_row_eq G hk p

/-- Take a backend that computes the transform.

The codeword at position i is the polynomial of Proposition 3.19 at G_k^i. -/
theorem encode_with_randomness (G : Gen K) {t l k : ℕ} {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x))
    (hle : l + t ≤ 2 ^ k) (f : Fin l → K) (ρ : Fin t → K) :
    ∃ y, (ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch (List.ofFn f)
        (List.ofFn ρ) = some y ∧
      ∀ i : Fin (2 ^ k), y i = rsZkEnc (fun j : Fin (2 ^ k) => G.gen k ^ (j : ℕ)) f ρ i :=
  encode_eq_rsZkEnc G hd hle f ρ

/-- The radix-2 decimation-in-time backend computes the transform.

So its codeword is the polynomial at G_k^i. -/
theorem encode_with_randomness.radix2Dit (G : Gen K) (hG : GenValid G) {t l k : ℕ}
    (hk : k ≤ G.adicity) (hle : l + t ≤ 2 ^ k) (f : Fin l → K) (ρ : Fin t → K) :
    ∃ y, (ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness (Radix2Dit.dft_batch G)
        (List.ofFn f) (List.ofFn ρ) = some y ∧
      ∀ i : Fin (2 ^ k), y i = rsZkEnc (fun j : Fin (2 ^ k) => G.gen k ^ (j : ℕ)) f ρ i :=
  encode_eq_rsZkEnc G (fun x => Proofs.Dft.radix2Dit_dft_batch G hG hk x) hle f ρ

/-- The small-batch backend computes the transform.

So its codeword is the polynomial at G_k^i. -/
theorem encode_with_randomness.smallBatch (G : Gen K) (hG : GenValid G) (hN : GenNested G)
    {t l k L : ℕ} (hkL : k ≤ L) (hL : L ≤ G.adicity) (c : ℕ) (hle : l + t ≤ 2 ^ k) (f : Fin l → K)
    (ρ : Fin t → K) :
    ∃ y, (ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness
        (Radix2DFTSmallBatch.dft_batch G L c 1) (List.ofFn f) (List.ofFn ρ) = some y ∧
      ∀ i : Fin (2 ^ k), y i = rsZkEnc (fun j : Fin (2 ^ k) => G.gen k ^ (j : ℕ)) f ρ i :=
  encode_eq_rsZkEnc G (fun x => Proofs.Dft.smallBatch_dft_batch G hG hN hkL hL c 1 x) hle f ρ

/-- A message of the wrong length panics. -/
theorem encode_with_randomness.panics_msg_len (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) {msg : List K} (h : msg.length ≠ rs.msg_len) (r : List K) :
    rs.encode_with_randomness dft_batch msg r = none :=
  encode_with_randomness_msg_len dft_batch rs h r

/-- A randomness of the wrong length panics. -/
theorem encode_with_randomness.panics_rand_len (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) (msg : List K) {r : List K} (h : r.length ≠ rs.t) :
    rs.encode_with_randomness dft_batch msg r = none :=
  encode_with_randomness_rand_len dft_batch rs msg h

/-- The constructor accepts m = 2^k beyond the two-adicity.

Every evaluation point then panics.

So does every encoding with a backend that panics there. -/
theorem beyond_adicity (G : Gen K) {t l k : ℕ} (hk : G.adicity < k) (hk64 : k < 64)
    (hle : l + t ≤ 2 ^ k) {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    (hd : ∀ x, dft_batch (2 ^ k) x = none) (p : ℕ) (msg r : List K) :
    ReedSolomonZkEncoding.new t l (2 ^ k) = some ⟨t, l, 2 ^ k⟩ ∧
      (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p = none ∧
      (ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch msg r = none :=
  Proofs.ZkCodes.beyond_adicity G hk hk64 hle hd p msg r

/-- The codeword at position p is a sum of two dot products:

- the message row times the message
- the randomness row times the randomness. -/
theorem encode_rows (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity)
    {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x))
    (hle : l + t ≤ 2 ^ k) {msg r : List K} (hmsg : msg.length = l) (hr : r.length = t) :
    ∃ y, (ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch msg r = some y ∧
      ∀ p < 2 ^ k, ∃ mrow rrow,
        (ReedSolomonZkEncoding.mk t l (2 ^ k)).message_row G p = some mrow ∧
        (ReedSolomonZkEncoding.mk t l (2 ^ k)).randomness_row G p = some rrow ∧
        y p = (List.zipWith (· * ·) mrow msg).sum + (List.zipWith (· * ·) rrow r).sum :=
  Proofs.ZkCodes.encode_rows G hk hd hle hmsg hr

/-- Linearity.

The encoding of a f_1 + f_2 with a rho_1 + rho_2 is a times the first codeword plus the second. -/
theorem encode_linear {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)} {ω : K}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) (a : K) (f₁ f₂ : Fin rs.msg_len → K) (ρ₁ ρ₂ : Fin rs.t → K) :
    Computes (rs.encode_with_randomness dft_batch (List.ofFn (a • f₁ + f₂)) (List.ofFn (a • ρ₁ + ρ₂)))
      rs.m (fun i => a * (rsZkPoly f₁ ρ₁).eval (ω ^ i) + (rsZkPoly f₂ ρ₂).eval (ω ^ i)) :=
  Proofs.ZkCodes.encode_linear hd hle a f₁ f₂ ρ₁ ρ₂

/-- In the packed batch encoding, column c is the encoding of message c with randomness c. -/
theorem encode_batch_with_randomness {w : ℕ}
    {dft_batch : ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)} {ω : K}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) {ms rss : List (List K)} (hw : ms.length = w) (hw0 : w ≠ 0)
    (hrw : rss.length = w)
    (hlen : ∀ c < w, (ms.getD c []).length = rs.msg_len ∧ (rss.getD c []).length = rs.t) :
    Computes (rs.encode_batch_with_randomness dft_batch ms rss) rs.m
      (fun r c => encValue (ms.getD c []) (rss.getD c []) (ω ^ r)) :=
  encode_batch_computes hd hle hw hw0 hrw hlen

/-- The default batch encoding interleaves the single encodings.

Its entry (r, c) is the same as in the packed encoding. -/
theorem default_encode_batch_with_randomness {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)} {ω : K}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) {ms rss : List (List K)} (hne : ms ≠ [])
    (hrw : rss.length = ms.length)
    (hlen : ∀ c < ms.length, (ms.getD c []).length = rs.msg_len ∧ (rss.getD c []).length = rs.t) :
    ∃ M, p3_zk_codes.encoding.mirror.encode_batch_with_randomness
        (fun msg r => (rs.encode_with_randomness dft_batch msg r).map
          fun y => (⟨rs.m, 1, fun r _ => y r⟩ : p3_zk_codes.encoding.mirror.Mat K)) ms rss = some M ∧
      M.height = rs.m ∧ M.width = ms.length ∧
      ∀ r < rs.m, ∀ c < ms.length, M.get r c = encValue (ms.getD c []) (rss.getD c []) (ω ^ r) :=
  default_batch_computes hd hle hne hrw hlen

/-- The sampled message and randomness are the first l and t draws, in order.

Encoding with a generator uses the sampled randomness. -/
theorem sampling (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)) (rs : ReedSolomonZkEncoding)
    (msg : List K) (draw : ℕ → K) :
    rs.sample_message draw = List.ofFn (fun i : Fin rs.msg_len => draw i) ∧
      rs.sample_randomness draw = List.ofFn (fun i : Fin rs.t => draw i) ∧
      rs.encode dft_batch msg draw = rs.encode_with_randomness dft_batch msg (rs.sample_randomness draw) :=
  ⟨sample_message_eq rs draw, sample_randomness_eq rs draw, encode_eq dft_batch rs msg draw⟩

/-- The simulator gives each distinct position the next draw, in order of first appearance.

It panics exactly when there are more than t distinct positions. -/
theorem simulate (rs : ReedSolomonZkEncoding) (Q : List ℕ) (draw : ℕ → K) :
    rs.simulate Q draw =
      if (keys Q).length ≤ rs.t then some (Q.map fun p => draw ((keys Q).idxOf p)) else none :=
  simulate_eq rs Q draw

/-- The simulator's output has the distribution of the real codeword at the queried positions.

This holds for all of these:

- every message of length l
- every list of positions below 2^k with at most t distinct ones
- every backend that computes the transform. -/
theorem simulate_matches_encode [Fintype K] (G : Gen K) (hG : GenValid G)
    {t l k : ℕ} (hk : k ≤ G.adicity) (hle : l + t ≤ 2 ^ k)
    {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x)) {msg : List K}
    (hmsg : msg.length = l) {Q : List ℕ} (hQ : ∀ p ∈ Q, p < 2 ^ k) (hQt : (keys Q).length ≤ t) :
    pushUniform (fun ρ : Fin t → K =>
        ((ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch msg
          (List.ofFn ρ)).map (Q.map ·)) =
      pushUniform (fun s : Fin (keys Q).length → K =>
        (ReedSolomonZkEncoding.mk t l (2 ^ k)).simulate Q (ext s)) :=
  Proofs.ZkCodes.simulate_matches_encode G hG hk hle hd hmsg hQ hQt

/-- With t = 0 the simulator answers only the empty query. -/
theorem simulate.t_zero (l m : ℕ) (draw : ℕ → K) (p : ℕ) (Q : List ℕ) :
    (ReedSolomonZkEncoding.mk 0 l m).simulate [] draw = some [] ∧
      (ReedSolomonZkEncoding.mk 0 l m).simulate (p :: Q) draw = none :=
  simulate_t_zero l m draw p Q

/-- The simulator accepts positions at or above m.

It gives p and p + m two independent draws, although their evaluation points coincide. -/
theorem simulate.wraps (G : Gen K) (hG : GenValid G) {t l k : ℕ} (hk : k ≤ G.adicity) (ht : 2 ≤ t)
    (p : ℕ) (draw : ℕ → K) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).simulate [p, p + 2 ^ k] draw = some [draw 0, draw 1] ∧
      (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G (p + 2 ^ k) =
        (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p :=
  simulate_wraps G hG hk ht p draw

end rust

end Plonky3Lean.Claims.ZkCodes
