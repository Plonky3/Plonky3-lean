module

public import Plonky3Lean.Proofs.Dft.SmallBatch
public import Plonky3Lean.Proofs.Dft.Lde
public import Plonky3Lean.Proofs.Dft.Rows
public import Plonky3Lean.Proofs.Dft.Fields

@[expose] public section

/-!
# p3-dft: claims

The transforms are transcriptions over a field K, not extractions.

A matrix of height h is its rows: entries of a vector space V over K, K^w for width w.

A result agrees with its specification on the first h rows.

The field's generators form a table G.

Entry G_b generates the subgroup of order 2^b, for b up to the two-adicity.

The specifications follow Cormen et al., Introduction to Algorithms, chapter 30.

```text
    dft_omega(x)_i      = sum_{j < n} omega^(i j) x_j
    coset_s(x)_i        = sum_{j < n} (s omega^i)^j x_j
    idft_omega(x)_i     = (1 / n) sum_{j < n} omega^(-i j) x_j
    c = idft_omega(x),  padded with zeros to the larger height:  the coefficients of the interpolant
```

The map rev_k(i) reverses the k low bits of i.
-/

open p3_dft.mirror Plonky3Lean.Spec.Dft Plonky3Lean.Proofs.Dft
open p3_dft.naive.mirror p3_dft.radix_2_dit.mirror p3_dft.radix_2_bowers.mirror
open p3_dft.radix_2_dit_parallel.mirror p3_dft.butterflies.mirror p3_dft.radix_2_small_batch.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Dft

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-! ## The transform -/

section spec

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The inverse transform undoes the transform, for a primitive n-th root omega. -/
theorem idft_dft {ω : K} {n : ℕ} [NeZero n] (hω : IsPrimitiveRoot ω n) (x : ℕ → V) {i : ℕ}
    (hi : i < n) : idft ω n (dft ω n x) i = x i :=
  Proofs.Dft.idft_dft hω x hi

/-- The inverse coset transform undoes the coset transform, for a nonzero shift. -/
theorem cosetIdft_cosetDft {s ω : K} {n : ℕ} [NeZero n] (hs : s ≠ 0) (hω : IsPrimitiveRoot ω n)
    (x : ℕ → V) {i : ℕ} (hi : i < n) : cosetIdft s ω n (cosetDft s ω n x) i = x i :=
  Proofs.Dft.cosetIdft_cosetDft hs hω x hi

/-- Column c of the transform evaluates the polynomial sum_j x_(j, c) X^j at omega^i. -/
theorem dft.column (ω : K) (n : ℕ) {w : ℕ} (x : ℕ → Fin w → K) (c : Fin w) (i : ℕ) :
    dft ω n x i c = (poly n (fun j => x j c)).eval (ω ^ i) :=
  Proofs.Dft.dft_col_eval ω n x c i

/-- The inverse transform gives the coefficients of the interpolant through the points (omega^i, x_i). -/
theorem idft.interpolant {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → K) :
    poly (2 ^ k) (idft ω (2 ^ k) x) = interpolant ω (2 ^ k) x :=
  Proofs.Dft.poly_idft_eq_interpolant hω x

/-- Column c of an extension is the interpolant of column c on the subgroup of order 2^k, evaluated at s g^r.

This holds for every shift s, including zero and shifts in either subgroup. -/
theorem lde.column {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) {N : ℕ} (hN : 2 ^ k ≤ N)
    (s : K) {w : ℕ} (x : ℕ → Fin w → K) (c : Fin w) (r : ℕ) :
    cosetDft s g N (padCoeffs ω (2 ^ k) x) r c =
      (interpolant ω (2 ^ k) (fun i => x i c)).eval (s * g ^ r) :=
  Proofs.Dft.lde_col_eval hω hN s x c r

/-- When g^(2^a) = omega and the shift is one, row i 2^a of the extension is row i of the input. -/
theorem lde.extends {ω g : K} {k a : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hg : g ^ 2 ^ a = ω)
    (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    cosetDft 1 g (2 ^ (k + a)) (padCoeffs ω (2 ^ k) x) (i * 2 ^ a) = x i :=
  Proofs.Dft.lde_extends hω hg x hi

end spec

/-! ## Butterfly networks

The iterative Cooley-Tukey network (Cooley and Tukey, 1965) runs k decimation-in-time layers.

It reads its input in bit-reversed order.

The Gentleman-Sande network runs k decimation-in-frequency layers on natural input. -/

section networks

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The k decimation-in-time layers, on the input in bit-reversed order, return the transform. -/
theorem cooley_tukey {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : ditNet ω k k (bitRevVec (rev k) x) i = dft ω (2 ^ k) x i :=
  Proofs.Dft.ditNet_eq_dft hω x hi

/-- The k decimation-in-frequency layers return the transform in bit-reversed order. -/
theorem gentleman_sande {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : difNet ω k k x i = dft ω (2 ^ k) x (rev k i) :=
  Proofs.Dft.difNet_eq_dft hω x hi

/-- The decimation-in-time layers with the shift c baked into the twiddles return the coset transform. -/
theorem cooley_tukey.coset {c ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : ditNetC c ω k k (bitRevVec (rev k) x) i = cosetDft c ω (2 ^ k) x i :=
  Proofs.Dft.ditNetC_eq_cosetDft hω x hi

/-- Conjugating a layer by the bit reversal of 2^(L+1+j) rows exchanges blocks and offsets.

Before, the layer has half block 2^L and twiddle t(s) at offset s.

After, it has half block 2^j and twiddle t(rev_L(sigma)) at block sigma. -/
theorem layer.bit_reversed (f : K → V → V → V × V) (tw : ℕ → K) (L j : ℕ) (y : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ (L + 1 + j)) :
    layer (fun _ s => f (tw s)) (2 ^ L) (2 ^ j) y (rev (L + 1 + j) i) =
      layer (fun σ _ => f (tw (rev L σ))) (2 ^ j) (2 ^ L) (fun p => y (rev (L + 1 + j) p)) i :=
  Proofs.Dft.conj_layer f tw L j y hi

end networks

/-! ## The backends -/

section backends

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The naive transform of 2^k rows is the transform at G_k. -/
theorem naive.dft_batch (G : Gen K) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (NaiveDft.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.naive_dft_batch G hk x

/-- The naive transform panics when the height is not a power of two, including height 0. -/
theorem naive.dft_batch.panics_not_pow (G : Gen K) {h : ℕ} (hh : ∀ k, h ≠ 2 ^ k) (x : ℕ → V) :
    NaiveDft.dft_batch G h x = none :=
  Proofs.Dft.naive_dft_batch_not_pow G hh x

/-- The naive transform of 2^k rows panics when k exceeds the two-adicity. -/
theorem naive.dft_batch.panics_too_big (G : Gen K) {k : ℕ} (hk : G.adicity < k) (x : ℕ → V) :
    NaiveDft.dft_batch G (2 ^ k) x = none :=
  Proofs.Dft.naive_dft_batch_too_big G hk x

/-- The radix-2 decimation-in-time transform of 2^k rows is the transform at G_k. -/
theorem radix2Dit.dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2Dit.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.radix2Dit_dft_batch G hG hk x

/-- The radix-2 decimation-in-time transform panics when the height is not a power of two. -/
theorem radix2Dit.dft_batch.panics_not_pow (G : Gen K) {h : ℕ} (hh : ∀ k, h ≠ 2 ^ k) (x : ℕ → V) :
    Radix2Dit.dft_batch G h x = none :=
  Proofs.Dft.radix2Dit_dft_batch_not_pow G hh x

/-- The radix-2 decimation-in-time transform of 2^k rows panics when k exceeds the two-adicity. -/
theorem radix2Dit.dft_batch.panics_too_big (G : Gen K) {k : ℕ} (hk : G.adicity < k) (x : ℕ → V) :
    Radix2Dit.dft_batch G (2 ^ k) x = none :=
  Proofs.Dft.radix2Dit_dft_batch_too_big G hk x

/-- The radix-2 decimation-in-time extension sees the coefficients in natural order.

It evaluates the zero-padded transformed coefficients on s times the subgroup of order 2^(k+a).

It needs a nonzero width when the shift is not one, and a padded length below 2^64. -/
theorem radix2Dit.coset_lde_batch_with_transform (G : Gen K) (hG : GenValid G) {k a w : ℕ}
    (hka : k + a ≤ G.adicity) (s : K) (hw : w ≠ 0 ∨ s = 1) (ha : a < 64)
    (hlen : w * 2 ^ (k + a) < 2 ^ 64) (T : (ℕ → V) → ℕ → V) (x : ℕ → V) :
    ∃ c : ℕ → V, (∀ i < 2 ^ k, c i = idft (G.gen k) (2 ^ k) x i) ∧
    Computes (Radix2Dit.coset_lde_batch_with_transform G w (2 ^ k) a s T x) (2 ^ (k + a))
      (cosetDft s (G.gen (k + a)) (2 ^ (k + a)) (fun j => if j < 2 ^ k then T c j else 0)) :=
  Proofs.Dft.radix2Dit_coset_lde_batch_with_transform G hG hka s hw ha hlen T x

/-- The Bowers transform of 2^k rows is the transform at G_k. -/
theorem bowers.dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2Bowers.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.bowers_dft_batch G hG hk x

/-- The Bowers inverse of 2^k rows is the inverse transform at G_k. -/
theorem bowers.idft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2Bowers.idft_batch G (2 ^ k) x) (2 ^ k) (idft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.bowers_idft_batch G hG hk x

/-- The G network of 2^n rows returns the transform of its input read in bit-reversed order. -/
theorem bowers.g (G : Gen K) (hG : GenValid G) {n : ℕ} (hn : n ≤ G.adicity) (y : ℕ → V) :
    Computes (bowers_g G (2 ^ n) y) (2 ^ n) (dft (G.gen n) (2 ^ n) (fun j => y (rev n j))) :=
  Proofs.Dft.bowers_g_spec G hG hn y

/-- The G^T network of 2^n rows returns the transform at G_n^(-1), in bit-reversed order, without the 1/n. -/
theorem bowers.g_t (G : Gen K) (hG : GenValid G) {n : ℕ} (hn : n ≤ G.adicity) (y : ℕ → V) :
    Computes (bowers_g_t G (2 ^ n) y) (2 ^ n) (fun i => dft (G.gen n)⁻¹ (2 ^ n) y (rev n i)) :=
  Proofs.Dft.bowers_g_t_spec G hG hn y

/-- The Bowers extension evaluates the padded coefficients on the subgroup of order 2^(k+a). -/
theorem bowers.lde_batch (G : Gen K) (hG : GenValid G) {k a : ℕ} (hka : k + a ≤ G.adicity)
    (x : ℕ → V) :
    Computes (Radix2Bowers.lde_batch G (2 ^ k) a x) (2 ^ (k + a))
      (dft (G.gen (k + a)) (2 ^ (k + a)) (padCoeffs (G.gen k) (2 ^ k) x)) :=
  Proofs.Dft.bowers_lde_batch G hG hka x

/-- The Bowers coset extension evaluates the padded coefficients on s times the subgroup of order 2^(k+a). -/
theorem bowers.coset_lde_batch (G : Gen K) (hG : GenValid G) {k a : ℕ} (hka : k + a ≤ G.adicity)
    (s : K) (x : ℕ → V) :
    Computes (Radix2Bowers.coset_lde_batch G (2 ^ k) a s x) (2 ^ (k + a))
      (cosetDft s (G.gen (k + a)) (2 ^ (k + a)) (padCoeffs (G.gen k) (2 ^ k) x)) :=
  Proofs.Dft.bowers_coset_lde_batch G hG hka s x

/-- The Bowers extension with a transform sees coefficient j at row rev_k(j), the bit-reversed layout. -/
theorem bowers.coset_lde_batch_with_transform (G : Gen K) (hG : GenValid G) {k a : ℕ}
    (hka : k + a ≤ G.adicity) (s : K) (T : (ℕ → V) → ℕ → V) (x : ℕ → V) :
    ∃ c : ℕ → V, (∀ i < 2 ^ k, c (rev k i) = idft (G.gen k) (2 ^ k) x i) ∧
    Computes (Radix2Bowers.coset_lde_batch_with_transform G (2 ^ k) a s T x) (2 ^ (k + a))
      (cosetDft s (G.gen (k + a)) (2 ^ (k + a)) (fun j => if j < 2 ^ k then T c (rev k j) else 0)) :=
  Proofs.Dft.bowers_coset_lde_batch_with_transform G hG hka s T x

/-- The parallel transform of 2^k rows, read through its bit-reversed view, is the transform at G_k. -/
theorem parallel.dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2DitParallel.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.parallel_dft_batch G hG hk x

/-- The parallel inverse of 2^k rows is the inverse transform at G_k, with the 1/2^k folded into a layer. -/
theorem parallel.idft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2DitParallel.idft_batch G (2 ^ k) x) (2 ^ k) (idft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.parallel_idft_batch G hG hk x

/-- The parallel coset transform, read through its bit-reversed view, is the coset transform. -/
theorem parallel.coset_dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (s : K)
    (x : ℕ → V) :
    Computes (Radix2DitParallel.coset_dft_batch G (2 ^ k) s x) (2 ^ k) (cosetDft s (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.parallel_coset_dft_batch G hG hk s x

/-- The parallel inverse coset transform is the inverse coset transform, for a nonzero shift. -/
theorem parallel.coset_idft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity)
    {w : ℕ} {s : K} (hs : s ≠ 0) (hw : w ≠ 0 ∨ s = 1) (x : ℕ → V) :
    Computes (Radix2DitParallel.coset_idft_batch G w (2 ^ k) s x) (2 ^ k) (cosetIdft s (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.parallel_coset_idft_batch G hG hk hs hw x

/-- The parallel extension, for nested generators, sees coefficient j at row rev_k(j).

Read through its bit-reversed view, it evaluates the transformed coefficients.

The evaluation points are s times the subgroup of order 2^(k+a).

Each coset of the large subgroup is evaluated with the small generator G_k.

So the result needs G_(k+a)^(2^a) = G_k. -/
theorem parallel.lde (G : Gen K) (hG : GenValid G) (hN : GenNested G) {k a w : ℕ}
    (hka : k + a ≤ G.adicity) (s : K) (ha : a < 64) (hlen : w * (2 ^ k * 2 ^ a) < 2 ^ 64)
    (T : (ℕ → V) → ℕ → V) (x : ℕ → V) :
    ∃ c : ℕ → V, (∀ i < 2 ^ k, c (rev k i) = idft (G.gen k) (2 ^ k) x i) ∧
    Computes (Radix2DitParallel.lde_with_consumer G w (2 ^ k) a s T x) (2 ^ (k + a))
      (cosetDft s (G.gen (k + a)) (2 ^ (k + a)) (fun j => if j < 2 ^ k then T c (rev k j) else 0)) :=
  Proofs.Dft.parallel_lde G hG hN hka s ha hlen T x

/-- The small-batch transform of 2^k rows is the transform at G_k, for nested generators.

Its shared cache may hold the tables of any larger size 2^L, built from G_L.

The result holds for every rows-per-chunk estimate c and width w. -/
theorem smallBatch.dft_batch (G : Gen K) (hG : GenValid G) (hN : GenNested G) {k L : ℕ}
    (hkL : k ≤ L) (hL : L ≤ G.adicity) (c w : ℕ) (x : ℕ → V) :
    Computes (Radix2DFTSmallBatch.dft_batch G L c w (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.smallBatch_dft_batch G hG hN hkL hL c w x

/-- The small-batch inverse of 2^k rows is the inverse transform at G_k.

This holds for nested generators and any cache size 2^L >= 2^k. -/
theorem smallBatch.idft_batch (G : Gen K) (hG : GenValid G) (hN : GenNested G) {k L : ℕ}
    (hkL : k ≤ L) (hL : L ≤ G.adicity) (c w : ℕ) (x : ℕ → V) :
    Computes (Radix2DFTSmallBatch.idft_batch G L c w (2 ^ k) x) (2 ^ k) (idft (G.gen k) (2 ^ k) x) :=
  Proofs.Dft.smallBatch_idft_batch G hG hN hkL hL c w x

end backends

/-! ## The default methods

Each holds for any backend whose own methods meet their specifications. -/

section defaults

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The default inverse, from a transform at omega with omega^(2^k) = 1, is the inverse transform.

It divides by 2^k and swaps row r with row 2^k - r. -/
theorem default.idft_batch {ω : K} {k : ℕ} (hω : ω ^ 2 ^ k = 1)
    {dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft ω (2 ^ k) x)) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.idft_batch (K := K) dft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x) :=
  Proofs.Dft.traits_idft_batch hω hd x

/-- The default coset transform is the coset transform, for a nonzero width or a shift of one. -/
theorem default.coset_dft_batch {ω : K} {k : ℕ} {dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft ω (2 ^ k) x)) {w : ℕ} (s : K)
    (hw : w ≠ 0 ∨ s = 1) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_dft_batch dft_batch w (2 ^ k) x s) (2 ^ k) (cosetDft s ω (2 ^ k) x) :=
  Proofs.Dft.traits_coset_dft_batch hd s hw x

/-- The default inverse coset transform is the inverse coset transform, for a nonzero shift. -/
theorem default.coset_idft_batch {ω : K} {k : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x)) {w : ℕ} {s : K}
    (hs : s ≠ 0) (hw : w ≠ 0 ∨ s = 1) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_idft_batch idft_batch w (2 ^ k) x s) (2 ^ k) (cosetIdft s ω (2 ^ k) x) :=
  Proofs.Dft.traits_coset_idft_batch hi hs hw x

/-- The default inverse coset transform panics at a zero shift. -/
theorem default.coset_idft_batch.panics {k : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    {ω : K} (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x)) (w : ℕ)
    (x : ℕ → V) : p3_dft.traits.mirror.coset_idft_batch idft_batch w (2 ^ k) x (0 : K) = none :=
  Proofs.Dft.traits_coset_idft_batch_zero hi w x

/-- The default extension evaluates the padded coefficients on s times the subgroup of order 2^(k+a). -/
theorem default.coset_lde_batch {ω g : K} {k a w : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    {coset_dft_batch : ℕ → (ℕ → V) → K → Option (ℕ → V)} (s : K)
    (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x))
    (hc : ∀ x, Computes (coset_dft_batch (2 ^ (k + a)) x s) (2 ^ (k + a)) (cosetDft s g (2 ^ (k + a)) x))
    (ha : a < 64) (hlen : 2 ^ k * w * 2 ^ a < 2 ^ 64) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_lde_batch_with_transform idft_batch coset_dft_batch w
      (2 ^ k) a s id x) (2 ^ (k + a)) (cosetDft s g (2 ^ (k + a)) (padCoeffs ω (2 ^ k) x)) :=
  Proofs.Dft.traits_coset_lde_batch s hi hc ha hlen x

/-- A method on an algebra over the field is the base-field method, read through the coordinates.

So an algebra transform is the transform of the algebra-valued rows. -/
theorem default.algebra {W U : Type _} [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (e : W ≃ₗ[K] U) {base : (ℕ → U) → Option (ℕ → U)} {n : ℕ} {spec : (ℕ → W) → ℕ → W}
    (hb : ∀ x : ℕ → W, Computes (base (e ∘ x)) n (e ∘ spec x)) (x : ℕ → W) :
    Computes (p3_dft.traits.mirror.via_base e e.symm base x) n (spec x) :=
  Proofs.Dft.via_base_spec e hb x

/-- Linear maps commute with the transform.

So the coordinates of an algebra transform are base-field transforms. -/
theorem dft.linear {U : Type _} [AddCommGroup U] [Module K U] (f : V →ₗ[K] U) (ω : K) (n : ℕ)
    (x : ℕ → V) (i : ℕ) : dft ω n (f ∘ x) i = f (dft ω n x i) :=
  Proofs.Dft.dft_map f ω n x i

end defaults

/-! ## Twiddle tables -/

section tables

variable {K : Type _} [Field K] [DecidableEq K]

/-- Entry b of the bit-reversed half table of g, for b below 2^(n-1-l), is g^(rev_(n-1-l)(b) 2^l). -/
theorem bitrev_table {g : K} {n l b : ℕ} (hl : l < n) (hb : b < 2 ^ (n - 1 - l)) :
    (revIndex (2 ^ n / 2) (powersList g (2 ^ n / 2))).getD b 0 = g ^ (rev (n - 1 - l) b * 2 ^ l) :=
  Proofs.Dft.getD_bowers_table g hl hb

/-- The coset table of layer l below ceil(k/2) holds (c omega^i)^(2^(k-1-l)) at entry i. -/
theorem coset_table.first (ω c : K) {k l i : ℕ} (hl : l < (k + 1) / 2) (hk : l < k)
    (hi : i < 2 ^ l) :
    ((cosetTbl ω c k).getD (k - 1 - l) []).getD i 0 = (c * ω ^ i) ^ 2 ^ (k - 1 - l) :=
  Proofs.Dft.coset_table_first ω c hl hk hi

/-- The coset table of layer l from ceil(k/2) on holds (c omega^(rev_l(b)))^(2^(k-1-l)) at entry b. -/
theorem coset_table.second (ω c : K) {k l b : ℕ} (hl : (k + 1) / 2 ≤ l) (hk : l < k)
    (hb : b < 2 ^ l) :
    ((cosetTbl ω c k).getD (k - 1 - l) []).getD b 0 = (c * ω ^ rev l b) ^ 2 ^ (k - 1 - l) :=
  Proofs.Dft.coset_table_second ω c hl hk hb

end tables

/-! ## Butterflies on rows

The unrolled loops compute the butterflies entry by entry, for rows of equal length. -/

section rows

variable {F : Type _} [Field F]

/-- The decimation-in-time butterfly sends rows (a, b) to (a + b t, a - b t). -/
theorem dit.apply_to_rows (t : F) (r1 r2 : List F) (h : r1.length = r2.length) :
    DitButterfly.apply_to_rows t r1 r2 =
      (List.zipWith (fun a b => a + b * t) r1 r2, List.zipWith (fun a b => a - b * t) r1 r2) :=
  Proofs.Dft.dit_apply_to_rows t r1 r2 h

/-- The decimation-in-frequency butterfly sends rows (a, b) to (a + b, (a - b) t). -/
theorem dif.apply_to_rows (t : F) (r1 r2 : List F) (h : r1.length = r2.length) :
    DifButterfly.apply_to_rows t r1 r2 =
      (List.zipWith (fun a b => a + b) r1 r2, List.zipWith (fun a b => (a - b) * t) r1 r2) :=
  Proofs.Dft.dif_apply_to_rows t r1 r2 h

/-- The scaled butterfly sends rows (a, b) to ((a + b t) s, (a - b t) s). -/
theorem scaled.apply_to_rows (t s : F) (r1 r2 : List F) (h : r1.length = r2.length) :
    ScaledDitButterfly.apply_to_rows (ScaledDitButterfly.new t s) r1 r2 =
      (List.zipWith (fun a b => (a + b * t) * s) r1 r2, List.zipWith (fun a b => (a - b * t) * s) r1 r2) :=
  Proofs.Dft.scaled_apply_to_rows t s r1 r2 h

end rows

/-! ## The fields

Each table, read in its field, holds nested generators.

Entry b has order 2^b and squares to entry b - 1. -/

/-- BabyBear: 28 entries, two-adicity 27. -/
theorem babyBear.generators :
    ∃ t, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)).adicity = 27 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) :=
  Proofs.Dft.babyBear_generators

/-- KoalaBear: 25 entries, two-adicity 24. -/
theorem koalaBear.generators :
    ∃ t, Plonky3Lean.Spec.KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)).adicity = 24 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.KoalaBear.toField)) :=
  Proofs.Dft.koalaBear_generators

/-- Goldilocks: 33 entries, two-adicity 32. -/
theorem goldilocks.generators :
    ∃ t, p3_goldilocks.goldilocks.Goldilocks.TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)).adicity = 32 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.Goldilocks.toField)) :=
  Proofs.Dft.goldilocks_generators

/-- Mersenne31 is not two-adic.

Its complex extension has 33 entries, two-adicity 32. -/
theorem mersenne31Complex.generators :
    ∃ t, p3_mersenne_31.mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS = .ok t ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)).adicity = 32 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.Mersenne31.toComplex)) :=
  Proofs.Dft.mersenne31Complex_generators

end Plonky3Lean.Claims.Dft
