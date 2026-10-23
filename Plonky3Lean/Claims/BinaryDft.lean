module

public import Plonky3Lean.Proofs.BinaryDft.Concrete

@[expose] public section

/-!
# p3-binary-dft: claims

The crate is transcribed over a field of characteristic 2, not extracted.

A tower level is the field with its bit width 2^b and its Cantor basis beta.

The tower levels of the binary-field proofs, GF(2^(2^k)) for k up to 7, are such levels.

The specification is the additive NTT of Lin, Chung and Han (FOCS 2014):

```text
    S_l      = { point(m) : m < 2^l },   point(m) = sum_r (bit r of m) beta_r
    W_i(x)   = prod_(s in S_i) (x - s)            W^_i(x) = W_i(x) / W_i(beta_i)
    X_k(x)   = prod_(j < l) W^_j(x)^(bit j of k)
    ntt(d)_i = sum_(k < 2^l) X_k(shift + point(i)) d_k
```

A matrix of width w is its rows in a vector space V over the field.

Rows at the height and above are not part of the matrix.

A panic is none.
-/

open Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft Finset
open p3_binary_dft.mirror p3_binary_dft.domain.mirror p3_binary_dft.naive.mirror
open p3_binary_dft.lch.mirror p3_binary_dft.traits.mirror p3_binary_dft.butterfly.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.BinaryDft

/-! ## The subspace polynomials -/

section Spec

variable {F : Type _} [Field F] [CharP F 2] {V : Type _} [AddCommGroup V] [Module F V]

/-- Lin, Chung and Han, Lemma 1: W_i is additive. -/
theorem vanishing.add (β : ℕ → F) (i : ℕ) (x y : F) :
    vanishing β i (x + y) = vanishing β i x + vanishing β i y :=
  Proofs.BinaryDft.vanishing_add β i x y

/-- W_(i+1)(x) = W_i(x) (W_i(x) + W_i(beta_i)). -/
theorem vanishing.succ (β : ℕ → F) (i : ℕ) (x : F) :
    vanishing β (i + 1) x = vanishing β i x * (vanishing β i x + vanishing β i (β i)) :=
  Proofs.BinaryDft.vanishing_succ' β i x

/-- W_i vanishes on S_i. -/
theorem vanishing.point_eq_zero (β : ℕ → F) {i m : ℕ} (hm : m < 2 ^ i) :
    vanishing β i (point β m) = 0 :=
  Proofs.BinaryDft.vanishing_point β hm

/-- For a Cantor basis, W_j(x) is the j-th iterate of x^2 + x, and W^_j = W_j. -/
theorem normalized.cantor {β : ℕ → F} {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j < n) (x : F) :
    normalized β j x = sqAddIter j x :=
  Proofs.BinaryDft.normalized_eq_sqAddIter hβ hj x

/-- A Cantor basis is independent. -/
theorem IsCantor.independent' {β : ℕ → F} {n : ℕ} (hβ : IsCantor β n) : Independent β n :=
  Proofs.BinaryDft.IsCantor.independent hβ

/-- For a Cantor basis, the twiddle of stage j and block b is W_j(shift) + point(2b). -/
theorem twiddle.cantor {β : ℕ → F} {n : ℕ} (hβ : IsCantor β n) (shift : F) {j b : ℕ} (hj : j < n)
    (hb : b * 2 ^ (j + 1) < 2 ^ n) :
    twiddle β shift j b = sqAddIter j shift + point β (2 * b) :=
  Proofs.BinaryDft.twiddle_cantor hβ shift hj hb

/-- From block c - 1 to block c, point(2c) adds beta_1 + ... + beta_(t+1), t the trailing zeros of c. -/
theorem point.step (β : ℕ → F) {c : ℕ} (hc : 0 < c) :
    point β (2 * c) = point β (2 * (c - 1)) + ∑ q ∈ range (trailingZeros c + 1), β (q + 1) :=
  Proofs.BinaryDft.point_step β hc

/-! ## The network -/

/-- Lin, Chung and Han, section III: the network of the twiddles W^_j at the block points computes the additive NTT. -/
theorem network_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d : ℕ → V) {i : ℕ} (hi : i < 2 ^ l) :
    network (twiddle β shift) l d i = ntt β l shift d i :=
  Proofs.BinaryDft.network_ntt β hβ hl shift d hi

/-- The inverse network undoes the network, for any twiddles. -/
theorem inetwork_network (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) : inetwork τ l (network τ l x) = x :=
  Proofs.BinaryDft.inetwork_network τ l x

/-- The network undoes the inverse network, for any twiddles. -/
theorem network_inetwork (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) : network τ l (inetwork τ l x) = x :=
  Proofs.BinaryDft.network_inetwork τ l x

/-- The inverse network recovers the coefficients from the values on the coset. -/
theorem inetwork_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d y : ℕ → V) (hy : ∀ i < 2 ^ l, y i = ntt β l shift d i) {i : ℕ} (hi : i < 2 ^ l) :
    inetwork (twiddle β shift) l y i = d i :=
  Proofs.BinaryDft.inetwork_ntt β hβ hl shift d y hy hi

/-- Coefficients zero from 2^m on: row c 2^m + i over S_(m+r) is row i over the coset point(c 2^m) + S_m. -/
theorem ntt_pad (β : ℕ → F) {m : ℕ} (r : ℕ) (shift : F) (d : ℕ → V)
    (hd : ∀ k, 2 ^ m ≤ k → d k = 0) (c : ℕ) {i : ℕ} (hi : i < 2 ^ m) :
    ntt β (m + r) shift d (c * 2 ^ m + i) = ntt β m (shift + point β (c * 2 ^ m)) d i :=
  Proofs.BinaryDft.ntt_pad β r shift d hd c hi

end Spec

/-- A field isomorphism carries the transform over beta to the transform over the image of beta. -/
theorem ntt_map {F G : Type _} [Field F] [Field G] (φ : F →+* G) (β : ℕ → F) (l : ℕ) (shift : F)
    (d : ℕ → F) (i : ℕ) :
    φ (ntt β l shift d i) = ntt (φ ∘ β) l (φ shift) (φ ∘ d) i :=
  Proofs.BinaryDft.map_ntt φ β l shift d i

/-- A field isomorphism carries a Cantor basis to a Cantor basis. -/
theorem IsCantor.map' {F G : Type _} [Field F] [Field G] (φ : F →+* G) {β : ℕ → F} {n : ℕ}
    (h : IsCantor β n) : IsCantor (φ ∘ β) n :=
  Proofs.BinaryDft.IsCantor.map φ h

/-! ## The domain -/

section Domain

variable {F : Type _} [Field F]

/-- The domain point of an index is point(index), and panics past the level's 2^(2^b) points. -/
theorem domain_point.eq (L : Level F) (index : ℕ) :
    domain_point L index =
      if index < 2 ^ 2 ^ L.logBits then some (point L.cantor index) else none :=
  Proofs.BinaryDft.domain_point_eq L index

/-- Entry r of the steps table is beta_1 + ... + beta_(r+1), and the table panics past the level. -/
theorem domain_point_steps.eq (L : Level F) (count : ℕ) :
    domain_point_steps L count =
      if count < 2 ^ L.logBits then
        some ((List.range count).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1))
      else none :=
  Proofs.BinaryDft.domain_point_steps_eq L count

/-- The subspace polynomial is the j-th iterate of x^2 + x. -/
theorem subspace_polynomial.eq (j : ℕ) (x : F) : subspace_polynomial j x = sqAddIter j x :=
  Proofs.BinaryDft.subspace_polynomial_eq j x

/-- The twiddle state of 2^l rows: the bases W_j(shift) and the steps table. -/
theorem Twiddles.new.eq (L : Level F) {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) :
    Twiddles.new L l shift = some ⟨(List.range l).map fun j => sqAddIter j shift,
      (List.range (l - 1)).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1)⟩ :=
  Proofs.BinaryDft.Twiddles.new_eq L hl shift

end Domain

/-! ## The kernels -/

section Kernels

variable {F : Type _} [Field F] [DecidableEq F] {V : Type _} [AddCommGroup V] [Module F V]

/-- The work on a pair, zero twiddle included, is the forward or the inverse butterfly. -/
theorem pairOp.eq (inverse : Bool) (t : F) :
    (pairOp inverse t (decide (t = 0)) : V → V → V × V) =
      if inverse then ibutterfly t else butterfly t :=
  Proofs.BinaryDft.pairOp_eq inverse t

/-- The subfield kernel scales by the embedded twiddle. -/
theorem typed_butterfly.eq {S : Type _} (ι : S → F) (inverse : Bool) (lo hi m : ℕ) (t : S)
    (x : ℕ → V) :
    typed_butterfly ι inverse lo hi m t x =
      (List.range m).foldl (fun acc s => p3_dft.mirror.bfly
        (if inverse then ibutterfly (ι t) else butterfly (ι t)) (lo + s) (hi + s) acc) x := by
  unfold typed_butterfly
  congr 1
  funext acc s
  congr 1
  funext u v
  cases inverse <;> simp [butterfly, ibutterfly, add_comm]

end Kernels

/-! ## The Lin-Chung-Han transform -/

section Lch

variable {F : Type _} [Field F] [DecidableEq F] [CharP F 2] {V : Type _} [AddCommGroup V]
  [Module F V] {L : Level F} (hL : Cantor L)
include hL

/-- One stage pass, cut into tasks with their twiddles walked from block to block, is the stage. -/
theorem stage_pass.eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) (inverse : Bool) {width j : ℕ}
    (hw : 0 < width) (hj : j < l) (x : ℕ → V) :
    stage_pass L (canonTw L l shift) inverse width (2 ^ l) j x =
      some fun r => if r < 2 ^ l then
        (if inverse then istage (twiddle L.cantor shift j) j x r
          else stage (twiddle L.cantor shift j) j x r) else x r :=
  Proofs.BinaryDft.stage_pass_eq hL hl shift inverse hw hj x

/-- The blocked schedule on the serial pool is the network. -/
theorem run.eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) (inverse : Bool) {width bytes : ℕ}
    (hw : 0 < width) (x : ℕ → V) :
    run L (canonTw L l shift) inverse width l (Schedule.new bytes width l) x =
      some fun r => if r < 2 ^ l then
        (if inverse then inetwork (twiddle L.cantor shift) l x r
          else network (twiddle L.cantor shift) l x r) else x r := by
  rw [Proofs.BinaryDft.run_eq hL hl shift inverse hw x]
  cases inverse <;> rfl

/-- The forward transform of 2^l rows is the additive NTT over the coset shift + S_l. -/
theorem transform_ntt {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) {width : ℕ} (hw : 0 < width)
    (x : ℕ → V) :
    transform L false width (2 ^ l) shift x =
      some fun r => if r < 2 ^ l then ntt L.cantor l shift x r else x r :=
  Proofs.BinaryDft.transform_ntt hL hl shift hw x

/-- The inverse transform of values on the coset recovers their coefficients. -/
theorem transform_intt {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) {width : ℕ} (hw : 0 < width)
    (d y : ℕ → V) (hy : ∀ i < 2 ^ l, y i = ntt L.cantor l shift d i) {i : ℕ} (hi : i < 2 ^ l) :
    (transform L true width (2 ^ l) shift y).map (· i) = some (d i) :=
  Proofs.BinaryDft.transform_intt hL hl shift hw d y hy hi

/-- The transform panics on a height that is not a power of two, a domain wider than the level, or width zero. -/
theorem transform.panics (inverse : Bool) {n width : ℕ} (shift : F)
    (h : (∀ k, n ≠ 2 ^ k) ∨ (∃ l, n = 2 ^ l ∧ 2 ^ L.logBits < l) ∨ width = 0) (x : ℕ → V) :
    transform L inverse width n shift x = none :=
  Proofs.BinaryDft.transform_panics inverse shift h x

/-- The padded transform of a message of 2^m rows within one tile is the additive NTT of the padded message over S_(m+r). -/
theorem LchNtt.ntt_batch_padded.eq {m r width : ℕ} (hmr : m + r ≤ 2 ^ L.logBits) (hw : 0 < width)
    (hsmall : L.bytes * (width * 2 ^ m) ≤ DEEP_TILE_BYTES) (x : ℕ → V) :
    LchNtt.ntt_batch_padded L width (2 ^ (m + r)) x r =
      some fun i => if i < 2 ^ (m + r) then ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x) i else x i :=
  Proofs.BinaryDft.ntt_batch_padded_eq hL hmr hw hsmall x

/-- The padded transform panics on a padding past the height or a domain wider than the level. -/
theorem LchNtt.ntt_batch_padded.panics {l r width : ℕ} (h : l < r ∨ 2 ^ L.logBits < l)
    (x : ℕ → V) : LchNtt.ntt_batch_padded L width (2 ^ l) x r = none :=
  Proofs.BinaryDft.ntt_batch_padded_panics hL h x

/-- Reed-Solomon encoding at rate 2^(-r): the padded coefficients evaluated on S_(m+r). -/
theorem encode_batch.eq {m r width : ℕ} (hmr : m + r ≤ 2 ^ L.logBits) (hw : 0 < width)
    (hsmall : L.bytes * (width * 2 ^ m) ≤ DEEP_TILE_BYTES) (hr : r < 64)
    (hword : 2 ^ m * width * 2 ^ r < 2 ^ 64) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ (m + r)) :
    (p3_binary_dft.encoder.mirror.encode_batch (lchBackend L) width (2 ^ m) x r).map (· i) =
      some (ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x) i) := by
  rw [Proofs.BinaryDft.encode_batch_eq hL hmr hw hsmall hr hword x]
  simp [mask, hi]

/-- The default extension returns its input rows first, then the values of their interpolant. -/
theorem shifted_lde_batch.eq {l a width : ℕ} (hla : l + a ≤ 2 ^ L.logBits) (ha : 0 < a)
    (hw : 0 < width) (har : a < 64) (hword : 2 ^ l * width * 2 ^ a < 2 ^ 64) (shift : F)
    (y : ℕ → V) :
    ∃ d : ℕ → V, (∀ i < 2 ^ l, ntt L.cantor l shift d i = y i) ∧
      ∀ i < 2 ^ (l + a), (shifted_lde_batch L (lchBackend L) width (2 ^ l) y a shift).map (· i) =
        some (ntt L.cantor (l + a) shift (zeroBelow (2 ^ l) d) i) := by
  obtain ⟨d, hd, h⟩ := Proofs.BinaryDft.shifted_lde_eq hL hla ha hw har hword shift y
  exact ⟨d, hd, fun i hi => by rw [h]; simp [mask, hi]⟩

/-! ## The reference transform -/

/-- The forward reference transform is the additive NTT. -/
theorem NaiveAdditiveNtt.shifted_ntt_batch.eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F)
    (d : ℕ → V) :
    NaiveAdditiveNtt.shifted_ntt_batch L (2 ^ l) d shift =
      some fun r => if r < 2 ^ l then ntt L.cantor l shift d r else 0 :=
  Proofs.BinaryDft.naive_ntt_eq hL hl shift d

/-- The inverse reference transform is the inverse network. -/
theorem NaiveAdditiveNtt.shifted_intt_batch.eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F)
    (x : ℕ → V) :
    NaiveAdditiveNtt.shifted_intt_batch L (2 ^ l) x shift =
      some fun r => if r < 2 ^ l then inetwork (twiddle L.cantor shift) l x r else x r :=
  Proofs.BinaryDft.naive_intt_eq hL hl shift x

/-- The forward reference transform panics on a domain wider than the level. -/
theorem NaiveAdditiveNtt.shifted_ntt_batch.panics {l : ℕ} (hl : 2 ^ L.logBits < l) (shift : F)
    (d : ℕ → V) : NaiveAdditiveNtt.shifted_ntt_batch L (2 ^ l) d shift = none :=
  Proofs.BinaryDft.naive_ntt_panics_wide hl shift d

/-- Both reference transforms panic on a height that is not a power of two. -/
theorem NaiveAdditiveNtt.panics_height {n : ℕ} (hn : ∀ k, n ≠ 2 ^ k) (shift : F) (d : ℕ → V) :
    NaiveAdditiveNtt.shifted_ntt_batch L n d shift = none ∧
      NaiveAdditiveNtt.shifted_intt_batch L n d shift = none :=
  Proofs.BinaryDft.naive_panics_height hn shift d

end Lch

/-! ## The tower levels -/

/-- The tower level of 2^k bits, k up to 7, has a Cantor basis of its whole width. -/
theorem towerLevel.cantor {k : ℕ} (hk : k ≤ 7) (b : ℕ) : Cantor (towerLevel k b) :=
  Proofs.BinaryDft.towerLevel_cantor hk b

/-- Over GF(2^(2^k)), the transform of 2^l rows is the additive NTT, for every l up to the bit width. -/
theorem towerLevel.transform {k b l : ℕ} (hk : k ≤ 7) (hl : l ≤ 2 ^ k)
    (shift : ConcreteBinaryTower.ConcreteBTField k) {width : ℕ} (hw : 0 < width)
    (x : ℕ → Fin width → ConcreteBinaryTower.ConcreteBTField k) :
    transform (towerLevel k b) false width (2 ^ l) shift x =
      some fun r => if r < 2 ^ l then ntt (Plonky3Lean.Proofs.Binary.cantorTower k) l shift x r else x r :=
  Proofs.BinaryDft.transform_ntt (towerLevel_cantor hk b) hl shift hw x

end Plonky3Lean.Claims.BinaryDft
