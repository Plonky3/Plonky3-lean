module

public import Plonky3Lean.Proofs.BinaryDft.Run
public import Plonky3Lean.Proofs.Commit.Encoder

@[expose] public section

/-!
# Zero-padded coefficients and the encoder

Coefficients that vanish from 2^m on give the same polynomial in the novel basis of any larger subspace.

Row c 2^m + i of the larger transform is then row i of the transform over the coset point(c 2^m) + S_m.

So the encoder's coset transforms compute the Reed-Solomon codeword.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.lch.mirror p3_binary_dft.traits.mirror p3_binary_dft.encoder.mirror p3_dft.mirror
  p3_commit.encoder.mirror Plonky3Lean.Proofs.Dft

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-! ## The specification -/

theorem novelEval_pad (β : ℕ → F) {m : ℕ} (d : ℕ → V) (hd : ∀ k, 2 ^ m ≤ k → d k = 0) (r : ℕ)
    (x : F) : novelEval β (m + r) d x = novelEval β m d x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← add_assoc, novelEval_succ, ih]
    have h0 : novelEval β (m + r) (fun k => d (k + 2 ^ (m + r))) x = 0 := by
      refine sum_eq_zero fun k _ => ?_
      have : 2 ^ m ≤ k + 2 ^ (m + r) :=
        le_trans (Nat.pow_le_pow_right two_pos (Nat.le_add_right m r)) (Nat.le_add_left _ _)
      simp only [hd _ this, smul_zero]
    rw [h0, smul_zero, add_zero]

/-- Row c 2^m + i of the transform over S_(m+r) of a padded message is row i over point(c 2^m) + S_m. -/
theorem ntt_pad (β : ℕ → F) {m : ℕ} (r : ℕ) (shift : F) (d : ℕ → V)
    (hd : ∀ k, 2 ^ m ≤ k → d k = 0) (c : ℕ) {i : ℕ} (hi : i < 2 ^ m) :
    ntt β (m + r) shift d (c * 2 ^ m + i) = ntt β m (shift + point β (c * 2 ^ m)) d i := by
  rw [ntt, ntt, novelEval_pad β d hd, mul_comm c, point_add_mul β c m hi, add_assoc]

/-- The rows below n, with zeros from n on. -/
theorem zeroBelow_zero {n : ℕ} (x : ℕ → V) (k : ℕ) (hk : n ≤ k) : zeroBelow n x k = 0 := by
  simp [zeroBelow, show ¬ k < n by omega]

/-! ## The transcribed coset transform -/

variable [DecidableEq F] [CharP F 2] {L : Level F} (hL : Cantor L)
include hL

/-- The forward transform of 2^l rows is the additive NTT of those rows, over the coset. -/
theorem transform_ntt {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) {width : ℕ} (hw : 0 < width)
    (x : ℕ → V) :
    transform L false width (2 ^ l) shift x = some (mask l x (ntt L.cantor l shift x)) := by
  rw [transform_eq hL hl shift false hw x]
  congr 1
  funext r
  simp only [mask, lchNet, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hr
  · exact network_ntt L.cantor (IsCantor.independent hL) hl shift x hr
  · rfl

/-- The inverse transform of 2^l rows recovers the coefficients of values on the coset. -/
theorem transform_intt {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) {width : ℕ} (hw : 0 < width)
    (d y : ℕ → V) (hy : ∀ i < 2 ^ l, y i = ntt L.cantor l shift d i) {i : ℕ} (hi : i < 2 ^ l) :
    (transform L true width (2 ^ l) shift y).map (· i) = some (d i) := by
  rw [transform_eq hL hl shift true hw y]
  simp only [Option.map_some, mask, hi, ↓reduceIte, lchNet]
  exact congrArg some (inetwork_ntt L.cantor (IsCantor.independent hL) hl shift d y hy hi)

/-- The padded coset transform is the additive NTT of the zero-padded message over S_(m+r). -/
theorem transform_cosets_eq {m r width : ℕ} (hmr : m + r ≤ 2 ^ L.logBits) (hw : 0 < width)
    (hsmall : L.bytes * (width * 2 ^ m) ≤ DEEP_TILE_BYTES) (x : ℕ → V) :
    transform_cosets L width (2 ^ (m + r)) m x =
      some (mask (m + r) x (ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x))) := by
  have hm : m ≤ 2 ^ L.logBits := by omega
  have hM := Nat.two_pow_pos m
  have hR := Nat.two_pow_pos r
  have hpow : 2 ^ (m + r) = 2 ^ r * 2 ^ m := by rw [pow_add, mul_comm]
  have hcount : (2 ^ (m + r) - 2 ^ m + 2 ^ m - 1) / 2 ^ m = 2 ^ r - 1 := by
    rw [hpow, show 2 ^ r * 2 ^ m - 2 ^ m + 2 ^ m - 1 = (2 ^ m - 1) + (2 ^ r - 1) * 2 ^ m by
      rw [Nat.sub_mul, one_mul]; have : 2 ^ m ≤ 2 ^ r * 2 ^ m := Nat.le_mul_of_pos_left _ hR
      omega, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt (by omega), zero_add]
  have hidx : ∀ c, c + 1 < 2 ^ r → (c + 1) * 2 ^ m < 2 ^ 2 ^ L.logBits := fun c hc =>
    calc (c + 1) * 2 ^ m < 2 ^ r * 2 ^ m := Nat.mul_lt_mul_of_pos_right hc hM
      _ = 2 ^ (m + r) := hpow.symm
      _ ≤ 2 ^ 2 ^ L.logBits := Nat.pow_le_pow_right two_pos hmr
  -- the value of row c 2^m + i, for c < 2^r and i < 2^m
  set E := ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x)
  have hcos : ∀ (c : ℕ) (y : ℕ → V), (∀ i < 2 ^ m, y i = x i) → ∀ i < 2 ^ m,
      ntt L.cantor m (point L.cantor (c * 2 ^ m)) y i = E (c * 2 ^ m + i) := by
    intro c y hy i hi
    show _ = ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x) (c * 2 ^ m + i)
    rw [ntt_pad L.cantor r 0 _ (fun k hk => zeroBelow_zero x k hk) c hi, zero_add, ntt, ntt]
    exact novelEval_congr _ _ (fun k hk => by simp [zeroBelow, hk, hy k hk]) _
  let g : (ℕ → V) → ℕ → ℕ → V := fun acc c =>
    writeBack acc ((c + 1) * 2 ^ m) (2 ^ m)
      (mask m (slice acc 0) (ntt L.cantor m (point L.cantor ((c + 1) * 2 ^ m)) (slice acc 0)))
  unfold transform_cosets
  simp only [hsmall, ↓reduceIte, Option.bind_eq_bind]
  rw [hcount, foldlM_some _ g _ (fun acc c hc => by
    have hc' := List.mem_range.mp hc
    rw [domain_point_eq]
    simp only [hidx c (by omega), ↓reduceIte, Option.bind_some]
    rw [transform_ntt hL hm _ hw]
    rfl)]
  -- after k cosets, rows 2^m .. (k+1) 2^m hold the codeword, the rest the input
  have inv : ∀ k ≤ 2 ^ r - 1, (List.range k).foldl g x =
      fun q => if 2 ^ m ≤ q ∧ q < (k + 1) * 2 ^ m then E q else x q := by
    intro k hk
    induction k with
    | zero => funext q; simp only [List.range_zero, List.foldl_nil, zero_add, one_mul]; simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      funext q
      simp only [List.foldl_cons, List.foldl_nil, g, writeBack]
      have hsl : ∀ i < 2 ^ m, slice (fun q => if 2 ^ m ≤ q ∧ q < (k + 1) * 2 ^ m then E q else x q)
          0 i = x i := fun i hi => by simp [slice, show ¬ 2 ^ m ≤ i by omega]
      by_cases hq : (k + 1) * 2 ^ m ≤ q ∧ q < (k + 1) * 2 ^ m + 2 ^ m
      · obtain ⟨i, rfl⟩ : ∃ i, q = (k + 1) * 2 ^ m + i := ⟨q - (k + 1) * 2 ^ m, by omega⟩
        have hi : i < 2 ^ m := by omega
        simp only [hq, and_self, ↓reduceIte, Nat.add_sub_cancel_left, mask, hi]
        have hc : 2 ^ m ≤ (k + 1) * 2 ^ m + i ∧ (k + 1) * 2 ^ m + i < (k + 1 + 1) * 2 ^ m :=
          ⟨by nlinarith, by rw [add_mul (k + 1), one_mul]; omega⟩
        rw [hcos (k + 1) _ hsl i hi]; simp only [hc, and_self, ↓reduceIte]
      · simp only [hq, ↓reduceIte]
        congr 1
        apply propext
        rw [add_mul (k + 1), one_mul]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; by_contra h; exact hq ⟨by omega, h2⟩
  rw [inv _ le_rfl]
  simp only [Option.bind_some]
  rw [transform_ntt hL hm _ hw]
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq]
  funext q
  simp only [writeBack, mask, slice, zero_add, Nat.sub_zero]
  rw [show (2 ^ r - 1 + 1) * 2 ^ m = 2 ^ (m + r) by rw [Nat.sub_add_cancel hR, hpow]]
  have hmm : 2 ^ m ≤ 2 ^ (m + r) := Nat.pow_le_pow_right two_pos (Nat.le_add_right m r)
  by_cases hq : q < 2 ^ m
  · have hq' : q < 2 ^ (m + r) := by omega
    simp only [Nat.zero_le, hq, and_self, ↓reduceIte, hq']
    have := hcos 0 (slice (fun i => if 2 ^ m ≤ i ∧ i < 2 ^ (m + r) then E i else x i) 0)
      (fun i hi => by simp [slice, show ¬ 2 ^ m ≤ i by omega]) q hq
    simpa using this
  · simp [hq, show 2 ^ m ≤ q by omega]

/-! ## The padded transform and the encoder -/

omit hL in
/-- The transform's methods, as a backend of the interface defaults. -/
def lchBackend (L : Level F) : Backend F V :=
  ⟨fun w n x s => LchNtt.shifted_ntt_batch L w n x s, fun w n x s => LchNtt.shifted_intt_batch L w n x s,
    fun w n x r => LchNtt.ntt_batch_padded L w n x r⟩

/-- The padded transform of 2^(m+r) rows, the message in the first 2^m, is the additive NTT of the padded message. -/
theorem ntt_batch_padded_eq {m r width : ℕ} (hmr : m + r ≤ 2 ^ L.logBits) (hw : 0 < width)
    (hsmall : L.bytes * (width * 2 ^ m) ≤ DEEP_TILE_BYTES) (x : ℕ → V) :
    LchNtt.ntt_batch_padded L width (2 ^ (m + r)) x r =
      some (mask (m + r) x (ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x))) := by
  unfold LchNtt.ntt_batch_padded
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    show ¬ m + r < r by omega, show ¬ 2 ^ L.logBits < m + r by omega, ↓reduceIte,
    Nat.add_sub_cancel]
  exact transform_cosets_eq hL hmr hw hsmall x

/-- Encoding a message of 2^m rows at rate 2^(-r): its zero-padded coefficients, evaluated on S_(m+r). -/
theorem encode_batch_eq {m r width : ℕ} (hmr : m + r ≤ 2 ^ L.logBits) (hw : 0 < width)
    (hsmall : L.bytes * (width * 2 ^ m) ≤ DEEP_TILE_BYTES) (hr : r < 64)
    (hword : 2 ^ m * width * 2 ^ r < 2 ^ 64) (x : ℕ → V) :
    p3_binary_dft.encoder.mirror.encode_batch (lchBackend L) width (2 ^ m) x r =
      some (mask (m + r) (zeroBelow (2 ^ m) x) (ntt L.cantor (m + r) 0 (zeroBelow (2 ^ m) x))) := by
  unfold p3_binary_dft.encoder.mirror.encode_batch padded_len
  rw [Plonky3Lean.Proofs.Commit.paddedLen_eq]
  simp only [hr, hword, and_self, ↓reduceIte]
  have hh : heightOf (2 ^ m * width * 2 ^ r) width = 2 ^ (m + r) := by
    simp only [heightOf, show width ≠ 0 by omega, ↓reduceIte]
    rw [show 2 ^ m * width * 2 ^ r = 2 ^ (m + r) * width by ring, Nat.mul_div_cancel _ hw]
  simp only [Option.bind_eq_bind, Option.bind_some, hh, lchBackend]
  rw [ntt_batch_padded_eq hL hmr hw hsmall]
  have : zeroBelow (2 ^ m) (zeroBelow (2 ^ m) x) = zeroBelow (2 ^ m) x := by
    funext k; simp only [zeroBelow]; split_ifs <;> rfl
  rw [this]

/-- A padding past the height, or a domain wider than the level, panics. -/
theorem ntt_batch_padded_panics {l r width : ℕ} (h : l < r ∨ 2 ^ L.logBits < l) (x : ℕ → V) :
    LchNtt.ntt_batch_padded L width (2 ^ l) x r = none := by
  unfold LchNtt.ntt_batch_padded
  rcases h with h | h <;> simp [log2Strict_pow, h]

omit hL in
/-- A height that is not a power of two panics. -/
theorem ntt_batch_padded_panics_height {n r width : ℕ} (hn : ∀ k, n ≠ 2 ^ k) (x : ℕ → V) :
    LchNtt.ntt_batch_padded L width n x r = none := by
  simp [LchNtt.ntt_batch_padded, log2Strict_eq_none hn]

omit hL in
/-- A domain wider than the level panics, and so does a height that is not a power of two. -/
theorem transform_panics (inverse : Bool) {n width : ℕ} (shift : F)
    (h : (∀ k, n ≠ 2 ^ k) ∨ (∃ l, n = 2 ^ l ∧ 2 ^ L.logBits < l) ∨ width = 0) (x : ℕ → V) :
    transform L inverse width n shift x = none := by
  unfold transform
  rcases h with h | ⟨l, rfl, h⟩ | h
  · by_cases hw : width = 0 <;> simp [hw, log2Strict_eq_none h]
  · by_cases hw : width = 0 <;> simp [hw, log2Strict_pow, h]
  · simp [h]

end Plonky3Lean.Proofs.BinaryDft
