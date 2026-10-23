module

public import Plonky3Lean.Proofs.Dft.Basic

@[expose] public section

/-!
# The Bowers backend

The G network runs decimation-in-frequency layers on bit-reversed input, with bit-reversed twiddles.

It is the Gentleman-Sande network conjugated by the bit reversal, so it returns the transform in natural order.

The G^T network is the Cooley-Tukey network conjugated the same way, so it returns the transform bit-reversed.

The networks are those of Bowers et al., Improved Twiddle Access for Fast Fourier Transforms (2009).
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft p3_dft.radix_2_bowers.mirror

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

theorem rev_zero (n : ℕ) : rev n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Plonky3Lean.Spec.Matrix.bitRev, ih]

theorem rev_involutive {n i : ℕ} (hi : i < 2 ^ n) : rev n (rev n i) = i :=
  Plonky3Lean.Proofs.Matrix.bitRev_bitRev hi

/-- Entry b of the bit-reversed half table, for b below 2^(n-1-l), is g^(rev_(n-1-l)(b) 2^l). -/
theorem getD_bowers_table (g : K) {n l b : ℕ} (hl : l < n) (hb : b < 2 ^ (n - 1 - l)) :
    (revIndex (2 ^ n / 2) (powersList g (2 ^ n / 2))).getD b 0 = g ^ (rev (n - 1 - l) b * 2 ^ l) := by
  have h2 : 2 ^ n / 2 = 2 ^ (n - 1) :=
    Nat.div_eq_of_eq_mul_left (by norm_num) (by rw [← pow_succ]; congr 1; omega)
  have hb' : b < 2 ^ (n - 1) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [h2, getD_revIndex _ hb', getD_powersList _ (Plonky3Lean.Proofs.Matrix.bitRev_lt _ _)]
  congr 1
  have := Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt (k := l) hb
  rwa [show n - 1 - l + l = n - 1 by omega] at this

theorem bowers_layer_eq (g : K) {n l : ℕ} (hl : l < n)
    (fly : K → V → V → V × V) (hfly : fly 1 = p3_dft.butterflies.mirror.TwiddleFreeButterfly.apply)
    (x : ℕ → V) :
    butterfly_layer (2 ^ n) (2 ^ l)
      (fun b => fly ((revIndex (2 ^ n / 2) (powersList g (2 ^ n / 2))).getD b 0)) x =
    layer (fun σ _ => fly (g ^ (rev (n - 1 - l) σ * 2 ^ l))) (2 ^ l) (2 ^ (n - 1 - l)) x := by
  have hnb : 2 ^ n / (2 * 2 ^ l) = 2 ^ (n - 1 - l) := by
    rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring, Nat.pow_div (by omega) (by norm_num)]
    congr 1; omega
  unfold butterfly_layer
  rw [hnb, pairLoop_blocks _ _ (by positivity)]
  apply layer_op_congr
  intro b hb s _
  split_ifs with h0
  · subst h0; rw [rev_zero, zero_mul, pow_zero, hfly]
  · dsimp only; rw [getD_bowers_table g hl hb]

/-- The G network on 2^n rows returns the transform of its input read in bit-reversed order. -/
theorem bowers_g_spec (G : Gen K) (hG : GenValid G) {n : ℕ} (hn : n ≤ G.adicity) (y : ℕ → V) :
    Computes (bowers_g G (2 ^ n) y) (2 ^ n) (dft (G.gen n) (2 ^ n) (fun j => y (rev n j))) := by
  set ω := G.gen n
  have hω := hG n hn
  -- the network after c layers, against the Gentleman-Sande network
  have key : ∀ c ≤ n, ∀ i < 2 ^ n,
      (List.range c).foldl (fun acc l => butterfly_layer (2 ^ n) (2 ^ l)
        (fun b => dif ((revIndex (2 ^ n / 2) (powersList ω (2 ^ n / 2))).getD b 0)) acc) y i =
      difNet ω n c (fun j => y (rev n j)) (rev n i) := by
    intro c
    induction c with
    | zero => intro _ i hi; simp [difNet, rev_involutive hi]
    | succ c ih =>
      intro hc i hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        bowers_layer_eq ω (show c < n by omega) _ twiddleFree_eq_dif.symm]
      obtain ⟨L, hL⟩ : ∃ L, n = L + 1 + c := ⟨n - 1 - c, by omega⟩
      have hLn : n - 1 - c = L := by omega
      simp only [difNet, difLayer, hLn]
      have hi' : i < 2 ^ (L + 1 + c) := hL ▸ hi
      have := conj_layer (fun t : K => (dif t : V → V → V × V)) (fun s => ω ^ (s * 2 ^ c)) L c
        (difNet ω n c (fun j => y (rev n j))) hi'
      rw [← hL] at this
      rw [this]
      have hsz : 2 ^ L * (2 * 2 ^ c) = 2 ^ n := by rw [hL]; ring
      exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (by rw [hsz]; exact hi)
  refine ⟨_, by simp only [bowers_g, log2Strict_pow, gen_get_of_le G hn, Option.bind_eq_bind,
    Option.bind_some, difButterfly_eq]; rfl, fun i hi => ?_⟩
  rw [key n le_rfl i hi, difNet_eq_dft hω _ (Plonky3Lean.Proofs.Matrix.bitRev_lt n i),
    rev_involutive hi]

theorem range_reverse_eq (k : ℕ) : (List.range k).reverse = (List.range k).map (fun u => k - 1 - u) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_range, List.getElem_map, List.length_range]

/-- The G^T network on 2^n rows returns the transform at the inverse generator, in bit-reversed order. -/
theorem bowers_g_t_spec (G : Gen K) (hG : GenValid G) {n : ℕ} (hn : n ≤ G.adicity) (y : ℕ → V) :
    Computes (bowers_g_t G (2 ^ n) y) (2 ^ n) (fun i => dft (G.gen n)⁻¹ (2 ^ n) y (rev n i)) := by
  set ω := (G.gen n)⁻¹
  have hω : IsPrimitiveRoot ω (2 ^ n) := (hG n hn).inv
  have key : ∀ t ≤ n, ∀ i < 2 ^ n,
      ((List.range t).map (fun u => n - 1 - u)).foldl (fun acc l => butterfly_layer (2 ^ n) (2 ^ l)
        (fun b => dit ((revIndex (2 ^ n / 2) (powersList ω (2 ^ n / 2))).getD b 0)) acc) y i =
      ditNet ω n t (fun j => y (rev n j)) (rev n i) := by
    intro t
    induction t with
    | zero => intro _ i hi; simp [ditNet, rev_involutive hi]
    | succ t ih =>
      intro ht i hi
      rw [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil,
        bowers_layer_eq ω (show n - 1 - t < n by omega) _ twiddleFree_eq_dit.symm]
      obtain ⟨j, hj⟩ : ∃ j, n = t + 1 + j := ⟨n - 1 - t, by omega⟩
      have e2 : n - 1 - t = j := by omega
      simp only [ditNet, ditLayer, e2]
      rw [show n - 1 - j = t by omega]
      have hi' : i < 2 ^ (t + 1 + j) := hj ▸ hi
      have := conj_layer (fun c : K => (dit c : V → V → V × V)) (fun s => ω ^ (s * 2 ^ j)) t j
        (ditNet ω n t (fun j => y (rev n j))) hi'
      rw [← hj] at this
      rw [this]
      have hsz : 2 ^ t * (2 * 2 ^ j) = 2 ^ n := by rw [hj]; ring
      exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (by rw [hsz]; exact hi)
  refine ⟨_, by simp only [bowers_g_t, log2Strict_pow, gen_get_of_le G hn, Option.bind_eq_bind,
    Option.bind_some, ditButterfly_eq]; rfl, fun i hi => ?_⟩
  simp only []
  rw [range_reverse_eq, key n le_rfl i hi]
  have := ditNet_eq_dft hω y (Plonky3Lean.Proofs.Matrix.bitRev_lt n i)
  rw [← this]
  rfl

/-- The Bowers forward transform computes the transform. -/
theorem bowers_dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2Bowers.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) := by
  obtain ⟨y, hy1, hy2⟩ := bowers_g_spec G hG hk (revRows k x)
  refine ⟨y, by simp [Radix2Bowers.dft_batch, log2Strict_pow, hy1], fun i hi => ?_⟩
  rw [hy2 i hi]
  exact dft_congr _ _ (fun j hj => by
    rw [revRows_apply k x (Plonky3Lean.Proofs.Matrix.bitRev_lt k j), rev_involutive hj]) _

/-- The Bowers inverse computes the inverse transform. -/
theorem bowers_idft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2Bowers.idft_batch G (2 ^ k) x) (2 ^ k) (idft (G.gen k) (2 ^ k) x) := by
  obtain ⟨y, hy1, hy2⟩ := bowers_g_t_spec G hG hk x
  refine ⟨_, by simp only [Radix2Bowers.idft_batch, hy1, divide_by_height_pow, log2Strict_pow,
    Option.bind_eq_bind, Option.bind_some]; rfl, fun i hi => ?_⟩
  rw [revRows_apply k _ hi, scaleRows, hy2 _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k i)]
  dsimp only
  rw [rev_involutive hi, idft]
  congr 1
  push_cast; ring

/-- The coefficients the Bowers extensions pad: G^T of the input, scaled, read back in natural order. -/
theorem bowers_coeffs (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V)
    {y : ℕ → V} (hy : bowers_g_t G (2 ^ k) x = some y) {j : ℕ} (hj : j < 2 ^ k) :
    ((2 : K) ^ k)⁻¹ • y (rev k j) = idft (G.gen k) (2 ^ k) x j := by
  obtain ⟨y', hy1, hy2⟩ := bowers_g_t_spec G hG hk x
  rw [hy1] at hy; cases hy
  rw [hy2 _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k j)]
  dsimp only
  rw [rev_involutive hj, idft]
  congr 1; push_cast; ring

/-- Bit-reversed zero padding of bit-reversed coefficients, read in bit-reversed order, is the
coefficients padded with zeros. -/
theorem zero_pad_rev {k a : ℕ} (c b : ℕ → V) (hb : ∀ i < 2 ^ k, b i = c (rev k i)) {j : ℕ}
    (hj : j < 2 ^ (k + a)) :
    bit_reversed_zero_pad (2 ^ k) a b (rev (k + a) j) = if j < 2 ^ k then c j else 0 := by
  have hrj : rev (k + a) j < 2 ^ (k + a) := Plonky3Lean.Proofs.Matrix.bitRev_lt _ _
  have hiff := Plonky3Lean.Proofs.Matrix.bitRev_lt_iff_dvd (n := k) (k := a) hrj
  rw [rev_involutive hj] at hiff
  unfold bit_reversed_zero_pad
  by_cases ha : a = 0
  · subst ha
    simp only [↓reduceIte, add_zero] at hj ⊢
    rw [ite_eq_left hj, hb _ (Plonky3Lean.Proofs.Matrix.bitRev_lt _ _), rev_involutive hj]
  rw [ite_eq_right ha]
  by_cases hjk : j < 2 ^ k
  · have hd : 2 ^ a ∣ rev (k + a) j := hiff.mp hjk
    have hval : rev (k + a) j / 2 ^ a = rev k j := by
      rw [Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt hjk, Nat.mul_div_cancel _ (by positivity)]
    have hlt : rev k j < 2 ^ k := Plonky3Lean.Proofs.Matrix.bitRev_lt _ _
    rw [ite_eq_left ⟨Nat.mod_eq_zero_of_dvd hd, by rw [hval]; exact hlt⟩, hval, hb _ hlt,
      rev_involutive hjk, ite_eq_left hjk]
  · rw [ite_eq_right hjk, ite_eq_right]
    rintro ⟨hm, -⟩
    exact hjk (hiff.mpr (Nat.dvd_of_mod_eq_zero hm))

/-- The Bowers extension evaluates the padded coefficients on the subgroup of order 2^(k+a). -/
theorem bowers_lde_batch (G : Gen K) (hG : GenValid G) {k a : ℕ} (hka : k + a ≤ G.adicity)
    (x : ℕ → V) :
    Computes (Radix2Bowers.lde_batch G (2 ^ k) a x) (2 ^ (k + a))
      (dft (G.gen (k + a)) (2 ^ (k + a)) (padCoeffs (G.gen k) (2 ^ k) x)) := by
  have hk : k ≤ G.adicity := by omega
  obtain ⟨y, hy1, -⟩ := bowers_g_t_spec G hG hk x
  obtain ⟨z, hz1, hz2⟩ := bowers_g_spec G hG hka
    (bit_reversed_zero_pad (2 ^ k) a (scaleRows ((2 : K) ^ k)⁻¹ y))
  refine ⟨z, ?_, fun i hi => ?_⟩
  · simp only [Radix2Bowers.lde_batch, hy1, divide_by_height_pow, Option.bind_eq_bind,
      Option.bind_some, ← pow_add]
    exact hz1
  · rw [hz2 i hi]
    refine dft_congr _ _ (fun j hj => ?_) _
    rw [zero_pad_rev (idft (G.gen k) (2 ^ k) x) _ (fun i hi => by
      rw [scaleRows, ← bowers_coeffs G hG hk x hy1 (Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
        rev_involutive hi]) hj]
    rfl

/-- The Bowers coset extension evaluates the padded coefficients on the coset shift times the
subgroup of order 2^(k+a). -/
theorem bowers_coset_lde_batch (G : Gen K) (hG : GenValid G) {k a : ℕ} (hka : k + a ≤ G.adicity)
    (shift : K) (x : ℕ → V) :
    Computes (Radix2Bowers.coset_lde_batch G (2 ^ k) a shift x) (2 ^ (k + a))
      (cosetDft shift (G.gen (k + a)) (2 ^ (k + a)) (padCoeffs (G.gen k) (2 ^ k) x)) := by
  have hk : k ≤ G.adicity := by omega
  obtain ⟨y, hy1, -⟩ := bowers_g_t_spec G hG hk x
  set b : ℕ → V := fun i => (revIndex (2 ^ k) (shiftedPowersList shift ((2 : K) ^ k)⁻¹ (2 ^ k))).getD i 0 • y i
  obtain ⟨z, hz1, hz2⟩ := bowers_g_spec G hG hka (bit_reversed_zero_pad (2 ^ k) a b)
  refine ⟨z, ?_, fun i hi => ?_⟩
  · simp only [Radix2Bowers.coset_lde_batch, hy1, log2Strict_pow, Option.bind_eq_bind,
      Option.bind_some, ← pow_add]
    exact hz1
  · rw [hz2 i hi, cosetDft_eq]
    refine dft_congr _ _ (fun j hj => ?_) _
    rw [zero_pad_rev (fun j => shift ^ j • idft (G.gen k) (2 ^ k) x j) _ (fun i hi => by
      simp only [b]
      rw [getD_revIndex _ hi, getD_shiftedPowersList _ _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
        mul_smul, ← bowers_coeffs G hG hk x hy1 (Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
        rev_involutive hi, smul_comm]) hj]
    simp only [padCoeffs]
    split_ifs <;> simp

/-- The Bowers coset extension with a transform: the transform sees the scaled coefficients in
bit-reversed order, coefficient j at row rev(j), as the bit-reversed layout promises. -/
theorem bowers_coset_lde_batch_with_transform (G : Gen K) (hG : GenValid G) {k a : ℕ}
    (hka : k + a ≤ G.adicity) (shift : K) (T : (ℕ → V) → ℕ → V) (x : ℕ → V) :
    ∃ c : ℕ → V, (∀ i < 2 ^ k, c (rev k i) = idft (G.gen k) (2 ^ k) x i) ∧
    Computes (Radix2Bowers.coset_lde_batch_with_transform G (2 ^ k) a shift T x) (2 ^ (k + a))
      (cosetDft shift (G.gen (k + a)) (2 ^ (k + a))
        (fun j => if j < 2 ^ k then T c (rev k j) else 0)) := by
  have hk : k ≤ G.adicity := by omega
  obtain ⟨y, hy1, -⟩ := bowers_g_t_spec G hG hk x
  refine ⟨scaleRows ((2 : K) ^ k)⁻¹ y, fun i hi => ?_, ?_⟩
  · rw [scaleRows, bowers_coeffs G hG hk x hy1 hi]
  set b : ℕ → V := fun i => (revIndex (2 ^ k) (powersList shift (2 ^ k))).getD i 0 •
    T (scaleRows ((2 : K) ^ k)⁻¹ y) i
  obtain ⟨z, hz1, hz2⟩ := bowers_g_spec G hG hka (bit_reversed_zero_pad (2 ^ k) a b)
  refine ⟨z, ?_, fun i hi => ?_⟩
  · simp only [Radix2Bowers.coset_lde_batch_with_transform, hy1, log2Strict_pow,
      Option.bind_eq_bind, Option.bind_some, ← pow_add]
    exact hz1
  · rw [hz2 i hi, cosetDft_eq]
    refine dft_congr _ _ (fun j hj => ?_) _
    rw [zero_pad_rev (fun j => shift ^ j • T (scaleRows ((2 : K) ^ k)⁻¹ y) (rev k j)) _
      (fun i hi => by
        simp only [b]
        rw [getD_revIndex _ hi, getD_powersList _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
          rev_involutive hi]) hj]
    split_ifs <;> simp

end Plonky3Lean.Proofs.Dft
