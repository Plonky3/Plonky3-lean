module

public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# The naive transform, the trait's default methods and the radix-2 DIT backend
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- A transcription returns rows that agree with spec on the first n rows. -/
def Computes (o : Option (ℕ → V)) (n : ℕ) (spec : ℕ → V) : Prop :=
  ∃ y, o = some y ∧ ∀ i < n, y i = spec i

omit [DecidableEq K] in
theorem dft_congr (ω : K) (n : ℕ) {x x' : ℕ → V} (h : ∀ j < n, x j = x' j) (i : ℕ) :
    dft ω n x i = dft ω n x' i := by
  unfold dft; exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

omit [DecidableEq K] in
theorem idft_congr (ω : K) (n : ℕ) {x x' : ℕ → V} (h : ∀ j < n, x j = x' j) (i : ℕ) :
    idft ω n x i = idft ω n x' i := by
  unfold idft; congr 1; exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

omit [DecidableEq K] in
theorem cosetDft_congr (s ω : K) (n : ℕ) {x x' : ℕ → V} (h : ∀ j < n, x j = x' j) (i : ℕ) :
    cosetDft s ω n x i = cosetDft s ω n x' i := by
  unfold cosetDft; exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

/-- Two operations that agree on every block and pair below the layer's size give the same layer. -/
theorem layer_op_congr {W : Type _} {op op' : ℕ → ℕ → W → W → W × W} {m nb : ℕ}
    (h : ∀ b < nb, ∀ s < m, op b s = op' b s) (x : ℕ → W) : layer op m nb x = layer op' m nb x := by
  funext i
  unfold layer
  split_ifs with hi hr
  · have hm : 0 < 2 * m := by omega
    rw [h _ (Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)) _ hr]
  · have hm : 0 < 2 * m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hi
      · omega
    have := Nat.mod_lt i hm
    rw [h _ (Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)) _ (by omega)]
  · rfl

omit [DecidableEq K] in
theorem twiddleFree_eq_dit : (p3_dft.butterflies.mirror.TwiddleFreeButterfly.apply : V → V → V × V) =
    dit (1 : K) := by
  funext a b; simp [p3_dft.butterflies.mirror.TwiddleFreeButterfly.apply, dit]

omit [DecidableEq K] in
theorem twiddleFree_eq_dif : (p3_dft.butterflies.mirror.TwiddleFreeButterfly.apply : V → V → V × V) =
    dif (1 : K) := by
  funext a b; simp [p3_dft.butterflies.mirror.TwiddleFreeButterfly.apply, dif]

omit [DecidableEq K] in
theorem ditButterfly_eq (t : K) : (p3_dft.butterflies.mirror.DitButterfly.apply t : V → V → V × V) =
    dit t := rfl

omit [DecidableEq K] in
theorem difButterfly_eq (t : K) : (p3_dft.butterflies.mirror.DifButterfly.apply t : V → V → V × V) =
    dif t := rfl

/-- The decimation-in-time network reads only the first 2^k rows. -/
theorem ditNet_congr (ω : K) (k : ℕ) {x x' : ℕ → V} (h : ∀ p < 2 ^ k, x p = x' p) :
    ∀ L ≤ k, ∀ i < 2 ^ k, ditNet ω k L x i = ditNet ω k L x' i := by
  intro L
  induction L with
  | zero => intro _ i hi; exact h i hi
  | succ L ih =>
    intro hL i hi
    have hsz : 2 ^ (k - 1 - L) * (2 * 2 ^ L) = 2 ^ k := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    simp only [ditNet, ditLayer]
    exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (hsz ▸ hi)

/-- The decimation-in-frequency network reads only the first 2^k rows. -/
theorem difNet_congr (ω : K) (k : ℕ) {x x' : ℕ → V} (h : ∀ p < 2 ^ k, x p = x' p) :
    ∀ c ≤ k, ∀ i < 2 ^ k, difNet ω k c x i = difNet ω k c x' i := by
  intro c
  induction c with
  | zero => intro _ i hi; exact h i hi
  | succ c ih =>
    intro hc i hi
    have hsz : 2 ^ c * (2 * 2 ^ (k - 1 - c)) = 2 ^ k := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    simp only [difNet, difLayer]
    exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (hsz ▸ hi)

/-! ## The naive transform -/

omit [DecidableEq K] in
theorem naive_inner (x : ℕ → V) (point : K) (r : ℕ) (res : ℕ → V) (n : ℕ) :
    (List.range n).foldl (fun res src_r => fun i => if i = r then res i + (point ^ src_r) • x src_r
      else res i) res = fun i => if i = r then res i + ∑ s ∈ range n, (point ^ s) • x s else res i := by
  induction n with
  | zero => funext i; simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext i
    simp only [List.foldl_cons, List.foldl_nil, sum_range_succ]
    split_ifs <;> simp [add_assoc]

omit [DecidableEq K] in
theorem naive_outer (x : ℕ → V) (g : K) (h n : ℕ) :
    (List.range n).foldl (fun res res_r =>
      (List.range h).foldl (fun res src_r =>
        fun i => if i = res_r then res i + ((g ^ res_r) ^ src_r) • x src_r else res i) res)
      (fun _ => 0) = fun i => if i < n then ∑ s ∈ range h, ((g ^ i) ^ s) • x s else 0 := by
  induction n with
  | zero => funext i; simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [naive_inner]
    funext i
    by_cases hi : i = n
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      by_cases hin : i < n
      · simp [hin, show i < n + 1 by omega]
      · simp [hin, show ¬ i < n + 1 by omega]

/-- The naive transform computes the transform at the generator of order 2^k. -/
theorem naive_dft_batch (G : Gen K) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (p3_dft.naive.mirror.NaiveDft.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) := by
  have : p3_dft.naive.mirror.NaiveDft.dft_batch G (2 ^ k) x = some (fun i =>
      if i < 2 ^ k then ∑ s ∈ range (2 ^ k), ((G.gen k ^ i) ^ s) • x s else 0) := by
    simp only [p3_dft.naive.mirror.NaiveDft.dft_batch, log2Strict_pow, Option.bind_some,
      gen_get_of_le G hk, Option.map_some, naive_outer]
  refine ⟨_, this, fun i hi => ?_⟩
  simp only [hi, ↓reduceIte, dft]
  exact sum_congr rfl fun s _ => by rw [← pow_mul]

theorem naive_dft_batch_not_pow (G : Gen K) {h : ℕ} (hh : ∀ k, h ≠ 2 ^ k) (x : ℕ → V) :
    p3_dft.naive.mirror.NaiveDft.dft_batch G h x = none := by
  simp [p3_dft.naive.mirror.NaiveDft.dft_batch, log2Strict_eq_none hh]

theorem naive_dft_batch_too_big (G : Gen K) {k : ℕ} (hk : G.adicity < k) (x : ℕ → V) :
    p3_dft.naive.mirror.NaiveDft.dft_batch G (2 ^ k) x = none := by
  simp [p3_dft.naive.mirror.NaiveDft.dft_batch, log2Strict_pow, gen_get_of_lt G hk]

/-! ## The default methods -/

omit [DecidableEq K] [AddCommGroup V] [Module K V] in
/-- Swapping row r with row h - r for 0 < r < m. -/
theorem swaps_apply {W : Type _} (d : ℕ → W) (h : ℕ) :
    ∀ m, 2 * m + 1 ≤ h → ∀ r < h,
      (List.range' 1 m).foldl (fun acc row => swapRows row (h - row) acc) d r =
        if (1 ≤ r ∧ r ≤ m) ∨ (h - m ≤ r ∧ r + 1 ≤ h ∧ 1 ≤ m) then d (h - r) else d r := by
  intro m
  induction m with
  | zero =>
    intro _ r hr
    simp only [List.range'_zero, List.foldl_nil]
    rw [ite_eq_right_iff.mpr (fun h => by omega)]
  | succ m ih =>
    intro hm r hr
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, swapRows, one_mul]
    split_ifs with h1 h2 <;>
      (rw [ih (by omega) _ (by omega)]; split_ifs <;> first | rfl | omega | (congr 1; omega))

/-- The default inverse computes the inverse transform, given a backend that computes the transform. -/
theorem traits_idft_batch {ω : K} {k : ℕ} (hω : ω ^ 2 ^ k = 1)
    {dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft ω (2 ^ k) x)) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.idft_batch (K := K) dft_batch (2 ^ k) x) (2 ^ k)
      (idft ω (2 ^ k) x) := by
  obtain ⟨d, hd1, hd2⟩ := hd x
  refine ⟨_, by simp [p3_dft.traits.mirror.idft_batch, hd1, divide_by_height_pow]; rfl,
    fun r hr => ?_⟩
  have hpos : 0 < 2 ^ k := by positivity
  have hpar : 2 ^ k = 1 ∨ 2 ^ k % 2 = 0 := by
    rcases k with _ | k
    · simp
    · right; simp [pow_succ]
  have key : scaleRows ((2 : K) ^ k)⁻¹ d ((2 ^ k - r) % 2 ^ k) = idft ω (2 ^ k) x r := by
    rw [scaleRows, hd2 _ (Nat.mod_lt _ hpos), dft_neg_index hω x hr, idft]
    congr 1; push_cast; ring
  rw [← key]
  generalize 2 ^ k = H at hr hpos hpar ⊢
  rw [swaps_apply _ _ _ (by omega) r hr]
  split_ifs with hc
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega)]
      congr 1; omega

/-- The default coset transform computes the coset transform. -/
theorem traits_coset_dft_batch {ω : K} {k : ℕ} {dft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft ω (2 ^ k) x)) {w : ℕ} (s : K)
    (hw : w ≠ 0 ∨ s = 1) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_dft_batch dft_batch w (2 ^ k) x s) (2 ^ k)
      (cosetDft s ω (2 ^ k) x) := by
  obtain ⟨d, hd1, hd2⟩ := hd (fun i => if i < 2 ^ k then (s ^ i) • x i else x i)
  refine ⟨d, by simp [p3_dft.traits.mirror.coset_dft_batch, coset_shift_cols_eq s x hw, hd1],
    fun i hi => ?_⟩
  rw [hd2 i hi, cosetDft_eq]
  exact dft_congr _ _ (fun j hj => by simp [hj]) _

/-- The default inverse coset transform computes the inverse coset transform, for a nonzero shift. -/
theorem traits_coset_idft_batch {ω : K} {k : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x)) {w : ℕ} {s : K}
    (hs : s ≠ 0) (hw : w ≠ 0 ∨ s = 1) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_idft_batch idft_batch w (2 ^ k) x s) (2 ^ k)
      (cosetIdft s ω (2 ^ k) x) := by
  obtain ⟨c, hc1, hc2⟩ := hi x
  have hw' : w ≠ 0 ∨ s⁻¹ = 1 := hw.imp id (fun h => by simp [h])
  refine ⟨_, by simp [p3_dft.traits.mirror.coset_idft_batch, hc1, inverse, hs,
    coset_shift_cols_eq s⁻¹ c hw']; rfl, fun i hi => ?_⟩
  simp [hi, cosetIdft, hc2 i hi]

/-- The default inverse coset transform panics at a zero shift. -/
theorem traits_coset_idft_batch_zero {k : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    {ω : K} (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x)) (w : ℕ)
    (x : ℕ → V) :
    p3_dft.traits.mirror.coset_idft_batch idft_batch w (2 ^ k) x (0 : K) = none := by
  obtain ⟨c, hc1, -⟩ := hi x
  simp [p3_dft.traits.mirror.coset_idft_batch, hc1, inverse]

/-- The zero-padded coefficients of the inverse transform: the coefficient vector of the interpolant. -/
def padCoeffs (ω : K) (n : ℕ) (x : ℕ → V) : ℕ → V := fun j => if j < n then idft ω n x j else 0

/-- The default extension evaluates the padded coefficients on the coset of the larger subgroup. -/
theorem traits_coset_lde_batch {ω g : K} {k a w : ℕ} {idft_batch : ℕ → (ℕ → V) → Option (ℕ → V)}
    {coset_dft_batch : ℕ → (ℕ → V) → K → Option (ℕ → V)} (s : K)
    (hi : ∀ x, Computes (idft_batch (2 ^ k) x) (2 ^ k) (idft ω (2 ^ k) x))
    (hc : ∀ x, Computes (coset_dft_batch (2 ^ (k + a)) x s) (2 ^ (k + a)) (cosetDft s g (2 ^ (k + a)) x))
    (ha : a < 64) (hlen : 2 ^ k * w * 2 ^ a < 2 ^ 64) (x : ℕ → V) :
    Computes (p3_dft.traits.mirror.coset_lde_batch_with_transform idft_batch coset_dft_batch w
      (2 ^ k) a s id x) (2 ^ (k + a)) (cosetDft s g (2 ^ (k + a)) (padCoeffs ω (2 ^ k) x)) := by
  obtain ⟨c, hc1, hc2⟩ := hi x
  obtain ⟨y, hy1, hy2⟩ := hc (fun i => if i < 2 ^ k then c i else 0)
  refine ⟨y, ?_, fun i hi' => ?_⟩
  · simp only [p3_dft.traits.mirror.coset_lde_batch_with_transform, hc1, Option.bind_eq_bind,
      Option.bind_some, id, ha, hlen, and_self, ↓reduceIte]
    rw [← pow_add]; exact hy1
  · rw [hy2 i hi']
    exact cosetDft_congr _ _ _ (fun j _ => by simp [padCoeffs]; split_ifs <;> simp [hc2 j, *]) _

/-- A method on an algebra over the field is the base-field method, read through the coordinates. -/
theorem via_base_spec {W U : Type _} [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (e : W ≃ₗ[K] U) {base : (ℕ → U) → Option (ℕ → U)} {n : ℕ} {spec : (ℕ → W) → ℕ → W}
    (hb : ∀ x : ℕ → W, Computes (base (e ∘ x)) n (e ∘ spec x)) (x : ℕ → W) :
    Computes (p3_dft.traits.mirror.via_base e e.symm base x) n (spec x) := by
  obtain ⟨y, hy1, hy2⟩ := hb x
  refine ⟨_, by simp [p3_dft.traits.mirror.via_base, hy1]; rfl, fun i hi => ?_⟩
  simp [hy2 i hi]

/-! ## Radix-2 decimation in time -/

open p3_dft.radix_2_dit.mirror in
theorem dit_layer_eq (g : K) {k l : ℕ} (hl : l < k) (x : ℕ → V) :
    dit_layer (2 ^ k) l (powersList g (2 ^ k / 2)) x =
      some (ditLayer (2 ^ l) (2 ^ (k - 1 - l)) (fun _ s => g ^ (s * 2 ^ (k - 1 - l))) x) := by
  have hnb : 2 ^ k / (2 * 2 ^ l) = 2 ^ (k - 1 - l) := by
    rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring, Nat.pow_div (by omega) (by norm_num)]
    congr 1; omega
  simp only [dit_layer, log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    show l + 1 ≤ k by omega, ↓reduceIte, hnb]
  rw [pairLoop_blocks _ _ (by positivity)]
  congr 1
  apply layer_op_congr
  intro b _ s hs
  split_ifs with h0
  · subst h0; simp only [zero_mul, pow_zero]; exact twiddleFree_eq_dit
  · have h1 : s * 2 ^ (k - 1 - l) < 2 ^ k / 2 := by
      have : s * 2 ^ (k - 1 - l) < 2 ^ l * 2 ^ (k - 1 - l) :=
        Nat.mul_lt_mul_of_pos_right hs (by positivity)
      rw [← pow_add, show l + (k - 1 - l) = k - 1 by omega] at this
      have h2 : 2 ^ k / 2 = 2 ^ (k - 1) :=
        Nat.div_eq_of_eq_mul_left (by norm_num) (by rw [← pow_succ]; congr 1; omega)
      rwa [h2]
    rw [getD_powersList _ h1, ditButterfly_eq]

theorem foldlM_dit_layer (g : K) (k : ℕ) (x0 : ℕ → V) :
    ∀ n ≤ k, (List.range n).foldlM (fun acc layer =>
      p3_dft.radix_2_dit.mirror.dit_layer (2 ^ k) layer (powersList g (2 ^ k / 2)) acc) x0 =
      some (ditNet g k n x0) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldlM_append, ih (by omega)]
    simp [dit_layer_eq g (show n < k by omega), ditNet]

/-- The radix-2 decimation-in-time backend computes the transform. -/
theorem radix2Dit_dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity)
    (x : ℕ → V) :
    Computes (p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch G (2 ^ k) x) (2 ^ k)
      (dft (G.gen k) (2 ^ k) x) := by
  refine ⟨ditNet (G.gen k) k k (revRows k x), ?_, fun i hi => ?_⟩
  · simp only [p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch, log2Strict_pow,
      p3_dft.radix_2_dit.mirror.Radix2Dit.get_or_compute_twiddles, gen_get_of_le G hk,
      Option.bind_eq_bind, Option.bind_some, Option.map_some]
    exact foldlM_dit_layer _ _ _ k le_rfl
  · rw [ditNet_congr _ k (x' := bitRevVec (rev k) x) (fun p hp => by
      rw [revRows_apply k x hp, bitRevVec]) k le_rfl i hi]
    exact ditNet_eq_dft (hG k hk) x hi

theorem radix2Dit_dft_batch_not_pow (G : Gen K) {h : ℕ} (hh : ∀ k, h ≠ 2 ^ k) (x : ℕ → V) :
    p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch G h x = none := by
  simp [p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch, log2Strict_eq_none hh]

theorem radix2Dit_dft_batch_too_big (G : Gen K) {k : ℕ} (hk : G.adicity < k) (x : ℕ → V) :
    p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch G (2 ^ k) x = none := by
  simp [p3_dft.radix_2_dit.mirror.Radix2Dit.dft_batch, log2Strict_pow,
    p3_dft.radix_2_dit.mirror.Radix2Dit.get_or_compute_twiddles, gen_get_of_lt G hk]

/-- The radix-2 decimation-in-time extension with a transform.

The transform sees the coefficients in natural order, coefficient j at row j.

The result evaluates the transformed coefficients, padded with zeros, on the coset shift times the
subgroup of order 2^(k+a). -/
theorem radix2Dit_coset_lde_batch_with_transform (G : Gen K) (hG : GenValid G) {k a w : ℕ}
    (hka : k + a ≤ G.adicity) (shift : K) (hw : w ≠ 0 ∨ shift = 1) (ha : a < 64)
    (hlen : w * 2 ^ (k + a) < 2 ^ 64) (T : (ℕ → V) → ℕ → V) (x : ℕ → V) :
    ∃ c : ℕ → V, (∀ i < 2 ^ k, c i = idft (G.gen k) (2 ^ k) x i) ∧
    Computes (p3_dft.radix_2_dit.mirror.Radix2Dit.coset_lde_batch_with_transform G w (2 ^ k) a
      shift T x) (2 ^ (k + a))
      (cosetDft shift (G.gen (k + a)) (2 ^ (k + a)) (fun j => if j < 2 ^ k then T c j else 0)) := by
  have hk : k ≤ G.adicity := by omega
  obtain ⟨c, hc1, hc2⟩ := traits_idft_batch (hG k hk).pow_eq_one
    (radix2Dit_dft_batch G hG hk) x
  refine ⟨c, hc2, ?_⟩
  obtain ⟨z, hz1, hz2⟩ := radix2Dit_dft_batch G hG hka
    (fun i => if i < 2 ^ k then (fun i => if i < 2 ^ k then (shift ^ i) • T c i else T c i) i else 0)
  refine ⟨z, ?_, fun i hi => ?_⟩
  · simp only [p3_dft.radix_2_dit.mirror.Radix2Dit.coset_lde_batch_with_transform, hc1,
      Option.bind_eq_bind, Option.bind_some, coset_shift_cols_eq shift _ hw, ← pow_add]
    simp only [ha, hlen, true_and, ↓reduceIte]
    exact hz1
  · rw [hz2 i hi, cosetDft_eq]
    exact dft_congr _ _ (fun j _ => by split_ifs <;> simp_all) _

end Plonky3Lean.Proofs.Dft
