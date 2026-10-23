module

public import Plonky3Lean.Proofs.Dft.Parallel

@[expose] public section

/-!
# The small-batch backend

Its forward layers are the bit-reversed Cooley-Tukey layers of the parallel backend's second half,
run from the one-block layer down, followed by a bit reversal.

Its inverse is the Bowers G network at the inverse generator, on bit-reversed rows divided by the height.

Its cache may hold tables for a larger size 2^L, built from G_L, so the results need nested generators.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft p3_dft.radix_2_small_batch.mirror

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type} [Field K] [DecidableEq K] {V : Type} [AddCommGroup V] [Module K V]

/-! ## The cache -/

theorem filterMap_of_some {α β : Type _} (l : List α) (f : α → Option β) (g : α → β)
    (h : ∀ a ∈ l, f a = some (g a)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, h a (by simp), ih (fun a ha => h a (by simp [ha]))]
    rfl

theorem stepBy_powers (g : K) {L i : ℕ} (hi : i < L) :
    stepBy (powersList g (2 ^ (L - 1))) (2 ^ i) = powersList (g ^ 2 ^ i) (2 ^ (L - 1 - i)) := by
  have hlen : (2 ^ (L - 1) + 2 ^ i - 1) / 2 ^ i = 2 ^ (L - 1 - i) := by
    have h1 : 2 ^ (L - 1) = 2 ^ (L - 1 - i) * 2 ^ i := by rw [← pow_add]; congr 1; omega
    rw [h1]
    have : 0 < 2 ^ i := by positivity
    rw [show 2 ^ (L - 1 - i) * 2 ^ i + 2 ^ i - 1 = 2 ^ (L - 1 - i) * 2 ^ i + (2 ^ i - 1) by omega,
      Nat.add_comm, Nat.add_mul_div_right _ _ this, Nat.div_eq_of_lt (by omega), zero_add]
  unfold stepBy powersList
  rw [List.length_map, List.length_range, hlen]
  refine filterMap_of_some _ _ _ (fun j hj => ?_)
  · have hj' : j < 2 ^ (L - 1 - i) := List.mem_range.mp hj
    have : j * 2 ^ i < 2 ^ (L - 1) := by
      calc j * 2 ^ i < 2 ^ (L - 1 - i) * 2 ^ i := Nat.mul_lt_mul_of_pos_right hj' (by positivity)
        _ = 2 ^ (L - 1) := by rw [← pow_add]; congr 1; omega
    simp [this, ← pow_mul, mul_comm]

/-- Forward table j of a cache of size 2^L: the first half of the powers of g^(2^j), bit-reversed. -/
abbrev fwTable (g : K) (L j : ℕ) : List K :=
  revIndex (2 ^ (L - 1 - j)) (powersList (g ^ 2 ^ j) (2 ^ (L - 1 - j)))

/-- Inverse table j: the same for the inverse of g^(2^j). -/
abbrev invTable (g : K) (L j : ℕ) : List K :=
  revIndex (2 ^ (L - 1 - j)) (powersList (g ^ 2 ^ j)⁻¹ (2 ^ (L - 1 - j)))

/-- Keeping the one and listing the rest reversed and negated gives the inverse powers, when h^M = -1. -/
theorem inv_list {h : K} {M : ℕ} (hM : 0 < M) (hneg : h ^ M = -1) :
    (1 :: ((powersList h M).tail.reverse.map fun f => -f)) = powersList h⁻¹ M := by
  have h0 : h ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega)] at hneg; exact one_ne_zero (neg_eq_zero.mp hneg.symm)
  apply List.ext_getElem
  · simp [powersList]; omega
  · intro j h1 h2
    rcases j with _ | j
    · simp [powersList]
    · simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_reverse, List.getElem_tail,
        powersList, List.getElem_range, List.length_tail, List.length_map, List.length_range]
      have hj : j + 1 < M := by simpa [powersList] using h2
      rw [inv_pow]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [neg_mul, ← pow_add, show M - 1 - 1 - j + 1 + (j + 1) = M by omega, hneg, neg_neg]

theorem cache_spec (G : Gen K) (hG : GenValid G) {L : ℕ} (hL1 : 1 ≤ L) (hL : L ≤ G.adicity) :
    cache G L = some ((List.range L).map (fwTable (G.gen L) L),
      (List.range L).map (invTable (G.gen L) L)) := by
  have hrt : roots_of_unity_table G (2 ^ L) =
      some ((List.range L).map fun i => powersList (G.gen L ^ 2 ^ i) (2 ^ (L - 1 - i))) := by
    simp only [roots_of_unity_table, log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
      show L ≠ 0 by omega, ↓reduceIte, gen_get_of_le G hL]
    congr 1
    refine List.map_congr_left (fun i hi => stepBy_powers _ (List.mem_range.mp hi))
  simp only [cache, show L ≠ 0 by omega, ↓reduceIte, hrt, Option.map_some, List.map_map]
  congr 2
  · refine List.map_congr_left (fun i _ => ?_)
    simp [Function.comp, powersList, fwTable]
  · refine List.map_congr_left (fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    have hω := hG L hL
    have hneg : (G.gen L ^ 2 ^ i) ^ 2 ^ (L - 1 - i) = -1 := by
      rw [← pow_mul, ← pow_add, show i + (L - 1 - i) = L - 1 by omega]
      exact neg_one_of_primitive (by rw [show L - 1 + 1 = L by omega]; exact hω)
    simp only [Function.comp]
    rw [inv_list (by positivity) hneg]
    simp [powersList, inv_pow, invTable]

/-- The last k tables of a cache of size 2^L, with nested generators, are the tables of size 2^k. -/
theorem drop_tables {k L : ℕ} (hkL : k ≤ L) (tbl : ℕ → ℕ → List K) (htbl : ∀ j, tbl L (L - k + j) = tbl k j) :
    ((List.range L).map (tbl L)).drop (L - k) = (List.range k).map (tbl k) := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
    exact htbl j

theorem fwTable_nested (G : Gen K) (hN : GenNested G) {k L j : ℕ} (hkL : k ≤ L)
    (hL : L ≤ G.adicity) : fwTable (G.gen L) L (L - k + j) = fwTable (G.gen k) k j := by
  have h1 : G.gen L ^ 2 ^ (L - k + j) = G.gen k ^ 2 ^ j := by
    rw [pow_add, pow_mul, show L = k + (L - k) by omega, Nat.add_sub_cancel_left,
      nested_pow hN (by omega)]
  simp only [fwTable, h1, show L - 1 - (L - k + j) = k - 1 - j by omega]

theorem invTable_nested (G : Gen K) (hN : GenNested G) {k L j : ℕ} (hkL : k ≤ L)
    (hL : L ≤ G.adicity) : invTable (G.gen L) L (L - k + j) = invTable (G.gen k) k j := by
  have h1 : G.gen L ^ 2 ^ (L - k + j) = G.gen k ^ 2 ^ j := by
    rw [pow_add, pow_mul, show L = k + (L - k) by omega, Nat.add_sub_cancel_left,
      nested_pow hN (by omega)]
  simp only [invTable, h1, show L - 1 - (L - k + j) = k - 1 - j by omega]

/-- Entry b of forward table k - 1 - l is the twiddle of block b of bit-reversed layer l. -/
theorem fw_entry (g : K) {k l b : ℕ} (hl : l < k) (hb : b < 2 ^ l) :
    (fwTable g k (k - 1 - l)).getD b 0 = Tdft g k l (rev l b) := by
  have e : k - 1 - (k - 1 - l) = l := by omega
  simp only [fwTable, e]
  rw [getD_revIndex _ hb, getD_powersList _ (Plonky3Lean.Proofs.Matrix.bitRev_lt l b), Tdft,
    ← pow_mul, mul_comm, show k - 1 - l = k - 1 - l from rfl]

theorem length_fwTable (g : K) (k i : ℕ) : (fwTable g k i).length = 2 ^ (k - 1 - i) := by
  simp [fwTable, length_revIndex]

theorem length_invTable (g : K) (k i : ℕ) : (invTable g k i).length = 2 ^ (k - 1 - i) := by
  simp [invTable, length_revIndex]

/-! ## Layers on sub-blocks -/

theorem subBlocks_eq (c n m : ℕ) :
    subBlocks (c * n) n m = p3_dft.radix_2_dit_parallel.mirror.chunkOrder c n m false := by
  simp [subBlocks, p3_dft.radix_2_dit_parallel.mirror.chunkOrder, List.flatMap_map]

/-- The loop over sub-blocks c n to c n + n - 1 is a global layer restricted to chunk c of n 2m rows. -/
theorem pairLoop_sub {op op' : ℕ → ℕ → V → V → V × V} {c n m NB : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hc : c * n + n ≤ NB) (h : ∀ b, c * n ≤ b → b < c * n + n → ∀ s < m, op b s = op' b s)
    (x : ℕ → V) :
    pairLoop (subBlocks (c * n) n m) m op x = restrict (n * (2 * m)) c (layer op' m NB) x := by
  rw [subBlocks_eq, pairLoop_chunkOrder _ _ _ hm, layerOn_op_congr h, layerOn_eq_restrict _ hm hn hc]

/-- With the forward table of layer l, the butterfly at block b is the bit-reversed layer's. -/
theorem flyAt_fw (g : K) {k l b : ℕ} (hl : l < k) (hb : b < 2 ^ l) :
    flyAt (fwTable g k (k - 1 - l)) p3_dft.butterflies.mirror.DitButterfly.apply b =
      (dit (Tdft g k l (rev l b)) : V → V → V × V) := by
  unfold flyAt
  split_ifs with h0
  · subst h0; rw [rev_zero]; simp only [Tdft, zero_mul, pow_zero]; exact twiddleFree_eq_dit
  · rw [fw_entry g hl hb, ditButterfly_eq]

/-- One parallel layer with forward table k - 1 - l is bit-reversed layer l. -/
theorem dft_layer_par_fw (g : K) {k l : ℕ} (hl : l < k) (x : ℕ → V) :
    dft_layer_par (2 ^ k) (fwTable g k (k - 1 - l)) p3_dft.butterflies.mirror.DitButterfly.apply x =
      revL (Tdft g k) k l x := by
  unfold dft_layer_par
  have hh : 2 ^ k / (2 * 2 ^ l) = 2 ^ (k - 1 - l) := by
    rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring, pow_div_pow' (by omega)]; congr 1; omega
  rw [length_fwTable, show k - 1 - (k - 1 - l) = l by omega]
  dsimp only
  rw [hh, pairLoop_blocks _ _ (by positivity)]
  exact layer_op_congr (fun b hb _ _ => by
    have := flyAt_fw (V := V) g hl hb
    unfold flyAt at this
    exact this) x

/-- The bit-reversed layer l's butterfly, as the operation of a restricted loop with a forward table. -/
theorem sub_fw (g : K) {k l c n m lo : ℕ} (hl : l < k) (hm : m = 2 ^ (k - 1 - l)) (hn : 0 < n)
    (hlo : lo = c * n) (hc : c * n + n ≤ 2 ^ l) (x : ℕ → V) :
    pairLoop (subBlocks lo n m) m
      (fun b _ => flyAt (fwTable g k (k - 1 - l)) p3_dft.butterflies.mirror.DitButterfly.apply b) x =
    restrict (n * (2 * m)) c (revL (Tdft g k) k l) x := by
  subst hm hlo
  exact pairLoop_sub (by positivity) hn hc (fun b _ hb _ _ => flyAt_fw g hl (by omega)) x

/-- Three layers per outer block are bit-reversed layers l, l + 1 and l + 2 on the whole matrix. -/
theorem triple_dit_fw (g : K) {k l : ℕ} (hl : l + 3 ≤ k) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    dft_layer_par_triple_dit (2 ^ k) (fwTable g k (k - 1 - l)) (fwTable g k (k - 1 - (l + 1)))
      (fwTable g k (k - 1 - (l + 2))) p3_dft.butterflies.mirror.DitButterfly.apply x i =
    revL (Tdft g k) k (l + 2) (revL (Tdft g k) k (l + 1) (revL (Tdft g k) k l x)) i := by
  unfold dft_layer_par_triple_dit
  rw [length_fwTable, show k - 1 - (k - 1 - l) = l by omega]
  dsimp only
  have he : 2 ^ k / (8 * 2 ^ l) = 2 ^ (k - 1 - (l + 2)) := by
    rw [show 8 * 2 ^ l = 2 ^ (l + 3) by ring, pow_div_pow' (by omega)]; congr 1; omega
  have hS1 : 1 * (2 * (4 * 2 ^ (k - 1 - (l + 2)))) = 2 ^ (k - l) := by
    rw [show 4 * 2 ^ (k - 1 - (l + 2)) = 2 ^ (k - 1 - (l + 2) + 2) by ring,
      ← pow_succ']; simp only [one_mul]; congr 1; omega
  have hS2 : 2 * (2 * (2 * 2 ^ (k - 1 - (l + 2)))) = 2 ^ (k - l) := by
    rw [show 2 * (2 * (2 * 2 ^ (k - 1 - (l + 2)))) = 2 ^ (k - 1 - (l + 2) + 3) by ring]
    congr 1; omega
  have hS3 : 4 * (2 * 2 ^ (k - 1 - (l + 2))) = 2 ^ (k - l) := by
    rw [show 4 * (2 * 2 ^ (k - 1 - (l + 2))) = 2 ^ (k - 1 - (l + 2) + 3) by ring]
    congr 1; omega
  have hm1 : 4 * 2 ^ (k - 1 - (l + 2)) = 2 ^ (k - 1 - l) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hm2 : 2 * 2 ^ (k - 1 - (l + 2)) = 2 ^ (k - 1 - (l + 1)) := by
    rw [← pow_succ']; congr 1; omega
  rw [he]
  rw [foldl_congr_mem _ (g := fun acc ind =>
      [revL (Tdft g k) k l, revL (Tdft g k) k (l + 1), revL (Tdft g k) k (l + 2)].foldl
        (fun acc f => restrict (2 ^ (k - l)) ind f acc) acc) (fun ind hind acc => by
      have hind' := List.mem_range.mp hind
      simp only [List.foldl_cons, List.foldl_nil]
      rw [sub_fw g (by omega) hm1 (by norm_num) (by ring) (by omega), hS1,
        sub_fw g (by omega) hm2 (by norm_num) (by ring) (by rw [pow_succ]; omega), hS2,
        sub_fw g (by omega) rfl (by norm_num) (by ring) (by rw [pow_succ, pow_succ]; omega), hS3])]
  rw [chunked (S := 2 ^ (k - l)) (C := 2 ^ l) _ (fun f hf => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact revL_localTo _ (le_refl l) (by omega)
      · exact revL_localTo _ (by omega) (by omega)
      · exact revL_localTo _ (by omega) (by omega)) x
    (by rw [← pow_add, show l + (k - l) = k by omega]; exact hi)]
  rfl

/-- Two layers per outer block are bit-reversed layers l and l + 1 on the whole matrix. -/
theorem double_dit_fw (g : K) {k l : ℕ} (hl : l + 2 ≤ k) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    dft_layer_par_double_dit (2 ^ k) (fwTable g k (k - 1 - l)) (fwTable g k (k - 1 - (l + 1)))
      p3_dft.butterflies.mirror.DitButterfly.apply x i =
    revL (Tdft g k) k (l + 1) (revL (Tdft g k) k l x) i := by
  unfold dft_layer_par_double_dit
  rw [length_fwTable, show k - 1 - (k - 1 - l) = l by omega]
  dsimp only
  have hq : 2 ^ k / (4 * 2 ^ l) = 2 ^ (k - 1 - (l + 1)) := by
    rw [show 4 * 2 ^ l = 2 ^ (l + 2) by ring, pow_div_pow' (by omega)]; congr 1; omega
  have hm1 : 2 * 2 ^ (k - 1 - (l + 1)) = 2 ^ (k - 1 - l) := by rw [← pow_succ']; congr 1; omega
  have hS1 : 1 * (2 * (2 * 2 ^ (k - 1 - (l + 1)))) = 2 ^ (k - l) := by
    rw [show 1 * (2 * (2 * 2 ^ (k - 1 - (l + 1)))) = 2 ^ (k - 1 - (l + 1) + 2) by ring]
    congr 1; omega
  have hS2 : 2 * (2 * 2 ^ (k - 1 - (l + 1))) = 2 ^ (k - l) := by
    rw [show 2 * (2 * 2 ^ (k - 1 - (l + 1))) = 2 ^ (k - 1 - (l + 1) + 2) by ring]
    congr 1; omega
  rw [hq]
  rw [foldl_congr_mem _ (g := fun acc ind =>
      [revL (Tdft g k) k l, revL (Tdft g k) k (l + 1)].foldl
        (fun acc f => restrict (2 ^ (k - l)) ind f acc) acc) (fun ind hind acc => by
      have hind' := List.mem_range.mp hind
      simp only [List.foldl_cons, List.foldl_nil]
      rw [sub_fw g (by omega) hm1 (by norm_num) (by ring) (by omega), hS1,
        sub_fw g (by omega) rfl (by norm_num) (by ring) (by rw [pow_succ]; omega), hS2])]
  rw [chunked (S := 2 ^ (k - l)) (C := 2 ^ l) _ (fun f hf => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact revL_localTo _ (le_refl l) (by omega)
      · exact revL_localTo _ (by omega) (by omega)) x
    (by rw [← pow_add, show l + (k - l) = k by omega]; exact hi)]
  rfl

/-- A fold of bit-reversed layers reads only the first 2^k rows. -/
theorem revL_fold_congr (T : ℕ → ℕ → K) {k : ℕ} (ls : List ℕ) (hls : ∀ l ∈ ls, l < k)
    {x x' : ℕ → V} (h : ∀ p < 2 ^ k, x p = x' p) :
    ∀ i < 2 ^ k, ls.foldl (fun acc l => revL T k l acc) x i =
      ls.foldl (fun acc l => revL T k l acc) x' i := by
  induction ls generalizing x x' with
  | nil => exact h
  | cons l ls ih =>
    intro i hi
    simp only [List.foldl_cons]
    refine ih (fun l hl => hls l (by simp [hl])) (fun p hp => ?_) i hi
    have hl := hls l (by simp)
    have hsz : 2 ^ l * (2 * 2 ^ (k - 1 - l)) = 2 ^ k := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    exact layer_congr _ _ _ (fun q hq => h q (hsz ▸ hq)) (by rw [hsz]; exact hp)

/-- The triples of layers are the layers l0, l0 + 1, ..., up to the last full triple. -/
theorem tuples_dit (g : K) {k : ℕ} :
    ∀ n l0, l0 + n ≤ k → ∀ (x : ℕ → V), ∀ i < 2 ^ k,
      (tuples3 ((List.range' l0 n).map fun l => fwTable g k (k - 1 - l))).foldl
        (fun acc t => dft_layer_par_triple_dit (2 ^ k) t.1 t.2.1 t.2.2
          p3_dft.butterflies.mirror.DitButterfly.apply acc) x i =
      (List.range' l0 (n / 3 * 3)).foldl (fun acc l => revL (Tdft g k) k l acc) x i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l0 hn x i hi
    by_cases h3 : n < 3
    · have hz : n / 3 * 3 = 0 := by omega
      rw [hz]
      rcases n with _ | _ | _ | n
      · rfl
      · rfl
      · rfl
      · omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [show m + 3 = ((m + 1) + 1) + 1 by ring, List.range'_succ, List.range'_succ,
        List.range'_succ]
      simp only [List.map_cons, tuples3, List.foldl_cons]
      rw [show (m + 1 + 1 + 1) / 3 * 3 = ((m / 3 * 3 + 1) + 1) + 1 by omega, List.range'_succ,
        List.range'_succ, List.range'_succ]
      simp only [List.foldl_cons]
      rw [ih m (by omega) (l0 + 1 + 1 + 1) (by omega) _ i hi]
      refine revL_fold_congr _ _ (fun l hl => by
        simp only [List.mem_range'] at hl; omega) (fun p hp => ?_) i hi
      rw [show l0 + 1 + 1 = l0 + 2 by ring]
      exact triple_dit_fw g (by omega) x hp

/-- The layers of chunk idx are the bit-reversed layers k - lnpr to k - 1, restricted to the chunk. -/
theorem remaining_layers_eq (g : K) {k lnpr idx : ℕ} (hl : lnpr ≤ k) (hidx : idx < 2 ^ (k - lnpr))
    (acc : ℕ → V) :
    remaining_layers (2 ^ lnpr) idx ((List.range lnpr).map (fwTable g k)) acc =
      ((List.range lnpr).map fun layer => revL (Tdft g k) k (k - lnpr + layer)).foldl
        (fun acc f => restrict (2 ^ lnpr) idx f acc) acc := by
  unfold remaining_layers
  rw [List.foldl_map, List.length_map, List.length_range]
  refine foldl_congr_mem _ (fun layer hlayer acc => ?_) acc
  have hly := List.mem_range.mp hlayer
  have hget : ((List.range lnpr).map (fwTable g k)).getD (lnpr - 1 - layer) [] =
      fwTable g k (k - 1 - (k - lnpr + layer)) := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    congr 1; omega
  have hhalf : 2 ^ lnpr / (2 * 2 ^ layer) = 2 ^ (k - 1 - (k - lnpr + layer)) := by
    rw [show 2 * 2 ^ layer = 2 ^ (layer + 1) by ring, pow_div_pow' (by omega)]; congr 1; omega
  have hS : 2 ^ layer * (2 * 2 ^ (k - 1 - (k - lnpr + layer))) = 2 ^ lnpr := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hc : idx * 2 ^ layer + 2 ^ layer ≤ 2 ^ (k - lnpr + layer) := by
    have : (idx + 1) * 2 ^ layer ≤ 2 ^ (k - lnpr) * 2 ^ layer := Nat.mul_le_mul_right _ hidx
    rw [← pow_add] at this; nlinarith
  dsimp only
  rw [hget, hhalf]
  have := pairLoop_sub (V := V) (c := idx) (n := 2 ^ layer) (m := 2 ^ (k - 1 - (k - lnpr + layer)))
    (op := fun b _ => p3_dft.butterflies.mirror.DitButterfly.apply
      ((fwTable g k (k - 1 - (k - lnpr + layer))).getD b 0))
    (op' := fun σ _ => dit (Tdft g k (k - lnpr + layer) (rev (k - lnpr + layer) σ)))
    (by positivity) (by positivity) hc
    (fun b _ hb _ _ => by rw [ditButterfly_eq, fw_entry g (by omega) (by omega)]) acc
  rw [hS] at this
  exact this

/-- The chunked layers are the bit-reversed layers k - lnpr to k - 1 on the whole matrix. -/
theorem par_remaining_eq (g : K) {k lnpr : ℕ} (hl : lnpr ≤ k) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    par_remaining_layers (2 ^ k) (2 ^ lnpr) ((List.range lnpr).map (fwTable g k)) x i =
      (List.range' (k - lnpr) lnpr).foldl (fun acc l => revL (Tdft g k) k l acc) x i := by
  unfold par_remaining_layers
  rw [pow_div_pow' hl]
  rw [foldl_congr_mem _ (g := fun acc idx =>
      ((List.range lnpr).map fun layer => revL (Tdft g k) k (k - lnpr + layer)).foldl
        (fun acc f => restrict (2 ^ lnpr) idx f acc) acc) (fun idx hidx acc => by
      funext r
      rw [remaining_layers_eq g hl (List.mem_range.mp hidx), restrict_foldl (by positivity)
        (List.mem_range.mp hidx) _ (fun f hf => by
          obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hf
          have h' := revL_localTo (V := V) (Tdft g k) (k := k) (mid := k - lnpr)
            (l := k - lnpr + l) (by omega) (by have := List.mem_range.mp hl'; omega)
          rwa [show k - (k - lnpr) = lnpr by omega] at h') acc r]
      split_ifs <;> rfl)]
  rw [chunked (S := 2 ^ lnpr) (C := 2 ^ (k - lnpr)) _ (fun f hf => by
      obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hf
      have h' := revL_localTo (V := V) (Tdft g k) (k := k) (mid := k - lnpr)
        (l := k - lnpr + l) (by omega) (by have := List.mem_range.mp hl'; omega)
      rwa [show k - (k - lnpr) = lnpr by omega] at h') x
    (by rw [← pow_add, show k - lnpr + lnpr = k by omega]; exact hi), List.foldl_map,
    List.range'_eq_map_range, List.foldl_map]

theorem range'_append' {s m t n : ℕ} (h : t = s + m) :
    List.range' s m ++ List.range' t n = List.range' s (m + n) := by
  subst h; simp

theorem take_map_range {α : Type _} (f : ℕ → α) {k n : ℕ} (h : n ≤ k) :
    ((List.range k).map f).take n = (List.range n).map f := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2; simp

theorem estimate_pow (c w k : ℕ) :
    estimate_num_rows_in_l1 c w (2 ^ k) = 2 ^ min (Nat.clog 2 (c / w)) k := by
  unfold estimate_num_rows_in_l1
  rcases le_total (Nat.clog 2 (c / w)) k with h | h
  · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
  · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right (by norm_num) h)]

/-- The forward tables the transform of 2^k rows reads, from a cache of size 2^L >= 2^k. -/
theorem cache_fw (G : Gen K) (hG : GenValid G) (hN : GenNested G) {k L : ℕ} (hkL : k ≤ L)
    (hL : L ≤ G.adicity) :
    ∃ fw inv, cache G L = some (fw, inv) ∧ fw.drop (fw.length - k) = (List.range k).map (fwTable (G.gen k) k) ∧
      inv.drop (inv.length - k) = (List.range k).map (invTable (G.gen k) k) := by
  by_cases hL0 : L = 0
  · subst hL0
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨[], [], by simp [cache], rfl, rfl⟩
  refine ⟨_, _, cache_spec G hG (by omega) hL, ?_, ?_⟩
  · simp only [List.length_map, List.length_range]
    exact drop_tables (tbl := fun L' j => fwTable (G.gen L') L' j) hkL
      (fun j => fwTable_nested G hN hkL hL)
  · simp only [List.length_map, List.length_range]
    exact drop_tables (tbl := fun L' j => invTable (G.gen L') L' j) hkL
      (fun j => invTable_nested G hN hkL hL)

theorem reverse_drop_fw (g : K) {k lnpr : ℕ} (hl : lnpr ≤ k) :
    (((List.range k).map (fwTable g k)).drop lnpr).reverse =
      (List.range' 0 (k - lnpr)).map fun l => fwTable g k (k - 1 - l) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_reverse, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getElem_range', List.length_drop, List.length_map, List.length_range]
    congr 1; simp at h2; omega

theorem take_drop_fw (g : K) {k lnpr n : ℕ} (h : lnpr + n ≤ k) :
    (((List.range k).map (fwTable g k)).drop lnpr).take n = (List.range' lnpr n).map (fwTable g k) := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp [List.getElem_range']

/-- The small-batch forward transform of 2^k rows is the transform at G_k, for nested generators and a cache of any size 2^L >= 2^k. -/
theorem smallBatch_dft_batch (G : Gen K) (hG : GenValid G) (hN : GenNested G) {k L : ℕ}
    (hkL : k ≤ L) (hL : L ≤ G.adicity) (c w : ℕ) (x : ℕ → V) :
    Computes (Radix2DFTSmallBatch.dft_batch G L c w (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) := by
  obtain ⟨fw, inv, hcache, hfw, -⟩ := cache_fw G hG hN hkL hL
  set g := G.gen k
  set lnpr := min (Nat.clog 2 (c / w)) k with hlnpr
  have hl : lnpr ≤ k := min_le_right _ _
  obtain ⟨n, hn⟩ : ∃ n, n = k - lnpr := ⟨_, rfl⟩
  let F : ℕ → (ℕ → V) → ℕ → V := fun l acc => revL (Tdft g k) k l acc
  -- the triples
  obtain ⟨X1, hX1⟩ : ∃ X1, X1 = (tuples3 ((List.range' 0 n).map fun l => fwTable g k (k - 1 - l))).foldl
    (fun acc t => dft_layer_par_triple_dit (2 ^ k) t.1 t.2.1 t.2.2
      p3_dft.butterflies.mirror.DitButterfly.apply acc) x := ⟨_, rfl⟩
  have h1 : ∀ i < 2 ^ k, X1 i = (List.range' 0 (n / 3 * 3)).foldl (fun acc l => F l acc) x i := by
    rw [hX1]; exact tuples_dit g n 0 (by omega) x
  -- the extra layers
  have hextra : ∃ X2, extra_layers_dit (2 ^ k) ((List.range' lnpr (n % 3)).map (fwTable g k)) X1 = some X2 ∧
      ∀ i < 2 ^ k, X2 i = (List.range' (n / 3 * 3) (n % 3)).foldl (fun acc l => F l acc) X1 i := by
    have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
    · rw [h]; exact ⟨X1, rfl, fun i _ => rfl⟩
    · rw [h]
      refine ⟨_, rfl, fun i hi => ?_⟩
      simp only [List.range'_one, List.foldl_cons, List.foldl_nil]
      rw [show fwTable g k lnpr = fwTable g k (k - 1 - (n / 3 * 3)) by congr 1; omega,
        dft_layer_par_fw g (by omega)]
    · rw [h]
      refine ⟨_, rfl, fun i hi => ?_⟩
      simp only [List.range'_succ, List.range'_zero, List.foldl_cons, List.foldl_nil]
      rw [show fwTable g k (lnpr + 1) = fwTable g k (k - 1 - (n / 3 * 3)) by congr 1; omega,
        show fwTable g k lnpr = fwTable g k (k - 1 - (n / 3 * 3 + 1)) by congr 1; omega]
      exact double_dit_fw g (by omega) X1 hi
  obtain ⟨X2, hX2, h2⟩ := hextra
  refine ⟨revRows k (par_remaining_layers (2 ^ k) (2 ^ lnpr) ((List.range lnpr).map (fwTable g k)) X2),
    ?_, fun i hi => ?_⟩
  · simp only [Radix2DFTSmallBatch.dft_batch, log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
      hcache, estimate_pow, hfw]
    rw [reverse_drop_fw g hl, take_drop_fw g (show lnpr + (k - lnpr) % 3 ≤ k by omega), ← hn,
      ← hX1, hX2]
    rw [take_map_range _ hl]
    simp only [Option.bind_some, Option.pure_def, ← hlnpr]
  · have hri := Plonky3Lean.Proofs.Matrix.bitRev_lt k i
    have hls : ∀ (s m : ℕ), s + m ≤ k → ∀ l ∈ List.range' s m, l < k := fun s m h l hl' => by
      simp only [List.mem_range'] at hl'; omega
    have hX2 : ∀ p < 2 ^ k, X2 p = (List.range' 0 n).foldl (fun acc l => F l acc) x p := by
      intro p hp
      rw [h2 p hp, revL_fold_congr _ _ (hls _ _ (by omega)) h1 p hp, ← List.foldl_append,
        range'_append' (by ring), show n / 3 * 3 + n % 3 = n by omega]
    rw [revRows_apply k _ hi, par_remaining_eq g hl X2 hri,
      revL_fold_congr _ _ (hls _ _ (by omega)) hX2 _ hri, ← List.foldl_append,
      show List.range' 0 n ++ List.range' (k - lnpr) lnpr = List.range' 0 k by
        rw [range'_append' (by omega), show n + lnpr = k by omega]]
    rw [List.range'_eq_map_range, List.foldl_map]
    have := revL_chain (Tdft g k) (mid := 0) (Nat.zero_le k) (bitRevVec (rev k) x) k (by omega) _ hri
    rw [revL_chain_congr _ (Nat.zero_le k) (z' := fun p => bitRevVec (rev k) x (rev k p))
      (fun p hp => by simp [bitRevVec, rev_involutive hp]) k (by omega) _ hri, this,
      rev_involutive hi]
    have h3 := natL_chain_ditNet g k 0 (bitRevVec (rev k) x) k
    rw [zero_add] at h3
    exact (congrFun h3 i).trans (ditNet_eq_dft (hG k (by omega)) x hi)

end Plonky3Lean.Proofs.Dft
