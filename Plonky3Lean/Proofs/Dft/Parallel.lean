module

public import Plonky3Lean.Proofs.Dft.Chunks
public import Plonky3Lean.Proofs.Dft.Bowers

@[expose] public section

/-!
# The parallel radix-2 DIT backend

The first half runs the first ceil(log_h / 2) Cooley-Tukey layers, chunk by chunk.

The second half runs the remaining layers in bit-reversed order: each is a Cooley-Tukey layer
conjugated by the bit reversal, again chunk by chunk.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft p3_dft.radix_2_dit_parallel.mirror

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-! ## Chunk loops -/

section loops

variable {W : Type _}

theorem mem_chunkOrder (c nb m b s : ℕ) (bw : Bool) :
    (b, s) ∈ chunkOrder c nb m bw ↔ c * nb ≤ b ∧ b < c * nb + nb ∧ s < m := by
  have h : (b, s) ∈ chunkOrder c nb m bw ↔ (∃ a < nb, c * nb + a = b) ∧ s < m := by
    unfold chunkOrder; cases bw <;> simp
  rw [h]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hs⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨b - c * nb, by omega, by omega⟩, h3⟩

theorem chunkOrder_nodup (c nb m : ℕ) (bw : Bool) : (chunkOrder c nb m bw).Nodup := by
  unfold chunkOrder
  have hbs : ((List.range nb).map (c * nb + ·)).Nodup :=
    List.nodup_range.map (fun a b h => by simpa using h)
  rw [List.nodup_flatMap]
  refine ⟨fun b _ => List.nodup_range.map (fun _ _ h => by simpa using h), ?_⟩
  have hpw : ∀ l : List ℕ, l.Nodup →
      l.Pairwise (Function.onFun List.Disjoint fun b => (List.range m).map fun s => (b, s)) := by
    intro l hl
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp hl)
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
    rintro _ ⟨s, _, rfl⟩ ⟨s', _, h⟩
    exact hab (congrArg Prod.fst h).symm
  cases bw
  · exact hpw _ hbs
  · exact hpw _ (List.nodup_reverse.mpr hbs)

/-- A chunk's loop is the layer restricted to the chunk's blocks. -/
theorem pairLoop_chunkOrder (c nb m : ℕ) (hm : 0 < m) (bw : Bool) (op : ℕ → ℕ → W → W → W × W)
    (x : ℕ → W) : pairLoop (chunkOrder c nb m bw) m op x = layerOn op m (c * nb) (c * nb + nb) x := by
  rw [pairLoop_eq_runB, runB_layerList_on op m _ _ hm _ (chunkOrder_nodup c nb m bw)
    (fun b s => mem_chunkOrder c nb m b s bw)]

/-- The layer restricted to chunk c, of S = nb 2m rows, is the global layer applied to that chunk. -/
theorem layerOn_eq_restrict (op : ℕ → ℕ → W → W → W × W) {m nb NB c : ℕ} (hm : 0 < m)
    (hnb : 0 < nb) (hc : c * nb + nb ≤ NB) (x : ℕ → W) :
    layerOn op m (c * nb) (c * nb + nb) x = restrict (nb * (2 * m)) c (layer op m NB) x := by
  funext i
  unfold layerOn restrict
  have hm2 : 0 < 2 * m := by omega
  have hS : 0 < nb * (2 * m) := by positivity
  by_cases hic : i / (nb * (2 * m)) = c
  · rw [ite_eq_left hic]
    have h1 : c * (nb * (2 * m)) ≤ i := by rw [← hic]; exact Nat.div_mul_le_self i _
    have h2 : i < (c + 1) * (nb * (2 * m)) := by
      rw [← hic]
      have := Nat.mod_lt i hS
      have := Nat.div_add_mod' i (nb * (2 * m))
      nlinarith
    rw [ite_eq_left (by nlinarith)]
    unfold layer
    have h3 : i < (c * nb + nb) * (2 * m) := by nlinarith
    have h4 : i < NB * (2 * m) := lt_of_lt_of_le h3 (Nat.mul_le_mul_right _ hc)
    rw [ite_eq_left h3, ite_eq_left h4]
  · rw [ite_eq_right hic]
    split_ifs with h1
    · unfold layer
      rw [ite_eq_right]
      intro h3
      apply hic
      apply Nat.div_eq_of_lt_le <;> nlinarith
    · rfl

/-- The flag that alternates the direction does not change a fold of direction-independent steps. -/
theorem foldl_flag {α : Type _} (F : α → Bool → (ℕ → W) → ℕ → W) (G : α → (ℕ → W) → ℕ → W)
    (L : List α) (hFG : ∀ a ∈ L, ∀ b, F a b = G a) (acc : ℕ → W) (b0 : Bool) :
    (L.foldl (fun (st : (ℕ → W) × Bool) a => (F a st.2 st.1, !st.2)) (acc, b0)).1 =
      L.foldl (fun acc a => G a acc) acc := by
  induction L generalizing acc b0 with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [hFG a (by simp) b0]
    exact ih (fun a ha b => hFG a (by simp [ha]) b) _ _

theorem foldl_congr_mem {α β : Type _} (l : List α) {f g : β → α → β}
    (h : ∀ a ∈ l, ∀ acc, f acc a = g acc a) (x : β) : l.foldl f x = l.foldl g x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp)]
    exact ih (fun a ha => h a (by simp [ha])) _

end loops

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The natural decimation-in-time layer l of the transform of size 2^k. -/
abbrev natLayer (ω : K) (k l : ℕ) : (ℕ → V) → ℕ → V :=
  ditLayer (2 ^ l) (2 ^ (k - 1 - l)) (fun _ s => ω ^ (s * 2 ^ (k - 1 - l)))

theorem foldl_natLayer (ω : K) (k : ℕ) (x : ℕ → V) (n : ℕ) :
    (List.range n).foldl (fun acc l => natLayer ω k l acc) x = ditNet ω k n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem natLayer_localTo (ω : K) {k mid l : ℕ} (hl : l < mid) (hmid : mid ≤ k) :
    LocalTo (2 ^ mid) (2 ^ (k - mid)) (natLayer (V := V) ω k l) := by
  apply layer_localTo _ (by positivity)
  · rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring]; exact Nat.pow_dvd_pow 2 (by omega)
  · rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega

theorem pow_div_pow' {a b : ℕ} (h : b ≤ a) : 2 ^ a / 2 ^ b = 2 ^ (a - b) := by
  rw [Nat.pow_div h (by norm_num)]

/-- One step of a chunk of the first half is the natural layer restricted to the chunk. -/
theorem first_half_step (g : K) {k mid c l : ℕ} (hmid : mid ≤ k) (hc : c < 2 ^ (k - mid))
    (hl : l < mid) (bw : Bool) (acc : ℕ → V) :
    (if l = 0 then dit_layer_twiddle_free c (2 ^ mid) bw acc
      else dit_layer_first_one c (2 ^ mid) l
        (fun i => (powersList g (2 ^ k / 2)).getD (i * 2 ^ (k - 1 - l)) 0) bw acc) =
    restrict (2 ^ mid) c (natLayer g k l) acc := by
  have hdiv : 2 ^ mid / (2 * 2 ^ l) = 2 ^ (mid - 1 - l) := by
    rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring, pow_div_pow' (by omega)]; congr 1; omega
  have hnb : 2 ^ (mid - 1 - l) * (2 * 2 ^ l) = 2 ^ mid := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hcb : c * 2 ^ (mid - 1 - l) + 2 ^ (mid - 1 - l) ≤ 2 ^ (k - 1 - l) := by
    have : (c + 1) * 2 ^ (mid - 1 - l) ≤ 2 ^ (k - mid) * 2 ^ (mid - 1 - l) :=
      Nat.mul_le_mul_right _ hc
    rw [← pow_add, show k - mid + (mid - 1 - l) = k - 1 - l by omega] at this
    nlinarith
  have hcore : ∀ (op : ℕ → ℕ → V → V → V × V),
      (∀ b < 2 ^ (k - 1 - l), ∀ s < 2 ^ l, op b s = dit (g ^ (s * 2 ^ (k - 1 - l)))) →
      pairLoop (chunkOrder c (2 ^ (mid - 1 - l)) (2 ^ l) bw) (2 ^ l) op acc =
        restrict (2 ^ mid) c (natLayer g k l) acc := by
    intro op hop
    rw [pairLoop_chunkOrder _ _ _ (by positivity), layerOn_eq_restrict _ (by positivity)
      (by positivity) hcb, hnb]
    congr 1
    funext z
    exact layer_op_congr hop z
  have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) :=
    Nat.div_eq_of_eq_mul_left (by norm_num) (by rw [← pow_succ]; congr 1; omega)
  split_ifs with h0
  · subst h0
    unfold dit_layer_twiddle_free
    rw [show 2 ^ mid / 2 = 2 ^ (mid - 1 - 0) by rw [← hdiv]; simp]
    refine hcore _ (fun b _ s hs => ?_)
    simp at hs; subst hs; simp only [zero_mul, pow_zero]; exact twiddleFree_eq_dit
  · unfold dit_layer_first_one
    dsimp only
    rw [hdiv]
    refine hcore _ (fun b _ s hs => ?_)
    split_ifs with hs0
    · subst hs0; simp only [zero_mul, pow_zero]; exact twiddleFree_eq_dit
    · rw [ditButterfly_eq, getD_powersList]
      rw [hhalf]
      have : s * 2 ^ (k - 1 - l) < 2 ^ l * 2 ^ (k - 1 - l) :=
        Nat.mul_lt_mul_of_pos_right hs (by positivity)
      rwa [← pow_add, show l + (k - 1 - l) = k - 1 by omega] at this

/-- The first half runs the first mid Cooley-Tukey layers. -/
theorem first_half_spec (g : K) {k mid : ℕ} (hmid : mid ≤ k) (x : ℕ → V) :
    ∃ y, first_half (2 ^ k) mid (powersList g (2 ^ k / 2)) x = some y ∧
      ∀ i < 2 ^ k, y i = ditNet g k mid x i := by
  refine ⟨_, by simp only [first_half, log2Strict_pow, Option.bind_eq_bind, Option.bind_some]; rfl,
    fun i hi => ?_⟩
  rw [pow_div_pow' hmid]
  rw [foldl_congr_mem _ (g := fun acc c =>
      ((List.range mid).map (natLayer g k)).foldl (fun acc f => restrict (2 ^ mid) c f acc) acc)
    (fun c hc acc => by
      rw [foldl_flag _ (fun l acc => restrict (2 ^ mid) c (natLayer g k l) acc) _
        (fun l hl bw => funext fun acc => first_half_step g hmid (List.mem_range.mp hc)
          (List.mem_range.mp hl) bw acc), List.foldl_map])]
  rw [chunked _ (fun f hf => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
      exact natLayer_localTo g (List.mem_range.mp hl) hmid) x
    (by rw [← pow_add, show k - mid + mid = k by omega]; exact hi),
    List.foldl_map, foldl_natLayer]

/-! ## The second half -/

section second

variable {W : Type _}

theorem layerOn_op_congr {op op' : ℕ → ℕ → W → W → W × W} {m lo hi : ℕ}
    (h : ∀ b, lo ≤ b → b < hi → ∀ s < m, op b s = op' b s) (x : ℕ → W) :
    layerOn op m lo hi x = layerOn op' m lo hi x := by
  funext i
  unfold layerOn layer
  have hm : 0 < 2 * m ∨ m = 0 := by omega
  split_ifs with h1 h2 h3 <;> try rfl
  all_goals
    rcases hm with hm | hm
    · have hb1 : lo ≤ i / (2 * m) := (Nat.le_div_iff_mul_le hm).mpr h1
      have hb2 : i / (2 * m) < hi := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h2)
      first
      | rw [h _ hb1 hb2 _ h3]
      | (have := Nat.mod_lt i hm; rw [h _ hb1 hb2 _ (by omega)])
    · subst hm; simp at h2

end second

/-- A layer of the second half on chunk c: the global layer, restricted to the chunk, with block b
using twiddle function entry b. -/
theorem second_half_step {k mid c lyr : ℕ} (hmid : mid ≤ lyr) (hl : lyr < k)
    (hc : c < 2 ^ mid) (twf : ℕ → K) (fly : K → V → V → V × V) (bw : Bool) (acc : ℕ → V) :
    dit_layer_rev c (2 ^ (k - mid)) k lyr (c * 2 ^ (lyr - mid)) twf fly bw acc =
      restrict (2 ^ (k - mid)) c
        (layer (fun b _ => fly (twf b)) (2 ^ (k - 1 - lyr)) (2 ^ lyr)) acc := by
  have hdiv : 2 ^ (k - mid) / (2 * 2 ^ (k - 1 - lyr)) = 2 ^ (lyr - mid) := by
    rw [show 2 * 2 ^ (k - 1 - lyr) = 2 ^ (k - lyr) by
      rw [← pow_succ']; congr 1; omega, pow_div_pow' (by omega)]
    congr 1; omega
  have hnb : 2 ^ (lyr - mid) * (2 * 2 ^ (k - 1 - lyr)) = 2 ^ (k - mid) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hcb : c * 2 ^ (lyr - mid) + 2 ^ (lyr - mid) ≤ 2 ^ lyr := by
    have : (c + 1) * 2 ^ (lyr - mid) ≤ 2 ^ mid * 2 ^ (lyr - mid) := Nat.mul_le_mul_right _ hc
    rw [← pow_add, show mid + (lyr - mid) = lyr by omega] at this
    nlinarith
  unfold dit_layer_rev
  dsimp only
  rw [hdiv, pairLoop_chunkOrder _ _ _ (by positivity),
    layerOn_op_congr (op' := fun b _ => fly (twf b)) (fun b hb1 _ _ _ => by
      rw [show c * 2 ^ (lyr - mid) + (b - c * 2 ^ (lyr - mid)) = b by omega]),
    layerOn_eq_restrict _ (by positivity) (by positivity) hcb, hnb]

/-- A bit-reversed layer: half blocks of 2^(k-1-l) rows, block sigma with twiddle T l (rev_l(sigma)). -/
abbrev revL (T : ℕ → ℕ → K) (k l : ℕ) : (ℕ → V) → ℕ → V :=
  layer (fun σ _ => dit (T l (rev l σ))) (2 ^ (k - 1 - l)) (2 ^ l)

/-- A natural layer: half blocks of 2^l rows, offset s with twiddle T l s. -/
abbrev natL (T : ℕ → ℕ → K) (k l : ℕ) : (ℕ → V) → ℕ → V :=
  layer (fun _ s => dit (T l s)) (2 ^ l) (2 ^ (k - 1 - l))

theorem revL_localTo (T : ℕ → ℕ → K) {k mid l : ℕ} (hl1 : mid ≤ l) (hl2 : l < k) :
    LocalTo (2 ^ (k - mid)) (2 ^ mid) (revL (V := V) T k l) := by
  apply layer_localTo _ (by positivity)
  · rw [show 2 * 2 ^ (k - 1 - l) = 2 ^ (k - l) by rw [← pow_succ']; congr 1; omega]
    exact Nat.pow_dvd_pow 2 (by omega)
  · rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega

/-- Bit-reversed layers mid, mid + 1, ... on bit-reversed rows are the natural layers, bit-reversed. -/
theorem revL_chain (T : ℕ → ℕ → K) {k mid : ℕ} (hmid : mid ≤ k) (z : ℕ → V) :
    ∀ n ≤ k - mid, ∀ i < 2 ^ k,
      (List.range n).foldl (fun acc i => revL T k (mid + i) acc) (fun p => z (rev k p)) i =
        (List.range n).foldl (fun acc i => natL T k (mid + i) acc) z (rev k i) := by
  intro n
  induction n with
  | zero => intro _ i _; rfl
  | succ n ih =>
    intro hn i hi
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    obtain ⟨j, hj⟩ : ∃ j, k = (mid + n) + 1 + j := ⟨k - 1 - (mid + n), by omega⟩
    have e1 : k - 1 - (mid + n) = j := by omega
    simp only [revL, natL, e1]
    have hi' : i < 2 ^ ((mid + n) + 1 + j) := hj ▸ hi
    have := conj_layer (fun t : K => (dit t : V → V → V × V)) (fun s => T (mid + n) s) (mid + n) j
      ((List.range n).foldl (fun acc i => natL T k (mid + i) acc) z) hi'
    rw [← hj] at this
    rw [this]
    have hsz : 2 ^ (mid + n) * (2 * 2 ^ j) = 2 ^ k := by rw [hj]; ring
    exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (by rw [hsz]; exact hi)

/-- The natural chain from layer mid continues the decimation-in-time network. -/
theorem natL_chain_ditNet (ω : K) (k mid : ℕ) (y : ℕ → V) (n : ℕ) :
    (List.range n).foldl (fun acc i => natL (fun l s => ω ^ (s * 2 ^ (k - 1 - l))) k (mid + i) acc)
      (ditNet ω k mid y) = ditNet ω k (mid + n) y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/-- The same for the coset network. -/
theorem natL_chain_ditNetC (c ω : K) (k mid : ℕ) (y : ℕ → V) (n : ℕ) :
    (List.range n).foldl (fun acc i => natL (fun l s => (c * ω ^ s) ^ 2 ^ (k - 1 - l)) k (mid + i) acc)
      (ditNetC c ω k mid y) = ditNetC c ω k (mid + n) y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/-- The twiddles of the natural layers of the transform of size 2^k at the root g. -/
abbrev Tdft (g : K) (k : ℕ) : ℕ → ℕ → K := fun l s => g ^ (s * 2 ^ (k - 1 - l))

/-- The bit-reversed twiddle table of the second half reads T l (rev_l(b)) at block b of layer l. -/
theorem bitrev_table_layer (g : K) {k l b : ℕ} (hl : l < k) (hb : b < 2 ^ l) :
    (revIndex (2 ^ k / 2) (powersList g (2 ^ k / 2))).getD b 0 = Tdft g k l (rev l b) := by
  rw [getD_bowers_table g (l := k - 1 - l) (by omega) (by rw [show k - 1 - (k - 1 - l) = l by omega]; exact hb)]
  rw [show k - 1 - (k - 1 - l) = l by omega]

/-- One chunk step of the second half, with the bit-reversed forward table, is a bit-reversed layer. -/
theorem second_half_step_dit (g : K) {k mid c l : ℕ} (hmid : mid ≤ l) (hl : l < k) (hc : c < 2 ^ mid)
    (bw : Bool) (acc : ℕ → V) :
    dit_layer_rev c (2 ^ (k - mid)) k l (c * 2 ^ (l - mid))
      (fun j => (revIndex (2 ^ k / 2) (powersList g (2 ^ k / 2))).getD j 0)
      p3_dft.butterflies.mirror.DitButterfly.apply bw acc =
    restrict (2 ^ (k - mid)) c (revL (Tdft g k) k l) acc := by
  rw [second_half_step hmid hl hc]
  congr 1
  funext z
  exact layer_op_congr (fun b hb _ _ => by rw [ditButterfly_eq, bitrev_table_layer g hl hb]) z

/-- Without a scale, the second half runs the bit-reversed layers mid to k - 1. -/
theorem second_half_none (g : K) {k mid : ℕ} (hmid : mid ≤ k) (z : ℕ → V) :
    ∃ y, second_half (2 ^ k) mid (revIndex (2 ^ k / 2) (powersList g (2 ^ k / 2))) none z = some y ∧
      ∀ i < 2 ^ k, y i = (List.range (k - mid)).foldl (fun acc i => revL (Tdft g k) k (mid + i) acc) z i := by
  refine ⟨_, by simp only [second_half, log2Strict_pow, Option.bind_eq_bind, Option.bind_some]; rfl,
    fun i hi => ?_⟩
  rw [show 2 ^ k / 2 ^ (k - mid) = 2 ^ mid by rw [pow_div_pow' (by omega)]; congr 1; omega]
  rw [foldl_congr_mem _ (g := fun acc c =>
      ((List.range (k - mid)).map (fun i => revL (Tdft g k) k (mid + i))).foldl
        (fun acc f => restrict (2 ^ (k - mid)) c f acc) acc)
    (fun c hc acc => by
      rw [foldl_flag _ (fun i acc => restrict (2 ^ (k - mid)) c (revL (Tdft g k) k (mid + i)) acc) _
        (fun i hi bw => funext fun acc => by
          rw [ite_self, second_half_step_dit g (by omega) (by have := List.mem_range.mp hi; omega)
            (List.mem_range.mp hc)]), List.foldl_map])]
  rw [chunked _ (fun f hf => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
      exact revL_localTo _ (by omega) (by have := List.mem_range.mp hl; omega)) z
    (by rw [← pow_add, show mid + (k - mid) = k by omega]; exact hi), List.foldl_map]

/-- A chain of bit-reversed layers reads only the first 2^k rows. -/
theorem revL_chain_congr (T : ℕ → ℕ → K) {k mid : ℕ} (hmid : mid ≤ k) {z z' : ℕ → V}
    (h : ∀ p < 2 ^ k, z p = z' p) :
    ∀ n ≤ k - mid, ∀ i < 2 ^ k,
      (List.range n).foldl (fun acc i => revL T k (mid + i) acc) z i =
        (List.range n).foldl (fun acc i => revL T k (mid + i) acc) z' i := by
  intro n
  induction n with
  | zero => intro _ i hi; exact h i hi
  | succ n ih =>
    intro hn i hi
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    have hsz : 2 ^ (mid + n) * (2 * 2 ^ (k - 1 - (mid + n))) = 2 ^ k := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (by rw [hsz]; exact hi)

/-- The second half on bit-reversed rows, read bit-reversed, finishes the Cooley-Tukey network. -/
theorem second_half_finishes (g : K) {k mid : ℕ} (hmid : mid ≤ k) (y z : ℕ → V)
    (hz : ∀ p < 2 ^ k, z p = ditNet g k mid y (rev k p)) {i : ℕ} (hi : i < 2 ^ k) :
    (List.range (k - mid)).foldl (fun acc i => revL (Tdft g k) k (mid + i) acc) z (rev k i) =
      ditNet g k k y i := by
  have hri := Plonky3Lean.Proofs.Matrix.bitRev_lt k i
  rw [revL_chain_congr _ hmid hz _ le_rfl _ hri, revL_chain _ hmid _ _ le_rfl _ hri,
    rev_involutive hi, natL_chain_ditNet, show mid + (k - mid) = k by omega]

/-- The parallel backend's forward transform, read through its bit-reversed view, is the transform. -/
theorem parallel_dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2DitParallel.dft_batch G (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x) := by
  have hmid : (k + 1) / 2 ≤ k := by omega
  obtain ⟨y1, hy1, hy1'⟩ := first_half_spec (G.gen k) hmid (revRows k x)
  obtain ⟨y2, hy2, hy2'⟩ := second_half_none (G.gen k) hmid (revRows k y1)
  refine ⟨_, by simp only [Radix2DitParallel.dft_batch, log2Strict_pow,
    get_or_compute_twiddles, gen_get_of_le G hk, Option.bind_eq_bind, Option.bind_some,
    Option.map_some, hy1, hy2]; rfl, fun i hi => ?_⟩
  simp only [bitRev_eq]
  rw [hy2' _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k i), second_half_finishes _ hmid (revRows k x) _
    (fun p hp => by rw [revRows_apply k _ hp, hy1' _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k p)]) hi,
    ditNet_congr _ k (x' := bitRevVec (rev k) x) (fun p hp => by
      rw [revRows_apply k x hp, bitRevVec]) k le_rfl i hi]
  exact ditNet_eq_dft (hG k hk) x hi

/-! ## Scaling -/

theorem layer_dit_smul (tw : ℕ → ℕ → K) (m nb : ℕ) (c : K) (x : ℕ → V) :
    layer (fun b t => dit (tw b t)) m nb (scaleRows c x) = scaleRows c (layer (fun b t => dit (tw b t)) m nb x) := by
  funext i
  unfold layer scaleRows dit
  by_cases h1 : i < nb * (2 * m) <;> by_cases h2 : i % (2 * m) < m <;>
    simp [h1, h2, smul_add, smul_sub, smul_comm c]

theorem ditNet_smul (ω : K) (k : ℕ) (c : K) (x : ℕ → V) :
    ∀ L, ditNet ω k L (scaleRows c x) = scaleRows c (ditNet ω k L x) := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih => simp only [ditNet, ditLayer, ih, layer_dit_smul]

/-- The scaled butterfly is the plain one on scaled inputs. -/
theorem layer_scaled (tw : ℕ → K) (m nb : ℕ) (c : K) (x : ℕ → V) {i : ℕ} (hi : i < nb * (2 * m)) :
    layer (fun b _ => (p3_dft.butterflies.mirror.ScaledDitButterfly.new (tw b) c).apply) m nb x i =
      layer (fun b _ => dit (tw b)) m nb (scaleRows c x) i := by
  unfold layer scaleRows
  simp only [hi, ↓reduceIte, p3_dft.butterflies.mirror.ScaledDitButterfly.apply,
    p3_dft.butterflies.mirror.ScaledDitButterfly.new, dit, mul_smul]

/-- With a scale s, the second half runs the bit-reversed layers mid to k - 1 on the scaled rows. -/
theorem second_half_some (g : K) {k mid : ℕ} (hmid : mid ≤ k) (c : K) (z : ℕ → V) :
    ∃ y, second_half (2 ^ k) mid (revIndex (2 ^ k / 2) (powersList g (2 ^ k / 2))) (some c) z = some y ∧
      ∀ i < 2 ^ k, y i = (List.range (k - mid)).foldl (fun acc i => revL (Tdft g k) k (mid + i) acc)
        (scaleRows c z) i := by
  refine ⟨_, by simp only [second_half, log2Strict_pow, Option.bind_eq_bind, Option.bind_some]; rfl,
    fun i hi => ?_⟩
  rw [show 2 ^ k / 2 ^ (k - mid) = 2 ^ mid by rw [pow_div_pow' (by omega)]; congr 1; omega]
  by_cases hlt : mid < k
  · obtain ⟨n, hn⟩ : ∃ n, k - mid = n + 1 := ⟨k - mid - 1, by omega⟩
    let Φ : ℕ → (ℕ → V) → ℕ → V := fun j =>
      if j = 0 then fun x => revL (Tdft g k) k mid (scaleRows c x) else revL (Tdft g k) k (mid + j)
    rw [foldl_congr_mem _ (g := fun acc t =>
        ((List.range (k - mid)).map Φ).foldl (fun acc f => restrict (2 ^ (k - mid)) t f acc) acc)
      (fun t ht acc => by
        simp only [hlt, ↓reduceIte]
        rw [foldl_flag _ (fun j acc => restrict (2 ^ (k - mid)) t (Φ j) acc) _
          (fun j hj bw => funext fun acc => by
            have hj' := List.mem_range.mp hj
            by_cases hj0 : j = 0
            · subst hj0
              simp only [↓reduceIte, Φ, add_zero]
              rw [second_half_step (le_refl mid) hlt (List.mem_range.mp ht)]
              funext r
              unfold restrict
              split_ifs with hr
              · have hrk : r < 2 ^ mid * (2 * 2 ^ (k - 1 - mid)) := by
                  have := Nat.lt_mul_of_div_lt (show r / 2 ^ (k - mid) < 2 ^ mid by
                    rw [hr]; exact List.mem_range.mp ht) (by positivity)
                  rwa [show 2 ^ mid * (2 * 2 ^ (k - 1 - mid)) = 2 ^ mid * 2 ^ (k - mid) by
                    rw [← pow_succ']; congr 2; omega]
                rw [layer_scaled _ _ _ _ _ hrk]
                exact congrFun (layer_op_congr (fun b hb _ _ => by
                  rw [bitrev_table_layer g hlt hb]) _) r
              · rfl
            · simp only [hj0, ↓reduceIte, Φ]
              rw [second_half_step_dit g (by omega) (by omega) (List.mem_range.mp ht)]), List.foldl_map])]
    rw [chunked _ (fun f hf => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
        have hj' := List.mem_range.mp hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [↓reduceIte, Φ]
          intro x x' r hr hx
          exact revL_localTo _ (le_refl mid) hlt _ _ r hr (fun p hp => by simp [scaleRows, hx p hp])
        · simp only [hj0, ↓reduceIte, Φ]
          exact revL_localTo _ (by omega) (by omega)) z
      (by rw [← pow_add, show mid + (k - mid) = k by omega]; exact hi), List.foldl_map]
    rw [hn, List.range_succ_eq_map, List.foldl_cons, List.foldl_cons,
      List.foldl_map, List.foldl_map]
    simp [Φ]
  · have hmk : mid = k := by omega
    subst hmk
    simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, List.range_zero, List.foldl_nil]
    have := chunked (S := 1) (C := 2 ^ mid) [scaleRows c] (fun f hf => by
      simp at hf; subst hf
      intro x x' r _ hx; simp [scaleRows, hx r rfl]) z (by simpa using hi)
    simp only [List.foldl_cons, List.foldl_nil, pow_zero] at this ⊢
    rw [← this]
    rfl

/-- The parallel backend's inverse computes the inverse transform. -/
theorem parallel_idft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (x : ℕ → V) :
    Computes (Radix2DitParallel.idft_batch G (2 ^ k) x) (2 ^ k) (idft (G.gen k) (2 ^ k) x) := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨x, by simp [Radix2DitParallel.idft_batch], fun i hi => ?_⟩
    simp at hi; subst hi; simp [idft]
  have hmid : (k + 1) / 2 ≤ k := by omega
  have h1 : (2 : ℕ) ^ k ≠ 1 := by
    intro h; exact hk0 ((Nat.pow_eq_one).mp h |>.resolve_left (by norm_num))
  obtain ⟨y1, hy1, hy1'⟩ := first_half_spec (G.gen k)⁻¹ hmid (revRows k x)
  obtain ⟨y2, hy2, hy2'⟩ := second_half_some (G.gen k)⁻¹ hmid ((2 : K) ^ k)⁻¹ (revRows k y1)
  refine ⟨_, by simp only [Radix2DitParallel.idft_batch, h1, ↓reduceIte, log2Strict_pow,
    get_or_compute_inverse_twiddles, gen_get_of_le G hk, Option.bind_eq_bind, Option.bind_some,
    Option.map_some, hy1, hy2]; rfl, fun i hi => ?_⟩
  rw [revRows_apply k _ hi, hy2' _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
    second_half_finishes _ hmid (scaleRows ((2 : K) ^ k)⁻¹ (revRows k x)) _
    (fun p hp => by
      rw [scaleRows, revRows_apply k _ hp, hy1' _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k p),
        ditNet_smul]
      rfl) hi, ditNet_smul, scaleRows,
    ditNet_congr _ k (x' := bitRevVec (rev k) x) (fun p hp => by
      rw [revRows_apply k x hp, bitRevVec]) k le_rfl i hi,
    ditNet_eq_dft ((hG k hk).inv) x hi, idft, dft]
  congr 1
  push_cast; ring

/-! ## The coset transform -/

/-- The twiddles of the coset network of size 2^k: layer l, offset s uses (c omega^s)^(2^(k-1-l)). -/
abbrev Tcoset (c ω : K) (k : ℕ) : ℕ → ℕ → K := fun l s => (c * ω ^ s) ^ 2 ^ (k - 1 - l)

/-- The coset tables of size 2^k for the root omega and the shift c. -/
abbrev cosetTbl (ω c : K) (k : ℕ) : List (List K) := (List.range k).map fun t =>
  let tw := shiftedPowersList (ω ^ 2 ^ t) (c ^ 2 ^ t) (2 ^ k / 2 ^ (t + 1))
  if (k + 1) / 2 ≤ k - 1 - t then revIndex (2 ^ k / 2 ^ (t + 1)) tw else tw

theorem coset_tables (G : Gen K) {k : ℕ} (hk : k ≤ G.adicity) (c : K) :
    get_or_compute_coset_twiddles G k c = some (cosetTbl (G.gen k) c k) := by
  simp [get_or_compute_coset_twiddles, gen_get_of_le G hk]

/-- The first-half reading of a coset table: layer l < mid reads entry i as (c omega^i)^(2^(k-1-l)). -/
theorem coset_table_first (ω c : K) {k l i : ℕ} (hl : l < (k + 1) / 2) (hk : l < k) (hi : i < 2 ^ l) :
    (((List.range k).map fun t =>
      let tw := shiftedPowersList (ω ^ 2 ^ t) (c ^ 2 ^ t) (2 ^ k / 2 ^ (t + 1))
      if (k + 1) / 2 ≤ k - 1 - t then revIndex (2 ^ k / 2 ^ (t + 1)) tw else tw).getD (k - 1 - l) []).getD i 0 =
      Tcoset c ω k l i := by
  have hlen : 2 ^ k / 2 ^ (k - 1 - l + 1) = 2 ^ l := by rw [pow_div_pow' (by omega)]; congr 1; omega
  rw [List.getD_eq_getElem (d := ([] : List K)) _ (by simp; omega), List.getElem_map, List.getElem_range]
  simp only [show ¬ ((k + 1) / 2 ≤ k - 1 - (k - 1 - l)) by omega, ↓reduceIte, hlen]
  rw [getD_shiftedPowersList _ _ hi, Tcoset, mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ (k - 1 - l)) i]

/-- The second-half reading of a coset table: layer l >= mid reads block b as (c omega^(rev_l(b)))^(2^(k-1-l)). -/
theorem coset_table_second (ω c : K) {k l b : ℕ} (hl : (k + 1) / 2 ≤ l) (hk : l < k) (hb : b < 2 ^ l) :
    (((List.range k).map fun t =>
      let tw := shiftedPowersList (ω ^ 2 ^ t) (c ^ 2 ^ t) (2 ^ k / 2 ^ (t + 1))
      if (k + 1) / 2 ≤ k - 1 - t then revIndex (2 ^ k / 2 ^ (t + 1)) tw else tw).getD (k - 1 - l) []).getD b 0 =
      Tcoset c ω k l (rev l b) := by
  have hlen : 2 ^ k / 2 ^ (k - 1 - l + 1) = 2 ^ l := by rw [pow_div_pow' (by omega)]; congr 1; omega
  rw [List.getD_eq_getElem (d := ([] : List K)) _ (by simp; omega), List.getElem_map, List.getElem_range]
  simp only [show (k + 1) / 2 ≤ k - 1 - (k - 1 - l) by omega, ↓reduceIte, hlen]
  rw [getD_revIndex _ hb, getD_shiftedPowersList _ _ (Plonky3Lean.Proofs.Matrix.bitRev_lt l b), Tcoset,
    mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ (k - 1 - l)) (rev l b)]

theorem foldl_natL_coset (c ω : K) (k : ℕ) (x : ℕ → V) (n : ℕ) :
    (List.range n).foldl (fun acc l => natL (Tcoset c ω k) k l acc) x = ditNetC c ω k n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem natL_localTo (T : ℕ → ℕ → K) {k mid l : ℕ} (hl : l < mid) (hmid : mid ≤ k) :
    LocalTo (2 ^ mid) (2 ^ (k - mid)) (natL (V := V) T k l) := by
  apply layer_localTo _ (by positivity)
  · rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring]; exact Nat.pow_dvd_pow 2 (by omega)
  · rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega

theorem first_half_general_step (ω c : K) {k mid t l : ℕ} (hmid : mid = (k + 1) / 2)
    (ht : t < 2 ^ (k - mid)) (hl : l < mid) (bw : Bool) (acc : ℕ → V) :
    dit_layer t (2 ^ mid) l (fun i => ((cosetTbl ω c k).getD (k - 1 - l) []).getD i 0) bw acc =
      restrict (2 ^ mid) t (natL (Tcoset c ω k) k l) acc := by
  have hdiv : 2 ^ mid / (2 * 2 ^ l) = 2 ^ (mid - 1 - l) := by
    rw [show 2 * 2 ^ l = 2 ^ (l + 1) by ring, pow_div_pow' (by omega)]; congr 1; omega
  have hnb : 2 ^ (mid - 1 - l) * (2 * 2 ^ l) = 2 ^ mid := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hcb : t * 2 ^ (mid - 1 - l) + 2 ^ (mid - 1 - l) ≤ 2 ^ (k - 1 - l) := by
    have : (t + 1) * 2 ^ (mid - 1 - l) ≤ 2 ^ (k - mid) * 2 ^ (mid - 1 - l) :=
      Nat.mul_le_mul_right _ ht
    rw [← pow_add, show k - mid + (mid - 1 - l) = k - 1 - l by omega] at this
    nlinarith
  unfold dit_layer
  dsimp only
  rw [hdiv, pairLoop_chunkOrder _ _ _ (by positivity), layerOn_eq_restrict _ (by positivity)
    (by positivity) hcb, hnb]
  congr 1
  funext z
  exact layer_op_congr (fun b _ s hs => by
    rw [ditButterfly_eq, coset_table_first ω c (by omega) (by omega) hs]) z

theorem first_half_general_spec (ω c : K) (k : ℕ) (x : ℕ → V) :
    ∃ y, first_half_general (2 ^ k) ((k + 1) / 2) (cosetTbl ω c k) x = some y ∧
      ∀ i < 2 ^ k, y i = ditNetC c ω k ((k + 1) / 2) x i := by
  have hmid : (k + 1) / 2 ≤ k := by omega
  refine ⟨_, by simp only [first_half_general, log2Strict_pow, Option.bind_eq_bind,
    Option.bind_some]; rfl, fun i hi => ?_⟩
  rw [pow_div_pow' hmid]
  rw [foldl_congr_mem _ (g := fun acc t =>
      ((List.range ((k + 1) / 2)).map (natL (Tcoset c ω k) k)).foldl
        (fun acc f => restrict (2 ^ ((k + 1) / 2)) t f acc) acc)
    (fun t ht acc => by
      rw [foldl_flag _ (fun l acc => restrict (2 ^ ((k + 1) / 2)) t (natL (Tcoset c ω k) k l) acc) _
        (fun l hl bw => funext fun acc => first_half_general_step ω c rfl (List.mem_range.mp ht)
          (List.mem_range.mp hl) bw acc), List.foldl_map])]
  rw [chunked _ (fun f hf => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
      exact natL_localTo _ (List.mem_range.mp hl) hmid) x
    (by rw [← pow_add, show k - (k + 1) / 2 + (k + 1) / 2 = k by omega]; exact hi),
    List.foldl_map, foldl_natL_coset]

theorem second_half_general_spec (ω c : K) (k : ℕ) (z : ℕ → V) :
    ∃ y, second_half_general (2 ^ k) ((k + 1) / 2) (cosetTbl ω c k) z = some y ∧
      ∀ i < 2 ^ k, y i = (List.range (k - (k + 1) / 2)).foldl
        (fun acc i => revL (Tcoset c ω k) k ((k + 1) / 2 + i) acc) z i := by
  have hmid : (k + 1) / 2 ≤ k := by omega
  refine ⟨_, by simp only [second_half_general, log2Strict_pow, Option.bind_eq_bind,
    Option.bind_some]; rfl, fun i hi => ?_⟩
  rw [show 2 ^ k / 2 ^ (k - (k + 1) / 2) = 2 ^ ((k + 1) / 2) by
    rw [pow_div_pow' (by omega)]; congr 1; omega]
  rw [foldl_congr_mem _ (g := fun acc t =>
      ((List.range (k - (k + 1) / 2)).map (fun i => revL (Tcoset c ω k) k ((k + 1) / 2 + i))).foldl
        (fun acc f => restrict (2 ^ (k - (k + 1) / 2)) t f acc) acc)
    (fun t ht acc => by
      rw [foldl_flag _ (fun i acc => restrict (2 ^ (k - (k + 1) / 2)) t
          (revL (Tcoset c ω k) k ((k + 1) / 2 + i)) acc) _
        (fun i hi bw => funext fun acc => by
          have hi' := List.mem_range.mp hi
          rw [second_half_step (by omega) (by omega) (List.mem_range.mp ht)]
          congr 1
          funext z
          exact layer_op_congr (fun b hb _ _ => by
            rw [ditButterfly_eq, coset_table_second ω c (by omega) (by omega) hb]) z),
        List.foldl_map])]
  rw [chunked _ (fun f hf => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
      exact revL_localTo _ (by omega) (by have := List.mem_range.mp hl; omega)) z
    (by rw [← pow_add, show (k + 1) / 2 + (k - (k + 1) / 2) = k by omega]; exact hi), List.foldl_map]

/-- The in-place coset transform of the parallel backend, read bit-reversed, is the coset network. -/
theorem coset_dft_spec (G : Gen K) {k : ℕ} (hk : k ≤ G.adicity) (c : K) (y : ℕ → V) :
    ∃ z, coset_dft G (2 ^ k) c y = some z ∧
      ∀ i < 2 ^ k, z (rev k i) = ditNetC c (G.gen k) k k y i := by
  have hmid : (k + 1) / 2 ≤ k := by omega
  obtain ⟨y1, hy1, hy1'⟩ := first_half_general_spec (G.gen k) c k y
  obtain ⟨y2, hy2, hy2'⟩ := second_half_general_spec (G.gen k) c k (revRows k y1)
  refine ⟨y2, by simp only [coset_dft, log2Strict_pow, coset_tables G hk, Option.bind_eq_bind,
    Option.bind_some, hy1, hy2], fun i hi => ?_⟩
  have hri := Plonky3Lean.Proofs.Matrix.bitRev_lt k i
  rw [hy2' _ hri, revL_chain_congr _ hmid (z' := fun p => ditNetC c (G.gen k) k ((k + 1) / 2) y (rev k p))
    (fun p hp => by rw [revRows_apply k _ hp, hy1' _ (Plonky3Lean.Proofs.Matrix.bitRev_lt k p)])
    _ le_rfl _ hri, revL_chain _ hmid _ _ le_rfl _ hri, rev_involutive hi, natL_chain_ditNetC,
    show (k + 1) / 2 + (k - (k + 1) / 2) = k by omega]

/-- The parallel backend's coset transform, read through its bit-reversed view, is the coset transform. -/
theorem parallel_coset_dft_batch (G : Gen K) (hG : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (c : K)
    (x : ℕ → V) :
    Computes (Radix2DitParallel.coset_dft_batch G (2 ^ k) c x) (2 ^ k)
      (cosetDft c (G.gen k) (2 ^ k) x) := by
  obtain ⟨z, hz, hz'⟩ := coset_dft_spec G hk c (revRows k x)
  refine ⟨_, by simp only [Radix2DitParallel.coset_dft_batch, log2Strict_pow, Option.bind_eq_bind,
    Option.bind_some, hz]; rfl, fun i hi => ?_⟩
  simp only [bitRev_eq]
  rw [hz' i hi, ditNetC_congr _ _ k (x' := bitRevVec (rev k) x) (fun p hp => by
      rw [revRows_apply k x hp, bitRevVec]) k le_rfl i hi]
  exact ditNetC_eq_cosetDft (hG k hk) x hi

end Plonky3Lean.Proofs.Dft