module

public import Plonky3Lean.Proofs.Dft.Basic

@[expose] public section

/-!
# Layers run chunk by chunk, and the coset network

The parallel backends cut the rows into chunks and run several layers on one chunk before the next.

A layer whose blocks fit in a chunk only mixes rows of the same chunk, so the order does not matter.

The coset network bakes the powers of the shift into the twiddles.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-! ## A layer on a range of blocks -/

section region

variable {W : Type _}

/-- A layer restricted to the blocks lo to hi - 1: rows below lo 2m are left alone. -/
def layerOn (op : ℕ → ℕ → W → W → W × W) (m lo top : ℕ) (x : ℕ → W) : ℕ → W := fun i =>
  if lo * (2 * m) ≤ i then layer op m top x i else x i

/-- Running the butterflies of the blocks lo to hi - 1, in any order, gives the restricted layer. -/
theorem runB_layerList_on (op : ℕ → ℕ → W → W → W × W) (m lo top : ℕ) (hm : 0 < m)
    (order : List (ℕ × ℕ)) (hnd : order.Nodup)
    (hmem : ∀ b s, (b, s) ∈ order ↔ lo ≤ b ∧ b < top ∧ s < m) (x : ℕ → W) :
    runB (layerList op m order) x = layerOn op m lo top x := by
  have hT : (touched (layerList op m order)).Nodup := by
    unfold touched layerList
    rw [List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun bs _ => by simp; omega, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp hnd)
    rintro ⟨b, s⟩ ⟨b', s'⟩ h1 h2 hne
    have hs := ((hmem b s).mp h1).2.2
    have hs' := ((hmem b' s').mp h2).2.2
    simp only [Function.onFun, List.disjoint_cons_left, List.mem_cons, List.not_mem_nil,
      or_false, List.disjoint_nil_left, and_true, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, fun h => ?_⟩
    · obtain ⟨rfl, rfl⟩ := block_inj (m := m) (b := b) (b' := b') (by omega) (by omega) h
      exact hne rfl
    · have := block_inj (m := m) (b := b) (b' := b') (s := s) (s' := s' + m) (by omega) (by omega)
        (by omega)
      omega
    · have := block_inj (m := m) (b := b) (b' := b') (s := s + m) (s' := s') (by omega) (by omega)
        (by omega)
      omega
    · obtain ⟨rfl, h⟩ := block_inj (m := m) (b := b) (b' := b') (s := s + m) (s' := s' + m)
        (by omega) (by omega) (by omega)
      exact hne (by simp; omega)
  funext i
  have hm2 : 0 < 2 * m := by omega
  unfold layerOn layer
  by_cases hlo : lo * (2 * m) ≤ i
  · have hb0 : lo ≤ i / (2 * m) := (Nat.le_div_iff_mul_le hm2).mpr hlo
    rw [ite_eq_left hlo]
    split_ifs with hi hr
    · have hb : i / (2 * m) < top := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
      have he : ((i / (2 * m)) * (2 * m) + i % (2 * m), (i / (2 * m)) * (2 * m) + i % (2 * m) + m,
          op (i / (2 * m)) (i % (2 * m))) ∈ layerList op m order :=
        List.mem_map.mpr ⟨_, (hmem _ _).mpr ⟨hb0, hb, hr⟩, rfl⟩
      have := (runB_pair _ x hT _ he).1
      simp only [Nat.div_add_mod'] at this
      rw [this]
    · have hb : i / (2 * m) < top := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
      have hlt : i % (2 * m) < 2 * m := Nat.mod_lt _ hm2
      have he : ((i / (2 * m)) * (2 * m) + (i % (2 * m) - m),
          (i / (2 * m)) * (2 * m) + (i % (2 * m) - m) + m,
          op (i / (2 * m)) (i % (2 * m) - m)) ∈ layerList op m order :=
        List.mem_map.mpr ⟨_, (hmem _ _).mpr ⟨hb0, hb, by omega⟩, rfl⟩
      have := (runB_pair _ x hT _ he).2
      have hd := Nat.div_add_mod' i (2 * m)
      have e1 : i / (2 * m) * (2 * m) + (i % (2 * m) - m) + m = i := by omega
      have e2 : i / (2 * m) * (2 * m) + (i % (2 * m) - m) = i - m := by omega
      rw [e1, e2] at this
      rw [this]
    · rw [runB_untouched]
      unfold touched layerList
      simp only [List.flatMap_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
        not_exists, not_and, Prod.forall]
      intro b s h
      obtain ⟨-, hb, hs⟩ := (hmem b s).mp h
      have : (b + 1) * (2 * m) ≤ top * (2 * m) := Nat.mul_le_mul_right _ hb
      have h1 : b * (2 * m) + s < top * (2 * m) := by nlinarith
      have h2 : b * (2 * m) + s + m < top * (2 * m) := by nlinarith
      exact fun hc => hc.elim (fun hc => hi (hc ▸ h1)) (fun hc => hi (hc ▸ h2))
  · rw [ite_eq_right hlo, runB_untouched]
    unfold touched layerList
    simp only [List.flatMap_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
      not_exists, not_and, Prod.forall]
    intro b s h
    obtain ⟨hb, -, -⟩ := (hmem b s).mp h
    have : lo * (2 * m) ≤ b * (2 * m) := Nat.mul_le_mul_right _ hb
    exact fun hc => hc.elim (fun hc => hlo (by omega)) (fun hc => hlo (by omega))

/-! ## Chunks -/

/-- Each row below C S depends only on the rows of its own chunk of S rows. -/
def LocalTo (S C : ℕ) (f : (ℕ → W) → ℕ → W) : Prop :=
  ∀ x x' i, i < C * S → (∀ p, p / S = i / S → x p = x' p) → f x i = f x' i

/-- An operation applied to chunk c only. -/
def restrict (S c : ℕ) (f : (ℕ → W) → ℕ → W) (x : ℕ → W) : ℕ → W := fun i =>
  if i / S = c then f x i else x i

theorem localTo_foldl {S C : ℕ} (fs : List ((ℕ → W) → ℕ → W)) (h : ∀ f ∈ fs, LocalTo S C f) :
    LocalTo S C (fun x => fs.foldl (fun acc f => f acc) x) := by
  induction fs using List.reverseRecOn with
  | nil => intro x x' i _ hx; exact hx i rfl
  | append_singleton fs f ih =>
    intro x x' i hi hx
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine h f (by simp) _ _ i hi (fun p hp => ?_)
    have hpC : p < C * S := by
      rcases Nat.eq_zero_or_pos S with h0 | h0
      · subst h0; simp at hi
      · have := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi : i < S * C)
        rw [← hp] at this
        exact Nat.lt_mul_of_div_lt this h0
    exact ih (fun f hf => h f (by simp [hf])) x x' p hpC (fun q hq => hx q (hq.trans hp))

theorem restrict_foldl {S C c : ℕ} (hS : 0 < S) (hc : c < C) (fs : List ((ℕ → W) → ℕ → W))
    (h : ∀ f ∈ fs, LocalTo S C f) (y : ℕ → W) (i : ℕ) :
    fs.foldl (fun acc f => restrict S c f acc) y i =
      if i / S = c then fs.foldl (fun acc f => f acc) y i else y i := by
  induction fs using List.reverseRecOn generalizing i with
  | nil => simp
  | append_singleton fs f ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, restrict]
    split_ifs with hic
    · have hiC : i < C * S := Nat.lt_mul_of_div_lt (show i / S < C by omega) hS
      refine h f (by simp) _ _ i hiC (fun p hp => ?_)
      rw [ih (fun f hf => h f (by simp [hf])) p, ite_eq_left (hp.trans hic)]
    · rw [ih (fun f hf => h f (by simp [hf])) i, ite_eq_right hic]

/-- Running every operation on chunk 0, then on chunk 1, and so on, is running them on all rows. -/
theorem chunked {S C : ℕ} (fs : List ((ℕ → W) → ℕ → W)) (h : ∀ f ∈ fs, LocalTo S C f)
    (x : ℕ → W) {i : ℕ} (hi : i < C * S) :
    (List.range C).foldl (fun acc c => fs.foldl (fun acc f => restrict S c f acc) acc) x i =
      fs.foldl (fun acc f => f acc) x i := by
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; simp at hi
    · exact h0
  have hloc := localTo_foldl fs h
  have key : ∀ c ≤ C, ∀ i < C * S,
      (List.range c).foldl (fun acc c => fs.foldl (fun acc f => restrict S c f acc) acc) x i =
        if i / S < c then fs.foldl (fun acc f => f acc) x i else x i := by
    intro c
    induction c with
    | zero => intro _ i _; simp
    | succ c ih =>
      intro hc i hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        restrict_foldl hS (by omega) fs h]
      split_ifs with h1 h2 h2
      · refine hloc _ _ i hi (fun p hp => ?_)
        have hpC : p < C * S := Nat.lt_mul_of_div_lt (show p / S < C by omega) hS
        rw [ih (by omega) p hpC, ite_eq_right (by omega)]
      · omega
      · rw [ih (by omega) i hi, ite_eq_left (by omega)]
      · rw [ih (by omega) i hi, ite_eq_right (by omega)]
  rw [key C le_rfl i hi, ite_eq_left (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi))]

/-- A layer whose blocks of 2m rows divide the chunks of S rows is local to the chunks. -/
theorem layer_localTo (op : ℕ → ℕ → W → W → W × W) {m nb S C : ℕ} (hm : 0 < m)
    (hdvd : 2 * m ∣ S) (hsz : nb * (2 * m) = C * S) : LocalTo S C (layer op m nb) := by
  intro x x' i hi hx
  obtain ⟨q, hq⟩ := hdvd
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; simp at hi
    · exact h0
  have same : ∀ p, p / (2 * m) = i / (2 * m) → p / S = i / S := by
    intro p hp
    rw [hq, ← Nat.div_div_eq_div_mul p (2 * m) q, ← Nat.div_div_eq_div_mul i (2 * m) q, hp]
  have hm2 : 0 < 2 * m := by omega
  have hd := Nat.div_add_mod' i (2 * m)
  have hlt := Nat.mod_lt i hm2
  have hin : i < nb * (2 * m) := by omega
  unfold layer
  simp only [hin, ↓reduceIte]
  split_ifs with hr
  · have h1 : (i + m) / (2 * m) = i / (2 * m) := by
      rw [show i + m = i / (2 * m) * (2 * m) + (i % (2 * m) + m) by omega, dm_div (by omega)]
    rw [hx i rfl, hx (i + m) (same _ h1)]
  · have h1 : (i - m) / (2 * m) = i / (2 * m) := by
      rw [show i - m = i / (2 * m) * (2 * m) + (i % (2 * m) - m) by omega, dm_div (by omega)]
    rw [hx i rfl, hx (i - m) (same _ h1)]

end region

/-! ## The coset network -/

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The decimation-in-time network with the shift c baked in: layer l uses (c omega^s)^(2^(k-1-l)). -/
def ditNetC (c ω : K) (k : ℕ) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => ditLayer (2 ^ l) (2 ^ (k - 1 - l)) (fun _ s => (c * ω ^ s) ^ 2 ^ (k - 1 - l))
      (ditNetC c ω k l x)

theorem ditNetC_apply {c ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) :
    ∀ L ≤ k, ∀ b < 2 ^ (k - L), ∀ t < 2 ^ L,
      ditNetC c ω k L (bitRevVec (rev k) x) (b * 2 ^ L + t) =
        ∑ m ∈ range (2 ^ L), ((c * ω ^ t) ^ (2 ^ (k - L) * m)) •
          x (rev (k - L) b + 2 ^ (k - L) * m) := by
  intro L
  induction L with
  | zero =>
    intro _ b _ t ht
    simp at ht; subst ht
    simp [ditNetC, bitRevVec]
  | succ L ih =>
    intro hL B hB r hr
    obtain ⟨j, rfl⟩ : ∃ j, k = L + 1 + j := ⟨k - (L + 1), by omega⟩
    have e1 : L + 1 + j - (L + 1) = j := by omega
    have e2 : L + 1 + j - L = j + 1 := by omega
    have e3 : L + 1 + j - 1 - L = j := by omega
    rw [e1] at hB ⊢
    have ih' := ih (by omega)
    rw [e2] at ih'
    have hneg : ω ^ (2 ^ (L + j)) = -1 :=
      neg_one_of_primitive (j := L + j) (by rw [show L + j + 1 = L + 1 + j by ring]; exact hω)
    simp only [ditNetC, ditLayer, layer, e3, dit]
    have hsz : B * 2 ^ (L + 1) + r < 2 ^ j * (2 * 2 ^ L) := by
      have : (B + 1) * 2 ^ (L + 1) ≤ 2 ^ j * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hB
      have hr' : r < 2 ^ L * 2 := by rw [← pow_succ]; exact hr
      rw [pow_succ] at this ⊢; nlinarith
    have hmod : (B * 2 ^ (L + 1) + r) % (2 * 2 ^ L) = r := by
      rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    simp only [hsz, ↓reduceIte, hmod]
    have hsplit : ∀ f : ℕ → V, ∑ m ∈ range (2 ^ (L + 1)), f m =
        ∑ m ∈ range (2 ^ L), f (2 * m) + ∑ m ∈ range (2 ^ L), f (2 * m + 1) := fun f => by
      rw [pow_succ, mul_comm, sum_range_two_mul]
    rw [hsplit]
    split_ifs with hrl
    · have i1 : B * 2 ^ (L + 1) + r = (2 * B) * 2 ^ L + r := by ring
      have i2 : B * 2 ^ (L + 1) + r + 2 ^ L = (2 * B + 1) * 2 ^ L + r := by ring
      rw [i2, i1, ih' (2 * B) (by rw [pow_succ]; omega) r hrl,
        ih' (2 * B + 1) (by rw [pow_succ]; omega) r hrl, rev_double, rev_double_add_one, smul_sum]
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        congr 2
        · ring
        · ring
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add]
        congr 2
        · ring
        · ring
    · obtain ⟨t, rfl⟩ : ∃ t, r = 2 ^ L + t := ⟨r - 2 ^ L, by omega⟩
      have ht : t < 2 ^ L := by rw [pow_succ] at hr; omega
      have i1 : B * 2 ^ (L + 1) + (2 ^ L + t) - 2 ^ L = (2 * B) * 2 ^ L + t := by
        rw [pow_succ]; ring_nf; omega
      have i2 : B * 2 ^ (L + 1) + (2 ^ L + t) = (2 * B + 1) * 2 ^ L + t := by ring
      rw [i1, i2, ih' (2 * B) (by rw [pow_succ]; omega) t ht,
        ih' (2 * B + 1) (by rw [pow_succ]; omega) t ht, rev_double, rev_double_add_one, smul_sum,
        show 2 ^ L + t - 2 ^ L = t by omega, sub_eq_add_neg, ← sum_neg_distrib]
      have hshift : ∀ e, (c * ω ^ (2 ^ L + t)) ^ (2 ^ j * e) = (c * ω ^ t) ^ (2 ^ j * e) * (-1) ^ e := by
        intro e
        have h1 : c * ω ^ (2 ^ L + t) = (c * ω ^ t) * ω ^ 2 ^ L := by rw [pow_add]; ring
        have h2 : (ω ^ 2 ^ L) ^ (2 ^ j * e) = (-1) ^ e := by
          rw [← pow_mul, show 2 ^ L * (2 ^ j * e) = 2 ^ (L + j) * e by ring, pow_mul, hneg]
        rw [h1, mul_pow, h2]
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        congr 1
        · rw [hshift, Even.neg_one_pow ⟨m, by ring⟩, mul_one]
          congr 1; ring
        · congr 1; ring
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add, ← neg_smul]
        congr 1
        · rw [hshift, Odd.neg_one_pow ⟨m, rfl⟩, mul_neg_one]
          congr 2; ring
        · congr 1; ring

/-- The coset network on bit-reversed input computes the coset transform. -/
theorem ditNetC_eq_cosetDft {c ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : ditNetC c ω k k (bitRevVec (rev k) x) i = cosetDft c ω (2 ^ k) x i := by
  have := ditNetC_apply (c := c) hω x k le_rfl 0 (by simp) i hi
  simp only [zero_mul, zero_add, Nat.sub_self, pow_zero, one_mul] at this
  rw [this, cosetDft]
  refine sum_congr rfl fun m _ => ?_
  simp [Plonky3Lean.Spec.Matrix.bitRev]

theorem ditNetC_one (ω : K) (k : ℕ) : ∀ L, (ditNetC 1 ω k L : (ℕ → V) → ℕ → V) = ditNet ω k L := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih =>
    funext x
    simp only [ditNetC, ditNet, ih, one_mul, ← pow_mul]

/-- The coset network reads only the first 2^k rows. -/
theorem ditNetC_congr (c ω : K) (k : ℕ) {x x' : ℕ → V} (h : ∀ p < 2 ^ k, x p = x' p) :
    ∀ L ≤ k, ∀ i < 2 ^ k, ditNetC c ω k L x i = ditNetC c ω k L x' i := by
  intro L
  induction L with
  | zero => intro _ i hi; exact h i hi
  | succ L ih =>
    intro hL i hi
    have hsz : 2 ^ (k - 1 - L) * (2 * 2 ^ L) = 2 ^ k := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    simp only [ditNetC, ditLayer]
    exact layer_congr _ _ _ (fun p hp => ih (by omega) p (hsz ▸ hp)) (hsz ▸ hi)

end Plonky3Lean.Proofs.Dft
