module

public import Plonky3Lean.Proofs.ZkCodes.ReedSolomon

@[expose] public section

/-!
# The simulator against the real codeword

The simulator gives the k-th distinct position the k-th draw, in order of first appearance.

With a uniform draw, its output has the distribution of the real codeword at the queried positions.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.ZkCodes

open Finset Polynomial p3_dft.mirror Plonky3Lean.Spec.Dft Plonky3Lean.Spec.ZkCodes
open p3_zk_codes.reed_solomon.mirror Plonky3Lean.Proofs.Dft

variable {K : Type _} [Field K]

/-! ## The distinct positions -/

/-- The distinct positions of Q after those of ks, in order of first appearance. -/
def keysFrom (ks : List ℕ) : List ℕ → List ℕ
  | [] => ks
  | p :: Q => keysFrom (if p ∈ ks then ks else ks ++ [p]) Q

/-- The distinct positions of Q, in order of first appearance. -/
def keys (Q : List ℕ) : List ℕ := keysFrom [] Q

theorem keysFrom_prefix (ks Q : List ℕ) : ∃ e, keysFrom ks Q = ks ++ e := by
  induction Q generalizing ks with
  | nil => exact ⟨[], by simp [keysFrom]⟩
  | cons p Q ih =>
    obtain ⟨e, he⟩ := ih (if p ∈ ks then ks else ks ++ [p])
    simp only [keysFrom]
    by_cases h : p ∈ ks
    · simp only [h, ↓reduceIte] at he ⊢; exact ⟨e, he⟩
    · simp only [h, ↓reduceIte] at he ⊢; exact ⟨p :: e, by simpa using he⟩

theorem keysFrom_nodup {ks : List ℕ} (h : ks.Nodup) (Q : List ℕ) : (keysFrom ks Q).Nodup := by
  induction Q generalizing ks with
  | nil => exact h
  | cons p Q ih =>
    refine ih ?_
    split_ifs with hp
    · exact h
    · exact h.append (List.nodup_singleton p) (by simpa using hp)

theorem mem_keysFrom {ks Q : List ℕ} {p : ℕ} : p ∈ keysFrom ks Q ↔ p ∈ ks ∨ p ∈ Q := by
  induction Q generalizing ks with
  | nil => simp [keysFrom]
  | cons q Q ih =>
    rw [keysFrom, ih]
    by_cases hq : q ∈ ks
    · simp only [hq, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hq)
        · exact Or.inr h
    · simp only [hq, ↓reduceIte, List.mem_append, List.mem_cons]; tauto

theorem keys_nodup (Q : List ℕ) : (keys Q).Nodup := keysFrom_nodup List.nodup_nil Q

theorem mem_keys {Q : List ℕ} {p : ℕ} : p ∈ keys Q ↔ p ∈ Q := by simp [keys, mem_keysFrom]

/-! ## The simulator's loop -/

/-- The cache after seeing the positions ks: position ks_k holds draw k. -/
def cacheOf (draw : ℕ → K) (ks : List ℕ) : List (ℕ × K) :=
  (List.range ks.length).map fun k => (ks.getD k 0, draw k)

theorem cacheOf_length (draw : ℕ → K) (ks : List ℕ) : (cacheOf draw ks).length = ks.length := by
  simp [cacheOf]

theorem cacheOf_snoc (draw : ℕ → K) (ks : List ℕ) (p : ℕ) :
    cacheOf draw (ks ++ [p]) = cacheOf draw ks ++ [(p, draw ks.length)] := by
  simp only [cacheOf, List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hk)]
  · simp

theorem find_cacheOf_not_mem (draw : ℕ → K) {ks : List ℕ} {p : ℕ} (hp : p ∉ ks) :
    (cacheOf draw ks).find? (fun q => q.1 == p) = none := by
  rw [List.find?_eq_none]
  intro q hq
  simp only [cacheOf, List.mem_map, List.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  simp only [beq_iff_eq]
  rintro rfl
  exact hp (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)

theorem find_cacheOf_mem (draw : ℕ → K) {ks : List ℕ} (hnd : ks.Nodup) {p : ℕ} (hp : p ∈ ks) :
    (cacheOf draw ks).find? (fun q => q.1 == p) = some (p, draw (ks.idxOf p)) := by
  induction ks using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton ks x ih =>
    rw [cacheOf_snoc, List.find?_append]
    have hnd' : ks.Nodup := hnd.sublist (List.sublist_append_left _ _)
    by_cases hpk : p ∈ ks
    · rw [ih hnd' hpk, List.idxOf_append_of_mem hpk]; rfl
    · have hx : p = x := by simpa [hpk] using hp
      subst hx
      rw [find_cacheOf_not_mem draw hpk, List.idxOf_append_of_notMem hpk]
      simp

theorem foldl_simStep (draw : ℕ → K) (Q : List ℕ) {ks : List ℕ} (hnd : ks.Nodup) (out : List K) :
    Q.foldl (simStep draw) (cacheOf draw ks, out) =
      (cacheOf draw (keysFrom ks Q), out ++ Q.map fun p => draw ((keysFrom ks Q).idxOf p)) := by
  induction Q generalizing ks out with
  | nil => simp [keysFrom]
  | cons p Q ih =>
    rw [List.foldl_cons]
    by_cases hp : p ∈ ks
    · have hstep : simStep draw (cacheOf draw ks, out) p =
          (cacheOf draw ks, out ++ [draw (ks.idxOf p)]) := by
        simp [simStep, find_cacheOf_mem draw hnd hp]
      rw [hstep, ih hnd, keysFrom]
      simp only [hp, ↓reduceIte]
      obtain ⟨e, he⟩ := keysFrom_prefix ks Q
      simp [he, List.idxOf_append_of_mem hp]
    · have hstep : simStep draw (cacheOf draw ks, out) p =
          (cacheOf draw (ks ++ [p]), out ++ [draw ks.length]) := by
        simp [simStep, find_cacheOf_not_mem draw hp, cacheOf_length, cacheOf_snoc]
      have hnd' : (ks ++ [p]).Nodup := hnd.append (List.nodup_singleton p) (by simpa using hp)
      rw [hstep, ih hnd', keysFrom]
      simp only [hp, ↓reduceIte]
      obtain ⟨e, he⟩ := keysFrom_prefix (ks ++ [p]) Q
      have hidx : (ks ++ p :: e).idxOf p = ks.length := by
        rw [List.idxOf_append_of_notMem hp]
        simp
      simp [he, hidx]

/-- At each queried position, the simulator returns the draw of its rank among the distinct positions.

It panics exactly when there are more than t distinct positions, whatever the positions are. -/
theorem simulate_eq (rs : ReedSolomonZkEncoding) (Q : List ℕ) (draw : ℕ → K) :
    rs.simulate Q draw =
      if (keys Q).length ≤ rs.t then some (Q.map fun p => draw ((keys Q).idxOf p)) else none := by
  have := foldl_simStep draw Q List.nodup_nil []
  simp only [cacheOf, List.length_nil, List.range_zero, List.map_nil, List.nil_append] at this
  simp only [ReedSolomonZkEncoding.simulate, this, keys, List.length_map, List.length_range]
  by_cases h : (keysFrom [] Q).length ≤ rs.t <;> simp [h]


/-! ## The simulator's output has the real distribution -/

omit [Field K] in
theorem pushUniform_comp_apply {α β γ : Type _} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (g : α → β) (Φ : β → γ) (y : γ) :
    pushUniform (Φ ∘ g) y = ∑ z ∈ univ.filter (fun z => Φ z = y), pushUniform g z := by
  simp only [pushUniform, ← Finset.sum_div, Function.comp]
  congr 1
  have := Finset.card_eq_sum_card_fiberwise (s := univ.filter fun a => Φ (g a) = y)
    (t := univ.filter fun z => Φ z = y) (f := g) (fun a ha => by simpa using ha)
  rw [this, Nat.cast_sum]
  refine sum_congr rfl fun z hz => ?_
  congr 2
  ext a
  simp only [mem_filter, mem_univ, true_and] at hz ⊢
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hz, h⟩

omit [Field K] in
theorem pushUniform_comp {α₁ α₂ β γ : Type _} [Fintype α₁] [Fintype α₂] [Fintype β] [DecidableEq β]
    [DecidableEq γ] {g₁ : α₁ → β} {g₂ : α₂ → β} (h : pushUniform g₁ = pushUniform g₂) (Φ : β → γ) :
    pushUniform (Φ ∘ g₁) = pushUniform (Φ ∘ g₂) := by
  funext y
  rw [pushUniform_comp_apply, pushUniform_comp_apply, h]

omit [Field K] in
theorem pushUniform_id {β : Type _} [Fintype β] [DecidableEq β] [Nonempty β] :
    pushUniform (id : β → β) = uniform β :=
  pushUniform_eq_uniform _ fun y => by
    have : (univ.filter fun a : β => id a = y) = {y} := by ext; simp
    rw [this, card_singleton, one_mul]

variable [Fintype K] [DecidableEq K]

/-- Message part plus mask part, at d <= t distinct nonzero points: uniform. -/
theorem pushUniform_mask {ι : Type _} [Fintype ι] [DecidableEq ι] (l t : ℕ) {x : ι → K}
    (hx : Function.Injective x) (h0 : ∀ i, x i ≠ 0) (hcard : Fintype.card ι ≤ t) (b : ι → K) :
    pushUniform (fun ρ : Fin t → K => b + maskMap l t x ρ) = uniform (ι → K) :=
  pushUniform_eq_uniform _ (card_fiber_mul (maskMap l t x).toAddMonoidHom
    (maskMap_surjective l t hx h0 hcard) b)

/-- The extension of s to a stream of draws: draw n is s_n below the length, zero after. -/
def ext {d : ℕ} (s : Fin d → K) (n : ℕ) : K := if h : n < d then s ⟨n, h⟩ else 0

/-- Take a message of length l and at most t distinct queried positions below m = 2^k.

The codeword at those positions has the distribution of the simulator's output.

Both are some list, and the lists agree in distribution, duplicates included. -/
theorem simulate_matches_encode (G : Gen K) (hG : GenValid G) {t l k : ℕ} (hk : k ≤ G.adicity)
    (hle : l + t ≤ 2 ^ k) {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    (hd : ∀ x, Computes (dft_batch (2 ^ k) x) (2 ^ k) (dft (G.gen k) (2 ^ k) x)) {msg : List K}
    (hmsg : msg.length = l) {Q : List ℕ} (hQ : ∀ p ∈ Q, p < 2 ^ k) (hQt : (keys Q).length ≤ t) :
    pushUniform (fun ρ : Fin t → K =>
        ((ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch msg
          (List.ofFn ρ)).map (Q.map ·)) =
      pushUniform (fun s : Fin (keys Q).length → K =>
        (ReedSolomonZkEncoding.mk t l (2 ^ k)).simulate Q (ext s)) := by
  set ks := keys Q with hks
  set d := ks.length with hd_def
  set ω := G.gen k with hω_def
  have hω : IsPrimitiveRoot ω (2 ^ k) := hG k hk
  have hmemks : ∀ p ∈ Q, p ∈ ks := fun p hp => mem_keys.mpr hp
  have hidx : ∀ p ∈ Q, ks.idxOf p < d := fun p hp => List.idxOf_lt_length_iff.mpr (hmemks p hp)
  let Φ : (Fin d → K) → Option (List K) := fun v =>
    some (Q.map fun p => if h : ks.idxOf p < d then v ⟨_, h⟩ else 0)
  let v : (Fin t → K) → Fin d → K := fun ρ i => encValue msg (List.ofFn ρ) (ω ^ ks[i])
  have hL : (fun ρ : Fin t → K =>
      ((ReedSolomonZkEncoding.mk t l (2 ^ k)).encode_with_randomness dft_batch msg
        (List.ofFn ρ)).map (Q.map ·)) = Φ ∘ v := by
    funext ρ
    obtain ⟨y, hy, hyi⟩ := encode_with_randomness_computes (rs := ⟨t, l, 2 ^ k⟩) (ω := ω) hd
      hle hmsg (List.length_ofFn (f := ρ))
    rw [hy, Option.map_some, Function.comp_apply]
    simp only [Φ, v, Option.some.injEq]
    refine List.map_congr_left fun p hp => ?_
    simp only [hidx p hp, ↓reduceDIte, Fin.getElem_fin]
    rw [hyi p (hQ p hp), List.getElem_idxOf]
  have hR : (fun s : Fin d → K => (ReedSolomonZkEncoding.mk t l (2 ^ k)).simulate Q (ext s)) =
      Φ ∘ id := by
    funext s
    rw [simulate_eq]
    simp only [← hks, ← hd_def, hQt, ↓reduceIte]
    rfl
  rw [hL, hR]
  refine pushUniform_comp ?_ Φ
  rw [pushUniform_id]
  have hx : Function.Injective fun i : Fin d => ω ^ ks[i] := by
    intro i j hij
    have hi : ks[i] < 2 ^ k := hQ _ (mem_keys.mp (List.getElem_mem _))
    have hj : ks[j] < 2 ^ k := hQ _ (mem_keys.mp (List.getElem_mem _))
    have := hω.pow_inj hi hj hij
    exact Fin.ext ((keys_nodup Q).getElem_inj_iff.mp this)
  have h0 : ∀ i : Fin d, ω ^ ks[i] ≠ 0 := fun i => pow_ne_zero _ (hω.ne_zero (by positivity))
  have hv : v = fun ρ => (fun i : Fin d => ∑ j ∈ range msg.length, msg.getD j 0 * (ω ^ ks[i]) ^ j) +
      maskMap l t (fun i : Fin d => ω ^ ks[i]) ρ := by
    funext ρ i
    simp only [v, encValue, Pi.add_apply, maskMap, LinearMap.coe_mk, AddHom.coe_mk,
      List.length_ofFn, hmsg]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun j => (List.ofFn ρ).getD j 0 * (ω ^ ks[i]) ^ (l + j))]
    simp [List.getD_eq_getElem?_getD]
  rw [hv]
  exact pushUniform_mask l t hx h0 (by simpa using hQt) _

end Plonky3Lean.Proofs.ZkCodes
