module

public import Plonky3Lean.Proofs.Dft.Network
public import Plonky3Lean.Proofs.Dft.Algebra

@[expose] public section

/-!
# The objects of the transcriptions

This file covers:

- the logarithm and the generators
- the in-place bit reversal
- the loops over butterflies
- the twiddle tables
- the coset shift and the division by the height
- the bit-reversed form of a layer.

Conjugating a layer by the bit reversal of the rows exchanges the block and offset roles.

It also bit-reverses the twiddles.
-/

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-! ## Logarithm and generators -/

theorem log2Strict_pow (k : ℕ) : log2Strict (2 ^ k) = some k := by
  simp [log2Strict, Nat.log_pow (by norm_num : 1 < 2)]

theorem log2Strict_eq_none {h : ℕ} (hh : ∀ k, h ≠ 2 ^ k) : log2Strict h = none := by
  unfold log2Strict
  rw [ite_eq_right]
  rintro ⟨_, h2⟩
  exact hh _ h2.symm

theorem log2Strict_eq_some {h k : ℕ} (hk : log2Strict h = some k) : h = 2 ^ k := by
  unfold log2Strict at hk
  split_ifs at hk with hh
  · cases hk; exact hh.2.symm

/-- The generators the field promises.

Entry b generates the subgroup of order 2^b, for b up to the adicity. -/
def GenValid {K : Type _} [Field K] (G : Gen K) : Prop :=
  ∀ b ≤ G.adicity, IsPrimitiveRoot (G.gen b) (2 ^ b)

/-- The generators are nested: each squares to the one before it. -/
def GenNested {K : Type _} [Field K] (G : Gen K) : Prop :=
  ∀ b < G.adicity, G.gen (b + 1) ^ 2 = G.gen b

theorem gen_get_of_le {K : Type _} (G : Gen K) {b : ℕ} (hb : b ≤ G.adicity) :
    G.get b = some (G.gen b) := by simp [Gen.get, hb]

theorem gen_get_of_lt {K : Type _} (G : Gen K) {b : ℕ} (hb : G.adicity < b) : G.get b = none := by
  simp [Gen.get]; omega

/-- With nested generators, entry k + a raised to 2^a is entry k. -/
theorem nested_pow {K : Type _} [Field K] {G : Gen K} (hG : GenNested G) {k a : ℕ}
    (h : k + a ≤ G.adicity) : G.gen (k + a) ^ 2 ^ a = G.gen k := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show k + (a + 1) = (k + a) + 1 by ring, pow_succ', pow_mul, hG _ (by omega), ih (by omega)]

/-! ## In-place bit reversal -/

theorem revRows_apply {V : Type _} (k : ℕ) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    revRows k x i = x (rev k i) := by
  unfold revRows
  rw [dite_eq_left hi, Plonky3Lean.Proofs.Matrix.BitRevSwap.reverse_matrix_index_bits_eq]
  · simp [bitRev_eq, Nat.mod_eq_of_lt (Plonky3Lean.Proofs.Matrix.bitRev_lt k i)]
  · intro r
    apply Fin.ext
    simp [bitRev_eq, Nat.mod_eq_of_lt (Plonky3Lean.Proofs.Matrix.bitRev_lt _ _),
      Plonky3Lean.Proofs.Matrix.bitRev_bitRev r.isLt, Nat.mod_eq_of_lt r.isLt]

/-! ## Loops over butterflies -/

theorem pairLoop_eq_runB {V : Type _} (order : List (ℕ × ℕ)) (m : ℕ)
    (op : ℕ → ℕ → V → V → V × V) (x : ℕ → V) :
    pairLoop order m op x = runB (layerList op m order) x := by
  simp [pairLoop, runB, layerList, List.foldl_map]

theorem blocks_eq (nb m : ℕ) : p3_dft.mirror.blocks nb m = blockOrder nb m := rfl

/-- The block loop, blocks outer and pairs inner, is the layer. -/
theorem pairLoop_blocks {V : Type _} (nb m : ℕ) (hm : 0 < m) (op : ℕ → ℕ → V → V → V × V)
    (x : ℕ → V) : pairLoop (p3_dft.mirror.blocks nb m) m op x = layer op m nb x := by
  rw [pairLoop_eq_runB, blocks_eq,
    runB_layerList op m nb hm _ (blockOrder_nodup nb m) (mem_blockOrder nb m)]

/-- A layer reads only the rows below nb 2m to write those rows. -/
theorem layer_congr {V : Type _} (op : ℕ → ℕ → V → V → V × V) (m nb : ℕ) {x x' : ℕ → V}
    (h : ∀ p < nb * (2 * m), x p = x' p) {i : ℕ} (hi : i < nb * (2 * m)) :
    layer op m nb x i = layer op m nb x' i := by
  unfold layer
  rw [ite_eq_left hi, ite_eq_left hi]
  have hm : 0 < 2 * m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hi
    · omega
  split_ifs with hr
  · have : i + m < nb * (2 * m) := by
      have h1 := Nat.div_add_mod i (2 * m)
      have h2 : i / (2 * m) < nb := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)
      have h3 : (i / (2 * m) + 1) * (2 * m) ≤ nb * (2 * m) := Nat.mul_le_mul_right _ h2
      nlinarith
    rw [h i hi, h (i + m) this]
  · rw [h i hi, h (i - m) (by omega)]

/-- A layer leaves the rows at nb 2m and above alone. -/
theorem layer_of_ge {V : Type _} (op : ℕ → ℕ → V → V → V × V) (m nb : ℕ) (x : ℕ → V) {i : ℕ}
    (hi : nb * (2 * m) ≤ i) : layer op m nb x i = x i := by
  unfold layer; rw [ite_eq_right (by omega)]

/-! ## The bit-reversed form of a layer -/

theorem rev_upper (j : ℕ) {r : ℕ} (hr : r < 2 ^ j) : rev (j + 1) r = 2 * rev j r := by
  have := rev_split j 1 0 r hr
  simp only [zero_mul, zero_add] at this
  rw [this]; simp [Plonky3Lean.Spec.Matrix.bitRev]; ring

theorem rev_lower (j : ℕ) {t : ℕ} (ht : t < 2 ^ j) : rev (j + 1) (2 ^ j + t) = 2 * rev j t + 1 := by
  have := rev_split j 1 1 t ht
  simp only [one_mul] at this
  rw [this]; simp [Plonky3Lean.Spec.Matrix.bitRev]; ring

theorem dm_div {σ r m : ℕ} (hr : r < m) : (σ * m + r) / m = σ := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]

theorem dm_mod {σ r m : ℕ} (hr : r < m) : (σ * m + r) % m = r := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- Conjugating a layer by the bit reversal exchanges the roles of blocks and offsets.

Take a layer with half block 2^L, whose twiddle depends on the offset s.

It becomes a layer with half block 2^j, whose block sigma uses the twiddle of offset rev_L(sigma). -/
theorem conj_layer {K V : Type _} (f : K → V → V → V × V) (tw : ℕ → K) (L j : ℕ) (y : ℕ → V)
    {i : ℕ} (hi : i < 2 ^ (L + 1 + j)) :
    layer (fun _ s => f (tw s)) (2 ^ L) (2 ^ j) y (rev (L + 1 + j) i) =
      layer (fun σ _ => f (tw (rev L σ))) (2 ^ j) (2 ^ L) (fun p => y (rev (L + 1 + j) p)) i := by
  have hm : 0 < 2 * 2 ^ j := by positivity
  obtain ⟨σ, r, rfl, hr⟩ : ∃ σ r, i = σ * (2 * 2 ^ j) + r ∧ r < 2 * 2 ^ j :=
    ⟨i / (2 * 2 ^ j), i % (2 * 2 ^ j), (Nat.div_add_mod' i _).symm, Nat.mod_lt _ hm⟩
  have hsz : 2 ^ (L + 1 + j) = 2 ^ L * (2 * 2 ^ j) := by ring
  have hσ : σ < 2 ^ L := by
    by_contra h
    have : 2 ^ L * (2 * 2 ^ j) ≤ σ * (2 * 2 ^ j) := Nat.mul_le_mul_right _ (not_lt.mp h)
    omega
  have hrevi : rev (L + 1 + j) (σ * (2 * 2 ^ j) + r) = rev (j + 1) r * 2 ^ L + rev L σ := by
    rw [show σ * (2 * 2 ^ j) = σ * 2 ^ (j + 1) by ring, show L + 1 + j = (j + 1) + L by ring,
      rev_split (j + 1) L σ r (by rw [pow_succ]; omega)]
  have hβ : rev L σ < 2 ^ L := Plonky3Lean.Proofs.Matrix.bitRev_lt L σ
  have hA : rev (L + 1 + j) (σ * (2 * 2 ^ j) + r) < 2 ^ j * (2 * 2 ^ L) := by
    rw [show 2 ^ j * (2 * 2 ^ L) = 2 ^ (L + 1 + j) by ring]
    exact Plonky3Lean.Proofs.Matrix.bitRev_lt _ _
  have hB : σ * (2 * 2 ^ j) + r < 2 ^ L * (2 * 2 ^ j) := by
    have : (σ + 1) * (2 * 2 ^ j) ≤ 2 ^ L * (2 * 2 ^ j) := Nat.mul_le_mul_right _ hσ
    nlinarith
  unfold layer
  simp only [hA, hB, ↓reduceIte, dm_div hr, dm_mod hr]
  by_cases hup : r < 2 ^ j
  · have hP : rev (L + 1 + j) (σ * (2 * 2 ^ j) + r) = rev j r * (2 * 2 ^ L) + rev L σ := by
      rw [hrevi, rev_upper j hup]; ring
    have hpartner : rev (L + 1 + j) (σ * (2 * 2 ^ j) + r + 2 ^ j) =
        rev j r * (2 * 2 ^ L) + rev L σ + 2 ^ L := by
      rw [show σ * (2 * 2 ^ j) + r + 2 ^ j = σ * 2 ^ (j + 1) + (2 ^ j + r) by ring,
        show L + 1 + j = (j + 1) + L by ring, rev_split (j + 1) L σ _ (by rw [pow_succ]; omega),
        rev_lower j hup]
      ring
    rw [hpartner, hP]
    simp only [hup, ↓reduceIte, dm_mod (show rev L σ < 2 * 2 ^ L by omega), hβ]
  · obtain ⟨t, rfl⟩ : ∃ t, r = 2 ^ j + t := ⟨r - 2 ^ j, by omega⟩
    have htl : t < 2 ^ j := by omega
    have hP : rev (L + 1 + j) (σ * (2 * 2 ^ j) + (2 ^ j + t)) =
        rev j t * (2 * 2 ^ L) + (2 ^ L + rev L σ) := by
      rw [hrevi, rev_lower j htl]; ring
    have hpartner : rev (L + 1 + j) (σ * (2 * 2 ^ j) + (2 ^ j + t) - 2 ^ j) =
        rev j t * (2 * 2 ^ L) + (2 ^ L + rev L σ) - 2 ^ L := by
      rw [show σ * (2 * 2 ^ j) + (2 ^ j + t) - 2 ^ j = σ * 2 ^ (j + 1) + t from
          Nat.sub_eq_of_eq_add (by ring),
        show L + 1 + j = (j + 1) + L by ring, rev_split (j + 1) L σ _ (by rw [pow_succ]; omega),
        rev_upper j htl]
      rw [Nat.add_sub_assoc (by omega)]
      ring_nf
      omega
    rw [hpartner, hP]
    simp only [hup, ↓reduceIte, dm_mod (show 2 ^ L + rev L σ < 2 * 2 ^ L by omega),
      show ¬ (2 ^ L + rev L σ < 2 ^ L) by omega, show 2 ^ L + rev L σ - 2 ^ L = rev L σ by omega]

/-! ## Twiddle tables -/

theorem getD_powersList {K : Type _} [Field K] (g : K) {n i : ℕ} (hi : i < n) :
    (powersList g n).getD i 0 = g ^ i := by
  simp [powersList, hi]

theorem getD_shiftedPowersList {K : Type _} [Field K] (g s : K) {n i : ℕ} (hi : i < n) :
    (shiftedPowersList g s n).getD i 0 = s * g ^ i := by
  simp [shiftedPowersList, hi]

theorem getD_revIndex {K : Type _} [Field K] (l : List K) {k i : ℕ} (hi : i < 2 ^ k) :
    (revIndex (2 ^ k) l).getD i 0 = l.getD (rev k i) 0 := by
  simp [revIndex, hi, Nat.log_pow (by norm_num : 1 < 2), bitRev_eq]

theorem length_powersList {K : Type _} [Field K] (g : K) (n : ℕ) : (powersList g n).length = n := by
  simp [powersList]

theorem length_revIndex {K : Type _} [Field K] (n : ℕ) (l : List K) : (revIndex n l).length = n := by
  simp [revIndex]

/-! ## Rows updated once each -/

theorem foldl_flatMap {α β γ : Type _} (l : List α) (g : α → List β) (f : γ → β → γ) (x : γ) :
    (l.flatMap g).foldl f x = l.foldl (fun acc a => (g a).foldl f acc) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.foldl_append, ih]

section updates

variable {V : Type _}

/-- Update row e.1 by e.2, for each entry of a list in order. -/
def runU (L : List (ℕ × (V → V))) (x : ℕ → V) : ℕ → V :=
  L.foldl (fun acc e => fun i => if i = e.1 then e.2 (acc i) else acc i) x

theorem runU_apply (L : List (ℕ × (V → V))) (x : ℕ → V) (hnd : (L.map Prod.fst).Nodup) (i : ℕ) :
    runU L x i = match L.find? (fun e => e.1 = i) with
      | some e => e.2 (x i)
      | none => x i := by
  induction L generalizing x with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [runU, List.foldl_cons] at ih ⊢
    rw [ih _ hnd.2, List.find?_cons]
    by_cases he : e.1 = i
    · subst he
      have : L.find? (fun e' => e'.1 = e.1) = none := by
        rw [List.find?_eq_none]
        intro e' he' h
        exact hnd.1 ⟨e', he', by simpa using h⟩
      simp [this]
    · simp [he, Ne.symm he]

end updates

/-! ## The coset shift and the division by the height -/

variable {K : Type _} [Field K] [DecidableEq K] {V : Type _} [AddCommGroup V] [Module K V]

omit [DecidableEq K] in
theorem divide_by_height_pow (k : ℕ) (x : ℕ → V) :
    p3_dft.util.mirror.divide_by_height (K := K) (2 ^ k) x =
      some (scaleRows ((2 : K) ^ k)⁻¹ x) := by
  simp [p3_dft.util.mirror.divide_by_height, log2Strict_pow]

/-- The rows the chunked loop of the coset shift visits, each with its weight. -/
theorem coset_shift_cols_eq {w h : ℕ} (shift : K) (x : ℕ → V) (hw : w ≠ 0 ∨ shift = 1) :
    p3_dft.util.mirror.coset_shift_cols w h x shift =
      some (fun i => if i < h then (shift ^ i) • x i else x i) := by
  unfold p3_dft.util.mirror.coset_shift_cols
  by_cases h1 : shift = 1
  · rw [ite_eq_left h1]; congr 1; funext i; subst h1; simp
  rw [ite_eq_right h1, ite_eq_right (by tauto)]
  have hw' : w ≠ 0 := by tauto
  set cr := max (2 ^ 15 / w) 1 with hcr
  have hcr0 : 0 < cr := by omega
  -- the loop as one list of row updates
  let entries : List (ℕ × (V → V)) := (List.range ((h + cr - 1) / cr)).flatMap fun ci =>
    (List.range (min cr (h - ci * cr))).map fun j =>
      (ci * cr + j, fun v => (shift ^ (ci * cr) * shift ^ j) • v)
  have hloop : (List.range ((h + cr - 1) / cr)).foldl (fun acc chunk_idx =>
      (List.range (min cr (h - chunk_idx * cr))).foldl (fun acc j =>
        fun i => if i = chunk_idx * cr + j then (shift ^ (chunk_idx * cr) * shift ^ j) • acc i
          else acc i) acc) x = runU entries x := by
    simp only [runU, entries, foldl_flatMap, List.foldl_map]
  dsimp only
  rw [hloop]
  have hmem : ∀ e ∈ entries, e.1 < h ∧ ∀ v, e.2 v = (shift ^ e.1) • v := by
    intro e he
    simp only [entries, List.mem_flatMap, List.mem_range, List.mem_map] at he
    obtain ⟨ci, _, j, hj, rfl⟩ := he
    refine ⟨by omega, fun v => by simp [pow_add]⟩
  have hnd : (entries.map Prod.fst).Nodup := by
    simp only [entries, List.map_flatMap, List.map_map]
    rw [List.nodup_flatMap]
    refine ⟨fun ci _ => (List.nodup_range).map (fun a b hab => by simpa using hab), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range, Function.comp]
    rintro _ ⟨j, hj, rfl⟩ ⟨j', hj', heq⟩
    have hj1 : j < cr := by omega
    have hj2 : j' < cr := by omega
    have e1 := congrArg (· / cr) heq
    simp only [Nat.mul_comm _ cr, Nat.mul_add_div hcr0, Nat.div_eq_of_lt hj1,
      Nat.div_eq_of_lt hj2, add_zero] at e1
    exact hab e1.symm
  congr 1
  funext i
  rw [runU_apply _ _ hnd]
  split
  · rename_i e he
    have hein := List.mem_of_find?_eq_some he
    have hei := List.find?_some he
    simp only [decide_eq_true_eq] at hei
    obtain ⟨hlt, hf⟩ := hmem e hein
    rw [hf, hei, ite_eq_left (hei ▸ hlt)]
  · rename_i he
    rw [ite_eq_right]
    intro hi
    -- row i is visited by chunk i / cr, at position i mod cr
    have hci : i / cr < (h + cr - 1) / cr := by
      have h1 : (i + cr) / cr ≤ (h + cr - 1) / cr := Nat.div_le_div_right (by omega)
      have h2 : (i + cr) / cr = i / cr + 1 := Nat.add_div_right i hcr0
      omega
    have := List.find?_eq_none.mp he (i / cr * cr + i % cr, fun v =>
      (shift ^ (i / cr * cr) * shift ^ (i % cr)) • v)
    apply this
    · simp only [entries, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨i / cr, hci, i % cr, ?_, rfl⟩
      have := Nat.div_add_mod' i cr
      have := Nat.mod_lt i hcr0
      omega
    · simp [Nat.div_add_mod']

end Plonky3Lean.Proofs.Dft
