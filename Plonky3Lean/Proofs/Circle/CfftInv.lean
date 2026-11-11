module

public import Plonky3Lean.Proofs.Circle.Cfft

@[expose] public section

/-!
# p3-circle: the inverse circle FFT

A decimation-in-frequency layer with the inverted twiddles undoes a decimation-in-time layer.

It does so up to a factor 2:

```text
    (a, b)  ->  (a + t b, a - t b)  ->  (2 a, 2 t^(-1) t b) = (2 a, 2 b)
```

Interpolation runs these layers in the opposite order and scales by 1 / 2^n.

So interpolation and evaluation are mutually inverse on a twin coset whose twiddles are nonzero.

On a standard domain the twiddles are nonzero.

No twiddle there is the coordinate of a point of order 2 or 4.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft p3_circle.cfft.mirror p3_circle.point.mirror
  p3_circle.domain.mirror Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] {V : Type} [AddCommGroup V] [Module K V]

/-! ## Telescoping -/

/-- Two families of layers A and B on the rows below H.

For every j of the list, B j undoes A j up to the factor 2.

The layers B are local and linear. -/
theorem foldl_inverse (A B : ℕ → (ℕ → V) → ℕ → V) (H : ℕ) (L : List ℕ)
    (hBA : ∀ j ∈ L, ∀ (x : ℕ → V), ∀ i < H, B j (A j x) i = (2 : K) • x i)
    (hloc : ∀ j ∈ L, ∀ {x y : ℕ → V}, (∀ i < H, x i = y i) → ∀ i < H, B j x i = B j y i)
    (hlin : ∀ j ∈ L, ∀ (c : K) (x : ℕ → V) i, B j (fun r => c • x r) i = c • B j x i)
    (x : ℕ → V) :
    ∀ i < H, L.foldl (fun acc j => B j acc) (L.reverse.foldl (fun acc j => A j acc) x) i =
      ((2 : K) ^ L.length) • x i := by
  have floc : ∀ (L' : List ℕ), (∀ j ∈ L', j ∈ L) → ∀ {x y : ℕ → V}, (∀ i < H, x i = y i) →
      ∀ i < H, L'.foldl (fun acc j => B j acc) x i = L'.foldl (fun acc j => B j acc) y i := by
    intro L'
    induction L' with
    | nil => intro _ x y h; exact h
    | cons a L' ih =>
      intro hL x y h
      exact ih (fun j hj => hL j (by simp [hj])) (hloc a (hL a (by simp)) h)
  have flin : ∀ (L' : List ℕ), (∀ j ∈ L', j ∈ L) → ∀ (c : K) (x : ℕ → V) i,
      L'.foldl (fun acc j => B j acc) (fun r => c • x r) i = c • L'.foldl (fun acc j => B j acc) x i := by
    intro L'
    induction L' with
    | nil => intro _ c x i; rfl
    | cons a L' ih =>
      intro hL c x i
      simp only [List.foldl_cons]
      rw [show (B a fun r => c • x r) = (fun r => c • B a x r) from
        funext (hlin a (hL a (by simp)) c x), ih (fun j hj => hL j (by simp [hj]))]
  have key : ∀ (L' : List ℕ), (∀ j ∈ L', j ∈ L) → ∀ (x : ℕ → V), ∀ i < H,
      L'.foldl (fun acc j => B j acc) (L'.reverse.foldl (fun acc j => A j acc) x) i =
        ((2 : K) ^ L'.length) • x i := by
    intro L'
    induction L' with
    | nil => intro _ x i _; simp
    | cons a L' ih =>
      intro hL x i hi
      have hL' : ∀ j ∈ L', j ∈ L := fun j hj => hL j (by simp [hj])
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      rw [floc L' hL' (hBA a (hL a (by simp)) _) i hi, flin L' hL', ih hL' x i hi, List.length_cons,
        pow_succ, mul_smul, smul_comm]
  exact key L (fun _ h => h) x

/-! ## One layer -/

section pair

variable {W : Type _}

theorem pair_up {m nb i : ℕ} (hi : i < nb * (2 * m)) (h : i % (2 * m) < m) :
    (i + m) % (2 * m) = i % (2 * m) + m ∧ (i + m) / (2 * m) = i / (2 * m) ∧ i + m < nb * (2 * m) := by
  have hm : 0 < 2 * m := by omega
  have hd := Nat.div_add_mod i (2 * m)
  have hblk : (i / (2 * m) + 1) * (2 * m) ≤ nb * (2 * m) :=
    Nat.mul_le_mul_right _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi))
  have e : i + m = 2 * m * (i / (2 * m)) + (i % (2 * m) + m) := by omega
  refine ⟨?_, ?_, by nlinarith⟩
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · rw [e, Nat.mul_add_div hm, Nat.div_eq_of_lt (show i % (2 * m) + m < 2 * m by omega), add_zero]

/-- A lower row and its upper partner, as the layer writes them. -/
theorem layer_pair (op : ℕ → ℕ → W → W → W × W) {m nb i : ℕ} (hi : i < nb * (2 * m))
    (h : i % (2 * m) < m) (x : ℕ → W) :
    layer op m nb x i = (op (i / (2 * m)) (i % (2 * m)) (x i) (x (i + m))).1 ∧
      layer op m nb x (i + m) = (op (i / (2 * m)) (i % (2 * m)) (x i) (x (i + m))).2 := by
  obtain ⟨h1, h2, h3⟩ := pair_up hi h
  unfold layer
  simp only [hi, h, ↓reduceIte, h3, h1, h2, show ¬ (i % (2 * m) + m < m) by omega,
    Nat.add_sub_cancel, true_and]

/-- Composing two layers whose butterflies compose to doubling doubles every row in range. -/
theorem layer_comp (op₁ op₂ : ℕ → ℕ → V → V → V × V) (m nb : ℕ)
    (hop : ∀ b < nb, ∀ s a c, op₂ b s (op₁ b s a c).1 (op₁ b s a c).2 = ((2 : K) • a, (2 : K) • c))
    (x : ℕ → V) : ∀ i < nb * (2 * m), layer op₂ m nb (layer op₁ m nb x) i = (2 : K) • x i := by
  intro i hi
  have hb : ∀ {i}, i < nb * (2 * m) → i / (2 * m) < nb := fun h =>
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
  by_cases h : i % (2 * m) < m
  · obtain ⟨e1, e2⟩ := layer_pair op₁ hi h x
    rw [(layer_pair op₂ hi h _).1, e1, e2, hop _ (hb hi)]
  · have hm : m ≤ i := le_trans (by omega) (Nat.mod_le i (2 * m))
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hi
      · exact h0
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + m := ⟨i - m, by omega⟩
    have hd := Nat.div_add_mod (i0 + m) (2 * m)
    have hr := Nat.mod_lt (i0 + m) (show 2 * m > 0 by omega)
    have e : i0 = 2 * m * ((i0 + m) / (2 * m)) + ((i0 + m) % (2 * m) - m) := by omega
    have hlo : i0 % (2 * m) < m := by
      rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
    have hi0 : i0 < nb * (2 * m) := by omega
    obtain ⟨e1, e2⟩ := layer_pair op₁ hi0 hlo x
    rw [(layer_pair op₂ hi0 hlo _).2, e1, e2, hop _ (hb hi0)]

end pair

theorem layer_dif_dit (T T' : ℕ → K) (m nb : ℕ) (hT : ∀ b < nb, T' b * T b = 1) (x : ℕ → V) :
    ∀ i < nb * (2 * m), layer (fun b _ => dif (T' b)) m nb (layer (fun b _ => dit (T b)) m nb x) i =
      (2 : K) • x i :=
  layer_comp _ _ m nb (fun b hb _ a c => by
    simp only [dif, dit, Prod.mk.injEq]
    constructor
    · module
    · rw [show a + T b • c - (a - T b • c) = (2 : K) • (T b • c) by module, smul_smul, smul_smul,
        show T' b * 2 * T b = 2 * (T' b * T b) by ring, hT b hb, mul_one]) x

theorem layer_dit_dif (T T' : ℕ → K) (m nb : ℕ) (hT : ∀ b < nb, T b * T' b = 1) (x : ℕ → V) :
    ∀ i < nb * (2 * m), layer (fun b _ => dit (T b)) m nb (layer (fun b _ => dif (T' b)) m nb x) i =
      (2 : K) • x i :=
  layer_comp _ _ m nb (fun b hb _ a c => by
    simp only [dif, dit, Prod.mk.injEq, smul_smul, hT b hb, one_smul]
    constructor <;> module) x


/-! ## Interpolation and evaluation -/

section transforms

variable [DecidableEq K] {G : p3_dft.mirror.Gen (K × K)}

open p3_dft.butterflies.mirror p3_commit.domain.mirror p3_dft.mirror

theorem runLayer_dif {n j : ℕ} (hj : j < n) (ts : List K) (hts : ts.length = 2 ^ (n - 1 - j))
    (x : ℕ → V) :
    runLayer (fun (t : K) => DifButterfly.apply (V := V) t) n (CfftLayer.Butterflies ts) x =
      layer (fun b _ => dif (ts.getD b 0)) (2 ^ j) (2 ^ (n - 1 - j)) x := by
  have hm : 2 ^ n / (2 * 2 ^ (n - 1 - j)) = 2 ^ j := by
    rw [← pow_succ', Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  simp only [runLayer, CfftLayer.blocks, hts, hm]
  rw [pairLoop_blocks _ _ (by positivity)]
  rfl

/-- The decimation-in-frequency layer j with the inverted twiddles. -/
def fl (S g : C K) (n j : ℕ) : (ℕ → V) → ℕ → V :=
  layer (fun b _ => dif (twC S g n j b)⁻¹) (2 ^ j) (2 ^ (n - 1 - j))

/-- The decimation-in-time layer j. -/
def dl (S g : C K) (n j : ℕ) : (ℕ → V) → ℕ → V :=
  layer (fun b _ => dit (twC S g n j b)) (2 ^ j) (2 ^ (n - 1 - j))

theorem layer_smul_row {op : ℕ → ℕ → V → V → V × V} {m nb : ℕ}
    (hop : ∀ b s (c : K) a a', op b s (c • a) (c • a') = (c • (op b s a a').1, c • (op b s a a').2))
    (c : K) (x : ℕ → V) (i : ℕ) : layer op m nb (fun r => c • x r) i = c • layer op m nb x i := by
  unfold layer
  split_ifs <;> simp [hop]

theorem dif_smul (t c : K) (a a' : V) : dif t (c • a) (c • a') = (c • (dif t a a').1, c • (dif t a a').2) := by
  simp only [dif, Prod.mk.injEq]; constructor <;> module

theorem dit_smul (t c : K) (a a' : V) : dit t (c • a) (c • a') = (c • (dit t a a').1, c • (dit t a a').2) := by
  simp only [dit, Prod.mk.injEq]; constructor <;> module

/-- With nonzero twiddles, interpolation runs the decimation-in-frequency layers on the input.

It then scales by 1 / 2^n. -/
theorem interpolate_eq_layers (hV : CircleGenValid G) {n : ℕ} (hn : 1 ≤ n) (hG : n - 1 ≤ G.adicity)
    (S : C K) (htw : ∀ j < n, ∀ b < 2 ^ (n - 1 - j), twC S (genPt G (n - 1)) n j b ≠ 0)
    (v : ℕ → V) :
    interpolate G ⟨n, ofC S⟩ v = some (scaleRows ((2 : K) ^ n)⁻¹
      ((List.range n).foldl (fun acc j => fl S (genPt G (n - 1)) n j acc) v)) := by
  have hinv : (twTable S (genPt G (n - 1)) n).mapM batchInv = some ((twTable S (genPt G (n - 1)) n).map fun ts => ts.map (·⁻¹)) := by
    refine Plonky3Lean.Proofs.Circle.mapM_eq_some_map _ _ _ fun ts hts => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hts
    unfold batchInv
    rw [ite_eq_left]
    intro t ht
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact htw j (by simpa using hj) b (by simpa using hb)
  rw [interpolate, compute_twiddles_eq hV S hn hG]
  simp only [Option.bind_eq_bind, Option.bind_some, hinv]
  have hlen : ((twTable S (genPt G (n - 1)) n).map fun ts => ts.map (·⁻¹)).length = n := by simp [twTable]
  rw [List.length_map, hlen, ite_eq_right (by simp), cfft_layers,
    ite_eq_right (by simp [twTable]; omega)]
  simp only [Option.some.injEq]
  congr 1
  unfold twTable
  rw [List.map_map, List.map_map, List.foldl_map]
  refine foldl_congr_mem _ (fun j hj acc => ?_) v
  have hj' : j < n := by simpa using hj
  simp only [Function.comp_apply]
  rw [runLayer_dif hj' _ (by simp), fl]
  apply layer_op_congr
  intro b hb
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_map, List.getElem_range]


/-- On as many coefficients as points, evaluation runs the decimation-in-time network. -/
theorem evaluate_eq_net (hV : CircleGenValid G) {n : ℕ} (hn : 1 ≤ n) (hG : n - 1 ≤ G.adicity)
    (S : C K) (x : ℕ → V) :
    evaluate G ⟨n, ofC S⟩ (2 ^ n) x =
      some ((List.range n).reverse.foldl (fun acc j => dl S (genPt G (n - 1)) n j acc) x) := by
  unfold evaluate cfft_layers
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some, lt_irrefl, ↓reduceIte,
    compute_twiddles_eq hV S hn hG, Nat.sub_self, List.range_zero, List.map_nil, List.nil_append,
    List.drop_zero, Option.isSome_none, Bool.false_eq_true, and_false, Option.some.injEq]
  rw [twTable, List.map_map, ← List.map_reverse, List.foldl_map]
  refine foldl_congr_mem _ (fun j hj acc => ?_) x
  have hj' : j < n := by simpa using hj
  simp only [Function.comp_apply]
  rw [runLayer_butterflies hj' _ (by simp), dl]
  apply layer_op_congr
  intro b hb
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range]

theorem dl_local (S g : C K) {n j : ℕ} (hj : j < n) {x y : ℕ → V} (h : ∀ i < 2 ^ n, x i = y i) :
    ∀ i < 2 ^ n, dl S g n j x i = dl S g n j y i := by
  have e : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
  intro i hi
  exact layer_local _ _ _ (by rw [e]; exact h) i (by rw [e]; exact hi)

theorem fl_local (S g : C K) {n j : ℕ} (hj : j < n) {x y : ℕ → V} (h : ∀ i < 2 ^ n, x i = y i) :
    ∀ i < 2 ^ n, fl S g n j x i = fl S g n j y i := by
  have e : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
  intro i hi
  exact layer_local _ _ _ (by rw [e]; exact h) i (by rw [e]; exact hi)

/-- Decimation-in-time after decimation-in-frequency, with the same twiddles, scales rows by 2^n.

This holds for every row below 2^n. -/
theorem dl_fl (S g : C K) {n : ℕ} (htw : ∀ j < n, ∀ b < 2 ^ (n - 1 - j), twC S g n j b ≠ 0)
    (x : ℕ → V) :
    ∀ i < 2 ^ n, (List.range n).reverse.foldl (fun acc j => dl S g n j acc)
      ((List.range n).foldl (fun acc j => fl S g n j acc) x) i = ((2 : K) ^ n) • x i := by
  have h := foldl_inverse (K := K) (fun j => fl S g n j) (fun j => dl S g n j) (2 ^ n)
    (List.range n).reverse (fun j hj x i hi => ?_)
    (fun j hj _ _ h => dl_local S g (by simpa using hj) h)
    (fun j _ c x i => layer_smul_row (fun b s c a a' => dit_smul _ c a a') c x i) x
  · rwa [List.reverse_reverse, List.length_reverse, List.length_range] at h
  · have hj' : j < n := by simpa using hj
    have e : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
    exact layer_dit_dif _ _ _ _ (fun b hb => mul_inv_cancel₀ (htw _ hj' b hb)) x i (by rw [e]; exact hi)

/-- Decimation-in-frequency after decimation-in-time multiplies every row below 2^n by 2^n. -/
theorem fl_dl (S g : C K) {n : ℕ} (htw : ∀ j < n, ∀ b < 2 ^ (n - 1 - j), twC S g n j b ≠ 0)
    (x : ℕ → V) :
    ∀ i < 2 ^ n, (List.range n).foldl (fun acc j => fl S g n j acc)
      ((List.range n).reverse.foldl (fun acc j => dl S g n j acc) x) i = ((2 : K) ^ n) • x i := by
  have h := foldl_inverse (K := K) (fun j => dl S g n j) (fun j => fl S g n j) (2 ^ n)
    (List.range n) (fun j hj x i hi => ?_)
    (fun j hj _ _ h => fl_local S g (by simpa using hj) h)
    (fun j _ c x i => layer_smul_row (fun b s c a a' => dif_smul _ c a a') c x i) x
  · rwa [List.length_range] at h
  · have hj' : j < n := by simpa using hj
    have e : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
    exact layer_dif_dit _ _ _ _ (fun b hb => inv_mul_cancel₀ (htw _ hj' b hb)) x i (by rw [e]; exact hi)

theorem foldl_dl_smul (S g : C K) (n : ℕ) (L : List ℕ) (c : K) (x : ℕ → V) :
    L.foldl (fun acc j => dl S g n j acc) (scaleRows c x) =
      scaleRows c (L.foldl (fun acc j => dl S g n j acc) x) := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [show dl S g n a (scaleRows c x) = scaleRows c (dl S g n a x) from
      funext fun i => layer_smul_row (fun b s c a a' => dit_smul _ c a a') c x i, ih]

/-- The circle FFT, Theorem 2.

With nonzero twiddles, interpolation returns coefficients in the FFT basis.

Their polynomial takes the given values at the points of the rows. -/
theorem interpolate_spec (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n - 1 ≤ G.adicity) (S : C K)
    (htw : ∀ j < n, ∀ b < 2 ^ (n - 1 - j), twC S (genPt G (n - 1)) n j b ≠ 0) (v : ℕ → V) :
    ∃ cs, interpolate G ⟨n, ofC S⟩ v = some cs ∧
      ∀ i < 2 ^ n, fftEval n cs (ptAt S (genPt G (n - 1)) n i) = v i := by
  refine ⟨_, interpolate_eq_layers hV hn hG S htw v, fun i hi => ?_⟩
  obtain ⟨y, hy, hyi⟩ := evaluate_eq hV hn le_rfl hG S
    (scaleRows ((2 : K) ^ n)⁻¹ ((List.range n).foldl (fun acc j => fl S (genPt G (n - 1)) n j acc) v))
  rw [← hyi i hi]
  rw [evaluate_eq_net hV hn hG, Option.some.injEq] at hy
  rw [← hy, foldl_dl_smul, scaleRows, dl_fl _ _ htw v i hi, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero n h2), one_smul]

/-- Interpolation undoes evaluation, on as many coefficients as points, with nonzero twiddles. -/
theorem interpolate_evaluate (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n - 1 ≤ G.adicity) (S : C K)
    (htw : ∀ j < n, ∀ b < 2 ^ (n - 1 - j), twC S (genPt G (n - 1)) n j b ≠ 0) (c : ℕ → V) :
    ∃ y cs, evaluate G ⟨n, ofC S⟩ (2 ^ n) c = some y ∧ interpolate G ⟨n, ofC S⟩ y = some cs ∧
      ∀ i < 2 ^ n, cs i = c i := by
  refine ⟨_, _, evaluate_eq_net hV hn hG S c, interpolate_eq_layers hV hn hG S htw _, fun i hi => ?_⟩
  rw [scaleRows, fl_dl _ _ htw c i hi, smul_smul, inv_mul_cancel₀ (pow_ne_zero n h2), one_smul]

end transforms

end Plonky3Lean.Proofs.Circle
