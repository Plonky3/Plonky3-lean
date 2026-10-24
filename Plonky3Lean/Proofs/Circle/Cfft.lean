module

public import P3Circle.Cfft
public import Plonky3Lean.Proofs.Circle.CfftNet

@[expose] public section

/-!
# p3-circle: the circle FFT

The twiddle tables are the coordinates of the half coset, all in bit-reversed order:

- layer 0 holds the y-coordinates
- layer j >= 1 holds the x-coordinates after j - 1 squarings.

Evaluation works on a twin coset of size 2^n >= 2^m.

It maps 2^m coefficients in the FFT basis to the values of their polynomial, in circle FFT order.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft p3_circle.cfft.mirror p3_circle.point.mirror
  p3_circle.domain.mirror Finset

set_option linter.unusedSectionVars false

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K] [DecidableEq K]

/-! ## Lists -/

theorem revList_map_range {α : Type _} (d : α) (f : ℕ → α) (k : ℕ) :
    revList d ((List.range (2 ^ k)).map f) = (List.range (2 ^ k)).map fun i => f (rev k i) := by
  unfold revList
  simp only [List.length_map, List.length_range, Nat.log_pow (by norm_num : 1 < 2), bitRev_eq]
  refine List.map_congr_left fun i _ => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using Plonky3Lean.Proofs.Matrix.bitRev_lt k i),
    List.getElem_map, List.getElem_range]

theorem stepBy2_map_range {α : Type _} (f : ℕ → α) (m : ℕ) :
    stepBy2 ((List.range (2 * m)).map f) = (List.range m).map fun k => f (2 * k) := by
  induction m with
  | zero => simp [stepBy2]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
      List.map_append]
    unfold stepBy2 at ih ⊢
    rw [List.zipIdx_append, List.filter_append, List.map_append, List.zipIdx_append,
      List.filter_append, List.map_append, ih]
    simp [List.range_succ, Nat.add_mod]

/-! ## The twiddles -/

/-- The closed form of the twiddle tables: n layers, layer j of 2^(n - 1 - j) entries. -/
def twTable (S g : C K) (n : ℕ) : List (List K) :=
  (List.range n).map fun j => (List.range (2 ^ (n - 1 - j))).map (twC S g n j)

theorem twTable_succ (S g : C K) (n m : ℕ) :
    ((List.range (m + 1)).map fun j => (List.range (2 ^ (n - 1 - j))).map (twC S g n j)) =
      ((List.range m).map fun j => (List.range (2 ^ (n - 1 - j))).map (twC S g n j)) ++
        [(List.range (2 ^ (n - 1 - m))).map (twC S g n m)] := by
  rw [List.range_succ, List.map_append]; rfl

/-- Each round of the twiddle loop squares the even entries of the last table. -/
theorem twiddleLoop_eq (S g : C K) {n : ℕ} (m : ℕ) (hm : m + 2 ≤ n) :
    (List.range m).foldl (twiddleLoop n) (some [(List.range (2 ^ (n - 1))).map (twC S g n 0),
      (List.range (2 ^ (n - 2))).map (twC S g n 1)]) =
      some ((List.range (m + 2)).map fun j => (List.range (2 ^ (n - 1 - j))).map (twC S g n j)) := by
  induction m with
  | zero => simp [List.range_succ, show n - 1 - 1 = n - 2 by omega]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    unfold twiddleLoop
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [twTable_succ _ _ _ (m + 1 + 1)]
    have hlast : ((List.range (m + 2)).map fun j => (List.range (2 ^ (n - 1 - j))).map
        (twC S g n j)).getLastD [] = (List.range (2 ^ (n - 2 - m))).map (twC S g n (m + 1)) := by
      rw [twTable_succ, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
      simp only [Option.some_or, Option.getD_some]
      rw [show n - 1 - (m + 1) = n - 2 - m by omega]
    rw [hlast]
    simp only [List.length_map, List.length_range, ne_eq, not_true_eq_false, ↓reduceIte,
      Option.some.injEq]
    congr 2
    rw [show 2 ^ (n - 2 - m) = 2 * 2 ^ (n - 1 - (m + 2)) by
      rw [← pow_succ']; congr 1; omega, stepBy2_map_range, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, twC, show m + 1 ≠ 0 by omega, show m + 2 ≠ 0 by omega,
      ↓reduceIte, show m + 1 + 1 = m + 2 by omega]
    rw [vnStep_x, smul_smul, ← pow_succ', show m + 1 - 1 + 1 = m + 2 - 1 by omega,
      show n - 1 - (m + 1) = (n - 1 - (m + 2)) + 1 by omega, mul_comm,
      Plonky3Lean.Proofs.Matrix.bitRev_mul_two_pow (n - 1 - (m + 2)) 1 k |>.symm.trans (by rw [pow_one])]


variable {G : p3_dft.mirror.Gen (K × K)}

/-- The twiddle tables of a twin coset of size 2^n with shift S and step g, in closed form. -/
theorem compute_twiddles_eq (hV : CircleGenValid G) {n : ℕ} (S : C K) (hn : 1 ≤ n)
    (hG : n - 1 ≤ G.adicity) :
    compute_twiddles G ⟨n, ofC S⟩ = some (twTable S (genPt G (n - 1)) n) := by
  set g := genPt G (n - 1)
  have hc0 : CircleDomain.coset0 G ⟨n, ofC S⟩ =
      some ((List.range (2 ^ (n - 1))).map fun i => ofC (S + i • g)) := by
    simp only [CircleDomain.coset0, subgroup_generator_eq hV ⟨n, ofC S⟩ hn hG, Option.bind_eq_bind,
      Option.bind_some, chain_ofC, g]
  have hpts : revList Point.ZERO ((List.range (2 ^ (n - 1))).map fun i => ofC (S + i • g)) =
      (List.range (2 ^ (n - 1))).map fun k => ofC (S + rev (n - 1) k • g) :=
    revList_map_range _ _ _
  unfold compute_twiddles
  simp only [show ¬ n < 1 by omega, ↓reduceIte, hc0, Option.bind_eq_bind, Option.bind_some, hpts]
  have htw0 : ((List.range (2 ^ (n - 1))).map fun k => ofC (S + rev (n - 1) k • g)).map Point.y =
      (List.range (2 ^ (n - 1))).map (twC S g n 0) := by
    rw [List.map_map]; rfl
  rw [htw0]
  split_ifs with h2
  · have htw1 : (stepBy2 ((List.range (2 ^ (n - 1))).map fun k => ofC (S + rev (n - 1) k • g))).map
        Point.x = (List.range (2 ^ (n - 2))).map (twC S g n 1) := by
      rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; omega, stepBy2_map_range,
        List.map_map]
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_apply, ofC_x, twC, one_ne_zero, ↓reduceIte, Nat.sub_self, pow_zero,
        one_nsmul]
      have hb := Plonky3Lean.Proofs.Matrix.bitRev_mul_two_pow (n - 2) 1 k
      rw [pow_one, show n - 2 + 1 = n - 1 by omega] at hb
      rw [mul_comm, hb, show n - 1 - 1 = n - 2 by omega]
    rw [htw1, twiddleLoop_eq S g (n - 2) (by omega), show n - 2 + 2 = n by omega]
    rfl
  · obtain rfl : n = 1 := by omega
    rfl


/-! ## The layers -/

section layers

variable {V : Type _} [AddCommGroup V] [Module K V]

open p3_dft.butterflies.mirror

theorem runLayer_butterflies {n j : ℕ} (hj : j < n) (ts : List K) (hts : ts.length = 2 ^ (n - 1 - j))
    (x : ℕ → V) :
    runLayer (fun (t : K) => DitButterfly.apply (V := V) t) n (CfftLayer.Butterflies ts) x =
      layer (fun b _ => dit (ts.getD b 0)) (2 ^ j) (2 ^ (n - 1 - j)) x := by
  have hm : 2 ^ n / (2 * 2 ^ (n - 1 - j)) = 2 ^ j := by
    rw [← pow_succ', Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  simp only [runLayer, CfftLayer.blocks, hts, hm]
  rw [pairLoop_blocks _ _ (by positivity)]
  rfl

theorem runLayer_dup {n l : ℕ} (hl : l < n) (x : ℕ → V) :
    runLayer (fun (t : K) => DitButterfly.apply (V := V) t) n (CfftLayer.Dup (2 ^ l)) x =
      layer (fun _ _ a _ => (a, a)) (2 ^ (n - 1 - l)) (2 ^ l) x := by
  have hm : 2 ^ n / (2 * 2 ^ l) = 2 ^ (n - 1 - l) := by
    rw [← pow_succ', Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  simp only [runLayer, CfftLayer.blocks, hm]
  rw [pairLoop_blocks _ _ (by positivity)]

/-- Row i of a block decomposition: i mod 2^(a+1) is i mod 2^a, plus 2^a in the high half. -/
theorem mod_two_pow_succ (i a : ℕ) :
    i % 2 ^ a = if i % 2 ^ (a + 1) < 2 ^ a then i % 2 ^ (a + 1) else i % 2 ^ (a + 1) - 2 ^ a := by
  have h1 : i % 2 ^ a = i % 2 ^ (a + 1) % 2 ^ a :=
    (Nat.mod_mod_of_dvd i (pow_dvd_pow 2 (Nat.le_succ a))).symm
  have h2 : i % 2 ^ (a + 1) < 2 * 2 ^ a := by rw [← pow_succ']; exact Nat.mod_lt _ (by positivity)
  split_ifs with h
  · rw [h1, Nat.mod_eq_of_lt h]
  · rw [h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem layer_dup_apply {m nb : ℕ} (s : ℕ → V) {i : ℕ} (hi : i < nb * (2 * m)) :
    layer (fun _ _ a _ => (a, a)) m nb s i = if i % (2 * m) < m then s i else s (i - m) := by
  unfold layer; simp only [hi, ↓reduceIte]

theorem layer_dit_apply {m nb : ℕ} (T : ℕ → K) (s : ℕ → V) {i : ℕ} (hi : i < nb * (2 * m)) :
    layer (fun b _ => dit (T b)) m nb s i = if i % (2 * m) < m then s i + T (i / (2 * m)) • s (i + m)
      else s (i - m) - T (i / (2 * m)) • s i := by
  unfold layer; simp only [hi, ↓reduceIte, dit]

/-- i mod 2^(a+1) minus 2^a, on the upper half, reduces i - 2^a mod 2^(a+1). -/
theorem sub_mod_two_pow (i a : ℕ) (h : 2 ^ a ≤ i % 2 ^ (a + 1)) :
    (i - 2 ^ a) % 2 ^ (a + 1) = i % 2 ^ (a + 1) - 2 ^ a := by
  have hd := Nat.div_add_mod i (2 ^ (a + 1))
  have hm := Nat.mod_lt i (show 2 ^ (a + 1) > 0 by positivity)
  rw [show i - 2 ^ a = 2 ^ (a + 1) * (i / 2 ^ (a + 1)) + (i % 2 ^ (a + 1) - 2 ^ a) by omega,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem add_mod_two_pow (i a : ℕ) (h : i % 2 ^ (a + 1) < 2 ^ a) :
    (i + 2 ^ a) % 2 ^ (a + 1) = i % 2 ^ (a + 1) + 2 ^ a := by
  have hd := Nat.div_add_mod i (2 ^ (a + 1))
  have hp : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  rw [show i + 2 ^ a = 2 ^ (a + 1) * (i / 2 ^ (a + 1)) + (i % 2 ^ (a + 1) + 2 ^ a) by omega,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- After k duplication layers, row i holds the input at i mod 2^(n - k). -/
theorem dup_loop {n : ℕ} (x : ℕ → V) (k : ℕ) (hk : k ≤ n) :
    ∀ i < 2 ^ n, ((List.range k).foldl (fun acc l =>
      runLayer (fun (t : K) => DitButterfly.apply (V := V) t) n (CfftLayer.Dup (2 ^ l)) acc) x) i =
      x (i % 2 ^ (n - k)) := by
  induction k with
  | zero => intro i hi; simp [Nat.mod_eq_of_lt hi]
  | succ k ih =>
    intro i hi
    have hsz : 2 ^ k * (2 * 2 ^ (n - 1 - k)) = 2 ^ n := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have e : n - k = (n - 1 - k) + 1 := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      runLayer_dup (by omega), layer_dup_apply _ (by rw [hsz]; exact hi), ← pow_succ',
      show n - (k + 1) = n - 1 - k by omega, mod_two_pow_succ i (n - 1 - k)]
    split_ifs with h
    · rw [ih (by omega) i hi, e]
    · rw [ih (by omega) _ (by omega), e, sub_mod_two_pow _ _ (by omega)]

/-- The zero-padding of 2^m coefficients. -/
def pad (m : ℕ) (x : ℕ → V) : ℕ → V := fun j => if j < 2 ^ m then x j else 0

theorem pad_zero {m : ℕ} (x : ℕ → V) {j : ℕ} (h : 2 ^ m ≤ j) : pad m x j = 0 := by
  simp [pad, not_lt.mpr h]

/-- On zero-padded input, the first n - m decimation-in-time layers duplicate rows. -/
theorem dit_pad_loop {n m : ℕ} (hmn : m ≤ n) (T : ℕ → ℕ → K) (x : ℕ → V) (k : ℕ) (hk : k ≤ n - m) :
    ∀ i < 2 ^ n, runCl T (fun j => 2 ^ (n - 1 - j)) ((List.range k).map fun l => n - 1 - l)
      (pad m x) i = pad m x (i % 2 ^ (n - k)) := by
  induction k with
  | zero => intro i hi; simp [runCl, Nat.mod_eq_of_lt hi]
  | succ k ih =>
    intro i hi
    have hsz : 2 ^ (n - 1 - (n - 1 - k)) * (2 * 2 ^ (n - 1 - k)) = 2 ^ n := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have e : n - k = (n - 1 - k) + 1 := by omega
    have hpow : 2 ^ m ≤ 2 ^ (n - 1 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hstep : runCl T (fun j => 2 ^ (n - 1 - j)) ((List.range (k + 1)).map fun l => n - 1 - l)
        (pad m x) = cl (T (n - 1 - k)) (n - 1 - k) (2 ^ (n - 1 - (n - 1 - k)))
          (runCl T (fun j => 2 ^ (n - 1 - j)) ((List.range k).map fun l => n - 1 - l) (pad m x)) := by
      simp only [runCl, List.range_succ, List.map_append, List.foldl_append, List.map_singleton,
        List.foldl_cons, List.foldl_nil]
    rw [hstep, cl, layer_dit_apply _ _ (by rw [hsz]; exact hi), ← pow_succ',
      show n - (k + 1) = n - 1 - k by omega, mod_two_pow_succ i (n - 1 - k)]
    have hmod := Nat.mod_lt i (show 2 ^ (n - 1 - k + 1) > 0 by positivity)
    split_ifs with h
    · have hq : i / 2 ^ (n - 1 - k + 1) < 2 ^ k := Nat.div_lt_of_lt_mul (by
        rw [← pow_add, show n - 1 - k + 1 + k = n by omega]; exact hi)
      have hbnd : i + 2 ^ (n - 1 - k) < 2 ^ n := by
        have hd := Nat.div_add_mod i (2 ^ (n - 1 - k + 1))
        have h3 : (i / 2 ^ (n - 1 - k + 1) + 1) * 2 ^ (n - 1 - k + 1) ≤ 2 ^ k * 2 ^ (n - 1 - k + 1) :=
          Nat.mul_le_mul_right _ hq
        rw [← pow_add, show k + (n - 1 - k + 1) = n by omega] at h3
        have hp : 2 ^ (n - 1 - k + 1) = 2 * 2 ^ (n - 1 - k) := by ring
        nlinarith
      rw [ih (by omega) i hi, ih (by omega) _ hbnd, e, add_mod_two_pow _ _ h,
        pad_zero (j := i % 2 ^ (n - 1 - k + 1) + 2 ^ (n - 1 - k)) _ (by omega), smul_zero, add_zero]
    · rw [ih (by omega) _ (by omega), ih (by omega) i hi, e, sub_mod_two_pow _ _ (by omega),
        pad_zero (j := i % 2 ^ (n - 1 - k + 1)) _ (by omega), smul_zero, sub_zero]

theorem basis_low {m n j : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hj : j < 2 ^ m) (P : C K) :
    basis n j P = basis m j P := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [basis_succ_low (by omega) (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hmn)), ih]

/-- The padded coefficients evaluate as the unpadded ones in the basis of their own size. -/
theorem fftEval_pad {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (x : ℕ → V) (P : C K) :
    fftEval n (pad m x) P = fftEval m x P := by
  unfold fftEval
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num : 0 < 2) hmn)]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun j hj => by
    rw [pad_zero x (by simp at hj; omega), smul_zero], add_zero]
  exact Finset.sum_congr rfl fun j hj => by
    have hj' : j < 2 ^ m := by simpa using hj
    rw [basis_low hm hmn hj', pad, ite_eq_left hj']

theorem range_reverse_split {m n : ℕ} (hmn : m ≤ n) :
    (List.range n).reverse = (List.range (n - m)).map (fun l => n - 1 - l) ++ (List.range m).reverse := by
  obtain ⟨a, rfl⟩ : ∃ a, n = m + a := ⟨n - m, by omega⟩
  rw [List.range_add, List.reverse_append, Nat.add_sub_cancel_left]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_reverse, List.length_map, List.length_range] at h1
  simp [List.getElem_reverse]
  omega

theorem runCl_append {V : Type _} [AddCommGroup V] [Module K V] (T : ℕ → ℕ → K) (nbf : ℕ → ℕ)
    (l₁ l₂ : List ℕ) (x : ℕ → V) : runCl T nbf (l₁ ++ l₂) x = runCl T nbf l₂ (runCl T nbf l₁ x) :=
  List.foldl_append

theorem foldl_congr_mem {α β : Type _} (l : List α) {f g : β → α → β} (h : ∀ a ∈ l, ∀ b, f b a = g b a)
    (b : β) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp), ih (fun a ha => h a (by simp [ha]))]

end layers

/-! ## Evaluation -/

open p3_dft.butterflies.mirror in
/-- Evaluation on the twin coset of size 2^n with shift S.

It maps 2^m coefficients to the values of their polynomial in the FFT basis of order m.

The values come in circle FFT order.

Row 2 b holds the value at S + rev(b) g, and row 2 b + 1 the value at its conjugate. -/
theorem evaluate_eq {V : Type _} [AddCommGroup V] [Module K V] (hV : CircleGenValid G) {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hG : n - 1 ≤ G.adicity) (S : C K) (x : ℕ → V) :
    ∃ y, evaluate G ⟨n, ofC S⟩ (2 ^ m) x = some y ∧
      ∀ i < 2 ^ n, y i = fftEval m x (ptAt S (genPt G (n - 1)) n i) := by
  set g := genPt G (n - 1)
  have hn : 1 ≤ n := by omega
  unfold evaluate cfft_layers
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some, show ¬ n < m by omega,
    ↓reduceIte, compute_twiddles_eq hV S hn hG, Option.isSome_none, Bool.false_eq_true, and_false]
  refine ⟨_, rfl, fun i hi => ?_⟩
  rw [List.foldl_append]
  -- The duplication layers leave row i at the input's row i mod 2^m.
  have hD := dup_loop (K := K) (n := n) x (n - m) (by omega)
  -- The twiddle layers are the network's last m layers.
  have htw : ((twTable S g n).map CfftLayer.Butterflies).reverse.drop (n - m) =
      ((List.range m).reverse).map fun j =>
        CfftLayer.Butterflies ((List.range (2 ^ (n - 1 - j))).map (twC S g n j)) := by
    rw [twTable, List.map_map, ← List.map_reverse, range_reverse_split hmn, List.map_append,
      List.drop_left' (by simp)]
    rfl
  rw [htw, List.foldl_map]
  have hrest : ∀ z : ℕ → V, ((List.range m).reverse).foldl (fun acc j =>
      runLayer (fun (t : K) => DitButterfly.apply (V := V) t) n
        (CfftLayer.Butterflies ((List.range (2 ^ (n - 1 - j))).map (twC S g n j))) acc) z =
      runCl (twC S g n) (fun j => 2 ^ (n - 1 - j)) (List.range m).reverse z := fun z => by
    unfold runCl
    refine foldl_congr_mem _ (fun j hj acc => ?_) z
    have hj' : j < m := by simpa using hj
    rw [runLayer_butterflies (n := n) (j := j) (by omega) _ (by simp), cl]
    apply layer_op_congr
    intro b hb
    rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range]
  rw [hrest]
  have hnet := evalNet_eq hn S g (fun h2 => by
    rw [show g = genPt G (n - 1) from rfl, show n - 2 = n - 1 - 1 by omega,
      genPt_nsmul hV (j := 1) (by omega) hG, genPt,
      toC_of_on (hV.on_circle 1 (by omega))]
    ext <;> simp [negOne, hV.gen_one (by omega)]) (pad m x) i hi
  rw [fftEval_pad hm hmn] at hnet
  rw [← hnet, evalNet, range_reverse_split hmn, runCl_append, List.foldl_map]
  change runCl (twC S g n) (fun j => 2 ^ (n - 1 - j)) (List.range m).reverse _ i = _
  have hsz : ∀ j ∈ (List.range m).reverse, 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := fun j hj => by
    have : j < m := by simpa using hj
    rw [← pow_succ', ← pow_add]; congr 1; omega
  refine runCl_local _ _ _ _ hsz (fun r hr => ?_) i hi
  rw [hD r hr, dit_pad_loop hmn _ x (n - m) le_rfl r hr, show n - (n - m) = m by omega, pad,
    ite_eq_left (Nat.mod_lt _ (by positivity))]

end Plonky3Lean.Proofs.Circle
