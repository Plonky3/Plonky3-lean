module

public import Plonky3Lean.Proofs.Fri.Matrix

@[expose] public section

/-!
# The packed matrix fold

The packed kernel folds W rows at once, one row per lane.

Each round folds pairs in place.

A pair is never read after it is overwritten.

Its factors split the scalar table into a per-row part and a per-pair part.

So every lane computes the scalar fold of its row.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

theorem getD_set_ne' {A : Type _} [Zero A] (c : List A) {i x : ℕ} (v : A) (h : i ≠ x) :
    (c.set i v).getD x 0 = c.getD x 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_self' {A : Type _} [Zero A] (c : List A) {i : ℕ} (v : A) (h : i < c.length) :
    (c.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Writing positions j, j + 1, ... with values that read nothing from the list. -/
def writeFresh {A γ : Type _} (val : ℕ → γ → A) (L : List γ) (j : ℕ) (c : List A) : List A :=
  (L.zipIdx j).foldl (fun c e => c.set e.2 (val e.2 e.1)) c

theorem writeFresh_spec {A γ : Type _} [Zero A] [Inhabited γ] (val : ℕ → γ → A) :
    ∀ (L : List γ) (j : ℕ) (c : List A), j + L.length ≤ c.length →
      (writeFresh val L j c).length = c.length ∧
      (∀ kk < L.length, (writeFresh val L j c).getD (j + kk) 0 = val (j + kk) (L.getD kk default)) ∧
      ∀ x < j, (writeFresh val L j c).getD x 0 = c.getD x 0
  | [], _, c, _ => ⟨rfl, fun kk hk => absurd hk (by simp), fun _ _ => rfl⟩
  | a :: L, j, c, h => by
    simp only [List.length_cons] at h
    obtain ⟨h1, h2, h3⟩ := writeFresh_spec val L (j + 1) (c.set j (val j a)) (by simp; omega)
    simp only [writeFresh, List.zipIdx_cons, List.foldl_cons] at h1 h2 h3 ⊢
    refine ⟨by rw [h1, List.length_set], fun kk hk => ?_, fun x hx => ?_⟩
    · rcases kk with _ | kk
      · rw [add_zero, h3 j (by omega), getD_set_self' _ _ (by omega)]; rfl
      · rw [show j + (kk + 1) = j + 1 + kk by omega, h2 kk (by simp at hk; omega)]; rfl
    · rw [h3 x (by omega), getD_set_ne' _ _ (by omega)]

/-- Folding pairs in place: position kk becomes F of positions 2 kk and 2 kk + 1, for kk in order. -/
def writeInPlace {A γ : Type _} [Zero A] (F : A → A → γ → A) (L : List γ) (j : ℕ) (c : List A) : List A :=
  (L.zipIdx j).foldl (fun c e => c.set e.2 (F (c.getD (2 * e.2) 0) (c.getD (2 * e.2 + 1) 0) e.1)) c

/-- In place is safe: position kk reads positions 2 kk and 2 kk + 1, which no earlier step wrote. -/
theorem writeInPlace_spec {A γ : Type _} [Zero A] [Inhabited γ] (F : A → A → γ → A) (ps : List A) :
    ∀ (L : List γ) (j : ℕ) (c : List A), c.length = ps.length → 2 * (j + L.length) ≤ ps.length →
      (∀ x, j ≤ x → c.getD x 0 = ps.getD x 0) →
      (writeInPlace F L j c).length = ps.length ∧
      (∀ kk < L.length, (writeInPlace F L j c).getD (j + kk) 0 =
        F (ps.getD (2 * (j + kk)) 0) (ps.getD (2 * (j + kk) + 1) 0) (L.getD kk default)) ∧
      ∀ x < j, (writeInPlace F L j c).getD x 0 = c.getD x 0
  | [], _, c, hc, _, _ => ⟨hc, fun kk hk => absurd hk (by simp), fun _ _ => rfl⟩
  | a :: L, j, c, hc, hlen, hps => by
    simp only [List.length_cons] at hlen
    have hr1 := hps (2 * j) (by omega)
    have hr2 := hps (2 * j + 1) (by omega)
    obtain ⟨h1, h2, h3⟩ := writeInPlace_spec F ps L (j + 1)
      (c.set j (F (c.getD (2 * j) 0) (c.getD (2 * j + 1) 0) a)) (by simp [hc]) (by omega)
      (fun x hx => by rw [getD_set_ne' _ _ (by omega), hps x (by omega)])
    simp only [writeInPlace, List.zipIdx_cons, List.foldl_cons] at h1 h2 h3 ⊢
    refine ⟨h1, fun kk hk => ?_, fun x hx => ?_⟩
    · rcases kk with _ | kk
      · rw [add_zero, h3 j (by omega), getD_set_self' _ _ (by omega), hr1, hr2]; rfl
      · rw [show j + (kk + 1) = j + 1 + kk by omega, h2 kk (by simp at hk; omega)]; rfl
    · rw [h3 x (by omega), getD_set_ne' _ _ (by omega)]

variable {K : Type} [Field K] [DecidableEq K]

/-- The packed factors of pair kk of row t after s squarings are the scalar table's entry.

That entry is the pair part times the squared row part. -/
theorem packed_factor (G : Gen K) (hN : GenNested G) {n k s kk t : ℕ} (hnk : n + k ≤ G.adicity)
    (hs : s + 1 ≤ k) (hkk : kk < 2 ^ (k - 1 - s)) :
    (G.gen k)⁻¹ ^ bitRev (k - 1) kk * ((G.gen (n + k))⁻¹ ^ bitRev n t) ^ 2 ^ s =
      (G.gen (n + k - s))⁻¹ ^ bitRev (n + k - 1 - s) (t * 2 ^ (k - 1 - s) + kk) := by
  have hb1 : bitRev (k - 1) kk = bitRev (k - 1 - s) kk * 2 ^ s := by
    rw [show k - 1 = (k - 1 - s) + s by omega, bitRev_eq, Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt hkk,
      ← bitRev_eq, show k - 1 - s + s - s = k - 1 - s by omega]
  have hb2 : bitRev (n + k - 1 - s) (t * 2 ^ (k - 1 - s) + kk) =
      bitRev (k - 1 - s) kk * 2 ^ n + bitRev n t := by
    rw [show n + k - 1 - s = n + (k - 1 - s) by omega, bitRev_split n (k - 1 - s) t kk hkk]
  have hg1 : G.gen k = G.gen (n + k) ^ 2 ^ n := by
    rw [← Plonky3Lean.Proofs.Commit.gen_sub G hN hnk (by omega : n ≤ n + k), Nat.add_sub_cancel_left]
  have hg2 : G.gen (n + k - s) = G.gen (n + k) ^ 2 ^ s :=
    Plonky3Lean.Proofs.Commit.gen_sub G hN hnk (by omega)
  rw [hb1, hb2, hg1, hg2, ← inv_pow, ← inv_pow]
  simp only [← pow_mul]
  rw [← pow_add]
  congr 1
  ring

theorem foldPacked_apply {W : ℕ} (lo hi : Fin W → K) (β' wf : K) (rf : Fin W → K) (l : Fin W) :
    foldPacked lo hi (β' / 2 * wf) rf l = foldPair (lo l) (hi l) β' (1 / 2 * (wf * rf l)) := by
  simp only [foldPacked, foldPair]; ring

theorem revIndex_powers_getD (x : K) {m kk : ℕ} (hkk : kk < 2 ^ m) :
    (revIndex (2 ^ m) (powersList x (2 ^ m))).getD kk 0 = x ^ bitRev m kk := by
  simp only [revIndex, powersList, Nat.log_pow (by norm_num : 1 < 2)]
  rw [List.getD_eq_getElem _ _ (by simpa using hkk), List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ (by simpa using bitRev_lt' m kk)]
  simp

/-- The invariant after round r of the packed kernel.

Pair kk of lane l holds the fold of P by 2^(r + 1) at the matching point. -/
def PackedInv (G : Gen K) (P : K[X]) (β : K) (n k W b r : ℕ) (pairs : List (Fin W → K)) : Prop :=
  pairs.length = 2 ^ (k - 1) ∧ ∀ kk < 2 ^ (k - 1 - r), ∀ l : Fin W,
    (pairs.getD kk 0) l = (polyFold P (2 ^ (r + 1)) β).eval (dom G (n + k - 1 - r) ((b * W + l.val) * 2 ^ (k - 1 - r) + kk))

theorem packedRound_eq {W : ℕ} (scalars : List K) (rf : Fin W → K) (pairs : List (Fin W → K)) :
    packedRound scalars rf pairs = writeInPlace (fun lo hi sc => foldPacked lo hi sc rf) scalars 0 pairs := rfl

/-- One later round keeps the invariant.

Pair kk folds pairs 2 kk and 2 kk + 1 with the next challenge power. -/
theorem packedRound_step (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {P : K[X]} {n k W b r : ℕ} (hnk : n + k ≤ G.adicity) (hr : r + 2 ≤ k) (hb : (b + 1) * W ≤ 2 ^ n)
    (β : K) {wf : List K} (hwfl : wf.length = 2 ^ (k - 1))
    (hwf : ∀ kk < 2 ^ (k - 1), wf.getD kk 0 = (G.gen k)⁻¹ ^ bitRev (k - 1) kk)
    {rf : Fin W → K} (hrf : ∀ l : Fin W, rf l = (G.gen (n + k))⁻¹ ^ bitRev n (b * W + l.val))
    {pairs : List (Fin W → K)} (hI : PackedInv G P β n k W b r pairs) :
    PackedInv G P β n k W b (r + 1) (packedRound ((wf.take (2 ^ (k - 1) / 2 ^ (r + 1))).map
      fun x => β ^ 2 ^ (r + 1) / 2 * x) (rf ^ 2 ^ (r + 1)) pairs) := by
  have hsz : 2 ^ (k - 1) / 2 ^ (r + 1) = 2 ^ (k - 1 - (r + 1)) := by
    rw [Nat.pow_div (by omega) (by norm_num)]
  have hlenS : ((wf.take (2 ^ (k - 1) / 2 ^ (r + 1))).map fun x => β ^ 2 ^ (r + 1) / 2 * x).length ≤
      2 ^ (k - 1 - (r + 1)) := by simp [hsz]
  have : Inhabited K := ⟨0⟩
  set S := (wf.take (2 ^ (k - 1) / 2 ^ (r + 1))).map fun x => β ^ 2 ^ (r + 1) / 2 * x with hS
  rw [packedRound_eq]
  obtain ⟨h1, h2', -⟩ := writeInPlace_spec (fun lo hi sc => foldPacked lo hi sc (rf ^ 2 ^ (r + 1))) pairs
    S 0 pairs rfl (by
      rw [zero_add, hI.1]
      calc 2 * _ ≤ 2 * 2 ^ (k - 1 - (r + 1)) := by omega
        _ = 2 ^ (k - 1 - r) := by rw [← pow_succ']; congr 1; omega
        _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (fun _ _ => rfl)
  refine ⟨by rw [h1, hI.1], fun kk hkk l => ?_⟩
  have hkk' : kk < 2 ^ (k - 1) := lt_of_lt_of_le hkk (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hSl : kk < S.length := by
    rw [hS, List.length_map, List.length_take, hwfl, hsz]
    exact lt_of_lt_of_le hkk (le_min le_rfl (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hSg : S.getD kk default = β ^ 2 ^ (r + 1) / 2 * wf.getD kk 0 := by
    rw [hS, List.getD_eq_getElem _ _ (by rw [← hS]; exact hSl), List.getElem_map, List.getElem_take,
      List.getD_eq_getElem _ _ (by omega)]
  have hq := h2' kk hSl
  rw [zero_add] at hq
  have ht : b * W + l.val < 2 ^ n := by have := l.2; nlinarith
  have h2a : 2 ^ (k - 1 - r) = 2 * 2 ^ (k - 1 - (r + 1)) := by rw [← pow_succ']; congr 1; omega
  set i := (b * W + l.val) * 2 ^ (k - 1 - (r + 1)) + kk with hi
  have hidx : (b * W + l.val) * 2 ^ (k - 1 - r) + 2 * kk = 2 * i := by rw [hi, h2a]; ring
  have hi_lt : i < 2 ^ (n + k - 1 - (r + 1)) := by
    rw [show n + k - 1 - (r + 1) = n + (k - 1 - (r + 1)) by omega, pow_add]
    have := Nat.mul_le_mul_right (2 ^ (k - 1 - (r + 1))) (show b * W + l.val + 1 ≤ 2 ^ n by omega)
    rw [Nat.succ_mul] at this; omega
  rw [hq, hSg, foldPacked_apply, Pi.pow_apply, hwf kk hkk', hrf l,
    packed_factor G hN hnk (by omega) hkk, hI.2 (2 * kk) (by omega) l, hI.2 (2 * kk + 1) (by omega) l,
    show (b * W + l.val) * 2 ^ (k - 1 - r) + (2 * kk + 1) = 2 * i + 1 by omega, hidx]
  have hm : n + k - 1 - (r + 1) + 1 = n + k - 1 - r := by omega
  have := foldPair_dom G hV hN h2 (polyFold P (2 ^ (r + 1)) β) (m := n + k - 1 - (r + 1)) (i := i)
    (by omega) hi_lt (β ^ 2 ^ (r + 1))
  rw [hm, polyFold_two_after, show n + k - 1 - r = n + k - (r + 1) by omega] at this
  rw [show n + k - 1 - r = n + k - (r + 1) by omega,
    show n + k - 1 - (r + 1) = n + k - 1 - (r + 1) from rfl, this, ← pow_succ']

/-- The scalars of round r: the first 2^(k - 1 - r) pair factors, times beta^(2^r) / 2. -/
def roundScalars (β : K) (wf : List K) (k r : ℕ) : List K :=
  (wf.take (2 ^ (k - 1) / 2 ^ r)).map fun x => β ^ 2 ^ r / 2 * x

/-- The first round fills the pairs from the row's columns, whatever the buffer held. -/
theorem packedFirst_spec (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {P : K[X]} {n k W b : ℕ} (hnk : n + k ≤ G.adicity) (hk : 1 ≤ k) (hb : (b + 1) * W ≤ 2 ^ n)
    {v : List K} (hv : IsCodeword G P (n + k) v) (β : K) {wf : List K} (hwfl : wf.length = 2 ^ (k - 1))
    (hwf : ∀ kk < 2 ^ (k - 1), wf.getD kk 0 = (G.gen k)⁻¹ ^ bitRev (k - 1) kk)
    {rf : Fin W → K} (hrf : ∀ l : Fin W, rf l = (G.gen (n + k))⁻¹ ^ bitRev n (b * W + l.val))
    (init : List (Fin W → K)) (hinit : init.length = 2 ^ (k - 1)) :
    PackedInv G P β n k W b 0 ((roundScalars β wf k 0).zipIdx.foldl (fun ps e =>
      ps.set e.2 (foldPacked (fun l => v.getD ((b * W + l.val) * 2 ^ k + 2 * e.2) 0)
        (fun l => v.getD ((b * W + l.val) * 2 ^ k + (2 * e.2 + 1)) 0) e.1 rf)) init) := by
  have : Inhabited K := ⟨0⟩
  have hSl : (roundScalars β wf k 0).length = 2 ^ (k - 1) := by simp [roundScalars, hwfl]
  obtain ⟨h1, h2', -⟩ := writeFresh_spec (fun kk sc => foldPacked (fun l => v.getD ((b * W + l.val) * 2 ^ k + 2 * kk) 0)
    (fun l => v.getD ((b * W + l.val) * 2 ^ k + (2 * kk + 1)) 0) sc rf) (roundScalars β wf k 0) 0 init
    (by rw [zero_add, hSl, hinit])
  refine ⟨by rw [writeFresh] at h1; rw [h1, hinit], fun kk hkk l => ?_⟩
  simp only [Nat.sub_zero] at hkk ⊢
  have hq := h2' kk (by omega)
  rw [zero_add] at hq
  simp only [writeFresh] at hq
  have hSg : (roundScalars β wf k 0).getD kk default = β ^ 2 ^ 0 / 2 * wf.getD kk 0 := by
    rw [roundScalars, List.getD_eq_getElem _ _ (by simp [hwfl]; omega), List.getElem_map, List.getElem_take,
      List.getD_eq_getElem _ _ (by omega)]
  have ht : b * W + l.val < 2 ^ n := by have := l.2; nlinarith
  set i := (b * W + l.val) * 2 ^ (k - 1) + kk with hi
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hi_lt : i < 2 ^ (n + k - 1) := by
    rw [show n + k - 1 = n + (k - 1) by omega, pow_add]
    have := Nat.mul_le_mul_right (2 ^ (k - 1)) (show b * W + l.val + 1 ≤ 2 ^ n by omega)
    rw [Nat.succ_mul] at this; omega
  have hN1 : n + k - 1 + 1 = n + k := by omega
  have hc0 : (b * W + l.val) * 2 ^ k + 2 * kk = 2 * i := by rw [hi, h2k]; ring
  have hc1 : (b * W + l.val) * 2 ^ k + (2 * kk + 1) = 2 * i + 1 := by omega
  have hi2 : 2 * i + 1 < 2 ^ (n + k) := by rw [← hN1, pow_succ]; omega
  rw [hq, hSg, foldPacked_apply, hwf kk (by omega), hrf l, hc0, hc1, hv.2 _ (by omega), hv.2 _ hi2]
  have hf := packed_factor G hN (s := 0) (t := b * W + l.val) hnk (by omega) (by simpa using hkk)
  simp only [pow_zero, pow_one, Nat.sub_zero] at hf
  rw [hf]
  have := foldPair_dom G hV hN h2 P (m := n + k - 1) (i := i) (by omega) hi_lt β
  rw [hN1] at this
  simpa using this

/-- The later rounds keep the invariant up to the last round. -/
theorem packedRounds_spec (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {P : K[X]} {n k W b : ℕ} (hnk : n + k ≤ G.adicity) (hb : (b + 1) * W ≤ 2 ^ n)
    (β : K) {wf : List K} (hwfl : wf.length = 2 ^ (k - 1))
    (hwf : ∀ kk < 2 ^ (k - 1), wf.getD kk 0 = (G.gen k)⁻¹ ^ bitRev (k - 1) kk)
    {rf : Fin W → K} (hrf : ∀ l : Fin W, rf l = (G.gen (n + k))⁻¹ ^ bitRev n (b * W + l.val)) :
    ∀ (m r : ℕ) (pairs : List (Fin W → K)), r + m + 1 = k → PackedInv G P β n k W b r pairs →
      PackedInv G P β n k W b (k - 1)
        (packedRounds ((List.range m).map fun i => roundScalars β wf k (r + 1 + i)) (rf ^ 2 ^ r) pairs)
  | 0, r, pairs, hrm, hI => by
    simp only [List.range_zero, List.map_nil, packedRounds]
    rwa [show k - 1 = r by omega]
  | m + 1, r, pairs, hrm, hI => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, packedRounds, ← pow_mul, ← pow_succ]
    have hstep := packedRound_step G hV hN h2 hnk (by omega) hb β hwfl hwf hrf hI
    have := packedRounds_spec G hV hN h2 hnk hb β hwfl hwf hrf m (r + 1) _ (by omega) hstep
    convert this using 2
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply]; congr 1; omega
    · simp [roundScalars]

/-- The packed kernel returns the scalar fold.

This holds for every power-of-two packing width no taller than the matrix, and every scratch buffer. -/
theorem fold_matrix_packed_eq (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {W lw n k : ℕ} (hW : W = 2 ^ lw) (hlw : lw ≤ n) (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity)
    {v : List K} (hv : v.length = 2 ^ (n + k)) (init : List (Fin W → K)) (hinit : init.length = 2 ^ (k - 1))
    (β : K) :
    fold_matrix_packed G W init β k v = fold_matrix_scalar G β k v := by
  rw [fold_matrix_scalar_rows G hV hN h2 hk hnk hv β]
  subst hW
  have hlen : v.length / 2 ^ k = 2 ^ n := by rw [hv, pow_add, Nat.mul_div_cancel _ (by positivity)]
  have hppr : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hg : G.gen (n + k) ≠ 0 := (hV _ hnk).ne_zero (by positivity)
  have hw : G.gen k ≠ 0 := (hV k (by omega)).ne_zero (by positivity)
  have hmod : 2 ^ n % 2 ^ lw = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hlw)
  have hnb : 2 ^ n / 2 ^ lw = 2 ^ (n - lw) := Nat.pow_div hlw (by norm_num)
  have hne : ¬ (2 ^ k ≠ 2 * 2 ^ (k - 1)) := by simp [hppr]
  unfold fold_matrix_packed
  simp only [hlen]
  simp only [isPow2, Nat.log_pow (by norm_num : 1 < 2), decide_true, Nat.pow_le_pow_right (by norm_num : 0 < 2) hlw,
    hmod, and_self, not_true_eq_false, ↓reduceIte, hne, log2Strict_pow, hnb,
    gen_get_of_le G hnk, gen_get_of_le G (show k ≤ G.adicity by omega), inv,
    p3_commit.domain.mirror.inv, hg, hw, Option.bind_eq_bind, Option.bind_some]
  set wf := revIndex (2 ^ (k - 1)) (powersList (G.gen k)⁻¹ (2 ^ (k - 1))) with hwfdef
  have hwfl : wf.length = 2 ^ (k - 1) := by simp [hwfdef, revIndex]
  have hwf : ∀ kk < 2 ^ (k - 1), wf.getD kk 0 = (G.gen k)⁻¹ ^ bitRev (k - 1) kk :=
    fun kk hkk => revIndex_powers_getD _ hkk
  have hmap : (List.range k).map (fun r => (wf.take (2 ^ (k - 1) / 2 ^ r)).map fun x => β ^ 2 ^ r / 2 * x) =
      (List.range k).map (roundScalars β wf k) := rfl
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hwfl hwf hinit ⊢
  rw [show (List.range (k' + 1)).map (fun r => (wf.take (2 ^ k' / 2 ^ r)).map fun x => β ^ 2 ^ r / 2 * x) =
      roundScalars β wf (k' + 1) 0 :: (List.range k').map (fun i => roundScalars β wf (k' + 1) (0 + 1 + i)) by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]; simp [roundScalars, Function.comp_def, add_comm]]
  simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
  have hP := isCodeword_wordPoly G hV (N := n + (k' + 1)) hnk hv
  set P := wordPoly G (n + (k' + 1)) v
  have hrf : ∀ b < 2 ^ (n - lw), ∀ l : Fin (2 ^ lw),
      ((G.gen (n + (k' + 1)))⁻¹ ^ 2 ^ (n - lw)) ^ bitRev lw l.val *
        (revIndex (2 ^ (n - lw)) (powersList (G.gen (n + (k' + 1)))⁻¹ (2 ^ (n - lw)))).getD b 0 =
      (G.gen (n + (k' + 1)))⁻¹ ^ bitRev n (b * 2 ^ lw + l.val) := by
    intro b hb l
    rw [revIndex_powers_getD _ hb, show n = (n - lw) + lw by omega, bitRev_split (n - lw) lw b l.val l.2,
      ← pow_mul, ← pow_add, show n - lw + lw - lw = n - lw by omega, mul_comm (2 ^ (n - lw))]
  congr 1
  have hblock : ∀ b < 2 ^ (n - lw), ∀ l : Fin (2 ^ lw),
      ((packedRounds (List.map (fun i => roundScalars β wf (k' + 1) (0 + 1 + i)) (List.range k'))
          (fun l => ((G.gen (n + (k' + 1)))⁻¹ ^ 2 ^ (n - lw)) ^ bitRev lw ↑l *
            (revIndex (2 ^ (n - lw)) (powersList (G.gen (n + (k' + 1)))⁻¹ (2 ^ (n - lw)))).getD b 0)
          (List.foldl (fun ps e => ps.set e.2
            (foldPacked (fun l => v.getD ((b * 2 ^ lw + ↑l) * 2 ^ (k' + 1) + 2 * e.2) 0)
              (fun l => v.getD ((b * 2 ^ lw + ↑l) * 2 ^ (k' + 1) + (2 * e.2 + 1)) 0) e.1 fun l =>
              ((G.gen (n + (k' + 1)))⁻¹ ^ 2 ^ (n - lw)) ^ bitRev lw ↑l *
                (revIndex (2 ^ (n - lw)) (powersList (G.gen (n + (k' + 1)))⁻¹ (2 ^ (n - lw)))).getD b 0))
            init (roundScalars β wf (k' + 1) 0).zipIdx)).getD 0 0) l =
      (polyFold P (2 ^ (k' + 1)) β).eval (dom G n (b * 2 ^ lw + l.val)) := by
    intro b hb l
    have hbW : (b + 1) * 2 ^ lw ≤ 2 ^ n := by
      have := Nat.mul_le_mul_right (2 ^ lw) (show b + 1 ≤ 2 ^ (n - lw) by omega)
      rwa [← pow_add, show n - lw + lw = n by omega] at this
    have hrf' := hrf b hb
    have hI0 := packedFirst_spec G hV hN h2 (n := n) (k := k' + 1) (W := 2 ^ lw) (b := b) hnk hk hbW hP β
      (by simpa using hwfl) (by simpa using hwf) hrf' init (by simpa using hinit)
    have hIk := packedRounds_spec G hV hN h2 (k := k' + 1) (b := b) hnk hbW β (by simpa using hwfl)
      (by simpa using hwf) hrf' k' 0 _ (by omega) hI0
    simp only [pow_zero, pow_one] at hIk
    have := hIk.2 0 (by simp) l
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, add_zero] at this
    rw [this, show n + (k' + 1) - 1 - k' = n by omega]
  apply List.ext_getElem
  · rw [length_flatMap_blocks _ (2 ^ lw) _ (fun i _ => List.length_ofFn), List.length_map, List.length_range,
      ← pow_add, show n - lw + lw = n by omega]
  · intro t h1 h2'
    have ht : t < 2 ^ n := by simpa using h2'
    rw [← List.getD_eq_getElem _ 0, List.getElem_map, List.getElem_range,
      fold_row_codeword G hV hN h2 hnk hP ht β]
    have hl : t % 2 ^ lw < 2 ^ lw := Nat.mod_lt _ (by positivity)
    have hb : t / 2 ^ lw < 2 ^ (n - lw) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show n - lw + lw = n by omega]; exact ht
    conv_lhs => rw [show t = t / 2 ^ lw * 2 ^ lw + t % 2 ^ lw from (Nat.div_add_mod' t _).symm]
    rw [getD_flatMap_blocks _ (2 ^ lw) _ (fun i _ => List.length_ofFn) _ _ hb hl,
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_ofFn,
      hblock _ hb ⟨t % 2 ^ lw, hl⟩, Nat.div_add_mod']

/-- The matrix fold returns the scalar fold, whichever path it dispatches to. -/
theorem fold_matrix_eq_scalar (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (W field_bits : ℕ) {n k : ℕ} (hk : 1 ≤ k) (hnk : n + k ≤ G.adicity)
    {v : List K} (hv : v.length = 2 ^ (n + k)) (init : List (Fin W → K)) (hinit : init.length = 2 ^ (k - 1))
    (β : K) :
    fold_matrix G W field_bits init β k v = fold_matrix_scalar G β k v := by
  have hlen : v.length / 2 ^ k = 2 ^ n := by rw [hv, pow_add, Nat.mul_div_cancel _ (by positivity)]
  unfold fold_matrix
  split_ifs with hu
  · simp only [use_packed_fold, isPow2, hlen, Bool.and_eq_true, decide_eq_true_eq] at hu
    obtain ⟨⟨⟨-, hp⟩, hle⟩, -⟩ := hu
    have hlw : Nat.log 2 W ≤ n := by
      rw [← hp] at hle; exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
    exact fold_matrix_packed_eq G hV hN h2 hp.symm hlw hk hnk hv init hinit β
  · rfl

end Plonky3Lean.Proofs.Fri
