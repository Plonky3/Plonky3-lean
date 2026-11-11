module

public import Plonky3Lean.Proofs.ZkCodes.ReedSolomon

@[expose] public section

/-!
# The batch encodings

The packed batch encoding transforms one matrix whose column c is the coefficient vector of message c.

The trait's default encodes each message and interleaves the codewords.

The two agree entry by entry.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.ZkCodes

open Finset Polynomial p3_dft.mirror Plonky3Lean.Spec.Dft
open p3_zk_codes.reed_solomon.mirror Plonky3Lean.Proofs.Dft
open p3_zk_codes.encoding.mirror (Mat stack_codewords)

variable {K : Type _} [Field K]

/-! ## Writes into a flat buffer -/

theorem iteT {α : Type _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := by
  simp [h]

theorem iteF {α : Type _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := by
  simp [h]

theorem eq_mul_add_iff {w c q i : ℕ} (hc : c < w) : i = q * w + c ↔ i % w = c ∧ i / w = q := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
  · rintro ⟨h1, h2⟩
    rw [← h1, ← h2, Nat.mul_comm, Nat.div_add_mod]

/-- Writing rows off, ..., off + n - 1 of column c of a buffer of width w. -/
theorem foldl_write_col {w c : ℕ} (hc : c < w) (off n : ℕ) (val : ℕ → K) (acc : ℕ → K) (i : ℕ) :
    (List.range n).foldl (fun acc row => fun i => if i = (off + row) * w + c then val row else acc i)
      acc i =
      if i % w = c ∧ off ≤ i / w ∧ i / w < off + n then val (i / w - off) else acc i := by
  induction n generalizing i with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    split_ifs with h <;> first | rfl | omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    show (if i = (off + n) * w + c then val n else _) = _
    by_cases h0 : i = (off + n) * w + c
    · have h := (eq_mul_add_iff hc).mp h0
      rw [iteT h0,
        iteT (⟨h.1, by omega, by omega⟩ :
          i % w = c ∧ off ≤ i / w ∧ i / w < off + (n + 1)), h.2, Nat.add_sub_cancel_left]
    · have h : ¬ (i % w = c ∧ i / w = off + n) := fun h => h0 ((eq_mul_add_iff hc).mpr h)
      rw [iteF h0, ih]
      by_cases h' : i % w = c ∧ off ≤ i / w ∧ i / w < off + n
      · rw [iteT h', iteT (⟨h'.1, h'.2.1, by omega⟩ :
          i % w = c ∧ off ≤ i / w ∧ i / w < off + (n + 1))]
      · rw [iteF h', iteF (by omega)]

/-- Entry r of the coefficient vector of a message and its randomness.

The vector is the message, the randomness, then zeros. -/
def cell (l t : ℕ) (msg rnd : List K) (r : ℕ) : K :=
  if r < l then msg.getD r 0 else if r < l + t then rnd.getD (r - l) 0 else 0

/-- The flat buffer once columns 0, ..., n - 1 are written. -/
def bufAfter (l t w n : ℕ) (ms rs : List (List K)) (i : ℕ) : K :=
  if i % w < n then cell l t (ms.getD (i % w) []) (rs.getD (i % w) []) (i / w) else 0

/-- One column of the packed batch encoding, written into the buffer. -/
def colStep (rs : ReedSolomonZkEncoding) (width : ℕ) (coeffs : ℕ → K)
    (mrc : (List K × List K) × ℕ) : Option (ℕ → K) :=
  let ((msg, rnd), column) := mrc
  if msg.length ≠ rs.msg_len then none
  else if rnd.length ≠ rs.t then none
  else
    let coeffs := (List.range msg.length).foldl (fun acc row =>
      fun i => if i = row * width + column then msg.getD row 0 else acc i) coeffs
    some ((List.range rnd.length).foldl (fun acc row =>
      fun i => if i = (rs.msg_len + row) * width + column then rnd.getD row 0 else acc i) coeffs)

theorem colStep_bufAfter (rs : ReedSolomonZkEncoding) {w n : ℕ} (hn : n < w) (ms rss : List (List K))
    {msg rnd : List K} (hm : ms.getD n [] = msg) (hr : rss.getD n [] = rnd)
    (hml : msg.length = rs.msg_len) (hrl : rnd.length = rs.t) :
    colStep rs w (bufAfter rs.msg_len rs.t w n ms rss) ((msg, rnd), n) =
      some (bufAfter rs.msg_len rs.t w (n + 1) ms rss) := by
  simp only [colStep, hml, hrl, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq]
  funext i
  have h1 := foldl_write_col (K := K) hn rs.msg_len rs.t (fun row => rnd.getD row 0)
  have h0 := foldl_write_col (K := K) hn 0 rs.msg_len (fun row => msg.getD row 0)
  simp only [zero_add, Nat.sub_zero, zero_le, true_and] at h0
  rw [h1, h0]
  unfold bufAfter cell
  by_cases hc : i % w = n
  · simp only [hc, hm, hr, true_and, lt_add_one, ↓reduceIte, Nat.lt_irrefl]
    by_cases ha : i / w < rs.msg_len
    · simp [ha, show ¬ rs.msg_len ≤ i / w by omega]
    · by_cases hb : i / w < rs.msg_len + rs.t
      · simp [ha, hb, show rs.msg_len ≤ i / w by omega]
      · simp [ha, hb]
  · have hc' : ¬ (i % w = n ∧ rs.msg_len ≤ i / w ∧ i / w < rs.msg_len + rs.t) := fun h => hc h.1
    have hc'' : ¬ (i % w = n ∧ i / w < rs.msg_len) := fun h => hc h.1
    rw [iteF hc', iteF hc'']
    by_cases hlt : i % w < n
    · rw [iteT hlt, iteT (show i % w < n + 1 by omega)]
    · rw [iteF hlt, iteF (show ¬ i % w < n + 1 by omega)]

theorem foldlM_colStep (rs : ReedSolomonZkEncoding) {w : ℕ} (ms rss : List (List K))
    (L : List (List K × List K)) (n : ℕ) (hw : n + L.length = w)
    (hL : ∀ j (hj : j < L.length), L[j] = (ms.getD (n + j) [], rss.getD (n + j) []))
    (hlen : ∀ x ∈ L, x.1.length = rs.msg_len ∧ x.2.length = rs.t) :
    (L.zipIdx n).foldlM (colStep rs w) (bufAfter rs.msg_len rs.t w n ms rss) =
      some (bufAfter rs.msg_len rs.t w w ms rss) := by
  induction L generalizing n with
  | nil => simp at hw; subst hw; rfl
  | cons x L ih =>
    rw [List.zipIdx_cons, List.foldlM_cons]
    have hx := hL 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at hx
    obtain ⟨msg, rnd⟩ := x
    simp only [Prod.mk.injEq] at hx
    have hl := hlen (msg, rnd) (List.mem_cons_self ..)
    rw [colStep_bufAfter rs (by simp at hw; omega) ms rss hx.1.symm hx.2.symm hl.1 hl.2,
      Option.bind_eq_bind, Option.bind_some]
    refine ih (n + 1) (by simp at hw; omega) (fun j hj => ?_) (fun y hy => hlen y (List.mem_cons_of_mem _ hy))
    have := hL (j + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem bufAfter_zero (l t w : ℕ) (ms rs : List (List K)) : bufAfter l t w 0 ms rs = fun _ => 0 := by
  funext i; simp [bufAfter]

theorem cell_eq_resize {l t m : ℕ} {msg rnd : List K} (hm : msg.length = l) (hr : rnd.length = t)
    (hle : l + t ≤ m) (j : ℕ) : cell l t msg rnd j = (resize (msg ++ rnd) m).getD j 0 := by
  rw [getD_resize (by omega), hm, hr]; rfl

/-- Column c of the packed batch encoding is the encoding of message c with randomness c, at omega^r. -/
theorem encode_batch_computes {w : ℕ} {dft_batch : ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    {ω : K} {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) {ms rss : List (List K)} (hw : ms.length = w) (hw0 : w ≠ 0)
    (hrw : rss.length = w)
    (hlen : ∀ c < w, (ms.getD c []).length = rs.msg_len ∧ (rss.getD c []).length = rs.t) :
    Computes (rs.encode_batch_with_randomness dft_batch ms rss) rs.m
      (fun r c => encValue (ms.getD c []) (rss.getD c []) (ω ^ r)) := by
  have hne : ms.isEmpty = false := by
    cases ms with
    | nil => simp at hw; exact absurd hw.symm (Ne.symm hw0)
    | cons _ _ => rfl
  have hfold : ((ms.zip rss).zipIdx).foldlM (colStep rs w) (fun _ => 0) =
      some (bufAfter rs.msg_len rs.t w w ms rss) := by
    rw [← bufAfter_zero rs.msg_len rs.t w ms rss]
    refine foldlM_colStep rs ms rss (ms.zip rss) 0 (by simp [hw, hrw]) (fun j hj => ?_) ?_
    · simp only [List.getElem_zip, zero_add]
      simp at hj
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      simp only [List.getElem_zip]
      simp at hj
      have := hlen j (by omega)
      rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
  obtain ⟨y, hy, hyi⟩ := hd (fun r c => bufAfter rs.msg_len rs.t w w ms rss (r * w + c.val))
  refine ⟨y, ?_, fun r hr => ?_⟩
  · simp only [ReedSolomonZkEncoding.encode_batch_with_randomness, hne, hw, hrw, ne_eq,
      not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
    unfold colStep at hfold
    simp only [ne_eq] at hfold
    rw [hfold]
    exact hy
  · funext c
    rw [hyi r hr]
    have hc := hlen c.val c.isLt
    have hcol : ∀ j, bufAfter rs.msg_len rs.t w w ms rss (j * w + c.val) =
        (resize (ms.getD c [] ++ rss.getD c []) rs.m).getD j 0 := by
      intro j
      have hmod := (eq_mul_add_iff c.isLt).mp (rfl : j * w + c.val = j * w + c.val)
      simp only [bufAfter, hmod.1, hmod.2, c.isLt, ↓reduceIte]
      exact cell_eq_resize hc.1 hc.2 hle j
    beta_reduce
    rw [encValue, ← dft_coeffs ω (msg := ms.getD c []) (r := rss.getD c []) (m := rs.m) (by omega) r]
    simp only [dft, Finset.sum_apply, Pi.smul_apply, hcol]

/-! ## The default batch encoding: encode each message, then interleave -/

/-- The interleaving buffer once codewords 0, ..., n - 1 are written. -/
def stackAfter (h w n : ℕ) (cws : List (Mat K)) (i : ℕ) : K :=
  if i % w < n ∧ i / w < h then ((cws.getD (i % w) ⟨0, 0, fun _ _ => 0⟩).get (i / w) 0) else 0

/-- One codeword of the interleaving, written into the buffer. -/
def stackStep (height width : ℕ) (values : ℕ → K) (cc : Mat K × ℕ) : Option (ℕ → K) :=
  let (codeword, column) := cc
  if codeword.width ≠ 1 then none
  else if codeword.height ≠ height then none
  else some ((List.range codeword.height).foldl (fun acc row =>
    fun i => if i = row * width + column then codeword.get row 0 else acc i) values)

theorem foldlM_stackStep {h w : ℕ} (cws L : List (Mat K)) (n : ℕ) (hw : n + L.length = w)
    (hL : ∀ j (hj : j < L.length), L[j] = cws.getD (n + j) ⟨0, 0, fun _ _ => 0⟩)
    (hshape : ∀ x ∈ L, x.width = 1 ∧ x.height = h) :
    (L.zipIdx n).foldlM (stackStep h w) (stackAfter h w n cws) = some (stackAfter h w w cws) := by
  induction L generalizing n with
  | nil => simp at hw; subst hw; rfl
  | cons x L ih =>
    rw [List.zipIdx_cons, List.foldlM_cons]
    have hx := hL 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at hx
    have hs := hshape x (List.mem_cons_self ..)
    have hn : n < w := by simp at hw; omega
    have hstep : stackStep h w (stackAfter h w n cws) (x, n) = some (stackAfter h w (n + 1) cws) := by
      simp only [stackStep, hs.1, hs.2, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq]
      funext i
      have h0 := foldl_write_col (K := K) hn 0 h (fun row => x.get row 0) (stackAfter h w n cws) i
      simp only [zero_add, Nat.sub_zero, zero_le, true_and] at h0
      rw [h0]
      unfold stackAfter
      by_cases hc : i % w = n
      · by_cases hr : i / w < h
        · rw [iteT ⟨hc, hr⟩, iteT (show i % w < n + 1 ∧ i / w < h by omega), hc, ← hx]
        · rw [iteF (show ¬ (i % w = n ∧ i / w < h) by omega), iteF (show ¬ (i % w < n ∧ i / w < h) by omega),
            iteF (show ¬ (i % w < n + 1 ∧ i / w < h) by omega)]
      · rw [iteF (show ¬ (i % w = n ∧ i / w < h) by omega)]
        by_cases hlt : i % w < n ∧ i / w < h
        · rw [iteT hlt, iteT (show i % w < n + 1 ∧ i / w < h by omega)]
        · rw [iteF hlt, iteF (show ¬ (i % w < n + 1 ∧ i / w < h) by omega)]
    rw [hstep, Option.bind_eq_bind, Option.bind_some]
    refine ih (n + 1) (by simp at hw; omega) (fun j hj => ?_) (fun y hy => hshape y (List.mem_cons_of_mem _ hy))
    have := hL (j + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- Interleaving w single-column codewords of height h: entry (r, c) is entry r of codeword c. -/
theorem stack_codewords_eq {h : ℕ} {cws : List (Mat K)} (hne : cws ≠ [])
    (hshape : ∀ x ∈ cws, x.width = 1 ∧ x.height = h) :
    ∃ M, stack_codewords cws = some M ∧ M.height = h ∧ M.width = cws.length ∧
      ∀ r < h, ∀ c < cws.length, M.get r c = (cws.getD c ⟨0, 0, fun _ _ => 0⟩).get r 0 := by
  obtain ⟨c0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hh : c0.height = h := (hshape c0 (List.mem_cons_self ..)).2
  have hz : stackAfter h (c0 :: rest).length 0 (c0 :: rest) = fun _ => 0 := by
    funext i; simp [stackAfter]
  have hfold := foldlM_stackStep (h := h) (w := (c0 :: rest).length) (c0 :: rest) (c0 :: rest) 0
    (by simp) (fun j hj => by rw [zero_add, List.getD_eq_getElem _ _ hj]) hshape
  rw [hz] at hfold
  refine ⟨⟨h, (c0 :: rest).length, fun r c => stackAfter h (c0 :: rest).length (c0 :: rest).length
    (c0 :: rest) (r * (c0 :: rest).length + c)⟩, ?_, rfl, rfl, fun r hr c hc => ?_⟩
  · unfold stack_codewords
    unfold stackStep at hfold
    simp only [ne_eq] at hfold
    simp only [hh]
    rw [hfold]
    rfl
  · have hmod := (eq_mul_add_iff hc).mp (rfl : r * (c0 :: rest).length + c = r * (c0 :: rest).length + c)
    simp only [stackAfter, hmod.1, hmod.2, hc, hr, and_self, ↓reduceIte]

theorem mapM_option_some {α β : Type _} (f : α → Option β) (L : List α)
    (h : ∀ x ∈ L, (f x).isSome) :
    ∃ out, L.mapM f = some out ∧ out.length = L.length ∧
      ∀ j (hj : j < L.length) (hj' : j < out.length), f L[j] = some out[j] := by
  induction L with
  | nil => exact ⟨[], rfl, rfl, fun j hj => by simp at hj⟩
  | cons x L ih =>
    obtain ⟨out, hout, hlen, hget⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    refine ⟨b :: out, ?_, by simp [hlen], fun j hj hj' => ?_⟩
    · simp [List.mapM_cons, hb, hout]
    · cases j with
      | zero => simpa using hb
      | succ j => simpa using hget j (by simpa using hj) (by simpa using hj')

/-- The trait's default batch encoding, with the Reed-Solomon encoding.

Entry (r, c) is the encoding of message c with randomness c, at omega^r. -/
theorem default_batch_computes {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)} {ω : K}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) {ms rss : List (List K)} (hne : ms ≠ [])
    (hrw : rss.length = ms.length)
    (hlen : ∀ c < ms.length, (ms.getD c []).length = rs.msg_len ∧ (rss.getD c []).length = rs.t) :
    ∃ M, p3_zk_codes.encoding.mirror.encode_batch_with_randomness
        (fun msg r => (rs.encode_with_randomness dft_batch msg r).map
          fun y => (⟨rs.m, 1, fun r _ => y r⟩ : Mat K)) ms rss = some M ∧
      M.height = rs.m ∧ M.width = ms.length ∧
      ∀ r < rs.m, ∀ c < ms.length, M.get r c = encValue (ms.getD c []) (rss.getD c []) (ω ^ r) := by
  set f := fun (mr : List K × List K) => (rs.encode_with_randomness dft_batch mr.1 mr.2).map
    fun y => (⟨rs.m, 1, fun r _ => y r⟩ : Mat K) with hf
  have hzl : (ms.zip rss).length = ms.length := by simp [hrw]
  have hzget : ∀ j (hj : j < (ms.zip rss).length), (ms.zip rss)[j] = (ms.getD j [], rss.getD j []) := by
    intro j hj
    simp only [List.getElem_zip]
    rw [List.getD_eq_getElem _ _ (by simp at hj; omega), List.getD_eq_getElem _ _ (by simp at hj; omega)]
  have hcomp : ∀ j (hj : j < (ms.zip rss).length), ∃ y : ℕ → K, f (ms.zip rss)[j] = some ⟨rs.m, 1, fun r _ => y r⟩ ∧
      ∀ r < rs.m, y r = encValue (ms.getD j []) (rss.getD j []) (ω ^ r) := by
    intro j hj
    have hl := hlen j (by omega)
    obtain ⟨y, hy, hyi⟩ := encode_with_randomness_computes hd hle hl.1 hl.2
    exact ⟨y, by rw [hzget j hj]; simp only [hf, hy, Option.map_some], hyi⟩
  obtain ⟨cws, hcws, hcl, hcg⟩ := mapM_option_some f (ms.zip rss) (fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨y, hy, -⟩ := hcomp j hj
    rw [hy]; rfl)
  have hshape : ∀ x ∈ cws, x.width = 1 ∧ x.height = rs.m := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨y, hy, -⟩ := hcomp j (by omega)
    rw [hcg j (by omega) hj] at hy
    rw [Option.some.inj hy]; exact ⟨rfl, rfl⟩
  have hcne : cws ≠ [] := by
    intro h
    rw [h, List.length_nil, hzl] at hcl
    exact hne (List.length_eq_zero_iff.mp hcl.symm)
  obtain ⟨M, hM, hMh, hMw, hMg⟩ := stack_codewords_eq hcne hshape
  have hmsne : ms.isEmpty = false := by
    cases ms with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  refine ⟨M, ?_, hMh, by rw [hMw, hcl, hzl], fun r hr c hc => ?_⟩
  · simp only [p3_zk_codes.encoding.mirror.encode_batch_with_randomness, hmsne, hrw, ne_eq,
      not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [show (fun mr : List K × List K => _) = f from rfl, hcws]
    exact hM
  · have hc' : c < cws.length := by omega
    rw [hMg r (by omega) c hc', List.getD_eq_getElem _ _ hc']
    obtain ⟨y, hy, hyi⟩ := hcomp c (by omega)
    rw [hcg c (by omega) hc'] at hy
    rw [Option.some.inj hy]
    exact hyi r hr

end Plonky3Lean.Proofs.ZkCodes
