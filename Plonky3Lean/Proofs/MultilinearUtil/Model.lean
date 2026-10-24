module

public import P3MultilinearUtil.Model

@[expose] public section

/-!
# Packing: lane-wise operations are entry-wise operations

Packing groups W consecutive entries, and unpacking reads the lanes back in order.

So run a lane-wise operation on the packed prefix, then the same operation on the tail.

The result is the operation applied to every entry.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open p3_multilinear_util.mirror

variable {K L : Type _}

theorem ite_of_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a := by
  simp [h]

theorem ite_of_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : ite c a b = b := by
  simp [h]

theorem to_ext_iter_cons {W : ℕ} (a : Fin W → K) (v : List (Fin W → K)) :
    to_ext_iter (a :: v) = List.ofFn a ++ to_ext_iter v := by simp [to_ext_iter]

theorem to_ext_iter_append {W : ℕ} (u v : List (Fin W → K)) :
    to_ext_iter (u ++ v) = to_ext_iter u ++ to_ext_iter v := by simp [to_ext_iter]

@[simp] theorem length_packN [Zero K] (W k : ℕ) (l : List K) : (packN W k l).length = k := by
  induction k generalizing l <;> simp [packN, *]

/-- Unpacking the first k groups gives back the first k W entries. -/
theorem to_ext_iter_packN [Zero K] {W k : ℕ} {l : List K} (h : k * W ≤ l.length) :
    to_ext_iter (packN W k l) = l.take (k * W) := by
  induction k generalizing l with
  | zero => simp [packN, to_ext_iter]
  | succ k ih =>
    rw [packN, to_ext_iter_cons, ih (by simp; rw [Nat.succ_mul] at h; omega)]
    rw [Nat.succ_mul, Nat.add_comm, List.take_add]
    congr 1
    exact List.ext_getElem (by simp; rw [Nat.succ_mul] at h; omega) fun i _ h2 => by
      simp only [List.length_take] at h2
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

/-- A lane-wise map on the packed groups is the entry-wise map, packed. -/
theorem packN_map [Zero K] [Zero L] {W k : ℕ} (f : K → L) (hf : f 0 = 0) (l : List K) :
    (packN W k l).map (fun v i => f (v i)) = packN W k (l.map f) := by
  induction k generalizing l with
  | zero => simp [packN]
  | succ k ih =>
    simp only [packN, List.map_cons, ih, List.map_drop]
    congr 1
    funext i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[(i : ℕ)]? <;> simp [hf]

/-- The packed prefix and the suffix together are the whole slice. -/
theorem pack_slice_with_suffix_whole [Zero K] (W : ℕ) (l : List K) :
    to_ext_iter (pack_slice_with_suffix W l).1 ++ (pack_slice_with_suffix W l).2 = l := by
  have h := Nat.div_add_mod l.length W
  rw [pack_slice_with_suffix, to_ext_iter_packN (by rw [Nat.mul_comm]; omega)]
  rw [show l.length - l.length % W = l.length / W * W by rw [Nat.mul_comm]; omega]
  exact List.take_append_drop _ _

/-- An entry-wise map, run lane-wise on the packed prefix and entry-wise on the suffix, is the map. -/
theorem map_pack_slice_with_suffix [Zero K] [Zero L] (W : ℕ) (f : K → L) (hf : f 0 = 0) (l : List K) :
    to_ext_iter ((pack_slice_with_suffix W l).1.map fun v i => f (v i)) ++
      (pack_slice_with_suffix W l).2.map f = l.map f := by
  have := pack_slice_with_suffix_whole W (l.map f)
  simp only [pack_slice_with_suffix, List.length_map] at this ⊢
  rw [packN_map f hf, List.map_drop]
  exact this

/-- A loop that cannot fail returns the values it computes. -/
theorem mapM_some {α β : Type _} (xs : List α) (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a t ih => simp [List.mapM_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem length_chunks {c m : ℕ} (hc : 0 < c) {l : List K} (h : l.length = m * c) :
    (chunks c l).length = m := by
  simp only [chunks, List.length_map, List.length_range, h]
  rw [show m * c + c - 1 = (c - 1) + m * c by omega, Nat.add_mul_div_right _ _ hc,
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem length_of_mem_chunks {c m : ℕ} (hc : 0 < c) {l : List K} (h : l.length = m * c)
    {ch : List K} (hch : ch ∈ chunks c l) : ch.length = c := by
  have hm := length_chunks hc h
  simp only [chunks, List.length_map, List.length_range] at hm
  simp only [chunks, List.mem_map, List.mem_range] at hch
  obtain ⟨j, hj, rfl⟩ := hch
  rw [hm] at hj
  have : (j + 1) * c ≤ m * c := Nat.mul_le_mul_right c hj
  simp only [List.length_take, List.length_drop, h]
  rw [Nat.succ_mul] at this
  omega

/-- A loop over idx < s that rewrites row idx and writes row idx + s, both from row idx alone.

It reads no row it has written, so it is the simultaneous update. -/
theorem pairLoop_getElem {A : Type _} (f g : A → A) (d : A) (s : ℕ) (buf : List A)
    (hbuf : 2 * s ≤ buf.length) {j : ℕ} (hj : j ≤ s) :
    let res := (List.range j).foldl
      (fun b idx => (b.set idx (f (b.getD idx d))).set (idx + s) (g (b.getD idx d))) buf
    res.length = buf.length ∧ ∀ x < buf.length, res.getD x d =
      if x < j then f (buf.getD x d)
      else if s ≤ x ∧ x < s + j then g (buf.getD (x - s) d) else buf.getD x d := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hl, hx⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl _ buf (List.range j) = res at hl hx ⊢
    have hjd : res.getD j d = buf.getD j d := by
      rw [hx j (by omega)]; split_ifs <;> first | rfl | omega
    refine ⟨by simp [hl], fun x hxl => ?_⟩
    rw [hjd]
    have hxr := hx x hxl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set, hl] at hxr ⊢
    by_cases h1 : j + s = x
    · subst h1
      simp [hxl, show ¬ j + s < j + 1 by omega, show s ≤ j + s ∧ j + s < s + (j + 1) by omega]
    · by_cases h2 : j = x
      · subst h2
        simp [show j < buf.length by omega, show s ≠ 0 by omega]
      · simp only [h1, h2, ↓reduceIte, hxr]
        by_cases h3 : x < j
        · simp [h3, show x < j + 1 by omega]
        · by_cases h4 : s ≤ x ∧ x < s + j
          · simp [h3, h4, show ¬ x < j + 1 by omega, show s ≤ x ∧ x < s + (j + 1) by omega]
          · simp [h3, h4, show ¬ x < j + 1 by omega, show ¬ (s ≤ x ∧ x < s + (j + 1)) by omega]

end Plonky3Lean.Proofs.MultilinearUtil
