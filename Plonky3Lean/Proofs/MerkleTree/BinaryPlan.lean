module

public import Plonky3Lean.Proofs.MerkleTree.Batch
public import Plonky3Lean.Proofs.MerkleTree.Schedule
public import Plonky3Lean.Proofs.MerkleTree.Bugs

@[expose] public section

/-!
# The verifier's plan on the binary tree over power-of-two heights

Take arity 2, and matrices of heights 2^e.

Then the verifier computes, from the dimensions alone:

- the matrix order groups the matrices by height, tallest first, in input order within a height
- the leaf group is the tallest matrices
- the schedule is one binary step per level, n of them for a tallest height 2^n
- the plan injects the matrices of height 2^e after the fold to width 2^e.
-/

namespace Plonky3Lean.Proofs.MerkleTree

/-! ## The order, block by block -/

theorem logsDown_succ (e : ℕ) : logsDown (e + 1) = (e + 1) :: logsDown e := by
  simp [logsDown, List.range_succ]

theorem logsDown_eq_cons (e : ℕ) : logsDown e = e :: (List.range e).reverse := by
  simp [logsDown, List.range_succ]

theorem tallOrder_succ (lh : List ℕ) (e : ℕ) :
    tallOrder lh (e + 1) = atLog lh (e + 1) ++ tallOrder lh e := by
  simp [tallOrder, logsDown_succ]

theorem drop_logsDown {n e : ℕ} (he : e ≤ n) : (logsDown n).drop (n - e) = logsDown e := by
  simp only [logsDown, List.drop_reverse, List.length_range, List.take_range]
  congr 2
  omega

/-- The matrices of log height at most e come last in the order, after the block starts above e. -/
theorem tallOrder_split (lh : List ℕ) {n e : ℕ} (he : e ≤ n) :
    tallOrder lh n = ((logsDown n).take (n - e)).flatMap (atLog lh) ++ tallOrder lh e := by
  conv_lhs => rw [tallOrder, ← List.take_append_drop (n - e) (logsDown n)]
  rw [List.flatMap_append, drop_logsDown he]
  rfl

theorem blockStart_eq (lh : List ℕ) (n e : ℕ) :
    blockStart lh n e = (((logsDown n).take (n - e)).flatMap (atLog lh)).length := by
  simp [blockStart, List.length_flatMap]

theorem blockEnd_succ (lh : List ℕ) {n e : ℕ} (he : e + 1 ≤ n) :
    blockEnd lh n (e + 1) = blockStart lh n e := by
  have h1 := congrArg List.length (tallOrder_split lh he)
  have h2 := congrArg List.length (tallOrder_split lh (show e ≤ n by omega))
  rw [tallOrder_succ] at h1
  simp only [List.length_append] at h1 h2
  rw [blockEnd, blockStart_eq, blockStart_eq]
  omega

theorem mem_tallOrder {lh : List ℕ} {e m : ℕ} (hm : m ∈ tallOrder lh e) :
    m < lh.length ∧ lh.getD m 0 ≤ e := by
  simp only [tallOrder, logsDown, List.mem_flatMap, List.mem_reverse, List.mem_range] at hm
  obtain ⟨e', he', hm⟩ := hm
  obtain ⟨h1, h2⟩ := mem_atLog.1 hm
  exact ⟨h1, by omega⟩

/-! ## Scans over a block -/

/-- A scan from the start of a block of one height stops at the block's end. -/
theorem advance_block (g : ℕ → ℕ) (H : ℕ) :
    ∀ (blk pre rest : List ℕ), (∀ x ∈ blk, g x = H) → (∀ x ∈ rest.head?, g x ≠ H) →
      advance g (pre ++ blk ++ rest) H pre.length = pre.length + blk.length := by
  intro blk
  induction blk with
  | nil =>
    intro pre rest _ hr
    rw [advance]
    split
    · rename_i h
      obtain ⟨hlt, hg⟩ := h
      cases rest with
      | nil => simp at hlt
      | cons y rest => simp at hg hr; exact absurd hg hr
    · simp
  | cons x blk ih =>
    intro pre rest hb hr
    rw [advance]
    split
    · have := ih (pre ++ [x]) rest (fun y hy => hb y (by simp [hy])) hr
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_cons, List.length_nil] at this ⊢
      rw [this]
      omega
    · rename_i h
      exact absurd ⟨by simp, by simp [List.getD_eq_getElem?_getD, hb x (by simp)]⟩ h

/-- The leaf scan is the scan by rounded-up height. -/
theorem leafEnd_eq_advance (height : ℕ → ℕ) (order : List ℕ) (lnpt : ℕ) :
    ∀ k p, order.length - p = k →
      leafEnd height order lnpt p = advance (fun m => npt (height m)) order lnpt p := by
  intro k
  induction k with
  | zero =>
    intro p hk
    rw [leafEnd, advance]
    simp [show ¬ p < order.length by omega]
  | succ k ih =>
    intro p hk
    rw [leafEnd, advance]
    split
    · exact ih (p + 1) (by omega)
    · rfl

/-! ## Powers of two -/

theorem padded_two_pow (e : ℕ) : padded (2 ^ e) 2 = 2 ^ e := by
  rcases e with _ | e
  · simp [padded]
  · have : 2 ≤ 2 ^ (e + 1) := Nat.le_self_pow (by omega) 2
    have h2 : 2 ^ (e + 1) % 2 = 0 := by simp [pow_succ]
    unfold padded
    split_ifs <;> omega

/-- With arity 2, every step of the schedule is binary, one per halving down to width 1. -/
theorem schedRun_two (lnpt : ℕ) (height : ℕ → ℕ) (order : List ℕ) :
    ∀ k f pos acc v, schedRun 2 lnpt height order f (2 ^ k) pos acc = some v →
      v = acc ++ List.replicate k 2 := by
  intro k
  induction k with
  | zero =>
    intro f pos acc v h
    rcases f with _ | f
    · simp [schedRun] at h
    · simpa [schedRun] using h.symm
  | succ k ih =>
    intro f pos acc v h
    rcases f with _ | f
    · simp [schedRun] at h
    have h1 : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    have hs : selectSpec 2 (2 ^ (k + 1)) lnpt height order pos = 2 := by
      unfold selectSpec; split_ifs <;> rfl
    have hd : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    simp only [schedRun, h1, ↓reduceIte] at h
    rw [hs, hd, padded_two_pow] at h
    rw [ih _ _ _ _ h]
    simp [List.replicate_succ]

/-! ## The matrix order -/

theorem findIdx_append_of {l1 l2 : List ℕ} {p : ℕ → Bool} (h1 : ∀ x ∈ l1, p x = false)
    (h2 : ∀ x ∈ l2.head?, p x = true) : (l1 ++ l2).findIdx p = l1.length := by
  rw [List.findIdx_append, ite_eq_right (fun h => by rw [List.findIdx_eq_length.2 h1] at h; omega)]
  cases l2 with
  | nil => simp
  | cons y l2 => simp [List.findIdx_cons, h2 y (by simp)]

/-- The log heights from n down to 0 split around e. -/
theorem logsDown_around {n e : ℕ} (he : e ≤ n) :
    ∃ hi, (∀ x ∈ hi, e < x) ∧ logsDown n = hi ++ e :: (List.range e).reverse ∧
      hi = (logsDown n).take (n - e) := by
  refine ⟨(logsDown n).take (n - e), fun x hx => ?_, ?_, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_take, logsDown, List.length_reverse, List.length_range] at hi
    simp [logsDown, List.getElem_reverse]
    omega
  · conv_lhs => rw [← List.take_append_drop (n - e) (logsDown n)]
    rw [drop_logsDown he, logsDown_eq_cons e]

/-- The verifier's insertion sort groups the matrices by height, tallest first.

Within a height, the matrices keep their input order. -/
theorem sortTallest_eq (lh : List ℕ) (height : ℕ → ℕ) (n : ℕ)
    (hh : ∀ m < lh.length, height m = 2 ^ lh.getD m 0) (hn : ∀ m < lh.length, lh.getD m 0 ≤ n) :
    ∀ k ≤ lh.length, sortTallest height k =
      (logsDown n).flatMap fun e => (List.range k).filter fun m => lh.getD m 0 = e := by
  intro k
  induction k with
  | zero => intro _; simp [sortTallest]
  | succ k ih =>
    intro hk
    obtain ⟨lk, hlk⟩ : ∃ lk, lh.getD k 0 = lk := ⟨_, rfl⟩
    obtain ⟨hi, hhi, hsplit, -⟩ := logsDown_around (hlk ▸ hn k hk)
    have hA : ∀ e, ∀ j ∈ (List.range k).filter (fun m => lh.getD m 0 = e), height j = 2 ^ e := by
      intro e j hj
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      rw [hh j (by omega), hj.2]
    have hnew : ∀ e, ((List.range (k + 1)).filter fun m => lh.getD m 0 = e) =
        ((List.range k).filter fun m => lh.getD m 0 = e) ++ if lk = e then [k] else [] := by
      intro e
      simp only [List.range_succ, List.filter_append, List.filter_singleton, hlk]
      by_cases h : lk = e <;> simp [h]
    have hne : ∀ l : List ℕ, (∀ e ∈ l, e ≠ lk) →
        l.flatMap (fun e => ((List.range (k + 1)).filter fun m => lh.getD m 0 = e)) =
          l.flatMap (fun e => (List.range k).filter fun m => lh.getD m 0 = e) := by
      intro l hl
      refine List.flatMap_congr fun e he => ?_
      rw [hnew]
      simp [Ne.symm (hl e he)]
    rw [sortTallest]
    simp only [insertPos]
    rw [ih (by omega), hsplit, hh k (by omega), hlk]
    simp only [List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
    rw [findIdx_append_of]
    · rw [hne _ fun e he => (hhi e he).ne', hne _ fun e he => by simp at he; omega, hnew]
      rw [List.take_left' rfl, List.drop_left' rfl]
      simp
    · intro j hj
      simp only [List.mem_append, List.mem_flatMap] at hj
      rcases hj with ⟨e, he, hj⟩ | hj
      · rw [hA e j hj]
        simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (hhi e he).le
      · rw [hA lk j hj]; simp
    · intro j hj
      obtain ⟨e, he, hj⟩ := List.mem_flatMap.1 (List.mem_of_mem_head? hj)
      rw [hA e j hj]
      simp only [List.mem_reverse, List.mem_range] at he
      simpa using Nat.pow_lt_pow_right (by omega : 1 < 2) he

/-! ## The plan -/

/-- With arity 2, the verifier's plan is the binary plan.

It starts at the layer of width 2^e, at the end of the block of log height e. -/
theorem plan_binary (lh : List ℕ) (height : ℕ → ℕ) (n : ℕ)
    (hh : ∀ m < lh.length, height m = 2 ^ lh.getD m 0) :
    ∀ L e, L ≤ e → e ≤ n →
      plan 2 height (tallOrder lh n) (List.replicate L 2) (2 ^ e) (blockEnd lh n e) =
        bplan lh n e L := by
  intro L
  induction L with
  | zero => intro e _ _; simp [plan, bplan]
  | succ L ih =>
    intro e hL hen
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    obtain ⟨P, R, hP, hR, horder⟩ : ∃ P R, P.length = blockStart lh n e ∧
        (∀ y ∈ R, ∃ e' < e, height y = 2 ^ e') ∧ tallOrder lh n = P ++ (atLog lh e ++ R) := by
      refine ⟨_, (List.range e).reverse.flatMap (atLog lh), (blockStart_eq lh n e).symm,
        fun y hy => ?_, ?_⟩
      · obtain ⟨e', he', hy⟩ := List.mem_flatMap.1 hy
        obtain ⟨h1, h2⟩ := mem_atLog.1 hy
        exact ⟨e', by simpa using he', by rw [hh y h1, h2]⟩
      · rw [tallOrder_split lh (show e ≤ n by omega), tallOrder, logsDown_eq_cons e]
        simp
    have hRe : ∀ y ∈ R, npt (height y) ≠ 2 ^ e := fun y hy => by
      obtain ⟨e', he', h⟩ := hR y hy
      rw [h, npt_two_pow]
      exact (Nat.pow_lt_pow_right (by omega) he').ne
    have hblk : ∀ y ∈ atLog lh e, height y = 2 ^ e := fun y hy => by
      obtain ⟨h1, h2⟩ := mem_atLog.1 hy; rw [hh y h1, h2]
    have hd : 2 ^ (e + 1) / 2 = 2 ^ e := by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    have hrec := ih e (by omega) (by omega)
    rw [blockEnd_succ lh hen, List.replicate_succ, plan, bplan, hd, padded_two_pow, ← hP, horder]
    simp only [Nat.add_sub_cancel, npt_two_pow]
    have hget : (P ++ (atLog lh e ++ R)).getD P.length 0 = (atLog lh e ++ R).getD 0 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    rw [hget]
    rw [← horder, ← hP]
    by_cases hb : atLog lh e = []
    · have hc : ¬ (P.length < (tallOrder lh n).length ∧
          npt (height ((atLog lh e ++ R).getD 0 0)) = 2 ^ e) := by
        rintro ⟨hlt, heq⟩
        rw [hb, List.nil_append] at heq
        rw [horder, hb] at hlt
        cases R with
        | nil => simp at hlt
        | cons y R => exact hRe y (by simp) (by simpa using heq)
      rw [ite_eq_right hc, ite_eq_left hb, ← hrec, blockEnd, ← hP, hb]
      simp
    · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hb
      have hxh : height x = 2 ^ e := hblk x (by simp [hx])
      rw [ite_eq_left ⟨by rw [horder]; simp [hx], by simp [hx, hxh, npt_two_pow]⟩, ite_eq_right hb]
      simp only [hx, List.cons_append, List.getD_cons_zero, hxh]
      have hadv := advance_block height (2 ^ e) (atLog lh e) P R hblk (fun y hy =>
        fun h => hRe y (List.mem_of_mem_head? hy) (by rw [h, npt_two_pow]))
      rw [List.append_assoc, ← horder, hP, ← blockEnd] at hadv
      rw [← hP] at hadv
      rw [hadv, hrec]

end Plonky3Lean.Proofs.MerkleTree
