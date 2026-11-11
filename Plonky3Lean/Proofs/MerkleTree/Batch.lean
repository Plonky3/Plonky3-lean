module

public import Plonky3Lean.Proofs.MerkleTree.Complete
public import Plonky3Lean.Proofs.MerkleTree.Binding

@[expose] public section

/-!
# A binary tree over matrices of power-of-two heights

This is the batch layout the FRI PCS commits.

Every height is a power of two, and every node folds two children.

The tallest matrices, of height 2^n, fill the leaf layer.

A matrix of height 2^e enters the layer of width 2^e.

```text
    leaf layer   width 2^n       rows of the height-2^n matrices
    after fold 1 width 2^(n-1)   rows of the height-2^(n-1) matrices enter
    ...
    after fold L width 2^(n-L)   the cap
```

Within one height, the matrices keep their input order.

A matrix shorter than the cap enters no layer, so nothing binds its rows.
-/

namespace Plonky3Lean.Proofs.MerkleTree

open Plonky3Lean.Spec.MerkleTree

variable {F D : Type _}

/-! ## The order and the blocks -/

/-- The matrices of log height e, in input order. -/
def atLog (lh : List ℕ) (e : ℕ) : List ℕ :=
  (List.range lh.length).filter fun m => lh.getD m 0 = e

/-- The log heights from n down to 0. -/
def logsDown (n : ℕ) : List ℕ := (List.range (n + 1)).reverse

/-- The matrices tallest first, ties in input order. -/
def tallOrder (lh : List ℕ) (n : ℕ) : List ℕ := (logsDown n).flatMap (atLog lh)

/-- Where the matrices of log height e start in that order. -/
def blockStart (lh : List ℕ) (n e : ℕ) : ℕ :=
  (((logsDown n).take (n - e)).map fun e' => (atLog lh e').length).sum

/-- Where the matrices of log height e end in that order. -/
def blockEnd (lh : List ℕ) (n e : ℕ) : ℕ := blockStart lh n e + (atLog lh e).length

theorem flatMap_slice {α β : Type _} (f : α → List β) (L : List α) (k : ℕ) (hk : k < L.length) :
    ((L.flatMap f).drop ((L.take k).map fun x => (f x).length).sum).take (f L[k]).length = f L[k] := by
  have hL : L.flatMap f = (L.take k).flatMap f ++ (f L[k] ++ (L.drop (k + 1)).flatMap f) := by
    rw [← List.flatMap_cons, ← List.drop_eq_getElem_cons hk, ← List.flatMap_append, List.take_append_drop]
  rw [hL, List.drop_left' (by simp [List.length_flatMap]), List.take_left' rfl]

theorem logsDown_getElem {n e : ℕ} (he : e ≤ n) :
    (logsDown n)[n - e]'(by simp only [logsDown, List.length_reverse, List.length_range]; omega) = e := by
  simp only [logsDown, List.getElem_reverse, List.getElem_range, List.length_range]; omega

/-- The rows the verifier hashes for a block are the rows of the block's matrices, in input order. -/
theorem group_tallOrder (lh : List ℕ) {n e : ℕ} (he : e ≤ n) (o : List (List F)) :
    group (tallOrder lh n) o (blockStart lh n e) (blockEnd lh n e) = (atLog lh e).map (o.getD · []) := by
  have hk : n - e < (logsDown n).length := by
    simp only [logsDown, List.length_reverse, List.length_range]; omega
  have := flatMap_slice (atLog lh) (logsDown n) (n - e) hk
  rw [logsDown_getElem he] at this
  simp only [group, blockEnd, Nat.add_sub_cancel_left, tallOrder, blockStart]
  rw [this]

theorem mem_atLog {lh : List ℕ} {e m : ℕ} : m ∈ atLog lh e ↔ m < lh.length ∧ lh.getD m 0 = e := by
  simp [atLog]

/-! ## The plan and the honest layers -/

/-- The verifier's binary plan for L levels, from the layer of log width e. -/
def bplan (lh : List ℕ) (n : ℕ) : ℕ → ℕ → List Level
  | _, 0 => []
  | e, L + 1 =>
    (2, if atLog lh (e - 1) = [] then none else some (blockStart lh n (e - 1), blockEnd lh n (e - 1))) ::
      bplan lh n (e - 1) L

/-- Row j of every matrix, in input order. -/
def rowsAt (M : ℕ) (rowsOf : ℕ → ℕ → List F) (j : ℕ) : List (List F) :=
  (List.range M).map fun m => rowsOf m j

/-- The honest tree's layers above the layer of log width e, for L levels. -/
def bspecs (h : List (List F) → D) (lh : List ℕ) (n : ℕ) (rowsOf : ℕ → ℕ → List F) :
    ℕ → ℕ → List (LayerSpec D)
  | _, 0 => []
  | e, L + 1 =>
    ⟨2, if atLog lh (e - 1) = [] then none else some (2 ^ (e - 1), fun j =>
      h (group (tallOrder lh n) (rowsAt lh.length rowsOf j) (blockStart lh n (e - 1)) (blockEnd lh n (e - 1))))⟩ ::
      bspecs h lh n rowsOf (e - 1) L

/-- The leaf layer: node j hashes row j of the tallest matrices. -/
def bleaf (h : List (List F) → D) (lh : List ℕ) (n : ℕ) (rowsOf : ℕ → ℕ → List F) (j : ℕ) : D :=
  h (group (tallOrder lh n) (rowsAt lh.length rowsOf j) 0 (blockEnd lh n n))

theorem bplan_steps (lh : List ℕ) (n : ℕ) : ∀ L e, ∀ l ∈ bplan lh n e L, l.1 = 2 := by
  intro L
  induction L with
  | zero => simp [bplan]
  | succ L ih =>
    intro e l hl
    simp only [bplan, List.mem_cons] at hl
    rcases hl with rfl | hl
    · rfl
    · exact ih _ l hl

theorem capIndex_bplan (lh : List ℕ) (n : ℕ) : ∀ L e i, capIndex (bplan lh n e L) i = i / 2 ^ L := by
  intro L
  induction L with
  | zero => intro e i; simp [bplan, capIndex]
  | succ L ih =>
    intro e i
    simp only [bplan, capIndex, ih, Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem div_pow_succ (I a : ℕ) : I / 2 ^ a / 2 = I / 2 ^ (a + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The plan matches the honest layers along the path of leaf I.

The opening holds, for each matrix of log height e, its row I / 2^(n - e). -/
theorem bplan_matches (h : List (List F) → D) (z : D) (lh : List ℕ) (n : ℕ) (rowsOf : ℕ → ℕ → List F)
    (opened : List (List F)) (I : ℕ) (hI : I < 2 ^ n)
    (hop : ∀ m < lh.length, opened.getD m [] = rowsOf m (I / 2 ^ (n - lh.getD m 0))) :
    ∀ L e, L ≤ e → e ≤ n →
      Matches h [z, z] (tallOrder lh n) opened (bplan lh n e L) (bspecs h lh n rowsOf e L) (I / 2 ^ (n - e)) := by
  intro L
  induction L with
  | zero => intro e _ _; simp [bplan, bspecs, Matches]
  | succ L ih =>
    intro e hLe hen
    have hnext : I / 2 ^ (n - e) / 2 = I / 2 ^ (n - (e - 1)) := by
      rw [div_pow_succ, show n - e + 1 = n - (e - 1) by omega]
    have hrec := ih (e - 1) (by omega) (by omega)
    rw [← hnext] at hrec
    simp only [bplan, bspecs, Matches]
    by_cases hb : atLog lh (e - 1) = []
    · simp only [hb, ↓reduceIte]
      exact ⟨by simp, by norm_num, by simp, trivial, hrec⟩
    · simp only [hb, ↓reduceIte]
      refine ⟨by simp, by norm_num, by simp, ⟨?_, ?_⟩, hrec⟩
      · rw [hnext, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show e - 1 + (n - (e - 1)) = n by omega]
        exact hI
      · rw [hnext, group_tallOrder lh (by omega), group_tallOrder lh (by omega)]
        congr 1
        refine List.map_congr_left fun m hm => ?_
        obtain ⟨hml, hme⟩ := mem_atLog.1 hm
        rw [hop m hml, hme]
        simp [rowsAt, List.getD_eq_getElem?_getD, hml]

/-- The verifier's walk over an honest opening of leaf I reaches cap entry I / 2^L, as the tree defines it.

The opening holds:

- for each matrix of log height e, its row I / 2^(n - e)
- the siblings of the path. -/
theorem bwalk_honest (h : List (List F) → D) (c : List D → D) (z : D) (lh : List ℕ) (n L : ℕ)
    (rowsOf : ℕ → ℕ → List F) (opened : List (List F)) (I : ℕ) (hL : L ≤ n) (hI : I < 2 ^ n)
    (hop : ∀ m < lh.length, opened.getD m [] = rowsOf m (I / 2 ^ (n - lh.getD m 0))) :
    walk h c [z, z] z (tallOrder lh n) opened
        (path c [z, z] z (bleaf h lh n rowsOf) (bspecs h lh n rowsOf n L) I) (bplan lh n n L) I 0
        (h (group (tallOrder lh n) opened 0 (blockEnd lh n n))) =
      (I / 2 ^ L, top c [z, z] z (bleaf h lh n rowsOf) (bspecs h lh n rowsOf n L) (I / 2 ^ L)) := by
  have hleaf : h (group (tallOrder lh n) opened 0 (blockEnd lh n n)) = bleaf h lh n rowsOf I := by
    have h0 : blockStart lh n n = 0 := by simp [blockStart]
    have := group_tallOrder lh (le_refl n) opened
    rw [h0] at this
    rw [bleaf, this]
    have := group_tallOrder lh (le_refl n) (rowsAt lh.length rowsOf I)
    rw [h0] at this
    rw [this]
    congr 1
    refine List.map_congr_left fun m hm => ?_
    obtain ⟨hml, hme⟩ := mem_atLog.1 hm
    rw [hop m hml, hme]
    simp [rowsAt, List.getD_eq_getElem?_getD, hml]
  have hm := bplan_matches h z lh n rowsOf opened I hI hop L n hL le_rfl
  rw [Nat.sub_self, pow_zero, Nat.div_one] at hm
  rw [hleaf, walk_honest h c [z, z] z _ opened _ _ _ _ I 0 hm (fun j _ => by simp),
    capIndex_bplan]

/-- The path of the binary tree has one sibling per level. -/
theorem length_path_bspecs (h : List (List F) → D) (c : List D → D) (z : D) (lh : List ℕ) (n : ℕ)
    (rowsOf : ℕ → ℕ → List F) :
    ∀ L e (L0 : ℕ → D) i, (path c [z, z] z L0 (bspecs h lh n rowsOf e L) i).length = L := by
  intro L
  induction L with
  | zero => intro e L0 i; simp [bspecs, path]
  | succ L ih =>
    intro e L0 i
    simp only [bspecs, path, List.length_append, List.length_map, ih, filter_ne_length,
      Nat.mod_lt i (show 0 < 2 by norm_num), ↓reduceIte]
    omega

/-! ## Binding -/

theorem mem_injected_bplan (lh : List ℕ) (n : ℕ) :
    ∀ L e' e, L ≤ e' → e' - L ≤ e → e < e' → atLog lh e ≠ [] →
      (blockStart lh n e, blockEnd lh n e) ∈ injected (bplan lh n e' L) := by
  intro L
  induction L with
  | zero => intro e' e _ h1 h2; omega
  | succ L ih =>
    intro e' e hL h1 h2 hne
    simp only [bplan]
    by_cases he : e = e' - 1
    · subst he
      simp [hne, injected]
    · have := ih (e' - 1) e (by omega) (by omega) (by omega) hne
      split <;> simp [injected, this]

/-- Two walks of the binary plan that reach one digest from one leaf index.

Either the hasher or the compression collides, or the two openings agree on every matrix the tree takes in.

Those are the matrices of log height between n - L and n. -/
theorem bwalk_binding (h : List (List F) → D) (c : List D → D) (z : D) (lh : List ℕ) (n L : ℕ) (hL : L ≤ n)
    (o1 o2 : List (List F)) (p1 p2 : List D) (I : ℕ)
    (hlen : ∀ m, (o1.getD m []).length = (o2.getD m []).length)
    (heq : (walk h c [z, z] z (tallOrder lh n) o1 p1 (bplan lh n n L) I 0
        (h (group (tallOrder lh n) o1 0 (blockEnd lh n n)))).2 =
      (walk h c [z, z] z (tallOrder lh n) o2 p2 (bplan lh n n L) I 0
        (h (group (tallOrder lh n) o2 0 (blockEnd lh n n)))).2) :
    CCollision c ∨ HCollision h ∨
      ∀ m < lh.length, n - L ≤ lh.getD m 0 → lh.getD m 0 ≤ n → o1.getD m [] = o2.getD m [] := by
  have hpl : ∀ l ∈ bplan lh n n L, 0 < l.1 ∧ l.1 ≤ [z, z].length := fun l hl => by
    rw [bplan_steps lh n L n l hl]; simp
  rcases walk_binding h c [z, z] z _ o1 o2 p1 p2 hlen (by simp) _ hpl I 0 _ _ heq with hc | hh | ⟨hd, hg⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hh)
  by_cases hleaf : group (tallOrder lh n) o1 0 (blockEnd lh n n) = group (tallOrder lh n) o2 0 (blockEnd lh n n)
  · refine Or.inr (Or.inr fun m hml hlo hhi => ?_)
    have hm : m ∈ atLog lh (lh.getD m 0) := mem_atLog.2 ⟨hml, rfl⟩
    have hblock : group (tallOrder lh n) o1 (blockStart lh n (lh.getD m 0)) (blockEnd lh n (lh.getD m 0)) =
        group (tallOrder lh n) o2 (blockStart lh n (lh.getD m 0)) (blockEnd lh n (lh.getD m 0)) := by
      rcases Nat.lt_or_ge (lh.getD m 0) n with hlt | hge
      · exact hg _ (mem_injected_bplan lh n L n _ hL (by omega) hlt (List.ne_nil_of_mem hm))
      · have h0 : blockStart lh n n = 0 := by simp [blockStart]
        rw [show lh.getD m 0 = n by omega, h0]
        exact hleaf
    rw [group_tallOrder lh hhi, group_tallOrder lh hhi] at hblock
    exact (List.map_inj_left.1 hblock) m hm
  · exact Or.inr (Or.inl ⟨_, _, hleaf, group_lengths _ o1 o2 hlen 0 _, hd⟩)

end Plonky3Lean.Proofs.MerkleTree
