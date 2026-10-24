module

public import Plonky3Lean.Proofs.Fri.Honest
public import Plonky3Lean.Proofs.MerkleTree.Batch

@[expose] public section

/-!
# The Merkle tree as the FRI PCS's commitment scheme

The scheme commits a batch of matrices whose heights are powers of two.

It builds the binary multi-height tree, and the commitment is its cap of 2^c digests.

A multi-opening holds, for each query index, every matrix's row and the path's siblings.

```text
    query index I, tallest height 2^n
    row of a matrix of height 2^e:   I / 2^(n - e)
    siblings:                        one per level, n - c levels
```

The verifier walks each query from its leaf to the cap, as the extracted single-index verifier does.

Plonky3 prunes the siblings that queries share.

Its pruned proof expands back to these per-query paths, so pruning is not modelled.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Plonky3Lean.Spec.MerkleTree Plonky3Lean.Proofs.MerkleTree
open p3_commit.pcs.univariate.mirror p3_fri.mirror

variable {K D : Type}

/-! ## The scheme -/

/-- The tallest of some log heights, or 0 for none. -/
def topLog (lh : List ℕ) : ℕ := lh.foldl max 0

/-- The log heights of a batch. -/
def batchLogs (mats : List (Mat K)) : List ℕ := mats.map fun m => Nat.log 2 m.height

/-- Row j of matrix m of a batch, or nothing past the batch. -/
def rowsOfMats (mats : List (Mat K)) (m j : ℕ) : List K := (mats[m]?.map (matRow · j)).getD []

section scheme

variable (h : List (List K) → D) (c : List D → D) (z : D) (capH : ℕ)

/-- The honest tree's layers above the leaves, up to the cap. -/
def merkleSpecs (mats : List (Mat K)) : List (LayerSpec D) :=
  bspecs h (batchLogs mats) (topLog (batchLogs mats)) (rowsOfMats mats) (topLog (batchLogs mats))
    (topLog (batchLogs mats) - capH)

/-- The honest tree's leaf layer. -/
def merkleLeaf (mats : List (Mat K)) : ℕ → D :=
  bleaf h (batchLogs mats) (topLog (batchLogs mats)) (rowsOfMats mats)

/-- The commitment: the 2^c digests of the cap. -/
def merkleCap (mats : List (Mat K)) : List D :=
  (List.range (2 ^ capH)).map (top c [z, z] z (merkleLeaf h mats) (merkleSpecs h capH mats))

/-- The siblings of the path of leaf I. -/
def merklePath (mats : List (Mat K)) (I : ℕ) : List D :=
  path c [z, z] z (merkleLeaf h mats) (merkleSpecs h capH mats) I

/-- The rows an honest opening of leaf I holds: matrix by matrix, the row the tree takes in. -/
def merkleRows (mats : List (Mat K)) (I : ℕ) : List (List K) :=
  mats.map fun m => matRow m (I / 2 ^ (topLog (batchLogs mats) - Nat.log 2 m.height))

/-- The log heights the dimensions claim. -/
def dimLogs (dims : List (ℕ × ℕ)) : List ℕ := dims.map fun d => Nat.log 2 d.2

/-- The verifier's walk of one query, from the hash of the tallest rows: the cap index and the digest. -/
def queryWalk (dims : List (ℕ × ℕ)) (I : ℕ) (vals : List (List K)) (prf : List D) : ℕ × D :=
  walk h c [z, z] z (tallOrder (dimLogs dims) (topLog (dimLogs dims))) vals prf
    (bplan (dimLogs dims) (topLog (dimLogs dims)) (topLog (dimLogs dims)) (topLog (dimLogs dims) - capH)) I 0
    (h (group (tallOrder (dimLogs dims) (topLog (dimLogs dims))) vals 0
      (blockEnd (dimLogs dims) (topLog (dimLogs dims)) (topLog (dimLogs dims)))))

/-- The verifier accepts one query when all of these hold:

- the index is below the tallest height
- there is one row per matrix, at its width
- there is one sibling per level
- the walk from the leaf reaches the cap entry at its index. -/
def QueryAccepts (cap : List D) (dims : List (ℕ × ℕ)) (I : ℕ) (vals : List (List K)) (prf : List D) : Prop :=
  I < 2 ^ topLog (dimLogs dims) ∧ vals.length = dims.length ∧
  (∀ m < dims.length, (vals.getD m []).length = (dims.getD m (0, 0)).1) ∧
  prf.length = topLog (dimLogs dims) - capH ∧
  cap[(queryWalk h c z capH dims I vals prf).1]? = some (queryWalk h c z capH dims I vals prf).2

/-- The verifier accepts a multi-opening when all of these hold:

- the batch is not empty, and every height is a power of two
- the cap lies at or below the root
- there is one row set and one path per query
- every query is accepted. -/
def MultiAccepts (cap : List D) (dims : List (ℕ × ℕ)) (idxs : List ℕ) (vals : List (List (List K)))
    (prfs : List (List D)) : Prop :=
  dims ≠ [] ∧ (∀ d ∈ dims, 2 ^ Nat.log 2 d.2 = d.2) ∧ capH ≤ topLog (dimLogs dims) ∧
  vals.length = idxs.length ∧ prfs.length = idxs.length ∧
  ∀ q < idxs.length, QueryAccepts h c z capH cap dims (idxs.getD q 0) (vals.getD q []) (prfs.getD q [])

/-- The Merkle tree scheme, with hasher h, compression c, padding digest z and cap height c. -/
noncomputable def merkleOps : MmcsOps K where
  Commitment := List D
  ProverData := List (Mat K)
  MultiProof := List (List D)
  Error := Unit
  commit mats := (merkleCap h c z capH mats, mats)
  get_matrices mats := mats
  open_multi_batch idxs mats := (idxs.map (merkleRows mats), idxs.map (merklePath h c z capH mats))
  verify_multi_batch cap dims idxs vals prfs := by
    classical
    exact if MultiAccepts h c z capH cap dims idxs vals prfs then .ok () else .error ()

end scheme

/-! ## Helper facts -/

theorem le_foldl_max : ∀ (l : List ℕ) (a x : ℕ), x ∈ l ∨ x ≤ a → x ≤ l.foldl max a
  | [], _, _, hx => by simpa using hx
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    refine le_foldl_max l _ x ?_
    rcases hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl hx
    · exact Or.inr (le_max_of_le_left hx)

theorem le_topLog {lh : List ℕ} {x : ℕ} (hx : x ∈ lh) : x ≤ topLog lh := le_foldl_max lh 0 x (Or.inl hx)

theorem length_path_bspecs {F : Type _} (h : List (List F) → D) (c : List D → D) (z : D) (lh : List ℕ) (n : ℕ)
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

/-! ## Completeness and binding -/

section scheme

variable (h : List (List K) → D) (c : List D → D) (z : D) (capH : ℕ)

/-- An honest multi-opening of a committed batch verifies.

The batch is not empty, every height is a power of two, and the cap lies at or below the root.

The dimensions are the matrices' widths and heights, and every index is below the tallest height. -/
theorem merkle_verify_honest (mats : List (Mat K)) (dims : List (ℕ × ℕ)) (idxs : List ℕ)
    (hd : dims = mats.map fun m => (m.width, m.height)) (hne : mats ≠ [])
    (hpow : ∀ m ∈ mats, 2 ^ Nat.log 2 m.height = m.height) (hcap : capH ≤ topLog (batchLogs mats))
    (hidx : ∀ I ∈ idxs, I < 2 ^ topLog (batchLogs mats)) :
    (merkleOps h c z capH).verify_multi_batch ((merkleOps h c z capH).commit mats).1 dims idxs
      ((merkleOps h c z capH).open_multi_batch idxs mats).1 ((merkleOps h c z capH).open_multi_batch idxs mats).2 =
      .ok () := by
  have hlh : dimLogs dims = batchLogs mats := by subst hd; simp [dimLogs, batchLogs]
  suffices hP : MultiAccepts h c z capH (merkleCap h c z capH mats) dims idxs (idxs.map (merkleRows mats))
      (idxs.map (merklePath h c z capH mats)) by simp [merkleOps, hP]
  subst hd
  set n := topLog (batchLogs mats)
  refine ⟨by simpa using hne, by simpa using hpow, by rw [hlh]; exact hcap, by simp, by simp, fun q hq => ?_⟩
  set I := idxs.getD q 0
  have hI : I < 2 ^ n := hidx I (by simp [I, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq])
  have hvals : (idxs.map (merkleRows mats)).getD q [] = merkleRows mats I := by
    simp [I, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  have hprf : (idxs.map (merklePath h c z capH mats)).getD q [] = merklePath h c z capH mats I := by
    simp [I, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rw [hvals, hprf]
  have hop : ∀ m < (batchLogs mats).length, (merkleRows mats I).getD m [] =
      rowsOfMats mats m (I / 2 ^ (n - (batchLogs mats).getD m 0)) := by
    intro m hm
    simp only [batchLogs, List.length_map] at hm
    simp [merkleRows, rowsOfMats, batchLogs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, n]
  have hw := bwalk_honest h c z (batchLogs mats) n (n - capH) (rowsOfMats mats) (merkleRows mats I) I
    (Nat.sub_le _ _) hI hop
  unfold QueryAccepts queryWalk
  rw [hlh]
  refine ⟨hI, by simp [merkleRows], fun m hm => ?_, ?_, ?_⟩
  · simp only [List.length_map] at hm
    simp [merkleRows, matRow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  · exact length_path_bspecs h c z _ _ _ _ _ _ _
  · simp only [merklePath, merkleLeaf, merkleSpecs] at hw ⊢
    rw [hw]
    have hlt : I / 2 ^ (n - capH) < 2 ^ capH := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show capH + (n - capH) = n by omega]; exact hI
    simp [merkleCap, merkleLeaf, merkleSpecs, hlt, n]

/-- Two multi-openings of one commitment at the same indices that both verify.

Either the hasher or the compression collides, or the two agree on the row of every matrix at least as tall as the cap. -/
theorem merkle_verify_binding (cap : List D) (dims : List (ℕ × ℕ)) (idxs : List ℕ)
    (v1 v2 : List (List (List K))) (p1 p2 : List (List D))
    (h1 : (merkleOps h c z capH).verify_multi_batch cap dims idxs v1 p1 = .ok ())
    (h2 : (merkleOps h c z capH).verify_multi_batch cap dims idxs v2 p2 = .ok ()) :
    CCollision c ∨ HCollision h ∨
      ∀ q < idxs.length, ∀ m < dims.length, capH ≤ Nat.log 2 (dims.getD m (0, 0)).2 →
        (v1.getD q []).getD m [] = (v2.getD q []).getD m [] := by
  have acc : ∀ {v p}, (merkleOps h c z capH).verify_multi_batch cap dims idxs v p = .ok () →
      MultiAccepts h c z capH cap dims idxs v p := by
    intro v p hv
    simp only [merkleOps] at hv
    split_ifs at hv with hn
    · exact hn
  obtain ⟨-, -, hcap, -, -, hq1⟩ := acc h1
  obtain ⟨-, -, -, -, -, hq2⟩ := acc h2
  by_cases hcol : CCollision c ∨ HCollision h
  · rcases hcol with hc | hh
    · exact Or.inl hc
    · exact Or.inr (Or.inl hh)
  refine Or.inr (Or.inr fun q hq m hm hcm => ?_)
  set lh := dimLogs dims
  set n := topLog lh
  obtain ⟨hI, hl1, hw1, -, hc1⟩ := hq1 q hq
  obtain ⟨-, hl2, hw2, -, hc2⟩ := hq2 q hq
  simp only [queryWalk] at hc1 hc2
  have hlen : ∀ m, ((v1.getD q []).getD m []).length = ((v2.getD q []).getD m []).length := by
    intro m
    by_cases hm : m < dims.length
    · rw [hw1 m hm, hw2 m hm]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hfst := walk_fst h c [z, z] z (tallOrder lh n) (v1.getD q []) (p1.getD q [])
    (bplan lh n n (n - capH)) (idxs.getD q 0) 0
    (h (group (tallOrder lh n) (v1.getD q []) 0 (blockEnd lh n n)))
  have hfst2 := walk_fst h c [z, z] z (tallOrder lh n) (v2.getD q []) (p2.getD q [])
    (bplan lh n n (n - capH)) (idxs.getD q 0) 0
    (h (group (tallOrder lh n) (v2.getD q []) 0 (blockEnd lh n n)))
  rw [hfst] at hc1
  rw [hfst2] at hc2
  have heq := Option.some.inj (hc1.symm.trans hc2)
  have hlm : m < lh.length := by simpa [lh, dimLogs] using hm
  have hget : lh.getD m 0 = Nat.log 2 (dims.getD m (0, 0)).2 := by
    simp [lh, dimLogs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  rcases bwalk_binding h c z lh n (n - capH) (Nat.sub_le _ _) _ _ _ _ _ hlen heq with hc | hh | hall
  · exact absurd (Or.inl hc) hcol
  · exact absurd (Or.inr hh) hcol
  · refine hall m hlm (by rw [hget]; omega) (le_topLog (by rw [List.getD_eq_getElem _ _ hlm]; exact List.getElem_mem hlm))

end scheme

end Plonky3Lean.Proofs.Fri
