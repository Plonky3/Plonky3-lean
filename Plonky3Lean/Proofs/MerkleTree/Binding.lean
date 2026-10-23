module

public import Plonky3Lean.Proofs.MerkleTree.Walk

@[expose] public section

/-!
# Two openings that reach one digest give a collision

This is Merkle's argument (Merkle 1987).

Walk both openings down from the common digest.

At each compression, either the two inputs differ, which is a collision of the compression, or they agree.

Where they agree, the two paths' own digests agree, and so do the hashes of the injected rows.

At each row hash, either the two row lists differ, which is a collision of the hasher, or they agree.
-/

namespace Plonky3Lean.Proofs.MerkleTree

variable {F D : Type _}

/-- Two different lists of equal length that the compression maps to one digest. -/
def CCollision (c : List D → D) : Prop :=
  ∃ u v : List D, u.length = v.length ∧ u ≠ v ∧ c u = c v

/-- Two different lists of rows, of equal row lengths, that the hasher maps to one digest. -/
def HCollision (h : List (List F) → D) : Prop :=
  ∃ xs ys : List (List F), xs ≠ ys ∧ xs.map List.length = ys.map List.length ∧ h xs = h ys

/-- The matrix groups a plan injects. -/
def injected : List Level → List (ℕ × ℕ)
  | [] => []
  | (_, none) :: rest => injected rest
  | (_, some g) :: rest => g :: injected rest

theorem children_length (pad : List D) (s pg : ℕ) (d : D) (proof : List D) (pp : ℕ) (z : D) :
    (children pad s pg d proof pp z).length = pad.length := by
  simp [children]

theorem children_get (pad : List D) (s pg : ℕ) (d : D) (proof : List D) (pp : ℕ) (z : D)
    (hs : pg < s) (hpad : pg < pad.length) :
    (children pad s pg d proof pp z)[pg]? = some d := by
  simp [children, hs, hpad]

theorem group_lengths (order : List ℕ) (o1 o2 : List (List F))
    (hlen : ∀ m, (o1.getD m []).length = (o2.getD m []).length) (a b : ℕ) :
    (group order o1 a b).map List.length = (group order o2 a b).map List.length := by
  unfold group
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro m _
  exact hlen m

/-- Two walks over one plan that reach one digest started from one digest and read the same injected rows, or one of the two functions has a collision. -/
theorem walk_binding (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (o1 o2 : List (List F)) (p1 p2 : List D)
    (hlen : ∀ m, (o1.getD m []).length = (o2.getD m []).length) (hpad : 2 ≤ pad.length) :
    ∀ (pl : List Level), (∀ l ∈ pl, 0 < l.1 ∧ l.1 ≤ pad.length) →
    ∀ i pp d d', (walk h c pad z order o1 p1 pl i pp d).2 = (walk h c pad z order o2 p2 pl i pp d').2 →
      CCollision c ∨ HCollision h ∨
        (d = d' ∧ ∀ g ∈ injected pl, group order o1 g.1 g.2 = group order o2 g.1 g.2) := by
  intro pl
  induction pl with
  | nil =>
    intro _ i pp d d' heq
    exact Or.inr (Or.inr ⟨heq, by simp [injected]⟩)
  | cons l rest ih =>
    intro hpl i pp d d' heq
    obtain ⟨s, g⟩ := l
    have hs := hpl (s, g) (by simp)
    simp only at hs
    have hrest : ∀ l ∈ rest, 0 < l.1 ∧ l.1 ≤ pad.length := fun l hl => hpl l (by simp [hl])
    simp only [walk] at heq
    -- The digests after this level agree, or a collision shows up above.
    rcases ih hrest _ _ _ _ heq with hc | hh | ⟨hd2, hg⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl hh)
    -- One level down: the fold of the children.
    have hfold : ∀ e e' : D, c (children pad s (i % s) d p1 pp z) = e →
        c (children pad s (i % s) d' p2 pp z) = e' → e = e' →
        CCollision c ∨ d = d' := by
      intro e e' he he' hee
      by_cases hch : children pad s (i % s) d p1 pp z = children pad s (i % s) d' p2 pp z
      · right
        have hlt : i % s < s := Nat.mod_lt _ (by omega)
        have h1 := children_get pad s (i % s) d p1 pp z hlt (by omega)
        rw [hch, children_get pad s (i % s) d' p2 pp z hlt (by omega)] at h1
        exact (Option.some.inj h1).symm
      · left
        exact ⟨_, _, by simp [children_length], hch, he.trans (hee.trans he'.symm)⟩
    cases g with
    | none =>
      rcases hfold _ _ rfl rfl hd2 with hc | hd
      · exact Or.inl hc
      · exact Or.inr (Or.inr ⟨hd, by simpa [injected] using hg⟩)
    | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only at hd2
      set e := c (children pad s (i % s) d p1 pp z)
      set e' := c (children pad s (i % s) d' p2 pp z)
      set x := h (group order o1 a b)
      set x' := h (group order o2 a b)
      by_cases hin : (pad.set 0 e).set 1 x = (pad.set 0 e').set 1 x'
      · have h0 : e = e' := by
          have := congrArg (fun l => l[0]?) hin
          simpa [List.getElem?_set, show 0 < pad.length by omega] using this
        have h1 : x = x' := by
          have := congrArg (fun l => l[1]?) hin
          simpa [List.getElem?_set, show 1 < pad.length by omega] using this
        rcases hfold _ _ rfl rfl h0 with hc | hd
        · exact Or.inl hc
        · by_cases hgr : group order o1 a b = group order o2 a b
          · refine Or.inr (Or.inr ⟨hd, ?_⟩)
            intro g' hg'
            simp only [injected, List.mem_cons] at hg'
            rcases hg' with rfl | hg'
            · exact hgr
            · exact hg g' hg'
          · exact Or.inr (Or.inl ⟨_, _, hgr, group_lengths order o1 o2 hlen a b, h1⟩)
      · exact Or.inl ⟨_, _, by simp, hin, hd2⟩

end Plonky3Lean.Proofs.MerkleTree
