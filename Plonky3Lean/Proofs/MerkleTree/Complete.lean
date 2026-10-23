module

public import Plonky3Lean.Proofs.MerkleTree.Walk
public import Plonky3Lean.Spec.MerkleTree

@[expose] public section

/-!
# The verifier's walk recomputes the tree along an honest path

Fold the verifier's plan over an honest opening: the rows of every matrix at the path's node, and the siblings of the path.

The walk reaches the node of the top layer above the leaf, as the tree defines it.
-/

namespace Plonky3Lean.Proofs.MerkleTree

open Plonky3Lean.Spec.MerkleTree

variable {F D : Type _}

/-- The verifier's plan matches the tree's layers along the path of leaf `i`.

Each level folds as many children, and where matrices enter, the verifier hashes the rows the tree takes in at the path's node, which is below their height. -/
def Matches (h : List (List F) → D) (pad : List D) (order : List ℕ) (opened : List (List F)) :
    List Level → List (LayerSpec D) → ℕ → Prop
  | [], [], _ => True
  | (s, g) :: pl, l :: ls, i =>
    s = l.step ∧ 0 < s ∧ s ≤ pad.length ∧
    (match g, l.inj with
      | none, none => True
      | some (a, b), some (ht, rows) => i / s < ht ∧ h (group order opened a b) = rows (i / s)
      | _, _ => False) ∧
    Matches h pad order opened pl ls (i / s)
  | _, _, _ => False

theorem filter_ne_length (pg : ℕ) :
    ∀ s, ((List.range s).filter (· ≠ pg)).length = if pg < s then s - 1 else s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    have e : ([s].filter (· ≠ pg)).length = if pg = s then 0 else 1 := by
      by_cases hps : pg = s
      · subst hps; simp
      · simp [Ne.symm hps, hps]
    rw [e]
    by_cases h1 : pg < s
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega)]; omega
    · by_cases h2 : pg = s
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (by omega)]; omega
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]

theorem filter_ne_get (pg : ℕ) :
    ∀ s k, k < s → k ≠ pg →
      ((List.range s).filter (· ≠ pg))[if k < pg then k else k - 1]? = some k := by
  intro s
  induction s with
  | zero => intro k hk; omega
  | succ s ih =>
    intro k hk hkp
    rw [List.range_succ, List.filter_append]
    by_cases hks : k < s
    · have := ih k hks hkp
      rw [List.getElem?_append_left (by
        rcases (List.getElem?_eq_some_iff.mp this) with ⟨h, _⟩; exact h), this]
    · have hk' : k = s := by omega
      subst hk'
      have hlen := filter_ne_length pg k
      have hidx : (if k < pg then k else k - 1) = ((List.range k).filter (· ≠ pg)).length := by
        rw [hlen]; split_ifs <;> omega
      rw [List.getElem?_append_right (by omega), hidx, Nat.sub_self]
      simp [hkp]

theorem walk_honest (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (opened : List (List F)) (proof : List D) :
    ∀ (pl : List Level) (ls : List (LayerSpec D)) (L0 : ℕ → D) (i pp : ℕ),
      Matches h pad order opened pl ls i →
      (∀ j < (path c pad z L0 ls i).length,
        proof.getD (pp + j) z = (path c pad z L0 ls i).getD j z) →
      walk h c pad z order opened proof pl i pp (L0 i) = (capIndex pl i, top c pad z L0 ls (capIndex pl i)) := by
  intro pl
  induction pl with
  | nil =>
    intro ls L0 i pp hm _
    cases ls with
    | nil => rfl
    | cons l ls => exact hm.elim
  | cons lv pl ih =>
    intro ls L0 i pp hm hp
    obtain ⟨s, g⟩ := lv
    cases ls with
    | nil => exact hm.elim
    | cons l ls =>
    obtain ⟨hs, hs0, hsp, hinj, hrest⟩ := hm
    subst hs
    set s := l.step
    have hpg : i % s < s := Nat.mod_lt _ hs0
    set sib := ((List.range s).filter (· ≠ i % s)).map (fun k => L0 (i / s * s + k))
    have hsiblen : sib.length = s - 1 := by
      simp only [sib, List.length_map, filter_ne_length, ite_eq_left hpg]
    have hpath : path c pad z L0 (l :: ls) i = sib ++ path c pad z (node c pad z L0 l) ls (i / s) := rfl
    -- The children the verifier assembles are the node's children in the tree.
    have hch : children pad s (i % s) (L0 i) proof pp z =
        (List.range pad.length).map fun k => if k < s then L0 (i / s * s + k) else pad.getD k z := by
      apply List.map_congr_left
      intro k hk
      by_cases hks : k < s
      · rw [ite_eq_left hks, ite_eq_left hks]
        by_cases hkp : k = i % s
        · rw [ite_eq_left hkp, hkp, Nat.div_add_mod']
        · rw [ite_eq_right hkp]
          have hj : (if k < i % s then k else k - 1) < sib.length := by
            rw [hsiblen]; split_ifs <;> omega
          rw [hp _ (by rw [hpath, List.length_append]; omega), hpath,
            List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
          simp only [sib, List.getElem?_map, filter_ne_get (i % s) s k hks hkp, Option.map_some,
            Option.getD_some]
      · rw [ite_eq_right hks, ite_eq_right hks]
    have hfold : c (children pad s (i % s) (L0 i) proof pp z) = fold c pad z L0 s (i / s * s) := by
      rw [hch]; rfl
    simp only [walk, capIndex, top]
    rw [hfold]
    have hrest_p : ∀ j < (path c pad z (node c pad z L0 l) ls (i / s)).length,
        proof.getD (pp + (s - 1) + j) z =
          (path c pad z (node c pad z L0 l) ls (i / s)).getD j z := by
      intro j hj
      have := hp (s - 1 + j) (by rw [hpath, List.length_append, hsiblen]; omega)
      rw [show pp + (s - 1) + j = pp + (s - 1 + j) by omega, this, hpath,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hsiblen,
        show s - 1 + j - (s - 1) = j by omega, ← List.getD_eq_getElem?_getD]
    have key := ih ls (node c pad z L0 l) (i / s) (pp + (s - 1)) hrest hrest_p
    rw [← key]
    congr 1
    -- The digest after this level is the path's node in the layer above.
    show _ = node c pad z L0 l (i / s)
    unfold node
    cases g with
    | none =>
      cases hl : l.inj with
      | none => rfl
      | some p => rw [hl] at hinj; exact hinj.elim
    | some ab =>
      obtain ⟨a, b⟩ := ab
      cases hl : l.inj with
      | none => rw [hl] at hinj; exact hinj.elim
      | some p =>
        obtain ⟨ht, rows⟩ := p
        rw [hl] at hinj
        obtain ⟨hlt, heq⟩ := hinj
        simp only [ite_eq_left hlt, heq]
        rfl

end Plonky3Lean.Proofs.MerkleTree
