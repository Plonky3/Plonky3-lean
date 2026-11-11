module

public import Plonky3Lean.Proofs.MerkleTree.Access

@[expose] public section

/-!
# The verifier's walk up the tree, as a function

The verifier climbs from the leaf to the cap one level at a time.

Each level folds the path's digest with its siblings, then may mix in the rows of the matrices injected there.

Which matrices are injected, and where, depends only on the dimensions.

So the walk splits into a plan, read from the dimensions, and a fold of the plan over the opening.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Proofs.MerkleTree

/-- The first position at or after `p` whose matrix is not `h` rows tall. -/
def advance (height : ℕ → ℕ) (order : List ℕ) (h : ℕ) (p : ℕ) : ℕ :=
  if p < order.length ∧ height (order.getD p 0) = h then advance height order h (p + 1) else p
termination_by order.length - p

theorem advance_le_aux (height : ℕ → ℕ) (order : List ℕ) (h : ℕ) :
    ∀ n p, order.length - p = n → p ≤ order.length →
      p ≤ advance height order h p ∧ advance height order h p ≤ order.length := by
  intro n
  induction n with
  | zero =>
    intro p hn hp
    rw [advance]
    split
    · omega
    · omega
  | succ n ih =>
    intro p hn hp
    rw [advance]
    split
    · have := ih (p + 1) (by omega) (by omega)
      omega
    · omega

theorem advance_le (height : ℕ → ℕ) (order : List ℕ) (h p : ℕ) (hp : p ≤ order.length) :
    advance height order h p ≤ order.length :=
  (advance_le_aux height order h _ p rfl hp).2

theorem le_advance (height : ℕ → ℕ) (order : List ℕ) (h p : ℕ) (hp : p ≤ order.length) :
    p ≤ advance height order h p :=
  (advance_le_aux height order h _ p rfl hp).1

/-- One level of the plan: its arity, and the positions of the matrices injected after it. -/
abbrev Level := ℕ × Option (ℕ × ℕ)

/-- The verifier's plan over the levels `sched`, from layer width `curr` and position `pos`. -/
def plan (N : ℕ) (height : ℕ → ℕ) (order : List ℕ) : List ℕ → ℕ → ℕ → List Level
  | [], _, _ => []
  | s :: rest, curr, pos =>
    if pos < order.length ∧ npt (height (order.getD pos 0)) = npt (curr / s) then
      let p1 := advance height order (height (order.getD pos 0)) pos
      (s, some (pos, p1)) :: plan N height order rest (padded (curr / s) N) p1
    else (s, none) :: plan N height order rest (padded (curr / s) N) pos

/-- The rows of the matrices at positions `a` to `b` of `order`, in that order. -/
def group {F : Type _} (order : List ℕ) (opened : List (List F)) (a b : ℕ) : List (List F) :=
  ((order.drop a).take (b - a)).map fun m => opened.getD m []

/-- The children of one node: the path's digest at its position, the siblings in order elsewhere.

Slots past the arity keep the padding `pad`. -/
def children {D : Type _} (pad : List D) (s pg : ℕ) (d : D) (proof : List D) (pp : ℕ) (z : D) :
    List D :=
  (List.range pad.length).map fun k =>
    if k < s then (if k = pg then d else proof.getD (pp + if k < pg then k else k - 1) z)
    else pad.getD k z

/-- The fold of a plan over an opening: the cap index and the digest it reaches. -/
def walk {F D : Type _} (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (opened : List (List F)) (proof : List D) :
    List Level → ℕ → ℕ → D → ℕ × D
  | [], i, _, d => (i, d)
  | (s, g) :: rest, i, pp, d =>
    let d1 := c (children pad s (i % s) d proof pp z)
    let d2 := match g with
      | none => d1
      | some (a, b) => c ((pad.set 0 d1).set 1 (h (group order opened a b)))
    walk h c pad z order opened proof rest (i / s) (pp + (s - 1)) d2

/-- The cap index a plan reaches from leaf index `i`. -/
def capIndex : List Level → ℕ → ℕ
  | [], i => i
  | (s, _) :: rest, i => capIndex rest (i / s)

theorem walk_fst {F D : Type _} (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (opened : List (List F)) (proof : List D) :
    ∀ (pl : List Level) i pp d, (walk h c pad z order opened proof pl i pp d).1 = capIndex pl i := by
  intro pl
  induction pl with
  | nil => intro i pp d; rfl
  | cons l rest ih =>
    intro i pp d
    obtain ⟨s, g⟩ := l
    simp only [walk, capIndex]
    exact ih _ _ _

theorem plan_steps (N : ℕ) (height : ℕ → ℕ) (order : List ℕ) :
    ∀ (sched : List ℕ) curr pos, ∀ l ∈ plan N height order sched curr pos, l.1 ∈ sched := by
  intro sched
  induction sched with
  | nil => intro curr pos l hl; simp [plan] at hl
  | cons s rest ih =>
    intro curr pos l hl
    simp only [plan] at hl
    split at hl
    · rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact List.mem_cons_of_mem _ (ih _ _ l hl)
    · rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact List.mem_cons_of_mem _ (ih _ _ l hl)

theorem group_eq_get {F : Type _} (order : List ℕ) (o1 o2 : List (List F)) (a b k : ℕ)
    (h : group order o1 a b = group order o2 a b) (hak : a ≤ k) (hkb : k < b)
    (hk : k < order.length) : o1.getD (order.getD k 0) [] = o2.getD (order.getD k 0) [] := by
  have e := congrArg (fun l => l[k - a]?) h
  simp only [group] at e
  have hlt : k - a < ((order.drop a).take (b - a)).length := by simp; omega
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hlt] at e
  simp only [Option.map_some, Option.some.injEq] at e
  have : ((order.drop a).take (b - a))[k - a] = order.getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, show a + (k - a) = k by omega]
  rw [this] at e
  exact e

end Plonky3Lean.Proofs.MerkleTree
