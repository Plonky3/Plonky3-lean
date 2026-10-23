module

public import Plonky3Lean.Proofs.Whir.Constraint

@[expose] public section

/-!
# Weight tables

The prover keeps a weight as its table over the cube.

The weights WHIR adds, eq(z, .) and the selectors, are multilinear, so the extension of their table is the weight itself.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.constraints.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- The table of a function over the n-cube. -/
def cubeTable (g : List EF → EF) (n : ℕ) : List EF := (List.range (2 ^ n)).map fun b => g (vertex n b)

@[simp] theorem length_cubeTable (g : List EF → EF) (n : ℕ) : (cubeTable g n).length = 2 ^ n := by
  simp [cubeTable]

theorem getD_cubeTable (g : List EF → EF) {n b : ℕ} (hb : b < 2 ^ n) :
    (cubeTable g n).getD b 0 = g (vertex n b) := by
  simp [cubeTable, List.getD_eq_getElem?_getD, hb]

/-- g is multilinear in n variables: the extension of its table is g. -/
def IsML (g : List EF → EF) (n : ℕ) : Prop := ∀ y : List EF, y.length = n → mle (cubeTable g n) y = g y

theorem mle_map_mul_right (a : EF) (f r : List EF) : mle (f.map (· * a)) r = mle f r * a := by
  simp only [mle, sum_mul, getD_map_mul_right]
  exact sum_congr rfl fun _ _ => by ring

/-- The extension of eq(p, .)'s table is eq(p, .). -/
theorem mle_eqTable : ∀ (p y : List EF), p.length = y.length → mle (eqTable p) y = eq p y
  | [], [], _ => by simp
  | c :: p, a :: y, h => by
    have h' : p.length = y.length := by simpa using h
    have hl : ((eqTable p).map (· * (1 - c))).length = 2 ^ y.length := by simp [h']
    rw [mle_cons, eqTable_cons, List.take_left' hl, List.drop_left' (by simpa using hl),
      mle_map_mul_right, mle_map_mul_right, mle_eqTable p y h', eq_cons]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem isML_eq (p : List EF) : IsML (eq p) p.length := fun y hy => by
  rw [← mle_eqTable p y hy.symm]
  congr 1
  refine List.ext_getElem (by simp [eqTable]) fun b h1 h2 => ?_
  simp [cubeTable, eqTable, eq_comm']

theorem isML_sel (q : EF) (n : ℕ) : IsML (sel q) n := fun y hy => by
  rw [sel_eq_mle, hy]
  congr 1
  refine List.ext_getElem (by simp [powTable]) fun b h1 h2 => ?_
  simp only [cubeTable, List.getElem_map, List.getElem_range]
  rw [sel_vertex q (by simpa using h1)]
  simp [powTable]

theorem mle_add_tables {a b : List EF} (hab : a.length = b.length) (y : List EF) :
    mle (List.zipWith (· + ·) a b) y = mle a y + mle b y := by
  simp only [mle, ← sum_add_distrib, ← mul_add]
  refine sum_congr rfl fun i _ => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases hi : i < a.length
  · simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hab ▸ hi)]
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt hi), List.getElem?_eq_none (hab ▸ Nat.le_of_not_lt hi)]

theorem cubeTable_add (g g' : List EF → EF) (n : ℕ) :
    cubeTable (fun y => g y + g' y) n = List.zipWith (· + ·) (cubeTable g n) (cubeTable g' n) := by
  simp [cubeTable, List.zipWith_map, List.zipWith_self]

theorem IsML.add {g g' : List EF → EF} {n : ℕ} (h : IsML g n) (h' : IsML g' n) :
    IsML (fun y => g y + g' y) n := fun y hy => by
  rw [cubeTable_add, mle_add_tables (by simp), h y hy, h' y hy]

theorem IsML.mul_const {g : List EF → EF} {n : ℕ} (h : IsML g n) (a : EF) : IsML (fun y => g y * a) n :=
  fun y hy => by
    rw [show cubeTable (fun y => g y * a) n = (cubeTable g n).map (· * a) by simp [cubeTable],
      mle_map_mul_right, h y hy]

theorem isML_zero (n : ℕ) : IsML (fun _ => (0 : EF)) n := fun y hy =>
  sum_eq_zero fun b hb => by rw [getD_cubeTable _ (hy ▸ mem_range.mp hb), mul_zero]

theorem isML_dot : ∀ (gs : List (List EF → EF)) (pw : List EF) {n : ℕ}, (∀ g ∈ gs, IsML g n) →
    IsML (fun y => dot (gs.map (· y)) pw) n
  | [], _, n, _ => by simpa [dot] using isML_zero (EF := EF) n
  | _ :: _, [], n, _ => by simpa [dot] using isML_zero (EF := EF) n
  | g :: gs, p :: pw, n, h => by
    have := (h g (by simp)).mul_const p |>.add (isML_dot gs pw fun t ht => h t (by simp [ht]))
    simpa [dot] using this

/-- The weight functions of a group, one per point. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.fns : Statements F EF → List (List EF → EF)
  | .Eq s => s.points.map fun p => eq p
  | .Select s => s.vars.map fun v => sel (algebraMap F EF v)

theorem _root_.p3_sumcheck.constraints.mirror.Statements.weights_eq (s : Statements F EF) (y : List EF) :
    s.weights y = s.fns.map (· y) := by
  cases s <;> simp [Statements.weights, Statements.fns, Function.comp]

/-- Every point of a group has n coordinates. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.Dim (n : ℕ) : Statements F EF → Prop
  | .Eq s => ∀ p ∈ s.points, p.length = n
  | .Select _ => True

theorem isML_fns {s : Statements F EF} {n : ℕ} (h : s.Dim n) : ∀ g ∈ s.fns, IsML g n := by
  cases s with
  | Eq s =>
    simp only [Statements.fns, List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    simpa [h p hp] using isML_eq p
  | Select s =>
    simp only [Statements.fns, List.mem_map]
    rintro _ ⟨v, -, rfl⟩
    exact isML_sel _ n

/-- A constraint's weight is multilinear, so its table extends to it. -/
theorem isML_weightAt (c : Constraint F EF) {n : ℕ} (h : ∀ s ∈ c.statements, s.Dim n) :
    IsML (weightAt c) n := by
  have : weightAt c = fun y => dot ((c.statements.flatMap Statements.fns).map (· y))
      (powers c.challenge c.initial_power (c.statements.flatMap Statements.evals).length) := by
    funext y
    simp only [weightAt, List.map_flatMap]
    congr 2
    funext s
    exact Statements.weights_eq s y
  rw [this]
  refine isML_dot _ _ fun g hg => ?_
  obtain ⟨s, hs, hg⟩ := List.mem_flatMap.mp hg
  exact isML_fns (h s hs) g hg

end Plonky3Lean.Proofs.Whir
