module

public import P3Commit.Mmcs
public import Plonky3Lean.Proofs.Commit.PeriodicTable
public import Plonky3Lean.Spec.Commit

@[expose] public section

/-!
# p3-commit: the matrix commitment contract

The default methods meet their contract on any scheme that meets the scheme contract.

A scheme that commits the matrices themselves meets the contract, so the contract is satisfiable.

The extension-field adapter turns a scheme over the base field that meets the contract into one over the extension that meets it, with the same failure event.
-/

open p3_commit.pcs.univariate.mirror p3_commit.mmcs.mirror Plonky3Lean.Spec.Commit

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

/-! ## Default methods -/

section defaults

variable {T : Type _} (mmcs : Mmcs T)

theorem max?_eq_foldr (l : List ℕ) (h : l ≠ []) : l.max? = some (l.foldr max 0) := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · simp
    · rw [List.max?_cons, ih (List.cons_ne_nil _ _)]
      simp

/-- The heights the default reports are the committed matrices' heights. -/
theorem get_matrix_heights_eq (C : mmcs.Contract) (ms : List (Mat T)) cd (h : mmcs.commit ms = some cd) :
    get_matrix_heights mmcs.get_matrices cd.2 = ms.map Mat.height := by
  rw [get_matrix_heights, C.get_matrices ms cd h]

/-- The default maximum height is the tallest height, and panics exactly on an empty batch. -/
theorem get_max_height_eq (C : mmcs.Contract) (ms : List (Mat T)) cd (h : mmcs.commit ms = some cd) :
    get_max_height mmcs.get_matrices cd.2 = if ms = [] then none else some (maxHeight ms) := by
  rw [get_max_height, get_matrix_heights_eq mmcs C ms cd h]
  split_ifs with hms
  · simp [hms]
  · exact max?_eq_foldr _ (by simpa using hms)

/-- The default single-matrix commit is the commit of a batch of one. -/
theorem commit_matrix_eq (m : Mat T) : commit_matrix mmcs.commit m = mmcs.commit [m] := rfl

/-- The default vector commit is the commit of a one-column matrix holding the vector. -/
theorem commit_vec_eq [Inhabited T] (v : List T) :
    commit_vec mmcs.commit v = mmcs.commit [⟨v.length, 1, fun r _ => v.getD r default⟩] := rfl

end defaults

/-! ## A scheme that commits the matrices -/

section reference

variable {T : Type} [DecidableEq T]

/-- The reference scheme: the commitment is the matrices, and verification recomputes the rows. -/
abbrev referenceMmcs : Mmcs T where
  Commitment := List (Mat T)
  ProverData := List (Mat T)
  Proof := Unit
  commit ms := some (ms, ms)
  open_batch index pd := some (openedRows pd index, ())
  get_matrices pd := pd
  verify_batch cm dims index rows _ :=
    some (decide (dims = cm.map (fun m => (m.width, m.height)) ∧ rows = openedRows cm index))

/-- The reference scheme meets the contract, and nothing breaks its binding. -/
def referenceContract : (referenceMmcs (T := T)).Contract where
  Broken _ := False
  get_matrices ms cd h := by cases h; rfl
  completeness ms cd index h _ _ := by
    cases h
    exact ⟨(), rfl, by simp⟩
  binding cm dims index rows₁ rows₂ pf₁ pf₂ h₁ h₂ := by
    simp only [Option.some.injEq, decide_eq_true_eq] at h₁ h₂
    exact Or.inl (h₁.2.trans h₂.2.symm)
  widths cm dims index rows pf h := by
    simp only [Option.some.injEq, decide_eq_true_eq] at h
    rw [h.1, h.2]
    unfold openedRows
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun m _ => by simp

end reference

/-! ## The extension-field adapter -/

section extension

open p3_commit.adapters.extension_mmcs.mirror

variable {F EF : Type} [Zero F] (B : Basis F EF)

theorem length_flatten (row : List EF) : (flatten_to_base B row).length = row.length * B.D := by
  simp [flatten_to_base, List.length_flatMap, List.sum_replicate, Nat.mul_comm]

theorem flatten_getD (row : List EF) {i : ℕ} (hi : i < row.length) (j : Fin B.D) :
    (flatten_to_base B row).getD (i * B.D + j.val) 0 = B.coords row[i] j := by
  have := flatten_getElem? (row.map fun e => List.ofFn (B.coords e)) B.D (by simp) i j.val j.isLt
  rw [List.getD_eq_getElem?_getD, flatten_to_base, List.flatMap_def, this]
  simp [hi]

/-- Rebuilding the coordinates of a row gives the row back. -/
theorem reconstitute_flatten (hD : 0 < B.D) (hB : ∀ e, B.ofCoords (B.coords e) = e) (row : List EF) :
    reconstitute_from_base B (flatten_to_base B row) = some row := by
  have hlen := length_flatten B row
  unfold reconstitute_from_base
  rw [hlen, Nat.mul_mod_left]
  simp only [ne_eq, not_true_eq_false, ite_false, Nat.mul_div_cancel _ hD, Option.some.injEq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← hB row[i]]
    congr 1
    funext j
    exact flatten_getD B row h2 j

theorem flatten_injective (hD : 0 < B.D) (hB : ∀ e, B.ofCoords (B.coords e) = e) :
    Function.Injective (flatten_to_base B) := fun a b h => by
  have := reconstitute_flatten B hD hB a
  rw [h, reconstitute_flatten B hD hB b] at this
  exact (Option.some.inj this).symm

/-- A row of the flattened view is the flattened row. -/
theorem flatMat_row (m : Mat EF) (r : ℕ) :
    (List.finRange (flatMat B m).width).map ((flatMat B m).entry r) =
      flatten_to_base B ((List.finRange m.width).map (m.entry r)) := by
  apply List.ext_getElem
  · simp [flatMat, length_flatten]
  · intro i h1 h2
    have hD : 0 < B.D := Nat.pos_of_ne_zero fun h => by simp [flatMat, h] at h1
    have hi : i / B.D < ((List.finRange m.width).map (m.entry r)).length := by
      simp only [List.length_map, List.length_finRange]
      exact Nat.div_lt_of_lt_mul (by simpa [flatMat, Nat.mul_comm] using h1)
    have := flatten_getD B ((List.finRange m.width).map (m.entry r)) hi ⟨i % B.D, Nat.mod_lt _ hD⟩
    rw [Nat.div_add_mod'] at this
    rw [← List.getD_eq_getElem _ (0 : F) h2, this]
    simp [flatMat]

/-- The inner operations of a scheme. -/
def toInner (m : Mmcs F) : Inner F :=
  ⟨m.Commitment, m.ProverData, m.Proof, m.commit, m.open_batch, m.verify_batch⟩

/-- The adapter over a scheme, as a scheme over the extension. -/
abbrev extMmcs (m : Mmcs F) : Mmcs EF where
  Commitment := m.Commitment
  ProverData := m.ProverData × List (Mat EF)
  Proof := m.Proof
  commit := commit B (toInner m)
  open_batch := open_batch B (toInner m)
  get_matrices := get_matrices (EF := EF) (toInner m)
  verify_batch := verify_batch B (toInner m)

theorem openedRows_flat (ms : List (Mat EF)) (index : ℕ) :
    openedRows (ms.map (flatMat B)) index = (openedRows ms index).map (flatten_to_base B) := by
  have hmax : maxHeight (ms.map (flatMat B)) = maxHeight ms := by
    simp [maxHeight, List.map_map, Function.comp_def, flatMat]
  simp only [openedRows, List.map_map, hmax]
  exact List.map_congr_left fun m _ => flatMat_row B m _

/-- The adapter over a scheme that meets the contract meets it too, with the same failure event. -/
def extContract (hD : 0 < B.D) (hB : ∀ e, B.ofCoords (B.coords e) = e) (m : Mmcs F)
    (C : m.Contract) : (extMmcs B m).Contract where
  Broken := C.Broken
  get_matrices ms cd h := by
    simp only [extMmcs, commit, toInner] at h
    cases hc : m.commit (ms.map (flatMat B)) with
    | none => simp [hc] at h
    | some cd' => simp only [hc, Option.map_some, Option.some.injEq] at h; subst h; rfl
  completeness ms cd index h hne hlt := by
    simp only [extMmcs, commit, toInner] at h
    cases hc : m.commit (ms.map (flatMat B)) with
    | none => simp [hc] at h
    | some cd' =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst h
      have hmax : maxHeight (ms.map (flatMat B)) = maxHeight ms := by
        simp [maxHeight, List.map_map, Function.comp_def, flatMat]
      obtain ⟨pf, hopen, hver⟩ := C.completeness _ cd' index hc (by simpa using hne)
        (hmax ▸ hlt)
      refine ⟨pf, ?_, ?_⟩
      · simp only [extMmcs, open_batch, toInner, hopen, openedRows_flat, Option.bind_eq_bind,
          Option.bind_some]
        rw [List.mapM_map, mapM_some (reconstitute_from_base B ∘ flatten_to_base B) id _
          fun row _ => reconstitute_flatten B hD hB row, List.map_id]
        rfl
      · simp only [verify_batch, toInner]
        rw [← openedRows_flat]
        convert hver using 2
        simp [List.map_map, Function.comp_def, flatMat]
  binding cm dims index rows₁ rows₂ pf₁ pf₂ h₁ h₂ := by
    rcases C.binding _ _ _ _ _ _ _ h₁ h₂ with h | h
    · exact Or.inl (List.map_injective_iff.mpr (flatten_injective B hD hB) h)
    · exact Or.inr h
  widths cm dims index rows pf h := by
    have := C.widths _ _ _ _ _ h
    simp only [List.map_map, Function.comp_def, length_flatten] at this
    apply List.ext_getElem
    · simpa using congrArg List.length this
    · intro i h1 h2
      have := congrArg (·[i]?) this
      simp only [List.getElem?_map] at this
      simp only [List.getElem_map]
      rw [List.getElem?_eq_getElem (by simpa using h1), List.getElem?_eq_getElem (by simpa using h2)] at this
      simpa [Nat.mul_left_cancel_iff hD, Nat.mul_comm _ B.D] using this

end extension

end Plonky3Lean.Proofs.Commit
