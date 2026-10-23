/-
Transcriptions of the matrix commitment scheme's default methods, and of the extension-field adapter.

What a transcription abstracts:

* a matrix is its height, width and entries;
* a scheme's required methods are parameters;
* an extension element is its D coordinates over the base field, through a basis and its inverse;
* the flattened view keeps the original matrix, so the adapter's prover data keeps both;
* a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Commit.Types
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace p3_commit.mmcs.mirror

open p3_commit.pcs.univariate.mirror

variable {T : Type _}

/-- The default single-matrix commit: commit to a batch of one. -/
def commit_matrix {α : Type _} (commit : List (Mat T) → α) (input : Mat T) : α := commit [input]

/-- The default vector commit: the vector as a one-column matrix. -/
def commit_vec {α : Type _} [Inhabited T] (commit : List (Mat T) → α) (input : List T) : α :=
  commit_matrix commit ⟨input.length, 1, fun r _ => input.getD r default⟩

/-- The default heights: the height of every committed matrix. -/
def get_matrix_heights {PD : Type _} (get_matrices : PD → List (Mat T)) (prover_data : PD) :
    List ℕ :=
  (get_matrices prover_data).map Mat.height

/-- The default maximum height, which panics on an empty batch. -/
def get_max_height {PD : Type _} (get_matrices : PD → List (Mat T)) (prover_data : PD) :
    Option ℕ :=
  (get_matrix_heights get_matrices prover_data).max?

end p3_commit.mmcs.mirror

namespace p3_commit.adapters.extension_mmcs.mirror

open p3_commit.pcs.univariate.mirror

/-- An extension field with a basis of D elements over the base field: coordinates and their inverse. -/
structure Basis (F EF : Type _) where
  D : ℕ
  coords : EF → Fin D → F
  ofCoords : (Fin D → F) → EF

variable {F EF : Type _} [Zero F] (B : Basis F EF)

/-- Flatten extension elements into their coordinates, element after element. -/
def flatten_to_base (row : List EF) : List F :=
  row.flatMap fun e => List.ofFn (B.coords e)

/-- Rebuild extension elements from consecutive runs of D coordinates; the length must be a multiple of D. -/
def reconstitute_from_base (l : List F) : Option (List EF) :=
  if l.length % B.D ≠ 0 then none
  else some ((List.range (l.length / B.D)).map fun i => B.ofCoords fun j => l.getD (i * B.D + j.val) 0)

theorem div_lt_width {w D : ℕ} (c : Fin (w * D)) : c.val / D < w :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm w D ▸ c.isLt)

theorem mod_lt_dim {w D : ℕ} (c : Fin (w * D)) : c.val % D < D :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by have := c.isLt; simp [h] at this)

/-- The flattened view: entry (r, c) is coordinate c mod D of entry (r, c / D). -/
def flatMat (m : Mat EF) : Mat F :=
  ⟨m.height, m.width * B.D, fun r c => B.coords (m.entry r ⟨c.val / B.D, div_lt_width c⟩)
    ⟨c.val % B.D, mod_lt_dim c⟩⟩

/-- The adapter over an inner scheme, given as its operations. -/
structure Inner (F : Type _) where
  Commitment : Type
  ProverData : Type
  Proof : Type
  commit : List (Mat F) → Option (Commitment × ProverData)
  open_batch : ℕ → ProverData → Option (List (List F) × Proof)
  verify_batch : Commitment → List (ℕ × ℕ) → ℕ → List (List F) → Proof → Option Bool

variable (inner : Inner F)

/-- Commit: commit to the flattened views. -/
def commit (inputs : List (Mat EF)) : Option (inner.Commitment × (inner.ProverData × List (Mat EF))) :=
  (inner.commit (inputs.map (flatMat B))).map fun cd => (cd.1, (cd.2, inputs))

/-- Open: open the inner batch, then rebuild every row. -/
def open_batch (index : ℕ) (prover_data : inner.ProverData × List (Mat EF)) :
    Option (List (List EF) × inner.Proof) := do
  let (inner_opened_values, inner_proof) ← inner.open_batch index prover_data.1
  let opened_ext_values ← inner_opened_values.mapM (reconstitute_from_base B)
  pure (opened_ext_values, inner_proof)

/-- The committed matrices: the originals the flattened views hold. -/
def get_matrices (prover_data : inner.ProverData × List (Mat EF)) : List (Mat EF) := prover_data.2

/-- Verify: flatten the claimed rows and scale every width by D. -/
def verify_batch (commit : inner.Commitment) (dimensions : List (ℕ × ℕ)) (index : ℕ)
    (opened_values : List (List EF)) (proof : inner.Proof) : Option Bool :=
  let opened_base_values := opened_values.map (flatten_to_base B)
  let base_dimensions := dimensions.map fun d => (d.1 * B.D, d.2)
  inner.verify_batch commit base_dimensions index opened_base_values proof

end p3_commit.adapters.extension_mmcs.mirror
