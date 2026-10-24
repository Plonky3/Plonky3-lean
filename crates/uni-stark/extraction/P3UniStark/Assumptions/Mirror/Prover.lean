/-
Transcriptions of the prover's quotient sizing and quotient evaluation.

These do not extract.
They are generic over the configuration, the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the folder transcriptions:

* the domains are two-adic cosets over the base field F, as p3-commit's transcriptions model them
* the scheme's methods enter as their transcriptions in p3-commit, or as arguments
* a packed group is its lanes, each lane evaluating one point of the quotient domain
* the lanes past the quotient size, which Rust pads and then drops, are not modelled
* a packed periodic group is read through its period, proved equal to the direct read in p3-commit
* a panic is none.

The order of operations is kept.
-/
module

public import P3UniStark.Assumptions.Mirror.Folder
public import P3Commit

@[expose] public section

namespace p3_uni_stark.prover.mirror

open p3_air.builder.mirror p3_air.air.mirror p3_air.symbolic.mirror p3_uni_stark.folder.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror
open p3_field.coset.mirror p3_dft.mirror

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- The two-adic quotient sizing.

It takes the larger of the constraint degree and the degree hint, and adds the zero-knowledge bit.
It pads the result to at least 2, subtracts 1, and takes log_2 rounded up.

The flag must be 0 or 1. -/
def get_log_quotient_degree_extension (air : Air F) (layout : AirLayout) (trace_len is_zk : ℕ) :
    Except String ℕ := do
  if is_zk > 1 then throw "is_zk must be either 0 or 1"
  let degree := max (← get_max_constraint_degree air layout trace_len)
    (air.max_constraint_degree.getD 0)
  let constraint_degree := max (degree + is_zk) 2
  pure (log2_ceil_usize (constraint_degree - 1))

/-- The quotient sizing of a domain.

A two-adic coset's transition selector has degree multiple 0, so it takes the two-adic path. -/
def get_log_num_quotient_chunks_for_domain (air : Air F) (layout : AirLayout) (trace_len is_zk : ℕ) :
    Except String ℕ :=
  get_log_quotient_degree_extension air layout trace_len is_zk

/-- The prover's chunk count: 2^(log_2 chunks + is_zk). -/
def num_quotient_chunks (log_num_quotient_chunks is_zk : ℕ) : ℕ :=
  2 ^ (log_num_quotient_chunks + is_zk)

variable (G : Gen F)

/-- Row r of a matrix, wrapping past the last row as the vertical packing does. -/
def wrappingRow (m : p3_commit.pcs.univariate.mirror.Mat F) (r : ℕ) : List F :=
  (List.finRange m.width).map (m.entry (r % m.height))

/-- The quotient's value at each point x_i of the quotient domain.

It is the prover's combination of the constraints on rows i and i + s, times 1 / Z(x_i).
Here s is the ratio of the quotient domain size to the trace domain size.

The row i + s holds the trace at omega x_i, for omega the trace subgroup's generator. -/
noncomputable def quotient_values {D : ℕ} (B : Module.Basis (Fin D) F K) (air : Air F)
    (public_values : List F) (layout : AirLayout) (trace_domain quotient_domain : Coset G)
    (trace_on_quotient_domain : p3_commit.pcs.univariate.mirror.Mat F)
    (preprocessed_on_quotient_domain : Option (p3_commit.pcs.univariate.mirror.Mat F)) (alpha : K) :
    Option (List K) := do
  let quotient_size := Coset.size G quotient_domain
  let sels ← Coset.selectors_on_coset G trace_domain quotient_domain
  if quotient_domain.log_size < trace_domain.log_size then none
  let next_step := 2 ^ (quotient_domain.log_size - trace_domain.log_size)
  let constraint_layout ← (get_constraint_layout air layout).toOption
  let (base_alpha_powers, ext_alpha_powers) := constraint_layout.decompose_alpha B alpha
  let periodic_table ← build_periodic_lde_table G air.periodic_columns trace_domain quotient_domain
  (List.range quotient_size).mapM fun i => do
    let main : RowWindow F := ⟨wrappingRow trace_on_quotient_domain i,
      wrappingRow trace_on_quotient_domain (i + next_step)⟩
    let preprocessed : RowWindow F := match preprocessed_on_quotient_domain with
      | some p => ⟨wrappingRow p i, wrappingRow p (i + next_step)⟩
      | none => ⟨[], []⟩
    let periodic_values ← if periodic_table.is_empty then some []
      else (List.range periodic_table.width).mapM (periodic_table.get i)
    let folder := proverFolder main preprocessed public_values periodic_values
      (sels.is_first_row.getD i 0) (sels.is_last_row.getD i 0) (sels.is_transition.getD i 0)
    let quotient ← finalize_constraints B base_alpha_powers ext_alpha_powers (air.eval folder []) []
    pure (quotient * algebraMap F K (sels.inv_vanishing.getD i 0))

end p3_uni_stark.prover.mirror
