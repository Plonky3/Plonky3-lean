/-
Transcription of one instance's constraint check at the out-of-domain point.

It does not extract: it is generic over the configuration, the field traits, the AIR and the lookup gadget, which aeneas rejects.

What the transcription abstracts, beyond the p3-uni-stark and p3-lookup transcriptions:

- the folder with lookups is p3-lookup's permutation builder over p3-uni-stark's verifier folder;
- an extension assertion folds like a base one, into acc alpha + x;
- the permutation rows are the extension values Rust recomposes before the check;
- a failed assertion and a panic are none.

The order of checks is kept.
-/
module

public import P3UniStark
public import P3BatchStark.Assumptions.Mirror.Check

@[expose] public section

namespace p3_batch_stark.constraints.mirror

open p3_air.builder.mirror p3_air.air.mirror p3_lookup.mirror p3_uni_stark.folder.mirror
  p3_uni_stark.verifier.mirror p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror

variable {F K : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K] [Algebra F K]

/-- The verifier's folder with lookups.

It reads base values through the embedding, and folds every assertion into acc alpha + x. -/
def verifierPermFolder (main preprocessed : RowWindow K) (public_values : List F)
    (periodic_values : List K) (is_first_row is_last_row is_transition alpha : K)
    (permutation : RowWindow K) (challenges values : List K) : PermBuilder F K K K where
  toAirBuilder := verifierFolder main preprocessed public_values periodic_values is_first_row
    is_last_row is_transition alpha
  ext_sub := (· - ·)
  ext_mul_expr x c := x * c
  ext_one := 1
  assert_zero_ext acc x := acc * alpha + x
  ext := ⟨(· + ·), (· - ·), (· * ·), 0, 1⟩
  ext_of := id
  permutation _ := permutation
  permutation_randomness _ := challenges
  permutation_values _ := values

variable (G : Gen K)

/-- `VerifierData::verify_constraints_with_lookups`.

- An AIR with boundary cells panics.
- A zeta on the trace domain is rejected.
- The AIR and the lookup constraints are folded at the opened rows, with the selectors at zeta.
- The fold times 1 / Z(zeta) must be the recomposed quotient. -/
def verify_constraints_with_lookups (air : Air F) (trace_local trace_next preprocessed_local
    preprocessed_next permutation_local permutation_next challenges values periodic_values : List K)
    (lookups : List (Lookup F)) (public_values : List F) (trace_domain : Coset G)
    (zeta alpha quotient : K) : Option (Except VerificationError Unit) := do
  if air.public_boundary_io ≠ [] then none
  if Coset.vanishing_poly_at_point G trace_domain zeta = 0 then return .error .OodPointInDomain
  let sels ← Coset.selectors_at_point G trace_domain zeta
  let folder := verifierPermFolder ⟨trace_local, trace_next⟩ ⟨preprocessed_local, preprocessed_next⟩
    public_values periodic_values sels.is_first_row sels.is_last_row sels.is_transition alpha
    ⟨permutation_local, permutation_next⟩ challenges values
  let acc ← p3_batch_stark.checker.mirror.eval_air_and_lookups air folder 0 lookups
  if acc * sels.inv_vanishing ≠ quotient then return .error .OodEvaluationMismatch
  pure (.ok ())

end p3_batch_stark.constraints.mirror
