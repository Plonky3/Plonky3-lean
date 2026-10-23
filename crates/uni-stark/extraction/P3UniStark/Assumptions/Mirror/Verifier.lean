/-
Transcriptions of the verifier's checks: the chunk recombination, the constraint check at the out-of-domain point, and the shape checks.

These do not extract: they are generic over the configuration, the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the folder transcriptions:

* the domains are two-adic cosets over the challenge field K, as p3-commit's transcriptions model them, with base values read through their embedding;
* the basis of K over the base field F that Rust fixes is a parameter;
* an inverse of zero panics, as Rust's checked inverse does;
* a panic is none, and a rejection is an error value.

Loops, branches and the order of checks are kept.
-/
module

public import P3UniStark.Assumptions.Mirror.Folder
public import P3Commit

@[expose] public section

namespace p3_uni_stark.verifier.mirror

open p3_air.builder.mirror p3_air.air.mirror p3_uni_stark.folder.mirror
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K]

/-- The element whose coordinates in the basis are the given values, absent unless there are exactly D of them. -/
noncomputable def from_ext_basis_coefficients {D : ℕ} (B : Module.Basis (Fin D) F K) (ch : List K) :
    Option K :=
  if ch.length = D then some (∑ d : Fin D, ch.getD d 0 * B d) else none

variable (G : Gen K)

/-- The Lagrange factor of chunk i at zeta: the product over the other chunks j of Z_j(zeta) / Z_j(first point of chunk i). -/
def chunkFactor (domains : List (Coset G)) (zeta : K) (i : ℕ) : Option K := do
  let domain ← domains[i]?
  ((List.range domains.length).filter (· ≠ i)).foldlM (fun acc j => do
    let other ← domains[j]?
    let w ← inv (Coset.vanishing_poly_at_point G other (Coset.first_point G domain))
    pure (acc * (Coset.vanishing_poly_at_point G other zeta * w))) 1

/-- The quotient at zeta from its chunks' openings: each chunk's value, rebuilt from its coordinates, times its Lagrange factor.

A chunk without exactly D coordinates panics. -/
noncomputable def recompose_quotient_from_chunks {D : ℕ} (B : Module.Basis (Fin D) F K)
    (domains : List (Coset G)) (chunks : List (List K)) (zeta : K) : Option K := do
  let zps ← (List.range domains.length).mapM (chunkFactor G domains zeta)
  (List.range chunks.length).foldlM (fun acc i => do
    let zp ← zps[i]?
    let ch ← chunks[i]?
    let c ← from_ext_basis_coefficients B ch
    pure (acc + zp * c)) 0

end p3_uni_stark.verifier.mirror
