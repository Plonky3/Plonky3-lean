/-
The Lean model of p3-sumcheck.

Nothing is extracted: the crate is generic over the field and challenger traits, which aeneas rejects.

The verifier core is transcribed over a field, one definition per Rust item.
-/
module

public import P3Sumcheck.Model
public import P3Sumcheck.Lagrange
public import P3Sumcheck.Data
public import P3Sumcheck.GenericDegree
public import P3Sumcheck.Strategy
public import P3Sumcheck.Constraints

@[expose] public section
