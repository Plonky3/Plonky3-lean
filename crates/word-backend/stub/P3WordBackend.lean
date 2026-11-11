/-
The Lean model of p3-word-backend.

Nothing is extracted.

The crate's dependencies do not compile in the variant charon reads.

Its sumcheck, commitment and transcript code is generic over the field traits, which aeneas rejects.

The pure parts the relation checks rest on are transcribed, one definition per Rust item:

- the key codes;
- the statement shape and the relation columns;
- the shift transpose;
- the exponent lift of a product.
-/
module

public import P3WordBackend.Code
public import P3WordBackend.Columns
public import P3WordBackend.Wiring
public import P3WordBackend.IntegerMul

@[expose] public section
