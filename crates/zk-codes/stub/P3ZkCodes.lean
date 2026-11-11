/-
The Lean model of p3-zk-codes.

Nothing is extracted: the encoding is generic over the field traits and over the transform backend, which aeneas rejects.

Each item is transcribed over a field, one definition per Rust item.
-/
module

public import P3ZkCodes.Encoding
public import P3ZkCodes.ReedSolomon

@[expose] public section
