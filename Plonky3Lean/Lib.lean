module

public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Lib.Iter
public import Plonky3Lean.Lib.RustM
public import Plonky3Lean.Lib.Scalar
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Lib.Scalar.Signed
public import Plonky3Lean.Lib.Scalar.U64
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Lib.Scalar.Words
public import Plonky3Lean.Lib.Yields
public import Plonky3Lean.Lib.UsizeAdd

@[expose] public section

/-!
# Library

Lemmas and tactics shared across proofs: reasoning about `RustM`, Rust integer
types, `Array` and `Slice` construction. Nothing specific to one crate or claim.
Facts about fields belong in CompPoly, or in `ToCompPoly` until they are
upstreamed.
-/
