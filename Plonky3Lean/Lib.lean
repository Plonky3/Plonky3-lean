import Plonky3Lean.Lib.Iter
import Plonky3Lean.Lib.RustM
import Plonky3Lean.Lib.Scalar
import Plonky3Lean.Lib.Scalar.Bits
import Plonky3Lean.Lib.Scalar.Signed
import Plonky3Lean.Lib.Scalar.U64

/-!
# Library

Lemmas and tactics shared across proofs: reasoning about `RustM`, Rust integer
types, `Array` and `Slice` construction. Nothing specific to one crate or claim.
Facts about fields belong in CompPoly, or in `ToCompPoly` until they are
upstreamed.
-/
