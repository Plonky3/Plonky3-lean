import Plonky3Lean.Spec.BabyBear

/-!
# Specifications

The definitions that claims are stated in: `Prop`-valued predicates and the
functions they mention, for example "this `u32` is the Montgomery form of this
element of `ZMod p`". No proofs.

Prefer an existing specification (CompPoly, ArkLib, mathlib) over a new one.
Define one here only when none fits, and keep it independent of the extracted
code, so that a claim compares the model against something that was not derived
from it. CODEOWNERS assigns this module to the Plonky3 maintainers.

Spec modules may also name items of the model with `abbrev`s, so that claims
read in Rust's terms (`Spec.BabyBear.PRIME` for `BabyBearParameters::PRIME`).
Such names are aliases and specify nothing; they live here rather than beside
the proofs because a change to one changes what a claim says.
-/
