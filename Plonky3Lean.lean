import Plonky3Lean.Lib
import Plonky3Lean.Spec
import Plonky3Lean.Proofs
import Plonky3Lean.Claims

/-!
# Plonky3Lean

The hand-written half of the repository. The other half, under `crates/`, is
the Lean model of Plonky3's Rust: extracted by hax, or stubbed by hand until it
is.

* `Plonky3Lean.Claims`: the statements this repository asserts about Plonky3.
* `Plonky3Lean.Spec`: the definitions those statements are written in.
* `Plonky3Lean.Proofs`: the proofs.
* `Plonky3Lean.Lib`: lemmas and tactics shared by the proofs.

The tree is organized by property, not by crate: a statement about Poseidon2
over BabyBear involves several crates at once.
-/
