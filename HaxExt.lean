import Hax

/-!
# Extensions to the Hax Lean library

Declarations that the pinned Hax proof library lacks and that generated or stub
code needs in order to elaborate. They model Rust's `core`/`alloc`, not
Plonky3, so they are shared by every crate.

Each declaration here is a candidate to upstream to `cryspen/hax`, and is
deleted once the pinned Hax revision provides it.
-/
