# Patches

Two kinds, per crate, kept apart because they cost different amounts of trust.

- **`patches/pre/`** changes the Rust in `plonky3/` before hax runs, and is
  reverted afterwards. The model then describes a patched Plonky3, not the one
  that ships, and nothing proved on the Lean side can close that gap. Use one
  only when extraction is impossible otherwise, for example to gate SIMD modules
  that the extraction target does not already exclude. CODEOWNERS assigns these
  to the Plonky3 maintainers.
- **`patches/post/`** changes the Lean that hax generated. The Rust is untouched;
  the patch is a claim about the encoding.

## Rules

- One logical change per file, named `NNN-slug.patch` and applied in order.
- Every patch starts with a header that `xtask check` validates:

  ```
  # Patch:     040-sampling-bits-native-decide
  # Phase:     post
  # Target:    extraction/p3_baby_bear.lean
  # Hunks:     1
  # Cost:      Lean.ofReduceBool
  # Upstream:  <the extractor bug or limitation, with a link when reported>
  # Drop when: <the condition under which this patch is no longer needed>
  ```

- `Cost` is `none` or the axiom or assumption the patch adds. `STATUS.md` lists
  every patch whose `Cost` is not `none`.
- The declared `Hunks` must match the diff, and the ordered set must apply with
  zero fuzz, so drift fails loudly instead of landing somewhere plausible.
- Prefer fixing a stub over patching generated code, and prefer a patch over a
  `sorry`. A generated `sorry` is never accepted.
