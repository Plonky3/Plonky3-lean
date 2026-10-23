/-
The Lean model of tiny-keccak's Keccak-f[1600] permutation: hax's scoped
extraction of its tables, in `TinyKeccak/Extraction/`, rooted at `start_from`
in crate.toml, and the transcription of the permutation itself, in
`TinyKeccak/Assumptions/Mirror.lean`.
-/
module

public import TinyKeccak.Extraction
public import TinyKeccak.Assumptions.Mirror

@[expose] public section
