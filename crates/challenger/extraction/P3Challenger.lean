/-
The Lean model of p3-challenger.

`P3Challenger/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

`P3Challenger/Mirror/` transcribes the methods the extraction cannot produce, each with a `[[mirror]]` entry in crate.toml.
-/
module

public import P3Challenger.Extraction
public import P3Challenger.Mirror.Duplex

@[expose] public section
