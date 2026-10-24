/-
The Lean model of p3-bus.

`P3Bus/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the integer helpers: a direction's position, the boundary rows, and the RAM payload widths.

`P3Bus/Mirror/` transcribes the rest by hand, one definition per Rust item.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3Bus.Extraction
public import P3Bus.Mirror.Builder
public import P3Bus.Mirror.Ram
public import P3Bus.Mirror.Product
public import P3Bus.Mirror.Plan
public import P3Bus.Mirror.Evaluation
public import P3Bus.Mirror.Timestamped
public import P3Bus.Mirror.Security

@[expose] public section
