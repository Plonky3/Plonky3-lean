/-
The Lean model of p3-bus.

Nothing is extracted: most items are generic over the field traits or the builder, and code over `ExtensionField` does not extract (docs/extractor-issues.md 180).

Each item is transcribed by hand in `P3Bus/`, one definition per Rust item.
-/
module

public import P3Bus.Builder
public import P3Bus.Ram
public import P3Bus.Product
public import P3Bus.Plan
public import P3Bus.Evaluation
public import P3Bus.Timestamped
public import P3Bus.Security

@[expose] public section
