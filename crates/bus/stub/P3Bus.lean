/-
The Lean model of p3-bus.

Nothing is extracted: the crate's dependencies p3-multilinear-util and p3-sumcheck do not compile in the extraction variant (docs/extractor-issues.md 180), and most items are generic over the field traits or the builder.

Each item is transcribed by hand in `P3Bus/`, one definition per Rust item.
-/
module

public import P3Bus.Builder
public import P3Bus.Ram
public import P3Bus.Product
public import P3Bus.Plan
public import P3Bus.Evaluation

@[expose] public section
