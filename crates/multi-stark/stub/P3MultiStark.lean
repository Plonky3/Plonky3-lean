/-
The Lean model of p3-multi-stark.

Nothing is extracted: its items are generic over the field traits and the AIR (docs/extractor-issues.md 9), and code over `ExtensionField` does not extract (docs/extractor-issues.md 180).

Each item is transcribed by hand in `P3MultiStark/`, one definition per Rust item.
-/
module

public import P3MultiStark.Selectors
public import P3MultiStark.Opening
public import P3MultiStark.Zerocheck
public import P3MultiStark.Transcript
public import P3MultiStark.Security
public import P3MultiStark.FractionalGkr
public import P3MultiStark.Lookup

@[expose] public section
