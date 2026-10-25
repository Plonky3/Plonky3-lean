/-
The Lean model of p3-multi-stark.

`P3MultiStark/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the boundary selectors, the successor row and the zerocheck's free coordinates.

`P3MultiStark/Mirror/` transcribes the rest of the verifier by hand, one definition per Rust item.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3MultiStark.Extraction
public import P3MultiStark.Mirror.Selectors
public import P3MultiStark.Mirror.Opening
public import P3MultiStark.Mirror.Zerocheck
public import P3MultiStark.Mirror.Transcript
public import P3MultiStark.Mirror.Security
public import P3MultiStark.Mirror.FractionalGkr
public import P3MultiStark.Mirror.Lookup
public import P3MultiStark.Mirror.LogupStar
public import P3MultiStark.Mirror.Bus
public import P3MultiStark.Mirror.Indexed

@[expose] public section
