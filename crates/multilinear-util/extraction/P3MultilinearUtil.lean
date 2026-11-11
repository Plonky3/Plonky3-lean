/-
The Lean model of p3-multilinear-util.

`P3MultilinearUtil/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the equality polynomial of two points.

`P3MultilinearUtil/Mirror/` transcribes the rest over a field.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3MultilinearUtil.Extraction
public import P3MultilinearUtil.Mirror.Model
public import P3MultilinearUtil.Mirror.Point
public import P3MultilinearUtil.Mirror.EqBatch
public import P3MultilinearUtil.Mirror.Poly
public import P3MultilinearUtil.Mirror.SplitEq

@[expose] public section
