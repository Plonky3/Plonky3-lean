/-
# tiny-keccak: the permutation, transcribed

The rounds are written with crunchy's unroll macro, which inlines every inner loop.

aeneas runs out of memory on the result, so the function is transcribed below.

The loops are kept as loops, in the order and with the index arithmetic of the source.

The tables are the extracted ones.

A word is read with panicking indexing, which matches Rust wherever the index is below the length.

Every index has one of three forms:

* x + 5 y, with x, y < 5
* a remainder mod 5
* an entry of the table of pi.

The proofs show each table entry is below 25.
So the Rust never panics, and neither does this.
-/
module

public import TinyKeccak.Extraction

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

set_option linter.dupNamespace false

namespace tiny_keccak.keccakf

/-- One iteration of the round loop of the Keccak macro, on the 25 words, with a given round constant. -/
def round (a : List Std.U64) (rc : Std.U64) : List Std.U64 := Id.run do
  let mut a := a
  let mut array : List Std.U64 := List.replicate 5 0#u64
  -- Theta
  for x in List.range 5 do
    for y_count in List.range 5 do
      let y := y_count * 5
      array := array.set x (array[x]! ^^^ a[x + y]!)
  for x in List.range 5 do
    for y_count in List.range 5 do
      let y := y_count * 5
      let r := Aeneas.Std.core.num.U64.rotate_left array[(x + 1) % 5]! 1#u32
      a := a.set (y + x) (a[y + x]! ^^^ (array[(x + 4) % 5]! ^^^ r))
  -- Rho and pi
  let mut last := a[1]!
  for x in List.range 24 do
    let p := (tiny_keccak.PI.val[x]!).val
    array := array.set 0 a[p]!
    let r := Aeneas.Std.core.num.U64.rotate_left last tiny_keccak.RHO.val[x]!
    a := a.set p r
    last := array[0]!
  -- Chi
  for y_step in List.range 5 do
    let y := y_step * 5
    for x in List.range 5 do
      array := array.set x a[y + x]!
    for x in List.range 5 do
      a := a.set (y + x) (array[x]! ^^^ ((~~~array[(x + 1) % 5]!) &&& array[(x + 2) % 5]!))
  -- Iota
  return a.set 0 (a[0]! ^^^ rc)

/-- The round loop of the Keccak macro: round i uses the i-th round constant. -/
def rounds (a : List Std.U64) : List Std.U64 := Id.run do
  let mut a := a
  for i in List.range keccakf.ROUNDS.val do
    a := round a keccakf.RC.val[i]!
  return a

/-- The Keccak-f permutation, from the Keccak macro of src/lib.rs.

Upstream: tiny_keccak::keccakf::keccakf.

The length test always passes, since a round only overwrites words. -/
def keccakf (a : Std.Array Std.U64 25#usize) : RustM (Std.Array Std.U64 25#usize) :=
  let s := rounds a.val
  if h : s.length = 25 then ok (Std.Array.from s (by simpa using h)) else fail .panic

end tiny_keccak.keccakf
