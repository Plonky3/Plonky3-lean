module

public import Plonky3Lean.Proofs.Hash.Blake2s

@[expose] public section

/-!
# p3-blake2s: claims

What this repository asserts about the scalar `hash_many`, at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/blake2s`, which takes pre-patch `blake2s/010`'s body; a differential test equates it with the shipped one.

`Blake2s256::hash` is an opaque constant: its body is `blake2`'s incremental `Digest`, which aeneas does not extract (docs/extractor-issues.md 16).

So these claims say how `hash_many` splits its input and places the digests, for whatever `Blake2s256::hash` returns.

`m ⦃ v => P v ⦄` states that `m` returns a value `v`, so it does not panic, and that `P v` holds.
-/

open Aeneas Aeneas.Std

namespace Plonky3Lean.Claims.P3Blake2s

/-- With no digests requested, `hash_many` returns `out` unchanged, whatever the input. -/
theorem batch.hash_many.empty (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (h : out.val = []) : p3_blake2s.batch.hash_many input out = .ok out :=
  Proofs.Blake2s.hash_many_empty input out h

/-- With `n > 0` digests requested and an input length that `n` does not divide, `hash_many` panics. -/
theorem batch.hash_many.ragged (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (hn : 0 < out.val.length) (h : input.val.length % out.val.length ≠ 0) :
    p3_blake2s.batch.hash_many input out = .fail .panic :=
  Proofs.Blake2s.hash_many_ragged input out hn h

/-- With `n > 0` digests requested and `n · L` input bytes, digest `i` is `Blake2s256::hash` of bytes `[i L, (i + 1) L)`, and nothing else panics. -/
theorem batch.hash_many.eq_hash (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (L : Std.Usize) (d : ℕ → Std.Array Std.U8 32#usize) (hn : 0 < out.val.length)
    (hlen : input.val.length = out.val.length * L.val)
    (hd : ∀ i < out.val.length, ∀ s : Slice Std.U8,
      s.val = (input.val.drop (i * L.val)).take L.val → p3_blake2s.Blake2s256.hash s = .ok (d i)) :
    p3_blake2s.batch.hash_many input out ⦃ r => r.val = (List.range out.val.length).map d ⦄ := by
  obtain ⟨r, e, hr⟩ := Proofs.Blake2s.hash_many_eq input out L d hn hlen hd
  rw [e, WP.spec_ok]
  exact hr

end Plonky3Lean.Claims.P3Blake2s
