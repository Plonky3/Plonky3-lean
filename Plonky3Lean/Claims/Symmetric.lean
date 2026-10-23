module

public import Plonky3Lean.Proofs.Symmetric.Roots

@[expose] public section

/-!
# p3-symmetric: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/symmetric`.

The permutation, the padding function, the inner hasher and the input iterator stay abstract.

So each claim holds for every permutation and every input length.

The two sponges and the compression built from a hasher take the bodies of pre-patches `symmetric/020`, `030` and `040`.

A differential test equates each body with the shipped one.

The specification is the sponge of Bertoni, Daemen, Peeters and Van Assche, "Cryptographic sponge functions" (2011), in overwrite mode.

Each claim says the code returns a value, so it does not panic, and says what that value is.

# What the claims find

- Without padding, the empty input hashes to the zero state: the permutation never runs.
- Without padding, a message that ends inside a block collides with its extension by the values the rate already holds.
  In the first block those values are zeros, so `m` and `m ++ [0]` collide.
- With 10-padding, the padded blocks and the separator flag determine the message, as long as `d(0) != 0`.
- With `width = n * chunk`, the truncated permutation has collisions that anyone who can invert the permutation finds.
  The trait documents this: it promises collision resistance only in a hash tree.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Sponge
open Plonky3Lean.Proofs.Symmetric

namespace Plonky3Lean.Claims.P3Symmetric

/-! ## The padding-free sponge -/

/-- The padding-free sponge returns the block-wise sponge of whatever its iterator yields, and never panics.

The hypotheses are the shape checks of the constructor, a permutation that computes `f`, and plain-data `T`.
-/
theorem sponge.PaddingFreeSponge.hash_iter.eq_spec {T P I J : Type} {W RATE OUT : Std.Usize}
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J)
    (sp : p3_symmetric.sponge.PaddingFreeSponge P W RATE OUT) (input : I)
    (f : List T → List T) (z : T) (xs : List T)
    (hf : PermComputes permInst sp.permutation f) (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hit : ∃ it, iterInst.into_iter input = .ok it ∧ Yields iterInst.iteratorIteratorInst it xs)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ RATE.val) :
    ∃ out, p3_symmetric.sponge.PaddingFreeSponge.Insts.P3_symmetricHasherCryptographicHasherTArray.hash_iter
        defInst copyInst permInst iterInst sp input = .ok out ∧
      out.val = paddingFree f z W.val RATE.val OUT.val xs :=
  padding_free_hash_eq RATE OUT defInst copyInst permInst iterInst sp.permutation input f z xs hf hz
    hcl hit hr hrw (by omega)

/-- The constructor of the padding-free sponge accepts exactly `0 < rate < width` and `0 < out <= rate`. -/
theorem sponge.PaddingFreeSponge.new.eq {P : Type} (W RATE OUT : Std.Usize) (p : P) :
    p3_symmetric.sponge.PaddingFreeSponge.new W RATE OUT p =
      if 0 < RATE.val ∧ RATE.val < W.val ∧ 0 < OUT.val ∧ OUT.val ≤ RATE.val then
        .ok { permutation := p }
      else .fail .panic :=
  padding_free_new_eq W RATE OUT p

/-- The empty message hashes to the first `out` cells of the zero state. -/
theorem paddingFree.nil {T : Type} (f : List T → List T) (zero : T) (w r out : ℕ) :
    paddingFree f zero w r out [] = (List.replicate w zero).take out :=
  paddingFree_nil f zero w r out

/-- A message that ends with a short block `b` collides with its extension by the values the rate holds after `b`.

Here the message is `pre ++ b` with `pre` a whole number of blocks, and `s` the state after `pre`.
-/
theorem paddingFree.extend {T : Type} (f : List T → List T) (zero : T) (w r out : ℕ) (hr : 0 < r)
    (pre b x : List T) (q : ℕ) (hpre : pre.length = r * q) (hb : b ≠ [])
    (hbx : b.length + x.length ≤ r)
    (hx : x = ((((blocks r pre).foldl (absorb f) (List.replicate w zero)).drop b.length).take
      x.length)) :
    paddingFree f zero w r out (pre ++ b ++ x) = paddingFree f zero w r out (pre ++ b) :=
  paddingFree_extend f zero w r out hr pre b x q hpre hb hbx hx

/-- In the first block, a nonempty message collides with itself followed by zeros up to the rate. -/
theorem paddingFree.trailing_zeros {T : Type} (f : List T → List T) (zero : T) (w r out : ℕ)
    (hr : 0 < r) (m : List T) (k : ℕ) (hm : m ≠ []) (hk : m.length + k ≤ r) (hw : r ≤ w) :
    paddingFree f zero w r out (m ++ List.replicate k zero) = paddingFree f zero w r out m :=
  paddingFree_trailing_zeros f zero w r out hr m k hm hk hw

/-! ## The 10-padded sponge -/

/-- The 10-padded sponge returns the padded block-wise sponge of whatever its iterator yields, and never panics. -/
theorem sponge.Pad10Sponge.hash_iter.eq_spec {T P D I J : Type} {W RATE OUT : Std.Usize}
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (derInst : p3_symmetric.permutation.Derangement D T)
    (iterInst : core.iter.traits.collect.IntoIterator I T J)
    (sp : p3_symmetric.sponge.Pad10Sponge T P D W RATE OUT) (input : I)
    (f : List T → List T) (d : T → T) (z : T) (xs : List T)
    (hf : PermComputes permInst sp.permutation f)
    (hd : ∀ x, derInst.PermutationInst.permute sp.padding_derangement x = .ok (d x))
    (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hit : ∃ it, iterInst.into_iter input = .ok it ∧ Yields iterInst.iteratorIteratorInst it xs)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ RATE.val) :
    ∃ out, p3_symmetric.sponge.Pad10Sponge.Insts.P3_symmetricHasherCryptographicHasherTArray.hash_iter
        defInst copyInst permInst derInst iterInst sp input = .ok out ∧
      out.val = pad10 f d z W.val RATE.val OUT.val xs :=
  pad10_hash_eq RATE OUT defInst copyInst permInst derInst iterInst sp.permutation
    sp.padding_derangement input f d z xs hf hd hz hcl hit hr hrw (by omega)

/-- The constructor of the 10-padded sponge accepts exactly `0 < rate < width` and `0 < out <= rate`. -/
theorem sponge.Pad10Sponge.new.eq (T : Type) {P D : Type} (W RATE OUT : Std.Usize) (p : P)
    (d : D) :
    p3_symmetric.sponge.Pad10Sponge.new T W RATE OUT p d =
      if 0 < RATE.val ∧ RATE.val < W.val ∧ 0 < OUT.val ∧ OUT.val ≤ RATE.val then
        .ok { permutation := p, padding_derangement := d, _phantom := () }
      else .fail .panic :=
  pad10_new_eq T W RATE OUT p d

/-- The 10-padding is injective when the sentinel `d(0)` is not zero. -/
theorem pad10Blocks.injective {T : Type} (zero d0 : T) (r : ℕ) (hr : 0 < r) (hd : d0 ≠ zero) :
    Function.Injective (pad10Blocks zero d0 r) :=
  pad10Blocks_injective zero d0 r hr hd

/-- The increment rejects exactly the zero increment, for a lawful equality. -/
theorem sponge.Increment.new.eq {T : Type} [DecidableEq T] (defInst : core.default.Default T)
    (eqInst : core.cmp.PartialEq T T) (z inc : T) (hz : defInst.default = .ok z)
    (hne : ∀ a b, eqInst.ne a b = .ok (decide (a ≠ b))) :
    p3_symmetric.sponge.Increment.new defInst eqInst inc =
      if inc ≠ z then .ok inc else .fail .panic :=
  increment_new_eq defInst eqInst z inc hz hne

/-- The increment maps `x` to `x + inc`. -/
theorem sponge.Increment.permute.eq {T : Type} (cloneInst : core.clone.Clone T)
    (addInst : core.ops.arith.Add T T T) (inc x : T) (hcl : cloneInst.clone inc = .ok inc) :
    p3_symmetric.sponge.Increment.Insts.P3_symmetricPermutationPermutation.permute cloneInst addInst
      inc x = addInst.add x inc :=
  increment_permute_eq cloneInst addInst inc x hcl

/-! ## The compression functions -/

/-- The truncated permutation writes the chunks side by side into the zero state, permutes, and keeps the first chunk; it never panics. -/
theorem compression.TruncatedPermutation.compress.eq_spec {T P : Type} {N CHUNK W : Std.Usize}
    (copyInst : core.marker.Copy T) (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (c : p3_symmetric.compression.TruncatedPermutation P N CHUNK W)
    (input : Std.Array (Std.Array T CHUNK) N) (f : List T → List T) (z : T)
    (hf : PermComputes permInst c.inner_permutation f) (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hn : 0 < N.val) (hc : 0 < CHUNK.val) (hw : CHUNK.val * N.val ≤ W.val) :
    ∃ out, p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress
        copyInst defInst permInst c input = .ok out ∧
      out.val = truncated f z W.val CHUNK.val (input.val.map fun a => a.val) :=
  truncated_compress_eq copyInst defInst permInst c input f z hf hz hcl hn hc hw

/-- The constructor of the truncated permutation accepts exactly `n > 0`, `chunk > 0` and `chunk * n <= width`. -/
theorem compression.TruncatedPermutation.new.eq {P : Type} (N CHUNK W : Std.Usize) (p : P)
    (hm : CHUNK.val * N.val ≤ Usize.max) :
    p3_symmetric.compression.TruncatedPermutation.new N CHUNK W p =
      if 0 < N.val ∧ 0 < CHUNK.val ∧ CHUNK.val * N.val ≤ W.val then .ok { inner_permutation := p }
      else .fail .panic :=
  truncated_new_eq N CHUNK W p hm

/-- With `width = n * chunk`, two different tails after any output `y` give two different inputs that compress to `y`. -/
theorem truncated.collision_of_inverse {T : Type} (f g : List T → List T) (zero : T) (w chunk : ℕ)
    (hfg : ∀ y, y.length = w → f (g y) = y) (hg : ∀ y, y.length = w → (g y).length = w)
    (y t t' : List T) (hy : y.length = chunk) (ht : t.length = w - chunk)
    (ht' : t'.length = w - chunk) (hne : t ≠ t') (hcw : chunk ≤ w)
    (ins ins' : List (List T)) (hins : ins.flatten = g (y ++ t))
    (hins' : ins'.flatten = g (y ++ t')) :
    truncated f zero w chunk ins = y ∧ truncated f zero w chunk ins' = y ∧ ins ≠ ins' :=
  truncated_collision_of_inverse f g zero w chunk hfg hg y t t' hy ht ht' hne hcw ins ins' hins hins'

/-- The compression built from a hasher hands the hasher the chunks' items in order and returns its digest. -/
theorem compression.CompressionFunctionFromHasher.compress.eq {T H : Type} {N CHUNK : Std.Usize}
    (cloneInst : core.clone.Clone T)
    (hInst : p3_symmetric.hasher.CryptographicHasher H T (Std.Array T CHUNK))
    (c : p3_symmetric.compression.CompressionFunctionFromHasher H N CHUNK)
    (input : Std.Array (Std.Array T CHUNK) N) (hlen : N.val * CHUNK.val ≤ Usize.max) :
    ∃ items : alloc.vec.Vec T, items.val = (input.val.map fun a => a.val).flatten ∧
      p3_symmetric.compression.CompressionFunctionFromHasher.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress
        cloneInst hInst c input =
      hInst.hash_iter (alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter T) c.hasher
        items :=
  compress_from_hasher_eq cloneInst hInst c input hlen

/-! ## Digests and Merkle caps -/

/-- Wrapping an array as a digest and unwrapping it gives the array back. -/
theorem hash.Hash.from_into {F W : Type} {N : Std.Usize} (v : Std.Array W N) :
    (do
      let h ← p3_symmetric.hash.Hash.Insts.CoreConvertFromArray.from F v
      p3_symmetric.Array.Insts.CoreConvertFromHash.from h) = .ok v :=
  hash_from_into v

/-- A Merkle cap accepts exactly a power-of-two number of roots. -/
theorem hash.MerkleCap.new.eq (F : Type) {D : Type} (cap : alloc.vec.Vec D) :
    p3_symmetric.hash.MerkleCap.new F cap =
      if cap.val.length.isPowerOfTwo then .ok { cap, _marker := () } else .fail .panic :=
  merkle_cap_new_eq F cap

end Plonky3Lean.Claims.P3Symmetric
