module

public import Plonky3Lean.Proofs.MerkleTree.Bind
public import Plonky3Lean.Proofs.MerkleTree.Accept
public import Plonky3Lean.Proofs.MerkleTree.Edge
public import Plonky3Lean.Proofs.MerkleTree.Hiding
public import Plonky3Lean.Proofs.MerkleTree.Bugs

@[expose] public section

/-!
# p3-merkle-tree: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/merkle-tree`: the single-index verifier, its schedule, and the hiding verifier.

Their bodies are those of pre-patch `merkle-tree/010`, which a differential test equates with the shipped ones.

The hasher and the compression stay abstract, so each claim holds for every hash.

A hasher is read as a function of the row slices it is given, and a compression as a function of its children.

The extracted model checks arithmetic, as a debug build does, so an overflow panics.

# What the claims find

- Two accepting openings at one index agree on every row the verifier reads, or the hasher or the compression collides.
- An honest opening of the tree verifies.
- No index, rows, siblings or cap make the verifier panic, once the dimensions pass its own checks.
- With arity 8, heights 4 and 2 make the pinned schedule loop forever.
- With arity 2 and a cap two layers down, the pinned verifier never reads a height-1 matrix next to a height-8 one.

Plonky3/Plonky3#2471 removes both defects, after the pinned commit.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree
open Plonky3Lean.Proofs.MerkleTree
open Plonky3Lean.Spec.MerkleTree

namespace Plonky3Lean.Claims.P3MerkleTree

variable {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize} {D : Type _}

/-- Merkle's binding argument on the extracted verifier.

Two openings at one index, under one cap and one set of dimensions, that both verify agree on every row the verifier reads.

Otherwise the hasher maps two different row lists of equal row lengths to one digest, or the compression maps two different children lists to one digest.

The hasher and the compression are any functions.

The hasher sees only the slices its iterator yields. -/
theorem mmcs.hax_reshaped.verify_batch.binding {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y) (hN : 2 ≤ N.val)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize)
    (o1 o2 : Slice (alloc.vec.Vec F)) (p1 p2 : Slice (Std.Array W DIGEST_ELEMS))
    (h1 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o1 p1 =
      RustM.ok (core.result.Result.Ok ()))
    (h2 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o2 p2 =
      RustM.ok (core.result.Result.Ok ())) :
    CCollision c ∨ HCollision h ∨
      ∀ m, Reads N mt.cap_height dims m → (openedL o1).getD m [] = (openedL o2).getD m [] :=
  Plonky3Lean.Proofs.MerkleTree.verify_binding cl cp dfInst eqInst hInst cInst mt h c hH hC hcl heq hN commit dims index o1 o2 p1 p2 h1 h2

/-- Completeness: an honest opening of the tree verifies.

The tree is the one its documentation describes, its layers follow the verifier's schedule, and its padding digest is the default digest.

The leaf is the hash of the leaf rows, the siblings are the path's, and the cap holds the top layer.

The verifier must read each injected matrix at the row the tree takes in, below the matrix's height. -/
theorem mmcs.hax_reshaped.verify_batch.complete {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize)
    (pl expected : Std.Usize) (sched1 : alloc.vec.Vec Std.Usize) (epl : Std.Usize)
    (order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hexp : mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected)
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (hepl : mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos)
    (hheights : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1))
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS))
    (hlen0 : opened.val.length = dims.val.length)
    (hw : ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val)
    (hproof : proof.val.length = sibSum sched1 0) (hidx : index.val < val.val)
    (hcapl : commit.cap.val.length = expected.val)
    (t : W) (dflt : Std.Array W DIGEST_ELEMS) (padA : Std.Array (Std.Array W DIGEST_ELEMS) N)
    (ht : dfInst.default = RustM.ok t)
    (hdflt : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt)
    (hpad : core.array.repeat N (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst) dflt =
      RustM.ok padA)
    (ls : List (LayerSpec (Std.Array W DIGEST_ELEMS))) (L0 : ℕ → Std.Array W DIGEST_ELEMS)
    (hmatch : Matches h padA.val (ordL order) (openedL opened)
      (plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val) ls index.val)
    (hleaf : L0 index.val = h (group (ordL order) (openedL opened) 0 pos.val))
    (hpath : proof.val = path c padA.val dflt L0 ls index.val)
    (hcap : commit.cap.val[capIndex (plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0)
        curr.val pos.val) index.val]? =
      some (top c padA.val dflt L0 ls (capIndex (plan N.val (heightOf dims) (ordL order)
        (schedFrom sched1 0) curr.val pos.val) index.val))) :
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ()) :=
  Plonky3Lean.Proofs.MerkleTree.verify_complete cl cp dfInst eqInst hInst cInst mt h c hH hC hcl hrefl hN dims val sched pl expected sched1 epl order curr lnpt pos hval hsched hexp hsched1 hepl horder hcurr hlnpt hpos hheights commit index opened proof hlen0 hw hproof hidx hcapl t dflt padA ht hdflt hpad ls L0 hmatch hleaf hpath hcap

/-- The verifier accepts when the rows have their widths, the siblings number as the walked levels take, the index is below the tallest height, the cap holds as many roots as the top layers produce, and the fold of the opening reaches the cap entry at its index. -/
theorem mmcs.hax_reshaped.verify_batch.accepts_of_walk {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hdf : ∃ t, dfInst.default = RustM.ok t)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize)
    (pl expected : Std.Usize) (sched1 : alloc.vec.Vec Std.Usize) (epl : Std.Usize)
    (order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hexp : mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected)
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (hepl : mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos)
    (hheights : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1))
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS))
    (hlen0 : opened.val.length = dims.val.length)
    (hw : ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val)
    (hproof : proof.val.length = sibSum sched1 0) (hidx : index.val < val.val)
    (hcapl : commit.cap.val.length = expected.val)
    (hroot : ∀ (t : W) (dflt : Std.Array W DIGEST_ELEMS) (padA : Std.Array (Std.Array W DIGEST_ELEMS) N),
      dfInst.default = RustM.ok t → core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt →
      core.array.repeat N (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst) dflt =
        RustM.ok padA →
      let pl0 := plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val
      let w := walk h c padA.val dflt (ordL order) (openedL opened) proof.val pl0 index.val 0
        (h (group (ordL order) (openedL opened) 0 pos.val))
      commit.cap.val[w.1]? = some w.2) :
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ()) :=
  Plonky3Lean.Proofs.MerkleTree.verify_ok_of cl cp dfInst eqInst hInst cInst mt h c hH hC hcl hdf hrefl hN dims val sched pl expected sched1 epl order curr lnpt pos hval hsched hexp hsched1 hepl horder hcurr hlnpt hpos hheights commit index opened proof hlen0 hw hproof hidx hcapl hroot

/-- An accepting run computed every step to a value, checked the widths and the sibling count, hashed the leaf rows, folded its plan and found the result in the cap. -/
theorem mmcs.hax_reshaped.verify_batch.accepts_inv (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    ∃ (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize) (pl : Std.Usize)
      (sched1 order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize) (t : W)
      (dflt : Std.Array W DIGEST_ELEMS) (d0 : Std.Array W DIGEST_ELEMS) (ci : Std.Usize)
      (df : Std.Array W DIGEST_ELEMS) (a : Std.Array W DIGEST_ELEMS),
      mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
      mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
        RustM.ok (core.result.Result.Ok (sched, pl)) ∧
      alloc.vec.Vec.truncate sched pl = RustM.ok sched1 ∧
      mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ()) ∧
      mmcs.hax_reshaped.tallest_first dims = RustM.ok order ∧
      p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr ∧
      index.val < val.val ∧
      core.num.Usize.next_power_of_two val = RustM.ok lnpt ∧
      mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos ∧
      hInst.hash_iter_slices
        (core.iter.traits.collect.IntoIterator.Blanket
          (mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice F))
        mt.hash { opened_values := opened, order := vs order, pos := 0#usize, «end» := pos } =
        RustM.ok d0 ∧
      dfInst.default = RustM.ok t ∧
      core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt ∧
      mmcs.hax_reshaped.verify_batch_loop2 cl cp hInst cInst mt.hash mt.compress dims index opened
        proof sched1 order curr pos d0 dflt 0#usize 0#usize = RustM.ok (ci, df) ∧
      p3_symmetric.hash.MerkleCap.Insts.CoreOpsIndexIndexUsizeDigest.index commit ci = RustM.ok a ∧
      core.Array.Insts.CoreCmpPartialEqArray.eq eqInst a df = RustM.ok true ∧
      ∃ epl : Std.Usize, mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl ∧
        proof.val.length = epl.val :=
  Plonky3Lean.Proofs.MerkleTree.verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims index opened proof h

/-- An accepting run had a positive tallest height, an index below it, one row per matrix at its width, and exactly the siblings the walked levels take.

So an empty batch, a batch of zero-height matrices, an index at or past the tallest height, a missing row, a row of the wrong width and a wrong number of siblings are all rejected. -/
theorem mmcs.hax_reshaped.verify_batch.accepts_shape {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    0 < maxHeight dims ∧ index.val < maxHeight dims ∧
    opened.val.length = dims.val.length ∧
    (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val) ∧
    ∃ (sched : alloc.vec.Vec Std.Usize) (pl : Std.Usize),
      mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
        RustM.ok (core.result.Result.Ok (sched, pl)) ∧
      proof.val.length = ((sched.val.take pl.val).map fun s => s.val - 1).sum :=
  Plonky3Lean.Proofs.MerkleTree.verify_accepts_shape cl cp dfInst eqInst hInst cInst mt commit dims index opened proof h

/-- The verifier returns on every index, opened rows, siblings and cap, once the dimensions pass its own checks.

The prover controls all four, so no proof makes the verifier panic or loop.

The checks on the dimensions are the height ladder, the schedule, the cap size, the sibling count, the matrix order and the leaf group, all computed from the dimensions alone, and every height at most half the word range. -/
theorem mmcs.hax_reshaped.verify_batch.never_panics {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hdf : ∃ t, dfInst.default = RustM.ok t)
    (heqt : ∀ x y, ∃ b, eqInst.eq x y = RustM.ok b) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (hdims : DimsPass N mt.cap_height dims)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    ∃ r, mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok r :=
  Plonky3Lean.Proofs.MerkleTree.verify_total cl cp dfInst eqInst hInst cInst mt h c hH hC hcl hdf heqt hN dims hdims commit index opened proof

/-- The hiding verifier checks the unsalted widths and the number of salts, appends each salt to its row, widens each width by the salt length, and runs the plain verifier. -/
theorem mmcs.hax_reshaped.hiding_verify_batch.salted {P PW W H C : Type} {N DIGEST_ELEMS : Std.Usize} (SALT : Std.Usize)
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (hcl : ∀ x, cl.clone x = RustM.ok x)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened salts : Slice (alloc.vec.Vec F))
    (siblings : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index opened salts siblings = RustM.ok (core.result.Result.Ok ())) :
    ∃ (so : alloc.vec.Vec (alloc.vec.Vec F)) (sd : alloc.vec.Vec p3_matrix.Dimensions),
      mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ()) ∧
      opened.val.length = salts.val.length ∧
      so.val.map (fun v => v.val) = List.zipWith (· ++ ·) (rowsL opened) (rowsL salts) ∧
      mmcs.hax_reshaped.hiding_verify_batch_loop1 SALT dims (Slice.new p3_matrix.Dimensions) 0#usize = RustM.ok sd ∧
      sd.val.map (fun d => d.height) = dims.val.map (fun d => d.height) ∧
      sd.val.map (fun d => d.width.val) = dims.val.map (fun d => d.width.val + SALT.val) ∧
      mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit (vs sd) index (vs so)
        siblings = RustM.ok (core.result.Result.Ok ()) :=
  Plonky3Lean.Proofs.MerkleTree.hiding_accepts SALT cl cp dfInst eqInst hInst cInst hcl mt commit dims index opened salts siblings h

/-- Two hiding openings at one index that both verify agree on every row and every salt the verifier reads, or the hasher or the compression has a collision. -/
theorem mmcs.hax_reshaped.hiding_verify_batch.binding {P PW W H C : Type} {N DIGEST_ELEMS : Std.Usize} (SALT : Std.Usize)
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hclF : ∀ x, cl.clone x = RustM.ok x)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y) (hN : 2 ≤ N.val)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize)
    (o1 s1 o2 s2 : Slice (alloc.vec.Vec F)) (p1 p2 : Slice (Std.Array W DIGEST_ELEMS))
    (h1 : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index o1 s1 p1 = RustM.ok (core.result.Result.Ok ()))
    (h2 : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index o2 s2 p2 = RustM.ok (core.result.Result.Ok ())) :
    CCollision c ∨ HCollision h ∨
      ∃ sd : alloc.vec.Vec p3_matrix.Dimensions,
        mmcs.hax_reshaped.hiding_verify_batch_loop1 SALT dims (Slice.new p3_matrix.Dimensions) 0#usize =
          RustM.ok sd ∧
        ∀ m, m < dims.val.length → Reads N mt.cap_height (vs sd) m →
          (rowsL o1).getD m [] = (rowsL o2).getD m [] ∧ (rowsL s1).getD m [] = (rowsL s2).getD m [] :=
  Plonky3Lean.Proofs.MerkleTree.hiding_binding SALT cl cp dfInst eqInst hInst cInst mt h c hH hC hclF hcl heq hN commit dims index o1 s1 o2 s2 p1 p2 h1 h2

/-- A uniform salt of k elements lands a salted row in a fixed set Q of hash inputs for at most |Q| of the |F|^k salts.

In the random-oracle model this bounds the advantage of a distinguisher that makes |Q| queries by |Q| / |F|^k. -/
theorem salt_hits_le [Fintype F] [DecidableEq F] (m : List F) (k : ℕ) (Q : Finset (List F)) :
    (Finset.univ.filter fun s : Fin k → F => m ++ List.ofFn s ∈ Q).card ≤ Q.card :=
  Plonky3Lean.Proofs.MerkleTree.salt_hits_le m k Q

/-- Every arity of a schedule the verifier computes is 2 or the full arity, and its proof levels are at most its length. -/
theorem mmcs.hax_reshaped.arity_schedule_and_proof_levels.arities {N cap pl : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl))) :
    (∀ s ∈ sched.val, s.val = 2 ∨ s = N) ∧ pl.val ≤ sched.val.length :=
  Plonky3Lean.Proofs.MerkleTree.arity_schedule_ok h

/-- A height check that passes returns the tallest height, which is positive. -/
theorem mmcs.hax_reshaped.validate_heights.ok_max {dims : Slice p3_matrix.Dimensions} {val : Std.Usize}
    (h : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val)) :
    val.val = maxHeight dims ∧ 0 < val.val :=
  Plonky3Lean.Proofs.MerkleTree.validate_ok_val h

/-- The matrix order is the insertion sort of the indices, tallest first, ties in input order. -/
theorem mmcs.hax_reshaped.tallest_first.eq {dims : Slice p3_matrix.Dimensions} {order : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.tallest_first dims = RustM.ok order) :
    ordL order = sortTallest (heightOf dims) dims.val.length :=
  Plonky3Lean.Proofs.MerkleTree.tallest_first_eq h

/-- With arity 8, the pinned schedule for heights 4 and 2 never returns.

A binary step at padded width 8 pads back to width 8 without taking in the height-2 matrix, and the loop repeats that state.

Plonky3/Plonky3#2471 rejects this shape, after the pinned commit. -/
theorem mmcs.hax_reshaped.arity_schedule_and_proof_levels.never_returns_8_4_2 (w0 w1 cap : Std.Usize) (x : alloc.vec.Vec Std.Usize × Std.Usize) :
    mmcs.hax_reshaped.arity_schedule_and_proof_levels 8#usize cap (dims2 w0 4#usize w1 2#usize) ≠
      RustM.ok (core.result.Result.Ok x) :=
  Plonky3Lean.Proofs.MerkleTree.schedule_never_returns w0 w1 cap x

/-- With arity 2 and the cap two layers below the root, the pinned verifier never reads a matrix of height 1 committed next to one of height 8.

The matrix enters at the root, above the cap, so its row is bound by nothing but its width.

Plonky3/Plonky3#2471 lowers the cap to the last injection, after the pinned commit. -/
theorem mmcs.hax_reshaped.verify_batch.unread_8_1_cap_2 (w0 w1 : Std.Usize) :
    ¬ Reads 2#usize 2#usize (dims2 w0 8#usize w1 1#usize) 1 :=
  Plonky3Lean.Proofs.MerkleTree.short_matrix_unread w0 w1

/-- The verifier's fold of its plan over an honest path reaches the node of the top layer above the leaf. -/
theorem walk.honest (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (opened : List (List F)) (proof : List D) :
    ∀ (pl : List Level) (ls : List (LayerSpec D)) (L0 : ℕ → D) (i pp : ℕ),
      Matches h pad order opened pl ls i →
      (∀ j < (path c pad z L0 ls i).length,
        proof.getD (pp + j) z = (path c pad z L0 ls i).getD j z) →
      walk h c pad z order opened proof pl i pp (L0 i) = (capIndex pl i, top c pad z L0 ls (capIndex pl i)) :=
  Plonky3Lean.Proofs.MerkleTree.walk_honest h c pad z order opened proof

/-- Two folds of one plan that reach one digest started from one digest and read the same injected rows, or the hasher or the compression has a collision. -/
theorem walk.binding (h : List (List F) → D) (c : List D → D) (pad : List D) (z : D)
    (order : List ℕ) (o1 o2 : List (List F)) (p1 p2 : List D)
    (hlen : ∀ m, (o1.getD m []).length = (o2.getD m []).length) (hpad : 2 ≤ pad.length) :
    ∀ (pl : List Level), (∀ l ∈ pl, 0 < l.1 ∧ l.1 ≤ pad.length) →
    ∀ i pp d d', (walk h c pad z order o1 p1 pl i pp d).2 = (walk h c pad z order o2 p2 pl i pp d').2 →
      CCollision c ∨ HCollision h ∨
        (d = d' ∧ ∀ g ∈ injected pl, group order o1 g.1 g.2 = group order o2 g.1 g.2) :=
  Plonky3Lean.Proofs.MerkleTree.walk_binding h c pad z order o1 o2 p1 p2 hlen hpad

end Plonky3Lean.Claims.P3MerkleTree
