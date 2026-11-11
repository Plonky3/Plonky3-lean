module

public import Plonky3Lean.Proofs.Fri.Merkle
public import Plonky3Lean.Proofs.MerkleTree.BinaryAccept

@[expose] public section

/-!
# The scheme's query check is the extracted verifier

The FRI PCS model checks each query with a walk of the binary plan.

The extracted single-index verifier, at arity 2, accepts exactly the same queries.

It also checks the cap size, which the model leaves to the scheme's commitment.
-/

namespace Plonky3Lean.Proofs.Fri

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree
open Plonky3Lean.Proofs.MerkleTree

/-- The widths and heights of the dimensions, as natural numbers. -/
def dimsN (dims : Slice p3_matrix.Dimensions) : List (ℕ × ℕ) :=
  dims.val.map fun d => (d.width.val, d.height.val)

theorem dimLogs_dimsN (dims : Slice p3_matrix.Dimensions) : dimLogs (dimsN dims) = logsOf dims := by
  simp [dimLogs, dimsN, logsOf]

/-- On power-of-two heights, the tallest log height is the log of the tallest height. -/
theorem topLog_logsOf {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims)
    (hne : dims.val ≠ []) : topLog (logsOf dims) = Nat.log 2 (maxHeight dims) := by
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil _ hne
  have hpos : 0 < maxHeight dims := by
    have h1 := le_foldl_max_of (dims.val.map fun d => d.height.val) 0 d0.height.val
      (Or.inl (List.mem_map_of_mem hd0))
    have h2 : 1 ≤ d0.height.val := by rw [← hpow d0 hd0]; exact Nat.one_le_two_pow
    unfold maxHeight; omega
  refine le_antisymm (foldl_max_le _ 0 _ (fun x hx => ?_) (Nat.zero_le _)) ?_
  · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    have := (maxHeight_pow hpow hpos).2 m hm
    rwa [List.getD_eq_getElem _ _ hm] at this
  · rcases foldl_max_mem (dims.val.map fun d => d.height.val) 0 with h | h
    · exact absurd h (by unfold maxHeight at hpos; omega)
    · obtain ⟨d, hd, hd'⟩ := List.mem_map.1 h
      unfold maxHeight
      rw [← hd']
      exact le_topLog (List.mem_map_of_mem (f := fun d => Nat.log 2 d.height.val) hd)

variable {P PW F W H C : Type} {DIGEST_ELEMS : Std.Usize}

/-- The extracted verifier at arity 2 accepts exactly the queries the scheme accepts.

The batch is not empty and its heights are powers of two.

The tallest height is 2^n, and the scheme's cap height is min(c, n) for the verifier's cap height c.

The verifier also requires a cap of 2^min(c, n) digests. -/
theorem verify_iff_queryAccepts (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true ↔ x = y)
    (t : W) (z : Std.Array W DIGEST_ELEMS) (ht : dfInst.default = RustM.ok t)
    (hz : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok z)
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (hne : dims.val ≠ [])
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    let capH := min mt.cap_height.val (topLog (dimLogs (dimsN dims)))
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened proof =
        RustM.ok (core.result.Result.Ok ()) ↔
      QueryAccepts h c z capH commit.cap.val (dimsN dims) index.val (openedL opened) proof.val ∧
        commit.cap.val.length = 2 ^ capH := by
  intro capH
  have htop : topLog (dimLogs (dimsN dims)) = Nat.log 2 (maxHeight dims) := by
    rw [dimLogs_dimsN, topLog_logsOf hpow hne]
  simp only [capH, htop]
  have key := verify_iff_binary cl cp dfInst eqInst hInst cInst mt h c hH hC hcl heq t z ht hz dims
    hpow hne commit index opened proof
  dsimp only at key
  rw [key]
  have hlen : (dimsN dims).length = dims.val.length := by simp [dimsN]
  have hol : (openedL opened).length = opened.val.length := by simp [openedL]
  unfold QueryAccepts queryWalk
  rw [hlen, hol, dimLogs_dimsN, topLog_logsOf hpow hne]
  constructor
  · rintro ⟨hl, hw, hidx, hpl, hcl, hcap⟩
    refine ⟨⟨hidx, hl, fun m hm => ?_, by rw [hpl], hcap⟩, hcl⟩
    have hm' : m < opened.val.length := hl ▸ hm
    simp [openedL, dimsN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm,
      List.getElem?_eq_getElem hm', hw m hm hm']
  · rintro ⟨⟨hidx, hl, hw, hpl, hcap⟩, hcl⟩
    refine ⟨hl, fun m hm hm' => ?_, hidx, by rw [hpl], hcl, hcap⟩
    have := hw m hm
    simpa [openedL, dimsN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm,
      List.getElem?_eq_getElem hm'] using this

end Plonky3Lean.Proofs.Fri
