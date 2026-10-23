module

public import TinyKeccak
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Proofs.Hash.Keccak.Lanes

@[expose] public section

/-!
# tiny-keccak: the permutation is Keccak-f[1600]

The tables of the code are derived from FIPS 202 and compared entry by entry.

* The order of pi is the walk `(x, y) <- (y, 2 x + 3 y)` of Algorithm 2, from `(1, 0)`.
* The rotations of rho are the triangular numbers `(t + 1) (t + 2) / 2 mod 64`.
* The round constants are the bits of the LFSR of Algorithm 5, placed at `2^j - 1`.

One round of the transcription, run on 25 symbolic words, is the round on lanes.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Keccak Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Keccak

/-! ## The tables -/

/-- The table of pi is the walk of Algorithm 2: entry `t` is lane `t + 1` of the walk. -/
theorem PI_eq_walk : tiny_keccak.PI.val.map (·.val) = (List.range 24).map fun t => walk (t + 1) := by
  unfold tiny_keccak.PI
  decide +kernel

/-- The table of rho is the triangular numbers of Algorithm 2. -/
theorem RHO_eq_triangular :
    tiny_keccak.RHO.val.map (·.val) = (List.range 24).map fun t => (t + 1) * (t + 2) / 2 % 64 := by
  unfold tiny_keccak.RHO
  decide +kernel

/-- The round constants are those of Algorithm 6, computed with the LFSR of Algorithm 5. -/
theorem RC_eq_lfsr : tiny_keccak.keccakf.RC.val.map UScalar.bv = (List.range 24).map rcWord := by
  unfold tiny_keccak.keccakf.RC
  decide +kernel

theorem ROUNDS_val : tiny_keccak.keccakf.ROUNDS.val = 24 := by
  unfold tiny_keccak.keccakf.ROUNDS
  rfl

theorem rhoOffsets_eq :
    rhoOffsets = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14] := by
  decide

theorem getElem!_val {ty} (l : List (UScalar ty)) (x : ℕ) : (l[x]!).val = (l.map (·.val))[x]! := by
  rcases lt_or_ge x l.length with h | h
  · simp [getElem!_pos, h]
  · simp [getElem!_neg, h]

theorem PI_get (x : ℕ) : (tiny_keccak.PI.val[x]!).val =
    [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1][x]! := by
  rw [getElem!_val, PI_eq_walk]
  rfl

theorem RHO_get (x : ℕ) : (tiny_keccak.RHO.val[x]!).val =
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44][x]! := by
  rw [getElem!_val, RHO_eq_triangular]
  rfl

/-! ## One round -/

theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

theorem u64_bv_mk (x : BitVec 64) : (⟨x⟩ : Std.U64).bv = x := rfl

theorem u64_not_bv (x : Std.U64) : (~~~x).bv = ~~~x.bv := rfl

theorem u64_zero_xor (x : BitVec UScalarTy.U64.numBits) : (0#u64 : Std.U64).bv ^^^ x = x := BitVec.zero_xor

theorem u32_lit_val (n : ℕ) (h) : (UScalar.ofNatCore (ty := .U32) n h).val = n := rfl

theorem rotateLeft_zero {w : ℕ} (x : BitVec w) : x.rotateLeft 0 = x := by
  ext i
  simp [BitVec.getElem_rotateLeft]

theorem u64_rotate_left (x : Std.U64) (n : Std.U32) :
    Aeneas.Std.core.num.U64.rotate_left x n = ⟨x.bv.rotateLeft n.val⟩ := rfl

/-- One round on 25 named words: the loops unroll, and each word is the round on lanes. -/
theorem round_words (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    rc : Std.U64) :
    (tiny_keccak.keccakf.round [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
      a18, a19, a20, a21, a22, a23, a24] rc).map UScalar.bv =
    iotaL (stepsL ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, a22, a23, a24].map UScalar.bv)) rc.bv := by
  simp only [tiny_keccak.keccakf.round, List.range, List.range.loop, List.forIn_cons, List.forIn_nil, Id.run,
    u64_rotate_left, PI_get, RHO_get, pure_bind, bind_pure_comp, map_pure, List.getElem!_cons_zero,
    List.getElem!_cons_succ, List.set_cons_zero, List.set_cons_succ, List.replicate_succ, List.replicate_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod]
  simp only [iotaL, stepsL, chiL, piL, rhoL, thetaL, parity, rhoOffsets_eq, List.ofFn_succ, List.ofFn_zero,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, lane,
    List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, List.set_cons_zero]
  simp only [id_pure, List.map_cons, List.map_nil, xor_bv, and_bv, u64_bv_mk, u64_not_bv, u64_zero_xor,
    u32_lit_val, rotateLeft_zero]

theorem eq_ofFn25 {α : Type} (a : List α) (ha : a.length = 25) :
    a = List.ofFn fun i : Fin 25 => a[i.val]'(by omega) := by
  apply List.ext_getElem (by simp [ha])
  intro n h1 h2
  simp only [List.getElem_ofFn]

/-- One round of the transcription is the round on lanes, with round constant `rc`. -/
theorem round_eq (a : List Std.U64) (ha : a.length = 25) (rc : Std.U64) :
    (tiny_keccak.keccakf.round a rc).map UScalar.bv = iotaL (stepsL (a.map UScalar.bv)) rc.bv := by
  rw [eq_ofFn25 a ha]
  simp only [List.ofFn_succ, List.ofFn_zero]
  exact round_words ..

theorem length_round (a : List Std.U64) (ha : a.length = 25) (rc : Std.U64) :
    (tiny_keccak.keccakf.round a rc).length = 25 := by
  have := congrArg List.length (round_eq a ha rc)
  simpa [iotaL, length_stepsL] using this

/-! ## The 24 rounds -/

theorem forIn_id_yield {α β : Type} (l : List α) (f : α → β → β) (init : β) :
    (forIn l init (fun a b => (ForInStep.yield (f a b) : Id (ForInStep β))) : Id β) =
      l.foldl (fun b a => f a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih => rw [List.forIn_cons]; exact ih (f x init)

theorem rounds_eq_foldl (a : List Std.U64) :
    tiny_keccak.keccakf.rounds a =
      (List.range 24).foldl (fun a i => tiny_keccak.keccakf.round a tiny_keccak.keccakf.RC.val[i]!) a := by
  simp only [tiny_keccak.keccakf.rounds, ROUNDS_val, Id.run]
  exact forIn_id_yield _ _ _

theorem RC_get (i : ℕ) (hi : i < 24) : (tiny_keccak.keccakf.RC.val[i]!).bv = rcWord i := by
  have h : (tiny_keccak.keccakf.RC.val.map UScalar.bv)[i]? = some (rcWord i) := by
    rw [RC_eq_lfsr]; simp [hi]
  have hl : i < tiny_keccak.keccakf.RC.val.length := by simpa using hi
  rw [List.getElem?_map, List.getElem?_eq_getElem hl] at h
  rw [getElem!_pos tiny_keccak.keccakf.RC.val i hl]
  simpa using h

/-- The 24 rounds of the transcription are the 24 rounds on lanes. -/
theorem rounds_eq (a : List Std.U64) (ha : a.length = 25) :
    (tiny_keccak.keccakf.rounds a).map UScalar.bv = keccakFL (a.map UScalar.bv) ∧
      (tiny_keccak.keccakf.rounds a).length = 25 := by
  rw [rounds_eq_foldl, keccakFL]
  have : ∀ ts : List ℕ, (∀ t ∈ ts, t < 24) → ∀ a : List Std.U64, a.length = 25 →
      (ts.foldl (fun a i => tiny_keccak.keccakf.round a tiny_keccak.keccakf.RC.val[i]!) a).map UScalar.bv =
        ts.foldl roundL (a.map UScalar.bv) ∧
      (ts.foldl (fun a i => tiny_keccak.keccakf.round a tiny_keccak.keccakf.RC.val[i]!) a).length = 25 := by
    intro ts
    induction ts with
    | nil => intro _ a ha; exact ⟨rfl, ha⟩
    | cons t ts ih =>
      intro hts a ha
      have ht := hts t (by simp)
      simp only [List.foldl_cons]
      rw [show roundL (a.map UScalar.bv) t = (tiny_keccak.keccakf.round a tiny_keccak.keccakf.RC.val[t]!).map
          UScalar.bv by rw [round_eq a ha, RC_get t ht]; rfl]
      exact ih (fun t' h => hts t' (by simp [h])) _ (length_round a ha _)
  exact this _ (fun t h => by simpa using h) a ha

/-- tiny-keccak's `keccakf` returns, for every state, the state after Keccak-f[1600], and never panics.

Word `x + 5 y` of the array is lane `(x, y)`, and bit `z` of the word is `A[x, y, z]`. -/
theorem keccakf_spec (a : Std.Array Std.U64 25#usize) :
    ∃ b, tiny_keccak.keccakf.keccakf a = .ok b ∧
      ofLanes (b.val.map UScalar.bv) = keccakP 24 (ofLanes (a.val.map UScalar.bv)) := by
  obtain ⟨h1, h2⟩ := rounds_eq a.val (by simp)
  refine ⟨Std.Array.from _ (by simpa using h2), ?_, ?_⟩
  · simp [tiny_keccak.keccakf.keccakf, h2]
  · rw [Std.Array.from_val, h1, keccakFL_eq]

end Plonky3Lean.Proofs.Keccak
