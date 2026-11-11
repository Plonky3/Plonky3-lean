module

public import Plonky3Lean.Proofs.MerkleTree.Basic

@[expose] public section

/-!
# Reading lengths, indices and arrays backwards
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Proofs.MerkleTree

theorem slice_index_ok {α : Type _} {s : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize s i = RustM.ok x) : i.val < s.val.length ∧ s.val[i.val]? = some x := by
  unfold Slice.index_usize at h
  split at h
  · exact (ok_ne_fail _ _ h.symm).elim
  · rename_i y hy
    have := ok_inj h
    subst this
    simp only [Slice.getElem?_Usize_eq] at hy
    refine ⟨?_, hy⟩
    rw [List.getElem?_eq_some_iff] at hy
    exact hy.1

theorem vec_index_ok {α : Type _} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT α) v i = RustM.ok x) :
    i.val < v.val.length ∧ v.val[i.val]? = some x := by
  simp only [alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get, rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index] at h
  obtain ⟨s, hs, h⟩ := bind_tc_eq_ok h
  cases ok_inj hs
  obtain ⟨o, ho, h⟩ := bind_tc_eq_ok h
  obtain ⟨l, hl, ho⟩ := bind_tc_eq_ok ho
  cases ok_inj hl
  split at ho
  · obtain ⟨t, ht, ho⟩ := bind_tc_eq_ok ho
    cases ok_inj ho
    cases ok_inj h
    exact slice_index_ok ht
  · cases ok_inj ho
    simp only [core.panicking.internal.panic] at h
    exact (ok_ne_fail _ _ h.symm).elim


theorem array_update_ok {α : Type _} {n : Std.Usize} {a b : Std.Array α n} {i : Std.Usize} {x : α}
    (h : Std.Array.update a i x = RustM.ok b) : b.val = a.val.set i.val x ∧ i.val < a.val.length := by
  unfold Std.Array.update at h
  split at h
  · exact (ok_ne_fail _ _ h.symm).elim
  · rename_i y hy
    cases ok_inj h
    refine ⟨by simp, ?_⟩
    simp only [Std.Array.getElem?_Usize_eq] at hy
    rw [List.getElem?_eq_some_iff] at hy
    exact hy.1

theorem getD_set_of_ne {α : Type _} (l : List α) (i j : ℕ) (v d : α) (h : j ≠ i) :
    (l.set i v).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem getD_set_self' {α : Type _} (l : List α) (i : ℕ) (v d : α) (hi : i < l.length) :
    (l.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]

theorem vec_push_ok {α : Type _} {v w : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = RustM.ok w) : w.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push rust_primitives.sequence.seq_push at h
  obtain ⟨s, hs, h⟩ := bind_tc_eq_ok h
  cases ok_inj h
  dsimp only at hs
  split at hs
  · cases ok_inj hs
    simp
  · exact (ok_ne_fail _ _ hs.symm).elim

theorem vec_truncate_ok {α : Type _} {v w : alloc.vec.Vec α} {n : Std.Usize}
    (h : alloc.vec.Vec.truncate v n = RustM.ok w) : w.val = v.val.take n.val := by
  unfold alloc.vec.Vec.truncate at h
  obtain ⟨l, hl, h⟩ := bind_tc_eq_ok h
  simp only [rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  split at h
  · rename_i hlt
    obtain ⟨p, hp, h⟩ := bind_tc_eq_ok h
    unfold rust_primitives.sequence.seq_drain at hp
    split at hp
    · cases ok_inj hp
      cases ok_inj h
      simp
    · exact (ok_ne_fail _ _ hp.symm).elim
  · rename_i hlt
    cases ok_inj h
    have : v.val.length ≤ n.val := by
      have : ¬ n.val < v.val.length := by simpa using hlt
      omega
    rw [List.take_of_length_le this]

theorem vec_insert_ok {α : Type _} {v w : alloc.vec.Vec α} {j : Std.Usize} {x : α}
    (h : alloc.vec.Vec.insert v j x = RustM.ok w) :
    w.val = v.val.take j.val ++ x :: v.val.drop j.val := by
  unfold alloc.vec.Vec.insert at h
  obtain ⟨l, hl, h⟩ := bind_tc_eq_ok h
  simp only [rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  obtain ⟨p, hp, h⟩ := bind_tc_eq_ok h
  unfold rust_primitives.sequence.seq_drain at hp
  split at hp
  · cases ok_inj hp
    obtain ⟨s1, hs1, h⟩ := bind_tc_eq_ok h
    simp only [rust_primitives.sequence.seq_push] at hs1
    split at hs1
    · cases ok_inj hs1
      obtain ⟨q, hq, h⟩ := bind_tc_eq_ok h
      simp only [rust_primitives.sequence.seq_concat] at hq
      split at hq
      · cases ok_inj hq
        cases ok_inj h
        simp
      · exact (ok_ne_fail _ _ hq.symm).elim
    · exact (ok_ne_fail _ _ hs1.symm).elim
  · exact (ok_ne_fail _ _ hp.symm).elim

/-! ## The `?` operator -/

theorem branch_continue {T E : Type _} {r : core.result.Result T E} {v : T}
    (h : core.result.Result.Insts.CoreOpsTry_traitTry.branch r =
      RustM.ok (core.ops.control_flow.ControlFlow.Continue v)) : r = core.result.Result.Ok v := by
  cases r with
  | Ok w =>
    have := ok_inj h
    cases this
    rfl
  | Err e =>
    have := ok_inj h
    cases this

theorem branch_break {T E : Type _} {r : core.result.Result T E} {res}
    (h : core.result.Result.Insts.CoreOpsTry_traitTry.branch r =
      RustM.ok (core.ops.control_flow.ControlFlow.Break res)) :
    ∃ e, r = core.result.Result.Err e ∧ res = core.result.Result.Err e := by
  cases r with
  | Ok w =>
    have := ok_inj h
    cases this
  | Err e =>
    have := ok_inj h
    cases this
    exact ⟨e, rfl, rfl⟩

/-- Propagating an error never returns success. -/
theorem from_residual_ne_ok {T E : Type _} (res : core.result.Result core.convert.Infallible E)
    (v : T) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual T
      (core.convert.From.Blanket E) res ≠ RustM.ok (core.result.Result.Ok v) := by
  intro h
  cases res with
  | Ok x =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      core.panicking.internal.panic] at h
    exact ok_ne_fail _ _ h.symm
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      core.convert.From.Blanket.from] at h
    obtain ⟨t, ht, h⟩ := bind_tc_eq_ok h
    have := ok_inj h
    cases this

theorem vec_new_eq {α : Type _} {v : alloc.vec.Vec α} (h : alloc.vec.Vec.new α = RustM.ok v) :
    v = Slice.new α := by
  simp only [alloc.vec.Vec.new, rust_primitives.sequence.seq_empty] at h
  obtain ⟨e, he, h⟩ := bind_tc_eq_ok h
  cases ok_inj he
  exact (ok_inj h).symm

theorem vec_new_val {α : Type _} {v : alloc.vec.Vec α} (h : alloc.vec.Vec.new α = RustM.ok v) :
    v.val = [] := by
  rw [vec_new_eq h]; rfl

/-- The smallest power of two at least `n`, as Rust's `next_power_of_two` computes it. -/
def npt (n : ℕ) : ℕ := n.nextPowerOfTwo

theorem npt_ok {x r : Std.Usize} (h : core.num.Usize.next_power_of_two x = RustM.ok r) :
    r.val = npt x.val ∧ npt x.val < 2 ^ UScalarTy.Usize.numBits := by
  unfold core.num.Usize.next_power_of_two at h
  split at h
  · rename_i hlt
    have := ok_inj h
    subst this
    refine ⟨?_, hlt⟩
    show (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  · exact (ok_ne_fail _ _ h.symm).elim

/-- The padded width of a layer, as the tree's padding rule computes it. -/
def padded (raw n : ℕ) : ℕ :=
  if raw ≤ 1 then raw else if n ≤ raw then (raw / n + if raw % n = 0 then 0 else 1) * n else n

theorem div_ceil_ok {x y r : Std.Usize} (h : core.num.Usize.div_ceil x y = RustM.ok r) :
    r.val = x.val / y.val + (if x.val % y.val = 0 then 0 else 1) ∧ y.val ≠ 0 := by
  unfold core.num.Usize.div_ceil at h
  obtain ⟨d, hd, h⟩ := bind_tc_eq_ok h
  obtain ⟨m, hm, h⟩ := bind_tc_eq_ok h
  obtain ⟨hd, hy⟩ := usize_div_ok hd
  obtain ⟨hm, -⟩ := usize_rem_ok hm
  split at h
  · rename_i hpos
    have hpos' : 0 < m.val := hpos
    rw [usize_add_ok h, hd]
    refine ⟨?_, hy⟩
    rw [ite_eq_right (by omega)]
    rfl
  · rename_i hpos
    have hpos' : ¬ 0 < m.val := hpos
    cases ok_inj h
    refine ⟨?_, hy⟩
    rw [hd, ite_eq_left (by omega)]
    simp

theorem padded_len_ok {raw n r : Std.Usize}
    (h : p3_merkle_tree.merkle_tree.padded_len raw n = RustM.ok r) : r.val = padded raw.val n.val := by
  unfold p3_merkle_tree.merkle_tree.padded_len at h
  unfold padded
  split at h
  · rename_i hle
    have hle' : raw.val ≤ 1 := hle
    cases ok_inj h
    rw [ite_eq_left hle']
  · rename_i hle
    have hle' : ¬ raw.val ≤ 1 := hle
    rw [ite_eq_right hle']
    split at h
    · rename_i hge
      have hge' : n.val ≤ raw.val := hge
      rw [ite_eq_left hge']
      obtain ⟨d, hd, h⟩ := bind_tc_eq_ok h
      rw [usize_mul_ok h, (div_ceil_ok hd).1]
    · rename_i hge
      have hge' : ¬ n.val ≤ raw.val := hge
      rw [ite_eq_right hge']
      cases ok_inj h
      rfl

end Plonky3Lean.Proofs.MerkleTree
