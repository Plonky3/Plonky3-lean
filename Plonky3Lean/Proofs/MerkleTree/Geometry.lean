module

public import Plonky3Lean.Proofs.MerkleTree.Invert

@[expose] public section

/-!
# The schedule and the matrix order, read backwards

Every arity in a schedule the verifier computes is 2 or the full arity `N`.

Every entry of the matrix order names a matrix.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

theorem select_arity_ok {N curr lnpt from' v : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {order : Slice Std.Usize}
    (h : mmcs.hax_reshaped.select_arity_step N curr lnpt dims order from' = RustM.ok v) :
    v.val = 2 ∨ v = N := by
  unfold mmcs.hax_reshaped.select_arity_step at h
  split at h
  · exact Or.inl (by rw [← ok_inj h]; rfl)
  · obtain ⟨q, _hq, h⟩ := bind_tc_eq_ok h
    obtain ⟨tgt, _htgt, h⟩ := bind_tc_eq_ok h
    unfold mmcs.hax_reshaped.select_arity_step_loop at h
    refine loop_inv _ (fun _ => True) (fun v : Std.Usize => v.val = 2 ∨ v = N) ?_ _ _ h trivial
    intro k _ r hr
    unfold mmcs.hax_reshaped.select_arity_step_loop.body at hr
    obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
    split at hr
    · obtain ⟨i1, _hi1, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨d, _hd, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨npt', _hnpt, hr⟩ := bind_tc_eq_ok hr
      split at hr
      · split at hr
        · cases ok_inj hr; exact Or.inl rfl
        · obtain ⟨k1, _hk1, hr⟩ := bind_tc_eq_ok hr
          cases ok_inj hr; trivial
      · obtain ⟨k1, _hk1, hr⟩ := bind_tc_eq_ok hr
        cases ok_inj hr; trivial
    · cases ok_inj hr; exact Or.inr rfl

/-- Every arity the schedule loop pushes is 2 or `N`. -/
theorem sched_loop_ok {N curr lnpt pos : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {order sched sched' : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1 N dims order curr lnpt pos sched =
      RustM.ok sched')
    (hs : ∀ s ∈ sched.val, s.val = 2 ∨ s = N) : ∀ s ∈ sched'.val, s.val = 2 ∨ s = N := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1 at h
  refine loop_inv _ (fun x => ∀ s ∈ x.2.2.val, s.val = 2 ∨ s = N)
    (fun v : alloc.vec.Vec Std.Usize => ∀ s ∈ v.val, s.val = 2 ∨ s = N) ?_ _ _ h hs
  rintro ⟨c, p, sc⟩ hinv r hr
  dsimp only at hr hinv
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1.body at hr
  split at hr
  · obtain ⟨sl, _hsl, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨step, hstep, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨sc1, hsc1, hr⟩ := bind_tc_eq_ok hr
    have hnew : ∀ s ∈ sc1.val, s.val = 2 ∨ s = N := by
      rw [vec_push_ok hsc1]
      intro s hs'
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact hinv s hs'
      · rw [List.mem_singleton.mp hs']; exact select_arity_ok hstep
    obtain ⟨_x1, _hx1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨_x2, _hx2, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨_x3, _hx3, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨_x4, _hx4, hr⟩ := bind_tc_eq_ok hr
    split at hr
    · obtain ⟨_x5, _hx5, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨_x6, _hx6, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨_x7, _hx7, hr⟩ := bind_tc_eq_ok hr
      split at hr
      · obtain ⟨_x8, _hx8, hr⟩ := bind_tc_eq_ok hr
        cases ok_inj hr; exact hnew
      · cases ok_inj hr; exact hnew
    · cases ok_inj hr; exact hnew
  · cases ok_inj hr; exact hinv

/-- A schedule the verifier computes has only arities 2 and `N`, and its proof levels are at most its length. -/
theorem arity_schedule_ok {N cap pl : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl))) :
    (∀ s ∈ sched.val, s.val = 2 ∨ s = N) ∧ pl.val ≤ sched.val.length := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels at h
  obtain ⟨r, _hr, h⟩ := bind_tc_eq_ok h
  obtain ⟨cf, _hcf, h⟩ := bind_tc_eq_ok h
  split at h
  · obtain ⟨order, _hord, h⟩ := bind_tc_eq_ok h
    obtain ⟨_y9, _hy9, h⟩ := bind_tc_eq_ok h
    obtain ⟨_y10, _hy10, h⟩ := bind_tc_eq_ok h
    obtain ⟨_y11, _hy11, h⟩ := bind_tc_eq_ok h
    obtain ⟨s0, hs0, h⟩ := bind_tc_eq_ok h
    obtain ⟨s1, hs1, h⟩ := bind_tc_eq_ok h
    obtain ⟨tl, htl, h⟩ := bind_tc_eq_ok h
    simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at htl
    cases ok_inj htl
    obtain ⟨ech, hech, h⟩ := bind_tc_eq_ok h
    obtain ⟨i, hi, h⟩ := bind_tc_eq_ok h
    cases ok_inj h
    have hs0' : s0.val = [] := vec_new_val hs0
    refine ⟨sched_loop_ok hs1 (by simp [hs0']), ?_⟩
    rw [(usize_sub_ok hi).1]
    have : (Slice.len sched).val = sched.val.length := by simp
    omega
  · exact (from_residual_ne_ok _ _ h).elim

/-- Every entry of the matrix order names a matrix. -/
theorem tallest_first_ok {dims : Slice p3_matrix.Dimensions} {order : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.tallest_first dims = RustM.ok order) :
    ∀ x ∈ order.val, x.val < dims.val.length := by
  unfold mmcs.hax_reshaped.tallest_first at h
  obtain ⟨o0, ho0, h⟩ := bind_tc_eq_ok h
  have ho0' : o0.val = [] := vec_new_val ho0
  unfold mmcs.hax_reshaped.tallest_first_loop0 at h
  refine loop_inv _ (fun x => ∀ y ∈ x.1.val, y.val < dims.val.length)
    (fun v : alloc.vec.Vec Std.Usize => ∀ y ∈ v.val, y.val < dims.val.length) ?_ _ _ h
    (by simp [ho0'])
  rintro ⟨o, i⟩ hinv r hr
  dsimp only at hr hinv
  unfold mmcs.hax_reshaped.tallest_first_loop0.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [core.slice.Slice.len] at hl
  cases ok_inj hl
  split at hr
  · rename_i hlt
    have hlt' : i.val < dims.val.length := by simpa using hlt
    obtain ⟨d, _hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨j, _hj, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨o1, ho1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨i2, _hi2, hr⟩ := bind_tc_eq_ok hr
    cases ok_inj hr
    show ∀ y ∈ o1.val, y.val < dims.val.length
    rw [vec_insert_ok ho1]
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hinv y (List.mem_of_mem_take hy)
    · exact hlt'
    · exact hinv y (List.mem_of_mem_drop hy)
  · cases ok_inj hr
    exact hinv

end Plonky3Lean.Proofs.MerkleTree
