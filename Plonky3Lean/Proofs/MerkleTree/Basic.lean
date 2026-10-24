module

public import Plonky3Lean.Lib
public import P3MerkleTree
import all Init.Internal.Order.Basic

@[expose] public section

/-!
# Running a computation backwards

A computation that returns a value ran each of its steps to a value.

The binding proof compares two runs that both returned, so it only ever reads them backwards.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Proofs.MerkleTree

unseal RustM in
theorem ok_ne_fail {α : Type _} (a : α) (e : Error) : (RustM.ok a : RustM α) ≠ RustM.fail e := by
  intro h
  simp only [RustM.ok, RustM.fail, RustM.vis] at h
  exact Aeneas.Data.Coinductive.not_vis_ret h

unseal RustM in
theorem ok_ne_vis {α : Type _} (a : α) (i k) : (RustM.ok a : RustM α) ≠ RustM.vis i k := by
  intro h
  simp only [RustM.ok, RustM.vis] at h
  exact Aeneas.Data.Coinductive.not_vis_ret h

unseal RustM in
theorem ok_ne_div {α : Type _} (a : α) : (RustM.ok a : RustM α) ≠ RustM.div := by
  intro h
  simp only [RustM.ok, RustM.div] at h
  exact Aeneas.Data.Coinductive.not_ret_div h

unseal RustM in
theorem ok_inj {α : Type _} {a b : α} (h : (RustM.ok a : RustM α) = RustM.ok b) : a = b := by
  simp only [RustM.ok] at h
  exact Aeneas.Data.Coinductive.ret_inj.mp h

/-- A bind that returns ran its first step to a value. -/
theorem bind_eq_ok {α β : Type _} {x : RustM α} {f : α → RustM β} {v : β}
    (h : Std.bind x f = RustM.ok v) : ∃ a, x = RustM.ok a ∧ f a = RustM.ok v := by
  cases x with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k =>
    rw [bind_vis] at h
    exact (ok_ne_vis _ _ _ h.symm).elim
  | div =>
    rw [bind_div] at h
    exact (ok_ne_div _ h.symm).elim

theorem bind_tc_eq_ok {α β : Type _} {x : RustM α} {f : α → RustM β} {v : β}
    (h : (do let a ← x; f a) = RustM.ok v) : ∃ a, x = RustM.ok a ∧ f a = RustM.ok v :=
  bind_eq_ok h

/-- A loop that returned ran its body to a value, then either stopped there or looped again. -/
theorem loop_ok {α β : Type _} {body : α → RustM (ControlFlow α β)} {x : α} {v : β}
    (h : loop body x = RustM.ok v) :
    ∃ r, body x = RustM.ok r ∧
      match r with
      | ControlFlow.cont x' => loop body x' = RustM.ok v
      | ControlFlow.done y => y = v := by
  rw [loop] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok h
  refine ⟨r, hr, ?_⟩
  cases r with
  | cont x' => exact h
  | done y => exact ok_inj h

/-! ## Loop invariants without a termination measure

A loop that returned ran its body finitely often, so an invariant of the body holds at the end.

This needs no measure: a loop that diverges returns nothing to reason about.
-/

unseal RustM in
theorem admissible_ok {β : Type _} (Q : β → Prop) :
    Lean.Order.admissible (fun t : RustM β => ∀ v, t = RustM.ok v → Q v) := by
  unfold Lean.Order.admissible
  intro c hc hall v hv
  exact hall _ (Aeneas.Data.Coinductive.ITree.csup_ret_mem hc hv) v rfl

/-- Take an invariant that the body keeps, and that implies the postcondition when the body stops.

Then the postcondition holds of any value the loop returns. -/
theorem loop_inv {α β : Type _} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (post : β → Prop)
    (hb : ∀ x, inv x → ∀ r, body x = RustM.ok r →
      match r with
      | ControlFlow.cont x' => inv x'
      | ControlFlow.done y => post y) :
    ∀ x v, loop body x = RustM.ok v → inv x → post v := by
  have key := loop.fixpoint_induct body (fun f => ∀ x, ∀ v, f x = RustM.ok v → inv x → post v)
    (Lean.Order.admissible_pi_apply (fun x t => ∀ v, t = RustM.ok v → inv x → post v)
      (fun x => admissible_ok (fun v => inv x → post v)))
    (by
      intro f hf x v hrun hx
      obtain ⟨r, hr, hrun⟩ := bind_eq_ok hrun
      have := hb x hx r hr
      cases r with
      | cont x' => exact hf x' v hrun this
      | done y =>
        have := ok_inj hrun
        subst this
        exact this)
  exact key

/-! ## Word arithmetic that returned -/

theorem usize_add_ok {x y z : Std.Usize} (h : x + y = RustM.ok z) : z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  simp only [RustM.match.ok] at this
  exact this.2.1

theorem usize_succ_ok {x z : Std.Usize} (h : x + 1#usize = RustM.ok z) : z.val = x.val + 1 := by
  simpa using usize_add_ok h

theorem usize_sub_ok {x y z : Std.Usize} (h : x - y = RustM.ok z) :
    z.val = x.val - y.val ∧ y.val ≤ x.val := by
  have := UScalar.sub_equiv x y
  rw [h] at this
  simp only [RustM.match.ok] at this
  omega

theorem usize_mul_ok {x y z : Std.Usize} (h : x * y = RustM.ok z) : z.val = x.val * y.val := by
  have := UScalar.mul_equiv x y
  change UScalar.mul x y = _ at h
  rw [h] at this
  simp only [RustM.match.ok] at this
  exact this.2.1

theorem usize_div_ok {x y z : Std.Usize} (h : x / y = RustM.ok z) :
    z.val = x.val / y.val ∧ y.val ≠ 0 := by
  change UScalar.div x y = _ at h
  unfold UScalar.div at h
  split at h
  · have := ok_inj h
    subst this
    rename_i hne
    refine ⟨BitVec.toNat_udiv, ?_⟩
    intro h0
    apply absurd hne
    have : y.bv = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [UScalar.bv_toNat] using h0
    simp [this]
  · exact (ok_ne_fail _ _ h.symm).elim

theorem usize_rem_ok {x y z : Std.Usize} (h : x % y = RustM.ok z) :
    z.val = x.val % y.val ∧ y.val ≠ 0 := by
  change UScalar.rem x y = _ at h
  unfold UScalar.rem at h
  split at h
  · have := ok_inj h
    subst this
    rename_i hne
    refine ⟨BitVec.toNat_umod, ?_⟩
    simpa using hne
  · exact (ok_ne_fail _ _ h.symm).elim

end Plonky3Lean.Proofs.MerkleTree
