module

public import Plonky3Lean.Proofs.MerkleTree.Access

@[expose] public section

/-!
# Word arithmetic that cannot fail

Each operation returns a value when its operands are in range.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Proofs.MerkleTree

theorem usize_add_eq {x y : Std.Usize} (h : x.val + y.val ≤ Usize.max) :
    ∃ z, x + y = RustM.ok z ∧ z.val = x.val + y.val := by
  have : x + y ⦃ z => z.val = x.val + y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem usize_sub_eq {x y : Std.Usize} (h : y.val ≤ x.val) :
    ∃ z, x - y = RustM.ok z ∧ z.val = x.val - y.val := by
  have : x - y ⦃ z => z.val = x.val - y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem usize_mul_eq {x y : Std.Usize} (h : x.val * y.val ≤ Usize.max) :
    ∃ z, x * y = RustM.ok z ∧ z.val = x.val * y.val := by
  have : x * y ⦃ z => z.val = x.val * y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem usize_div_eq {x y : Std.Usize} (h : y.val ≠ 0) :
    ∃ z, x / y = RustM.ok z ∧ z.val = x.val / y.val := by
  have : x / y ⦃ z => z.val = x.val / y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem usize_rem_eq {x y : Std.Usize} (h : y.val ≠ 0) :
    ∃ z, x % y = RustM.ok z ∧ z.val = x.val % y.val := by
  have : x % y ⦃ z => z.val = x.val % y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem usize_max_half {x : Std.Usize} : x.val / 2 < 2 ^ (UScalarTy.Usize.numBits - 1) := by
  have h1 : x.val < 2 ^ UScalarTy.Usize.numBits := x.hBounds
  have h2 : 0 < UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have : 2 ^ UScalarTy.Usize.numBits = 2 * 2 ^ (UScalarTy.Usize.numBits - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem isPowerOfTwo_two_pow : ∀ k, Nat.isPowerOfTwo (2 ^ k)
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by rw [pow_succ]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

/-- The next power of two of a word at most half the word range fits. -/
theorem npt_eq {x : Std.Usize} (h : x.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)) :
    ∃ r, core.num.Usize.next_power_of_two x = RustM.ok r ∧ r.val = npt x.val := by
  have hb : x.val.nextPowerOfTwo < 2 ^ UScalarTy.Usize.numBits := by
    have h2 : 0 < UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
    have hle : x.val.nextPowerOfTwo ≤ 2 ^ (UScalarTy.Usize.numBits - 1) :=
      Nat.nextPowerOfTwo_le h (isPowerOfTwo_two_pow _)
    have : 2 ^ (UScalarTy.Usize.numBits - 1) < 2 ^ UScalarTy.Usize.numBits :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨⟨BitVec.ofNat _ x.val.nextPowerOfTwo⟩, ?_, ?_⟩
  · unfold core.num.Usize.next_power_of_two
    rw [ite_eq_left hb]
  · show (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    rfl

/-- A loop whose body always returns, keeps an invariant and decreases a measure, returns. -/
theorem loop_total {α β : Type _} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (μ : α → ℕ)
    (hb : ∀ x, inv x → ∃ r, body x = RustM.ok r ∧
      match r with
      | ControlFlow.cont x' => inv x' ∧ μ x' < μ x
      | ControlFlow.done _ => True) :
    ∀ x, inv x → ∃ v, loop body x = RustM.ok v := by
  intro x
  induction hm : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  intro hx
  obtain ⟨r, hr, hnext⟩ := hb x hx
  rw [loop, hr, bind_ok]
  cases r with
  | cont x' =>
    obtain ⟨hx', hlt⟩ := hnext
    exact ih (μ x') (hm ▸ hlt) x' rfl hx'
  | done y => exact ⟨y, rfl⟩

/-- The padded width of a layer at most half the word range fits. -/
theorem padded_total {x N : Std.Usize} (hx : x.val ≤ Usize.max / 2) (hN : 2 ≤ N.val) :
    ∃ r, p3_merkle_tree.merkle_tree.padded_len x N = RustM.ok r := by
  unfold p3_merkle_tree.merkle_tree.padded_len
  split
  · exact ⟨_, rfl⟩
  · split
    · rename_i hge
      have hge' : N.val ≤ x.val := hge
      unfold core.num.Usize.div_ceil
      obtain ⟨d, hd, hdv⟩ := usize_div_eq (x := x) (y := N) (by omega)
      obtain ⟨m, hm, hmv⟩ := usize_rem_eq (x := x) (y := N) (by omega)
      have hdN : d.val * N.val ≤ x.val := by rw [hdv]; exact Nat.div_mul_le_self _ _
      have hmax : x.val + N.val ≤ Usize.max := by omega
      rw [hd, bind_ok, hm, bind_ok]
      split
      · obtain ⟨d1, hd1, hd1v⟩ := usize_add_eq (x := d) (y := 1#usize) (by
          have : d.val * N.val + N.val ≤ Usize.max := by omega
          have : d.val + 1 ≤ d.val * N.val + N.val := by nlinarith
          simp; omega)
        rw [hd1, bind_ok]
        obtain ⟨p, hp, -⟩ := usize_mul_eq (x := d1) (y := N) (by
          have h1v : d1.val = d.val + 1 := by simpa using hd1v
          rw [h1v]
          have : (d.val + 1) * N.val = d.val * N.val + N.val := by ring
          omega)
        exact ⟨p, hp⟩
      · obtain ⟨p, hp, -⟩ := usize_mul_eq (x := d) (y := N) (by omega)
        exact ⟨p, by rw [bind_ok]; exact hp⟩
    · exact ⟨_, rfl⟩

/-- As above, with a postcondition on the value the loop returns. -/
theorem loop_total_post {α β : Type _} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (post : β → Prop) (μ : α → ℕ)
    (hb : ∀ x, inv x → ∃ r, body x = RustM.ok r ∧
      match r with
      | ControlFlow.cont x' => inv x' ∧ μ x' < μ x
      | ControlFlow.done y => post y) :
    ∀ x, inv x → ∃ v, loop body x = RustM.ok v ∧ post v := by
  intro x
  induction hm : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  intro hx
  obtain ⟨r, hr, hnext⟩ := hb x hx
  rw [loop, hr, bind_ok]
  cases r with
  | cont x' =>
    obtain ⟨hx', hlt⟩ := hnext
    exact ih (μ x') (hm ▸ hlt) x' rfl hx'
  | done y => exact ⟨y, rfl, hnext⟩

end Plonky3Lean.Proofs.MerkleTree
