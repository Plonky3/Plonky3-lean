module

public import Plonky3Lean.Proofs.Symmetric.Compression

@[expose] public section

/-!
# Constructors, digests and Merkle caps

The constructors check their shape parameters with `const` assertions.

In Rust a failed one is a compile error; the model runs it as a panic.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Sponge

namespace Plonky3Lean.Proofs.Symmetric

theorem padding_free_new_eq {P : Type} (W RATE OUT : Std.Usize) (p : P) :
    p3_symmetric.sponge.PaddingFreeSponge.new W RATE OUT p =
      if 0 < RATE.val ∧ RATE.val < W.val ∧ 0 < OUT.val ∧ OUT.val ≤ RATE.val then
        .ok { permutation := p }
      else .fail .panic := by
  unfold p3_symmetric.sponge.PaddingFreeSponge.new
  by_cases h1 : 0 < RATE.val <;> by_cases h2 : RATE.val < W.val <;>
    by_cases h3 : 0 < OUT.val <;> by_cases h4 : OUT.val ≤ RATE.val <;>
    simp [massert, h1, h2, h3, h4, UScalar.lt_equiv, UScalar.le_equiv]

theorem pad10_new_eq (T : Type) {P D : Type} (W RATE OUT : Std.Usize) (p : P) (d : D) :
    p3_symmetric.sponge.Pad10Sponge.new T W RATE OUT p d =
      if 0 < RATE.val ∧ RATE.val < W.val ∧ 0 < OUT.val ∧ OUT.val ≤ RATE.val then
        .ok { permutation := p, padding_derangement := d, _phantom := () }
      else .fail .panic := by
  unfold p3_symmetric.sponge.Pad10Sponge.new
  by_cases h1 : 0 < RATE.val <;> by_cases h2 : RATE.val < W.val <;>
    by_cases h3 : 0 < OUT.val <;> by_cases h4 : OUT.val ≤ RATE.val <;>
    simp [massert, h1, h2, h3, h4, UScalar.lt_equiv, UScalar.le_equiv]

/-- `TruncatedPermutation::new` succeeds exactly when `n > 0`, `chunk > 0` and `chunk * n <= width`.

The product is assumed to fit a `usize`: Rust evaluates it in a `const` block, where an overflow is a compile error.
-/
theorem truncated_new_eq {P : Type} (N CHUNK W : Std.Usize) (p : P)
    (hm : CHUNK.val * N.val ≤ Usize.max) :
    p3_symmetric.compression.TruncatedPermutation.new N CHUNK W p =
      if 0 < N.val ∧ 0 < CHUNK.val ∧ CHUNK.val * N.val ≤ W.val then .ok { inner_permutation := p }
      else .fail .panic := by
  unfold p3_symmetric.compression.TruncatedPermutation.new
  obtain ⟨z, ez, hz⟩ := usize_mul_ok CHUNK N hm
  by_cases h1 : 0 < N.val <;> by_cases h2 : 0 < CHUNK.val <;>
    by_cases h3 : CHUNK.val * N.val ≤ W.val <;>
    simp [massert, h1, h2, h3, ez, hz, UScalar.lt_equiv, UScalar.le_equiv]

/-! ## The increment padding -/

/-- `Increment::new` rejects exactly the zero increment, for a lawful equality. -/
theorem increment_new_eq {T : Type} [DecidableEq T] (defInst : core.default.Default T)
    (eqInst : core.cmp.PartialEq T T) (z inc : T) (hz : defInst.default = .ok z)
    (hne : ∀ a b, eqInst.ne a b = .ok (decide (a ≠ b))) :
    p3_symmetric.sponge.Increment.new defInst eqInst inc =
      if inc ≠ z then .ok inc else .fail .panic := by
  unfold p3_symmetric.sponge.Increment.new
  by_cases h : inc = z <;> simp [hz, hne, massert, h]

/-- The increment adds its value. -/
theorem increment_permute_eq {T : Type} (cloneInst : core.clone.Clone T)
    (addInst : core.ops.arith.Add T T T) (inc x : T) (hcl : cloneInst.clone inc = .ok inc) :
    p3_symmetric.sponge.Increment.Insts.P3_symmetricPermutationPermutation.permute cloneInst addInst
      inc x = addInst.add x inc := by
  unfold p3_symmetric.sponge.Increment.Insts.P3_symmetricPermutationPermutation.permute
  simp [hcl]

/-! ## Digests and Merkle caps -/

theorem hash_from_into {F W : Type} {N : Std.Usize} (v : Std.Array W N) :
    (do
      let h ← p3_symmetric.hash.Hash.Insts.CoreConvertFromArray.from F v
      p3_symmetric.Array.Insts.CoreConvertFromHash.from h) = .ok v := by
  simp [p3_symmetric.hash.Hash.Insts.CoreConvertFromArray.from,
    p3_symmetric.Array.Insts.CoreConvertFromHash.from]

/-- `usize::is_power_of_two`, as CoreModels runs it, decides whether the value is a power of two. -/
theorem is_power_of_two_eq (x : Std.Usize) :
    core.num.Usize.is_power_of_two x = .ok (decide x.val.isPowerOfTwo) := by
  unfold core.num.Usize.is_power_of_two
  by_cases h0 : x = 0#usize
  · subst h0
    simp [Nat.not_isPowerOfTwo_zero]
  · have hx : x.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    obtain ⟨y, ey, hy⟩ : ∃ y, x - 1#usize = RustM.ok y ∧ y.val = x.val - 1 := by
      have : x - 1#usize ⦃ z => z.val = x.val - (1#usize : Std.Usize).val ⦄ := by step*
      obtain ⟨y, e1, h1⟩ := Lib.spec_imp_exists this
      exact ⟨y, e1, by simpa using h1⟩
    have hne : (x != 0#usize) = true := by simpa using h0
    simp only [hne, ite_true, ey, bind_ok, lift]
    congr 1
    apply decide_eq_decide.mpr
    rw [← Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hx, ← hy, ← UScalar.val_and]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq (by rw [h]; rfl)

theorem merkle_cap_new_eq (F : Type) {D : Type} (cap : alloc.vec.Vec D) :
    p3_symmetric.hash.MerkleCap.new F cap =
      if cap.val.length.isPowerOfTwo then .ok { cap, _marker := () } else .fail .panic := by
  unfold p3_symmetric.hash.MerkleCap.new
  by_cases h : cap.val.length.isPowerOfTwo <;>
    simp [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, is_power_of_two_eq, h,
      core.fmt.rt.Argument.new_display, core.fmt.Arguments.new]

end Plonky3Lean.Proofs.Symmetric
