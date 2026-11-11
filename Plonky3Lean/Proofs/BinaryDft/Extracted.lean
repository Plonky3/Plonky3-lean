module

public import P3BinaryDft
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.UsizeAdd
public import Plonky3Lean.Lib.Scalar.Bits

@[expose] public section

/-!
# The extracted domain

hax extracts the domain point and the subspace polynomial, generic over the tower-level trait.

Their theorems assume one thing of the instance: each member they call computes the operation it names.

The Cantor basis member must return the level's basis vector below the bit width, and panic at or past it.

Under that assumption each returns what its transcription computes.

It panics exactly when the transcription does.

So every theorem about the transcriptions holds for the shipped code.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib p3_binary_dft.mirror

namespace Plonky3Lean.Proofs.BinaryDft

variable {F R : Type} [Field F]

/-- A transcription's result in the monad: none is a panic. -/
def ofOption {α : Type} : Option α → RustM α
  | some a => .ok a
  | none => .fail .panic

/-- The members of a tower-level instance that the domain calls compute:

- zero
- the sum, and the sum in place
- the square
- the Cantor basis vector of the level, which panics at or past the bit width. -/
structure TowerComputes (inst : p3_binary_field.tower.TowerLevel F R) (L : Level F) : Prop where
  zero : inst.p3_fieldfieldFieldInst.AlgebraInst.PrimeCharacteristicRingInst.ZERO = .ok 0
  add : ∀ a b : F, inst.p3_fieldfieldFieldInst.AlgebraInst.coreopsarithAddInst.add a b = .ok (a + b)
  add_assign : ∀ a b : F,
    inst.p3_fieldfieldFieldInst.AlgebraInst.coreopsarithAddAssignInst.add_assign a b = .ok (a + b)
  square : ∀ a : F,
    inst.p3_fieldfieldFieldInst.AlgebraInst.PrimeCharacteristicRingInst.square a = .ok (a ^ 2)
  cantor : ∀ i : Std.Usize, inst.cantor_basis i = ofOption (L.cantorBasis i.val)

variable {inst : p3_binary_field.tower.TowerLevel F R} {L : Level F}

theorem usize_lt_two_pow_64 (x : Std.Usize) : x.val < 2 ^ 64 := by
  have := x.hBounds
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalarTy.Usize_numBits_eq, h] at this <;> omega

omit [Field F] in
/-- One turn of the domain point's loop, then the rest of it. -/
theorem domain_point_loop_unfold (point : F) (remaining r : Std.Usize) :
    p3_binary_dft.domain.domain_point_loop inst point remaining r =
      (do
        let x ← p3_binary_dft.domain.domain_point_loop.body inst point remaining r
        match x with
        | .cont (p, m, r') => p3_binary_dft.domain.domain_point_loop inst p m r'
        | .done y => .ok y) := by
  rw [p3_binary_dft.domain.domain_point_loop, loop]
  congr 1; funext x; rcases x with ⟨p, m, r'⟩ | y <;> rfl

/-- The loop of the domain point returns what its transcription computes.

The invariant says the index still fits in the bits above r. -/
theorem domain_point_loop_eq (h : TowerComputes inst L) :
    ∀ (n : ℕ) (point : F) (remaining r : Std.Usize), remaining.val = n →
      remaining.val < 2 ^ (64 - r.val) → r.val ≤ 64 →
      p3_binary_dft.domain.domain_point_loop inst point remaining r =
        ofOption (p3_binary_dft.domain.mirror.domain_point.loop L point remaining.val r.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro point remaining r hn hrem hr
  rw [domain_point_loop_unfold, p3_binary_dft.domain.mirror.domain_point.loop]
  unfold p3_binary_dft.domain.domain_point_loop.body
  by_cases h0 : remaining.val = 0
  · have : remaining = 0#usize := UScalar.eq_of_val_eq (by simp [h0])
    subst this
    simp [ofOption]
  · have hne : (remaining != 0#usize) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact fun e => h0 (by simp [e])
    have hr64 : r.val < 64 := by
      by_contra hc
      have : 64 - r.val = 0 := by omega
      rw [this] at hrem
      omega
    have hand : (remaining &&& 1#usize = 1#usize) ↔ remaining.val % 2 = 1 := by
      rw [UScalar.eq_equiv]; simp [UScalar.val_and, Nat.and_one_is_mod]
    obtain ⟨r1, hr1, hr1v⟩ := usize_add_ok r 1#usize (by
      have := usize_max_ge (n := 65) (by norm_num)
      have e : Usize.numBits = UScalarTy.Usize.numBits := Usize.numBits_def
      simp only [Usize.max, UScalar.max, e] at *
      simp at *; omega)
    simp only [show (1#usize : Std.Usize).val = 1 from rfl] at hr1v
    have hsh := shiftRight_i32_eq remaining 1#i32 (by decide) (by
      simp [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> simp [e])
    set m : Std.Usize := ⟨remaining.bv >>> I32.toNat 1#i32⟩ with hm
    have hmv : m.val = remaining.val / 2 := by
      simp only [m, UScalar.val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
    have hfit : remaining.val / 2 < 2 ^ (64 - r1.val) := by
      rw [hr1v]
      have : 2 ^ (64 - r.val) = 2 * 2 ^ (64 - (r.val + 1)) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have hrec := fun p => ih (remaining.val / 2) (by omega) p m r1 hmv (hmv ▸ hfit) (by omega)
    simp only [hne, ↓reduceIte, h0, lift, bind_ok, hsh, hr1, hand]
    rw [← hmv, ← hr1v]
    split_ifs
    · rw [h.cantor]
      cases L.cantorBasis r.val <;> simp [ofOption, h.add_assign, hrec]
    · simp [hrec]

/-- The extracted domain point returns what its transcription computes. -/
theorem domain_point_eq_mirror (h : TowerComputes inst L) (index : Std.Usize) :
    p3_binary_dft.domain.domain_point inst index =
      ofOption (p3_binary_dft.domain.mirror.domain_point L index.val) := by
  rw [p3_binary_dft.domain.domain_point, h.zero, bind_ok,
    domain_point_loop_eq h _ _ index 0#usize rfl (by simpa using usize_lt_two_pow_64 index)
      (by simp)]
  rfl

/-- The loop of the subspace polynomial, from round k of j. -/
theorem subspace_polynomial_loop_eq (h : TowerComputes inst L) (j : Std.Usize) (x : F) :
    p3_binary_dft.domain.subspace_polynomial_loop inst { start := 0#usize, «end» := j } x =
      .ok (p3_binary_dft.domain.mirror.subspace_polynomial j.val x) := by
  unfold p3_binary_dft.domain.subspace_polynomial_loop
  refine loop_of_steps (fun st => p3_binary_dft.domain.subspace_polynomial_loop.body inst st.1 st.2)
    (fun k => ({ start := usz k, «end» := j }, p3_binary_dft.domain.mirror.subspace_polynomial k x))
    j.val _ (fun k hk => ?_) ?_
  · simp only [p3_binary_dft.domain.subspace_polynomial_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := usz k, «end» := j } = _ from range_step k j hk]
    simp [h.square, h.add, p3_binary_dft.domain.mirror.subspace_polynomial, List.range_succ]
  · simp only [p3_binary_dft.domain.subspace_polynomial_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := usz j.val, «end» := j } = _ from
      range_next_none _ _ (by rw [usz_val_le j le_rfl])]
    simp

/-- The extracted subspace polynomial returns what its transcription computes, and never panics. -/
theorem subspace_polynomial_eq_mirror (h : TowerComputes inst L) (j : Std.Usize) (x : F) :
    p3_binary_dft.domain.subspace_polynomial inst j x =
      .ok (p3_binary_dft.domain.mirror.subspace_polynomial j.val x) :=
  subspace_polynomial_loop_eq h j x

end Plonky3Lean.Proofs.BinaryDft
