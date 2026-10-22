module

public import Aeneas
public import CoreModels
public import Plonky3Lean.Lib.RustM
public import Plonky3Lean.Lib.Iter

@[expose] public section

/-!
# Loops over a `usize` range

A `for` loop is a `loop` whose body first asks the range for its next index.

A loop whose body steps through known states, one per index, returns what the last state says.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

/-- The next index of `i..K`, for `i < K`. -/
theorem range_next_some (i K : Std.Usize) (h : i.val < K.val) :
    ∃ i' : Std.Usize, core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := K } =
      .ok (core.option.Option.Some i, { start := i', «end» := K }) ∧ i'.val = i.val + 1 :=
  range_next_lt i K h

/-- An exhausted range, `K ≤ i`. -/
theorem range_next_none (i K : Std.Usize) (h : K.val ≤ i.val) :
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep { start := i, «end» := K } =
      .ok (core.option.Option.None, { start := i, «end» := K }) := by
  unfold core.IteratorRange.next
  rcases Nat.lt_or_ge K.val i.val with h1 | h1
  · simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, compare_gt_iff_gt.mpr h1]
  · simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
      compare_eq_iff_eq.mpr (show i.val = K.val by omega)]

/-- A loop whose body takes state `s k` to `s (k + 1)` for `k < n`, and stops at `s n` with `r`. -/
theorem loop_of_steps {α β : Type} (body : α → RustM (ControlFlow α β)) (s : ℕ → α) (n : ℕ)
    (r : β) (hstep : ∀ k < n, body (s k) = .ok (.cont (s (k + 1))))
    (hdone : body (s n) = .ok (.done r)) : loop body (s 0) = .ok r := by
  suffices h : ∀ m ≤ n, loop body (s (n - m)) = .ok r by simpa using h n le_rfl
  intro m
  induction m with
  | zero => intro _; rw [loop, Nat.sub_zero, hdone, bind_ok]
  | succ m ih =>
    intro hm
    rw [loop, hstep (n - (m + 1)) (by omega), bind_ok]
    simp only
    rw [show n - (m + 1) + 1 = n - m by omega]
    exact ih (by omega)

/-! ## Small `usize` values -/

/-- The `usize` with value `k`, for `k < 2^32`. -/
def usz (k : ℕ) : Std.Usize := ⟨BitVec.ofNat _ k⟩

theorem usz_val {k : ℕ} (h : k < 2 ^ 32) : (usz k).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with e | e <;>
    simp only [UScalarTy.Usize_numBits_eq, e] <;> omega

theorem eq_usz {x : Std.Usize} {k : ℕ} (h : k < 2 ^ 32) (hx : x.val = k) : x = usz k :=
  UScalar.eq_of_val_eq (by rw [hx, usz_val h])

/-- A literal is `usz` of its value. -/
theorem ofNatCore_eq_usz (k : ℕ) (h : k < 2 ^ UScalarTy.Usize.numBits) (hk : k < 2 ^ 32) :
    (UScalar.ofNatCore k h : Std.Usize) = usz k :=
  eq_usz hk (UScalar.ofNatCore_val_eq h)

theorem usize_max_ge {n : ℕ} (h : n < 2 ^ 32) : n ≤ UScalar.max .Usize := by
  simp only [UScalar.max]
  rcases System.Platform.numBits_eq with e | e <;>
    simp only [UScalarTy.Usize_numBits_eq, e] <;> omega

theorem usz_sub {a b : ℕ} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (usz a - usz b : RustM Std.Usize) = .ok (usz (a - b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.sub_bv_spec (x := usz a) (y := usz b) (by rw [usz_val ha, usz_val (by omega)]; omega))
  rw [hz, eq_usz (x := z) (k := a - b) (by omega) (by rw [hv.1, usz_val ha, usz_val (by omega)])]

theorem usz_add {a b : ℕ} (h : a + b < 2 ^ 32) :
    (usz a + usz b : RustM Std.Usize) = .ok (usz (a + b)) := by
  have hmax : (usz a).val + (usz b).val ≤ UScalar.max .Usize := by
    rw [usz_val (by omega), usz_val (by omega)]
    exact usize_max_ge h
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.add_bv_spec hmax)
  rw [hz, eq_usz (x := z) h (by rw [hv.1, usz_val (by omega), usz_val (by omega)])]

theorem usz_mul {a b : ℕ} (h : a * b < 2 ^ 32) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (usz a * usz b : RustM Std.Usize) = .ok (usz (a * b)) := by
  have hmax : (usz a).val * (usz b).val ≤ UScalar.max .Usize := by
    rw [usz_val ha, usz_val hb]
    exact usize_max_ge h
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz, eq_usz (x := z) h (by rw [hv, usz_val ha, usz_val hb])]

theorem usz_rem {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h0 : b ≠ 0) :
    (usz a % usz b : RustM Std.Usize) = .ok (usz (a % b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.rem_spec (usz a) (y := usz b) (by rw [usz_val hb]; exact h0))
  rw [hz, eq_usz (x := z) (k := a % b) (by have := Nat.mod_le a b; omega) (by rw [hv, usz_val ha, usz_val hb])]

theorem usz_lt_iff {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : usz a < usz b ↔ a < b := by
  rw [UScalar.lt_equiv, usz_val ha, usz_val hb]

end Plonky3Lean.Lib
