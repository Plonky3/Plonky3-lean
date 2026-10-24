module

public import Aeneas

@[expose] public section

/-!
# Checked usize addition

A usize sum returns the sum when it fits, and panics when it does not.
-/

open Aeneas Aeneas.Std

namespace Plonky3Lean.Lib

/-- A usize sum that fits returns the sum. -/
theorem usize_add_ok (x y : Std.Usize) (h : x.val + y.val ≤ Usize.max) :
    ∃ z : Std.Usize, (x + y : RustM Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hs := @Usize.add_spec x y
  generalize (x + y : RustM Std.Usize) = m at hs ⊢
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using hs⟩
  | vis i k => cases i with | fail e => (cases e <;> simp [WP.partialSpec] at hs; omega)
  | div => simp at hs

/-- A usize sum past the largest usize panics. -/
theorem usize_add_fail (x y : Std.Usize) (h : Usize.max < x.val + y.val) :
    (x + y : RustM Std.Usize) = .fail .panic := by
  have hs := @Usize.add_spec x y
  generalize (x + y : RustM Std.Usize) = m at hs ⊢
  cases m with
  | ret r => simp at hs; scalar_tac
  | vis i k =>
    cases i with
    | fail e =>
      cases e <;> simp [WP.partialSpec] at hs
      exact congrArg _ (funext fun x => nomatch x)
  | div => simp at hs

end Plonky3Lean.Lib
