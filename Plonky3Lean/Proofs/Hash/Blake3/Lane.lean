module

public import P3Blake3
public import Plonky3Lean.Spec.Blake3
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Lib.Scalar.Words

@[expose] public section

/-!
# p3-blake3 on the portable backend: one lane of words

The portable backend has one lane (`W = 1`) and one group (`G = 1`), so every loop over the groups
runs once, on group `0`.

A list of words stands for an array of `u32`s, padded with zeros or cut to the array's length.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The words of `s`, as an array of `n` `u32`s. -/
def arr (n : Std.Usize) (s : List Word) : Std.Array Std.U32 n :=
  Std.Array.make n (((s ++ List.replicate n.val 0).take n.val).map fun w => ⟨w⟩) (by simp)

theorem arr_val (n : Std.Usize) (s : List Word) (h : s.length = n.val) :
    (arr n s).val = s.map fun w => ⟨w⟩ := by
  simp [arr, List.take_append_of_le_length (by omega : n.val ≤ s.length), h]

/-- One group of a state: the words of `s` as the only group. -/
def grp (n : Std.Usize) (s : List Word) : Std.Array (Std.Array Std.U32 n) 1#usize :=
  Std.Array.make 1#usize [arr n s] (by rfl)

/-- A loop over the groups, `0..1`, whose body takes `x` to `y` on group `0`. -/
theorem lane_loop {α β : Type} (body : CoreModels.core.ops.range.Range Std.Usize × α →
      RustM (ControlFlow (CoreModels.core.ops.range.Range Std.Usize × α) β)) (x : α) (y : β)
    (y' : α)
    (h0 : body ({ start := 0#usize, «end» := 1#usize }, x) =
      .ok (.cont ({ start := usz 1, «end» := 1#usize }, y')))
    (h1 : body ({ start := usz 1, «end» := 1#usize }, y') = .ok (.done y)) :
    loop body ({ start := 0#usize, «end» := 1#usize }, x) = .ok y := by
  have := loop_of_steps body (fun k => if k = 0 then
      (({ start := 0#usize, «end» := 1#usize } : CoreModels.core.ops.range.Range Std.Usize), x)
      else ({ start := usz 1, «end» := 1#usize }, y')) 1 y
    (fun k hk => by have : k = 0 := by omega
                    subst this; simpa using h0) (by simpa using h1)
  simpa using this

theorem grp_val (n : Std.Usize) (s : List Word) : (grp n s).val = [arr n s] := by
  simp [grp]

theorem index_grp (n : Std.Usize) (s : List Word) :
    Std.Array.index_usize (grp n s) (usz 0) = .ok (arr n s) := by
  rw [index_usize_eq _ _ (by rw [grp_val, usz_val (by norm_num)]; simp)]
  simp [grp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem index_mut_grp (n : Std.Usize) (s : List Word) :
    Std.Array.index_mut_usize (grp n s) (usz 0) =
      .ok (arr n s, fun a => Std.Array.set (grp n s) (usz 0) a) := by
  simp only [Std.Array.index_mut_usize, index_grp]
  rw [bind_tc_ok]

theorem set_grp (n : Std.Usize) (s t : List Word) :
    Std.Array.set (grp n s) (usz 0) (arr n t) = grp n t := by
  apply Std.Array.ext
  simp [Std.Array.set_val_eq, grp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem index_arr (n : Std.Usize) (s : List Word) (h : s.length = n.val) (i : ℕ) (hi : i < n.val) :
    Std.Array.index_usize (arr n s) (usz i) = .ok ⟨s.getD i 0⟩ := by
  rw [index_usize_eq _ _ (by rw [arr_val n s h, usz_val_le n hi.le]; simpa [h] using hi)]
  simp [arr_val n s h, usz_val_le n hi.le, List.getElem?_eq_getElem (show i < s.length by omega)]

theorem update_arr (n : Std.Usize) (s : List Word) (h : s.length = n.val) (i : ℕ) (hi : i < n.val)
    (x : Std.U32) :
    Std.Array.update (arr n s) (usz i) x = .ok (arr n (s.set i x.bv)) := by
  rw [update_eq _ _ _ (by rw [arr_val n s h, usz_val_le n hi.le]; simpa [h] using hi)]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val, arr_val n s h, arr_val n _ (by simpa using h), usz_val_le n hi.le,
    List.map_set, u32_mk_bv]

end Plonky3Lean.Proofs.Blake3
