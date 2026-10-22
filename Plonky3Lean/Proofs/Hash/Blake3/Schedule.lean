module

public import Plonky3Lean.Proofs.Hash.Blake3.Mix

@[expose] public section

/-!
# p3-blake3: the message schedule

Instead of permuting the message after every round, p3-blake3 precomputes which message word each
round reads: row `r` of `SCHEDULE` is the permutation applied `r` times.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The message word round `r` reads at position `i`: the permutation applied `r` times. -/
def permPow : ℕ → ℕ → ℕ
  | 0, i => i
  | r + 1, i => permPow r (MSG_PERMUTATION.getD i 0)

/-- A row of 16 indices, as the Rust's array. -/
def rowArr (f : ℕ → ℕ) : Std.Array Std.Usize 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map fun j => usz (f j)) (by simp)

/-- A table of 7 rows of 16 indices, as the Rust's array. -/
def schedOf (F : ℕ → ℕ → ℕ) : Std.Array (Std.Array Std.Usize 16#usize) 7#usize :=
  Std.Array.make 7#usize ((List.range 7).map fun q => rowArr (F q)) (by simp)

/-- The schedule while row `r` is being filled, its first `k` entries done. -/
def schedAt (r k : ℕ) (q j : ℕ) : ℕ := if q < r ∨ (q = r ∧ j < k) then permPow q j else 0

theorem rowArr_val (f : ℕ → ℕ) : (rowArr f).val = (List.range 16).map fun j => usz (f j) := by
  simp [rowArr]

theorem schedOf_val (F : ℕ → ℕ → ℕ) : (schedOf F).val = (List.range 7).map fun q => rowArr (F q) := by
  simp [schedOf]

theorem rowArr_ext {f f' : ℕ → ℕ} (h : ∀ j < 16, f j = f' j) : rowArr f = rowArr f' := by
  apply Std.Array.ext
  rw [rowArr_val, rowArr_val]
  apply List.map_congr_left
  intro j hj; rw [h j (by simpa using hj)]

theorem schedOf_ext {F F' : ℕ → ℕ → ℕ} (h : ∀ q < 7, ∀ j < 16, F q j = F' q j) :
    schedOf F = schedOf F' := by
  apply Std.Array.ext
  rw [schedOf_val, schedOf_val]
  apply List.map_congr_left
  intro q hq; rw [rowArr_ext (h q (by simpa using hq))]

theorem index_sched (F : ℕ → ℕ → ℕ) (q : ℕ) (hq : q < 7) :
    Std.Array.index_usize (schedOf F) (usz q) = .ok (rowArr (F q)) := by
  rw [index_usize_eq _ _ (by rw [schedOf_val, usz_val (by omega)]; simpa using hq)]
  simp [schedOf_val, usz_val (show q < 2 ^ 32 by omega)]

theorem index_row (f : ℕ → ℕ) (i : ℕ) (hi : i < 16) :
    Std.Array.index_usize (rowArr f) (usz i) = .ok (usz (f i)) := by
  rw [index_usize_eq _ _ (by rw [rowArr_val, usz_val (by omega)]; simpa using hi)]
  simp [rowArr_val, usz_val (show i < 2 ^ 32 by omega)]

theorem index_mut_sched (F : ℕ → ℕ → ℕ) (q : ℕ) (hq : q < 7) :
    Std.Array.index_mut_usize (schedOf F) (usz q) =
      .ok (rowArr (F q), fun a => Std.Array.set (schedOf F) (usz q) a) := by
  simp only [Std.Array.index_mut_usize, index_sched F q hq]
  rw [bind_tc_ok]

theorem update_row (f : ℕ → ℕ) (i v : ℕ) (hi : i < 16) :
    Std.Array.update (rowArr f) (usz i) (usz v) =
      .ok (rowArr fun j => if j = i then v else f j) := by
  rw [update_eq _ _ _ (by rw [rowArr_val, usz_val (by omega)]; simpa using hi)]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val, rowArr_val, rowArr_val, usz_val (by omega)]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl

theorem set_sched (F : ℕ → ℕ → ℕ) (q : ℕ) (hq : q < 7) (f : ℕ → ℕ) :
    Std.Array.set (schedOf F) (usz q) (rowArr f) =
      schedOf fun q' => if q' = q then f else F q' := by
  apply Std.Array.ext
  rw [Std.Array.set_val_eq, schedOf_val, schedOf_val, usz_val (by omega)]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl

theorem index_PERMUTATION (i : ℕ) (hi : i < 16) :
    Std.Array.index_usize p3_blake3.batch.compress.PERMUTATION (usz i) =
      .ok (usz (MSG_PERMUTATION.getD i 0)) := by
  unfold p3_blake3.batch.compress.PERMUTATION
  rw [index_make _ _ _ (by rw [usz_val (by omega)]; simpa using hi)]
  congr 1
  simp only [usz_val (show i < 2 ^ 32 by omega)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
    i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact eq_usz (by simp [MSG_PERMUTATION]) rfl

theorem array_clone_eq {T : Type} {N : Std.Usize} (inst : CoreModels.core.clone.Clone T)
    (hclone : ∀ x, inst.clone x = .ok x) (a : Std.Array T N) :
    (CoreModels.core.Array.Insts.CoreCloneClone N inst).clone a = .ok a := by
  show CoreModels.core.Array.Insts.CoreCloneClone.clone inst a = .ok a
  unfold CoreModels.core.Array.Insts.CoreCloneClone.clone CoreModels.core.array.Array.map
  rw [array_map_eq _ a () id (fun x => by
    simp only [CoreModels.core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
      hclone, bind_ok, id])]
  congr 1
  apply Std.Array.ext
  simp

theorem BLOCK_WORDS_eq : p3_blake3.batch.compress.BLOCK_WORDS = usz 16 := by
  unfold p3_blake3.batch.compress.BLOCK_WORDS; exact eq_usz (by norm_num) rfl

theorem ROUNDS_eq : p3_blake3.batch.compress.ROUNDS = usz 7 := by
  unfold p3_blake3.batch.compress.ROUNDS; exact eq_usz (by norm_num) rfl

theorem lit0 : (0#usize : Std.Usize) = usz 0 := eq_usz (by norm_num) rfl
theorem lit1 : (1#usize : Std.Usize) = usz 1 := eq_usz (by norm_num) rfl

theorem usz_lt_iff' (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (usz a < usz b) = (a < b) := propext (usz_lt_iff ha hb)

theorem sched0_body (k : ℕ) (hk : k < 16) :
    p3_blake3.batch.compress.SCHEDULE_loop0.body (schedOf (schedAt 0 k)) (usz k) =
      .ok (.cont (schedOf (schedAt 0 (k + 1)), usz (k + 1))) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop0.body
  rw [BLOCK_WORDS_eq, ite_eq_left_of_eq_true _ _ (eq_true ((usz_lt_iff (by omega) (by omega)).2 hk)), lit0,
    index_mut_sched _ 0 (by omega), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [update_row _ k k hk, bind_ok, lit1, usz_add (by omega), bind_ok, set_sched _ 0 (by omega)]
  congr 3
  apply schedOf_ext
  intro q hq j hj
  by_cases hq0 : q = 0
  · subst hq0
    simp only [schedAt, permPow, Nat.lt_irrefl, false_or, true_and, ite_true]
    split_ifs <;> omega
  · simp [schedAt, hq0]

theorem sched0_done (sch : Std.Array (Std.Array Std.Usize 16#usize) 7#usize) :
    p3_blake3.batch.compress.SCHEDULE_loop0.body sch (usz 16) = .ok (.done sch) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop0.body
  rw [BLOCK_WORDS_eq, ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_lt_iff (by omega) (by omega)]; omega))]

theorem permPow_lt (r i : ℕ) (hi : i < 16) : permPow r i < 16 := by
  induction r generalizing i with
  | zero => exact hi
  | succ r ih =>
    apply ih
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
      i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem MSG_PERMUTATION_lt (i : ℕ) (hi : i < 16) : MSG_PERMUTATION.getD i 0 < 16 :=
  permPow_lt 1 i hi

theorem sched1_inner_body (r k : ℕ) (hr1 : 1 ≤ r) (hr : r < 7) (hk : k < 16) :
    p3_blake3.batch.compress.SCHEDULE_loop1_loop0.body (usz r) (schedOf (schedAt r k)) (usz k) =
      .ok (.cont (schedOf (schedAt r (k + 1)), usz (k + 1))) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop1_loop0.body
  have hp := MSG_PERMUTATION_lt k hk
  rw [BLOCK_WORDS_eq, ite_eq_left_of_eq_true _ _ (eq_true ((usz_lt_iff (by omega) (by omega)).2 hk)),
    lit1, usz_sub hr1 (by omega), bind_ok, index_PERMUTATION k hk, bind_ok,
    index_sched _ (r - 1) (by omega), bind_ok, index_row _ _ hp, bind_ok,
    index_mut_sched _ r hr, bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [update_row _ k _ hk, bind_ok, usz_add (by omega), bind_ok, set_sched _ r hr]
  congr 3
  apply schedOf_ext
  intro q hq j hj
  by_cases hqr : q = r
  · subst hqr
    have hpp : permPow q k = permPow (q - 1) (MSG_PERMUTATION.getD k 0) := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rfl
    simp only [schedAt, ite_true, show q - 1 < q by omega, true_or, Nat.lt_irrefl, false_or, true_and]
    split_ifs <;> first | omega | (subst_vars; exact hpp.symm)
  · simp [schedAt, hqr]

theorem sched1_inner_done (r : Std.Usize) (sch : Std.Array (Std.Array Std.Usize 16#usize) 7#usize) :
    p3_blake3.batch.compress.SCHEDULE_loop1_loop0.body r sch (usz 16) = .ok (.done sch) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop1_loop0.body
  rw [BLOCK_WORDS_eq, ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_lt_iff (by omega) (by omega)]; omega))]

theorem schedAt_full (r : ℕ) : schedOf (schedAt r 16) = schedOf (schedAt (r + 1) 0) := by
  apply schedOf_ext
  intro q hq j hj
  simp only [schedAt]
  split_ifs <;> omega

theorem sched1_inner (r : ℕ) (hr1 : 1 ≤ r) (hr : r < 7) :
    p3_blake3.batch.compress.SCHEDULE_loop1_loop0 (schedOf (schedAt r 0)) (usz r) 0#usize =
      .ok (schedOf (schedAt (r + 1) 0)) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop1_loop0
  rw [lit0, ← schedAt_full]
  exact loop_of_steps _ (fun k => (schedOf (schedAt r k), usz k)) 16 _
    (fun k hk => sched1_inner_body r k hr1 hr hk) (sched1_inner_done _ _)

theorem sched1_body (r : ℕ) (hr1 : 1 ≤ r) (hr : r < 7) :
    p3_blake3.batch.compress.SCHEDULE_loop1.body (schedOf (schedAt r 0)) (usz r) =
      .ok (.cont (schedOf (schedAt (r + 1) 0), usz (r + 1))) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop1.body
  rw [ROUNDS_eq, ite_eq_left_of_eq_true _ _ (eq_true ((usz_lt_iff (by omega) (by omega)).2 hr)),
    sched1_inner r hr1 hr, bind_ok, lit1, usz_add (by omega), bind_ok]

theorem sched1_done (sch : Std.Array (Std.Array Std.Usize 16#usize) 7#usize) :
    p3_blake3.batch.compress.SCHEDULE_loop1.body sch (usz 7) = .ok (.done sch) := by
  unfold p3_blake3.batch.compress.SCHEDULE_loop1.body
  rw [ROUNDS_eq, ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_lt_iff (by omega) (by omega)]; omega))]

theorem SCHEDULE_eq : p3_blake3.batch.compress.SCHEDULE = .ok (schedOf permPow) := by
  unfold p3_blake3.batch.compress.SCHEDULE
  rw [repeat_eq _ _ _ (fun _ => rfl) (by decide), bind_ok,
    repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide), bind_ok]
  have h0 : Std.Array.from (List.replicate (7#usize).val
      (Std.Array.from (List.replicate (16#usize).val (0#usize : Std.Usize)) (by simp))) (by simp) =
      schedOf (schedAt 0 0) := by
    apply Std.Array.ext
    rw [Std.Array.from_val, schedOf_val]
    apply List.ext_getElem (by simp)
    intro q h1 h2
    simp only [List.getElem_replicate, List.getElem_map, List.getElem_range]
    apply Std.Array.ext
    rw [Std.Array.from_val, rowArr_val]
    apply List.ext_getElem (by simp)
    intro j h3 h4
    simp [schedAt, lit0]
  rw [h0]
  have hl0 : p3_blake3.batch.compress.SCHEDULE_loop0 (schedOf (schedAt 0 0)) 0#usize =
      .ok (schedOf (schedAt 1 0)) := by
    unfold p3_blake3.batch.compress.SCHEDULE_loop0
    rw [lit0, ← schedAt_full]
    exact loop_of_steps _ (fun k => (schedOf (schedAt 0 k), usz k)) 16 _
      (fun k hk => sched0_body k hk) (sched0_done _)
  rw [hl0, bind_ok]
  have hl1 : p3_blake3.batch.compress.SCHEDULE_loop1 (schedOf (schedAt 1 0)) 1#usize =
      .ok (schedOf (schedAt 7 0)) := by
    unfold p3_blake3.batch.compress.SCHEDULE_loop1
    rw [lit1]
    exact loop_of_steps _ (fun k => (schedOf (schedAt (k + 1) 0), usz (k + 1))) 6 _
      (fun k hk => sched1_body (k + 1) (by omega) (by omega)) (sched1_done _)
  rw [hl1]
  congr 1

end Plonky3Lean.Proofs.Blake3
