module

public import Sha2
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Lib.Scalar.Words
public import Plonky3Lean.Proofs.Hash.Sha256.Schedule

@[expose] public section

/-!
# sha2: the SHA-256 compression function

The compact backend keeps the last 16 schedule words in a circular buffer.

Round `i` reads its word at index `i % 16`, computing it there first once `i ≥ 16`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Sha256 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Sha256

theorem index_usize_eq {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (h : i.val < v.val.length) : Std.Array.index_usize v i = .ok (v.val[i.val]) := by
  simp only [Std.Array.index_usize]
  rw [show v[i]? = some (v.val[i.val]) from List.getElem?_eq_getElem h]

theorem update_eq {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (h : i.val < v.val.length) :
    Std.Array.update v i x = .ok (Std.Array.from (v.val.set i.val x) (by simp)) := by
  simp only [Std.Array.update]
  rw [show v[i]? = some (v.val[i.val]) from List.getElem?_eq_getElem h]

theorem index_make {α : Type} {n : Std.Usize} (l : List α) (h : l.length = n.val) (i : Std.Usize)
    (hi : i.val < l.length) : Std.Array.index_usize (Std.Array.make n l h) i = .ok (l[i.val]) := by
  rw [index_usize_eq _ _ (by simpa using hi)]
  simp

theorem update_make {α : Type} {n : Std.Usize} (l : List α) (h : l.length = n.val) (i : Std.Usize)
    (x : α) (hi : i.val < l.length) :
    Std.Array.update (Std.Array.make n l h) i x =
      .ok (Std.Array.make n (l.set i.val x) (by simpa using h)) := by
  rw [update_eq _ _ _ (by simpa using hi)]
  congr 1
  apply Std.Array.ext
  simp

/-! ## The schedule buffer -/

/-- Word `t` of the schedule of block `M`. -/
abbrev Wd (M : List Word) (t : ℕ) : Word := (schedule M).getD t 0

/-- The schedule word that slot `j` of the buffer holds before round `k`. -/
def slot (k j : ℕ) : ℕ := max k 16 - 16 + (j + 16 - max k 16 % 16) % 16

theorem slot_le {k j : ℕ} (hk : k ≤ 16) (hj : j < 16) : slot k j = j := by
  unfold slot; omega

theorem slot_ge {k t : ℕ} (h16 : 16 ≤ k) (h1 : k - 16 ≤ t) (h2 : t < k) : slot k (t % 16) = t := by
  unfold slot; omega

/-- The buffer before round `k`. -/
def window (M : List Word) (k : ℕ) : Std.Array Std.U32 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map fun j => ⟨Wd M (slot k j)⟩)
    (by simp only [List.length_map, List.length_range]; rfl)

theorem window_val (M : List Word) (k : ℕ) :
    (window M k).val = (List.range 16).map fun j => ⟨Wd M (slot k j)⟩ := by
  simp [window]

theorem window_read (M : List Word) (k j : ℕ) (hj : j < 16) :
    Std.Array.index_usize (window M k) (usz j) = .ok ⟨Wd M (slot k j)⟩ := by
  rw [index_usize_eq _ _ (by rw [window_val, usz_val (by omega)]; simpa using hj)]
  simp [window_val, usz_val (show j < 2 ^ 32 by omega)]

/-- Round `k ≥ 16` writes word `k` over word `k - 16`. -/
theorem window_update (M : List Word) (k : ℕ) (h16 : 16 ≤ k) :
    Std.Array.update (window M k) (usz (k % 16)) ⟨Wd M k⟩ = .ok (window M (k + 1)) := by
  have hk : k % 16 < 2 ^ 32 := by omega
  rw [update_eq _ _ _ (by rw [window_val, usz_val hk]; simp; omega)]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val, window_val, window_val, usz_val hk]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < 16 := by simpa using h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  split
  · congr 2; unfold slot; omega
  · congr 2; unfold slot; omega

/-- Rounds below 16 leave the buffer as it was loaded. -/
theorem window_le (M : List Word) {k k' : ℕ} (hk : k ≤ 16) (hk' : k' ≤ 16) :
    window M k = window M k' := by
  apply Std.Array.ext
  rw [window_val, window_val]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [slot_le hk hj, slot_le hk' hj]

/-- The round constants are FIPS 180-4's. -/
theorem K32_bv : sha2.consts.K32.val.map UScalar.bv = K := by
  unfold sha2.consts.K32
  decide +kernel

theorem length_K32 : sha2.consts.K32.val.length = 64 := by
  have := congrArg List.length K32_bv
  rw [List.length_map] at this
  rw [this]; rfl

theorem K32_read (k : ℕ) (hk : k < 64) :
    Std.Array.index_usize sha2.consts.K32 (usz k) = .ok ⟨K.getD k 0⟩ := by
  rw [index_usize_eq _ _ (by rw [length_K32, usz_val (by omega)]; exact hk)]
  congr 1
  simp only [usz_val (show k < 2 ^ 32 by omega)]
  rw [← K32_bv, List.getD_eq_getElem _ _ (by rw [List.length_map, length_K32]; exact hk),
    List.getElem_map]

/-! ## The rounds -/

/-- The Rust adds the five terms of `T1` in another order. -/
theorem t1_perm_a (s c k w h t : Word) : s + c + k + w + h + t = h + s + c + k + w + t := by
  ac_rfl

theorem t1_perm_e (d s c k w h : Word) : d + (s + c + k + w + h) = d + (h + s + c + k + w) := by
  ac_rfl

/-- The loop state before round `k`: the range, the buffer and the working variables. -/
def st (M : List Word) (v0 : Vars) (k : ℕ) :
    CoreModels.core.ops.range.Range Std.Usize × Std.Array Std.U32 16#usize × Std.U32 × Std.U32 × Std.U32 ×
      Std.U32 × Std.U32 × Std.U32 × Std.U32 × Std.U32 :=
  let v := rounds (schedule M) v0 k
  ({ start := usz k, «end» := usz 64 }, window M k, ⟨v.a⟩, ⟨v.b⟩, ⟨v.c⟩, ⟨v.d⟩, ⟨v.e⟩, ⟨v.f⟩,
    ⟨v.g⟩, ⟨v.h⟩)

theorem body_lt (M : List Word) (v0 : Vars) (k : ℕ) (hk : k < 16) :
    sha2.sha256.soft.compact.compress_u32_loop.body (st M v0 k).1 (st M v0 k).2.1
      (st M v0 k).2.2.1 (st M v0 k).2.2.2.1 (st M v0 k).2.2.2.2.1 (st M v0 k).2.2.2.2.2.1
      (st M v0 k).2.2.2.2.2.2.1 (st M v0 k).2.2.2.2.2.2.2.1 (st M v0 k).2.2.2.2.2.2.2.2.1
      (st M v0 k).2.2.2.2.2.2.2.2.2 = .ok (.cont (st M v0 (k + 1))) := by
  obtain ⟨i', e, hi'⟩ := range_next_some (usz k) (usz 64) (by rw [usz_val (by omega), usz_val (by omega)]; omega)
  simp only [st]
  unfold sha2.sha256.soft.compact.compress_u32_loop.body
  rw [show i' = usz (k + 1) from eq_usz (by omega) (by rw [hi', usz_val (by omega)])] at e
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok]
  have hlt : usz k < 16#usize := by
    rw [UScalar.lt_equiv, usz_val (by omega)]; exact hk
  simp only [Aeneas.Std.uncurry_apply_pair]
  simp only [hlt, ite_true, window_read M k k hk, K32_read k (by omega), u32_rotate_right_eq,
    lift_eq, u32_wrapping_add_eq, bind_ok]
  rw [rounds_succ, window_le M (k' := k + 1) (by omega) (by omega), slot_le (by omega) hk]
  apply congrArg RustM.ok
  apply congrArg ControlFlow.cont
  simp only [round, Prod.mk.injEq, UScalar.mk.injEq]
  simp only [u32_xor_bv, u32_and_bv, u32_not_bv, UScalar.ofNatCore_val_eq, bigSigma0, bigSigma1,
    ch, maj, true_and, and_true, u32_bv_mk]
  exact ⟨t1_perm_a .., t1_perm_e ..⟩

theorem perm4 (a s b t : Word) : a + s + b + t = t + b + s + a := by
  ac_rfl

/-- The word the Rust computes into the buffer at round `k ≥ 16` is `W_k`. -/
theorem new_word (M : List Word) (hM : M.length = 16) (k : ℕ) (h16 : 16 ≤ k) (h64 : k < 64) :
    let W := schedule M
    W.getD (k - 16) 0 + ((W.getD (k - 15) 0).rotateRight 7 ^^^
      (W.getD (k - 15) 0).rotateRight 18 ^^^ W.getD (k - 15) 0 >>> 3) + W.getD (k - 7) 0 +
      ((W.getD (k - 2) 0).rotateRight 17 ^^^ (W.getD (k - 2) 0).rotateRight 19 ^^^
        W.getD (k - 2) 0 >>> 10) = W.getD k 0 := by
  intro W
  rw [show W.getD k 0 = (schedule M).getD k 0 from rfl, schedule_ge M k hM h16 h64, smallSigma0,
    smallSigma1]
  exact perm4 ..

theorem body_ge (M : List Word) (hM : M.length = 16) (v0 : Vars) (k : ℕ) (h16 : 16 ≤ k)
    (hk : k < 64) :
    sha2.sha256.soft.compact.compress_u32_loop.body (st M v0 k).1 (st M v0 k).2.1
      (st M v0 k).2.2.1 (st M v0 k).2.2.2.1 (st M v0 k).2.2.2.2.1 (st M v0 k).2.2.2.2.2.1
      (st M v0 k).2.2.2.2.2.2.1 (st M v0 k).2.2.2.2.2.2.2.1 (st M v0 k).2.2.2.2.2.2.2.2.1
      (st M v0 k).2.2.2.2.2.2.2.2.2 = .ok (.cont (st M v0 (k + 1))) := by
  obtain ⟨i', e, hi'⟩ := range_next_some (usz k) (usz 64)
    (by rw [usz_val (by omega), usz_val (by omega)]; omega)
  simp only [st]
  unfold sha2.sha256.soft.compact.compress_u32_loop.body
  rw [show i' = usz (k + 1) from eq_usz (by omega) (by rw [hi', usz_val (by omega)])] at e
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok]
  have hlt : ¬ usz k < 16#usize := by
    rw [UScalar.lt_equiv, usz_val (by omega)]
    intro h
    exact absurd (lt_of_lt_of_eq h rfl : k < 16) (by omega)
  simp only [Aeneas.Std.uncurry_apply_pair]
  simp only [hlt, ite_false]
  have l15 : (15#usize : Std.Usize) = usz 15 := ofNatCore_eq_usz _ _ (by norm_num)
  have l16 : (16#usize : Std.Usize) = usz 16 := ofNatCore_eq_usz _ _ (by norm_num)
  have l2 : (2#usize : Std.Usize) = usz 2 := ofNatCore_eq_usz _ _ (by norm_num)
  have l7 : (7#usize : Std.Usize) = usz 7 := ofNatCore_eq_usz _ _ (by norm_num)
  have hnw := new_word M hM k h16 hk
  simp only at hnw
  simp only [l15, l16, l2, l7, usz_sub (a := k) (b := 15) (by omega) (by omega),
    usz_sub (a := k) (b := 2) (by omega) (by omega), usz_sub (a := k) (b := 16) (by omega) (by omega),
    usz_sub (a := k) (b := 7) (by omega) (by omega),
    usz_rem (a := k - 15) (b := 16) (by omega) (by omega) (by omega),
    usz_rem (a := k - 2) (b := 16) (by omega) (by omega) (by omega),
    usz_rem (a := k - 16) (b := 16) (by omega) (by omega) (by omega),
    usz_rem (a := k - 7) (b := 16) (by omega) (by omega) (by omega),
    usz_rem (a := k) (b := 16) (by omega) (by omega) (by omega),
    window_read M k _ (Nat.mod_lt _ (by norm_num : 16 > 0)),
    slot_ge (t := k - 15) h16 (by omega) (by omega), slot_ge (t := k - 2) h16 (by omega) (by omega),
    slot_ge (t := k - 16) h16 (by omega) (by omega), slot_ge (t := k - 7) h16 (by omega) (by omega),
    u32_shiftRight_i32_eq _ 3#i32 (by decide) (by decide),
    u32_shiftRight_i32_eq _ 10#i32 (by decide) (by decide),
    K32_read k hk, u32_rotate_right_eq, lift_eq, u32_wrapping_add_eq, bind_ok, u32_bv_mk,
    u32_xor_bv, UScalar.ofNatCore_val_eq]
  have t3 : (3#i32 : Std.I32).toNat = 3 := by decide
  have t10 : (10#i32 : Std.I32).toNat = 10 := by decide
  simp only [t3, t10, hnw, window_update M k h16, bind_ok]
  rw [rounds_succ]
  apply congrArg RustM.ok
  apply congrArg ControlFlow.cont
  simp only [round, Prod.mk.injEq, UScalar.mk.injEq]
  simp only [u32_and_bv, u32_not_bv, bigSigma0, bigSigma1, ch, maj, true_and, and_true, u32_bv_mk]
  exact ⟨t1_perm_a .., t1_perm_e ..⟩

theorem body_done (M : List Word) (v0 : Vars) :
    sha2.sha256.soft.compact.compress_u32_loop.body (st M v0 64).1 (st M v0 64).2.1
      (st M v0 64).2.2.1 (st M v0 64).2.2.2.1 (st M v0 64).2.2.2.2.1 (st M v0 64).2.2.2.2.2.1
      (st M v0 64).2.2.2.2.2.2.1 (st M v0 64).2.2.2.2.2.2.2.1 (st M v0 64).2.2.2.2.2.2.2.2.1
      (st M v0 64).2.2.2.2.2.2.2.2.2 =
      let v := rounds (schedule M) v0 64
      .ok (.done (⟨v.a⟩, ⟨v.b⟩, ⟨v.c⟩, ⟨v.d⟩, ⟨v.e⟩, ⟨v.f⟩, ⟨v.g⟩, ⟨v.h⟩)) := by
  simp only [st]
  unfold sha2.sha256.soft.compact.compress_u32_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz 64) (usz 64) le_rfl, bind_ok, Aeneas.Std.uncurry_apply_pair]

/-- The 64 rounds, from working variables `v0` and the buffer loaded with block `M`. -/
theorem compress_u32_loop_eq (M : List Word) (hM : M.length = 16) (v0 : Vars) :
    sha2.sha256.soft.compact.compress_u32_loop { start := 0#usize, «end» := 64#usize }
      (window M 0) ⟨v0.a⟩ ⟨v0.b⟩ ⟨v0.c⟩ ⟨v0.d⟩ ⟨v0.e⟩ ⟨v0.f⟩ ⟨v0.g⟩ ⟨v0.h⟩ =
      let v := rounds (schedule M) v0 64
      .ok (⟨v.a⟩, ⟨v.b⟩, ⟨v.c⟩, ⟨v.d⟩, ⟨v.e⟩, ⟨v.f⟩, ⟨v.g⟩, ⟨v.h⟩) := by
  unfold sha2.sha256.soft.compact.compress_u32_loop
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by norm_num),
    show (64#usize : Std.Usize) = usz 64 from ofNatCore_eq_usz _ _ (by norm_num)]
  exact loop_of_steps _ (st M v0) 64 _
    (fun k hk => if h : k < 16 then body_lt M v0 k h else body_ge M hM v0 k (by omega) hk)
    (body_done M v0)

/-- A block of 16 words loads the buffer before round 0. -/
theorem window_zero (block : Std.Array Std.U32 16#usize) :
    window (block.val.map UScalar.bv) 0 = block := by
  apply Std.Array.ext
  rw [window_val]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < 16 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, slot_le (by omega : 0 ≤ 16) hj]
  rw [show Wd (block.val.map UScalar.bv) j = (block.val.map UScalar.bv).getD j 0 from
    schedule_lt _ _ (by simp) hj, List.getD_eq_getElem _ _ (by simpa using h2),
    List.getElem_map, u32_mk_bv]

theorem length_compress (H M : List Word) (hH : H.length = 8) : (compress H M).length = 8 := by
  simp [compress, Vars.toList, hH]

/-- Eight words, as the Rust's `[u32; 8]`. -/
def toArray8 (H : List Word) : Std.Array Std.U32 8#usize :=
  Std.Array.make 8#usize (((H ++ List.replicate 8 0).take 8).map fun w => ⟨w⟩)
    (by simp only [List.length_map, List.length_take, List.length_append, List.length_replicate]
        show _ = 8; omega)

/-- One block: the hash value `[s₀, …, s₇]` and the block's words give FIPS 180-4's next hash
value. -/
theorem compress_u32_eq (s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Std.U32) (block : Std.Array Std.U32 16#usize) :
    sha2.sha256.soft.compact.compress_u32 (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
      block =
      .ok (toArray8 (compress ([s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇].map UScalar.bv)
        (block.val.map UScalar.bv))) := by
  unfold sha2.sha256.soft.compact.compress_u32
  have hl := compress_u32_loop_eq (block.val.map UScalar.bv) (by simp)
    (Vars.ofList ([s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇].map UScalar.bv))
  simp only [Vars.ofList, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    u32_mk_bv, window_zero] at hl
  have i0 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    0#usize = .ok s₀ := rfl
  have i1 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    1#usize = .ok s₁ := rfl
  have i2 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    2#usize = .ok s₂ := rfl
  have i3 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    3#usize = .ok s₃ := rfl
  have i4 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    4#usize = .ok s₄ := rfl
  have i5 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    5#usize = .ok s₅ := rfl
  have i6 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    6#usize = .ok s₆ := rfl
  have i7 : Std.Array.index_usize (Std.Array.make 8#usize [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇])
    7#usize = .ok s₇ := rfl
  simp only [i0, i1, i2, i3, i4, i5, i6, i7, bind_ok, hl, Aeneas.Std.uncurry_apply_pair]
  simp (disch := simp only [UScalar.ofNatCore_val_eq, List.length_cons, List.length_nil,
      List.length_set]; decide) only [update_make, index_make, u32_wrapping_add_eq, bind_ok,
    UScalar.ofNatCore_val_eq, List.set_cons_zero, List.set_cons_succ, List.getElem_cons_zero,
    List.getElem_cons_succ]
  apply congrArg RustM.ok
  apply Std.Array.ext
  simp [toArray8, compress, Vars.toList, Vars.ofList]

/-! ## Loading a block -/

/-- The four bytes of word `k` of a block. -/
def chunk (block : Std.Array Std.U8 64#usize) (k : ℕ) : Std.Array Std.U8 4#usize :=
  Std.Array.make 4#usize [block.val[4 * k]!, block.val[4 * k + 1]!, block.val[4 * k + 2]!,
    block.val[4 * k + 3]!]

theorem to_u32s_call (block : Std.Array Std.U8 64#usize) (k : ℕ) (hk : k < 16) :
    sha2.sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut block (usz k)
      = .ok (Aeneas.Std.core.num.U32.from_be_bytes (chunk block k), block) := by
  unfold sha2.sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hlen : block.val.length = 64 := by simp
  have hm : (4#usize * usz k : RustM Std.Usize) = .ok (usz (4 * k)) := by
    rw [show (4#usize : Std.Usize) = usz 4 from ofNatCore_eq_usz _ _ (by norm_num)]
    exact usz_mul (by omega) (by omega) (by omega)
  rw [hm, bind_ok, index_rangeFrom_eq block _ (by rw [usz_val (by omega)]; omega), bind_ok,
    index_rangeTo_eq _ _ (by simp [List.slice_length, usz_val (show 4 * k < 2 ^ 32 by omega)]; omega),
    bind_ok, try_from_eq _ _ _ (by simp [List.slice_length, usz_val (show 4 * k < 2 ^ 32 by omega)]; omega)
      (by decide), bind_ok]
  simp only [CoreModels.core.result.Result.unwrap, bind_ok, CoreModels.core.num.U32.from_be_bytes,
    CoreModels.rust_primitives.arithmetic.from_be_bytes_u32]
  congr 3
  apply Std.Array.ext
  simp only [Std.Array.from_val, Slice.from_val, chunk, Std.Array.make_val,
    usz_val (show 4 * k < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp [List.slice_length]; omega)
  intro j h1 h2
  have hj : j < 4 := by simpa using h2
  rw [List.getElem_slice, List.getElem_slice]
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      exact (getElem!_pos _ _ (by omega)).symm
  all_goals (simp [List.slice_length, UScalar.ofNatCore_val_eq]; omega)

theorem to_u32s_eq (block : Std.Array Std.U8 64#usize) :
    sha2.sha256.soft.to_u32s block = .ok (Std.Array.from ((List.range 16).map fun k =>
      Aeneas.Std.core.num.U32.from_be_bytes (chunk block k)) (by simp)) := by
  unfold sha2.sha256.soft.to_u32s
  simp only [CoreModels.core.array.from_fn]
  exact array_from_fn_eq _ _ _ _ (fun k hk => to_u32s_call block k (by simpa using hk))

theorem compress_u32_toArray8 (H : List Word) (hH : H.length = 8)
    (block : Std.Array Std.U32 16#usize) :
    sha2.sha256.soft.compact.compress_u32 (toArray8 H) block =
      .ok (toArray8 (compress H (block.val.map UScalar.bv))) := by
  match H, hH with
  | [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇], _ =>
    have e : toArray8 [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇] =
        Std.Array.make 8#usize [⟨h₀⟩, ⟨h₁⟩, ⟨h₂⟩, ⟨h₃⟩, ⟨h₄⟩, ⟨h₅⟩, ⟨h₆⟩, ⟨h₇⟩] := rfl
    rw [e, compress_u32_eq]
    rfl

/-- The words a block loads are its bytes, four at a time, big-endian. -/
theorem to_u32s_bv (block : Std.Array Std.U8 64#usize) :
    ((List.range 16).map fun k => Aeneas.Std.core.num.U32.from_be_bytes (chunk block k)).map
      UScalar.bv = wordsOfBytes (block.val.map UScalar.bv) := by
  rw [wordsOfBytes_eq 16 _ (by simp), List.map_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  have hl : block.val.length = 64 := by simp
  have key : ∀ i < 64, (block.val.map UScalar.bv).getD i 0 = (block.val[i]!).bv := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi), List.getElem_map,
      getElem!_pos _ _ (by omega)]
  rw [key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega)]
  simp only [Function.comp, Aeneas.Std.core.num.U32.from_be_bytes, chunk]
  exact fromBEBytes_four ..

/-- The hash value after compressing each block in turn. -/
def compressBlocks (H : List Word) (blocks : List (Std.Array Std.U8 64#usize)) : List Word :=
  blocks.foldl (fun H b => compress H (wordsOfBytes (b.val.map UScalar.bv))) H

theorem length_compressBlocks (H : List Word) (hH : H.length = 8)
    (blocks : List (Std.Array Std.U8 64#usize)) : (compressBlocks H blocks).length = 8 := by
  induction blocks generalizing H with
  | nil => exact hH
  | cons b bs ih => exact ih _ (length_compress _ _ hH)

/-- A slice as the iterator over it. -/
def seqFrom {α : Type} (l : List α) (h : l.length ≤ Usize.max) : _root_.rust_primitives.sequence.Seq α :=
  Slice.from l h

theorem compress_body_nil (s : Slice (Std.Array Std.U8 64#usize)) (hs : s.val = [])
    (st : Std.Array Std.U32 8#usize) :
    sha2.sha256.soft.compact.compress_loop.body s st = .ok (.done st) := by
  have hl : Slice.len s = 0#usize := UScalar.eq_of_val_eq (by simp [hs])
  simp only [sha2.sha256.soft.compact.compress_loop.body,
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    CoreModels.rust_primitives.sequence.seq_len, bind_ok, hl, ite_true]
  rfl

theorem compress_body_cons (s : Slice (Std.Array Std.U8 64#usize)) (b : Std.Array Std.U8 64#usize)
    (rest : List (Std.Array Std.U8 64#usize)) (hs : s.val = b :: rest) (H : List Word)
    (hH : H.length = 8) :
    sha2.sha256.soft.compact.compress_loop.body s (toArray8 H) =
      .ok (.cont (seqFrom rest (by have := s.property; simp [hs] at this; omega),
        toArray8 (compress H (wordsOfBytes (b.val.map UScalar.bv))))) := by
  have hl : ¬ Slice.len s = 0#usize := fun e => by
    have := congrArg UScalar.val e; simp [hs] at this
  simp only [sha2.sha256.soft.compact.compress_loop.body,
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    CoreModels.rust_primitives.sequence.seq_len, bind_ok, hl, ite_false]
  have hr : CoreModels.rust_primitives.sequence.seq_remove s 0#usize =
      .ok (b, seqFrom rest (by have := s.property; simp [hs] at this; omega)) := by
    simp only [CoreModels.rust_primitives.sequence.seq_remove]
    rw [dite_eq_left_of_eq_true (eq_true (by simp [hs]))]
    congr 2
    · simp [hs]
    · apply Slice.ext; simp [hs, seqFrom]
  rw [hr]
  simp only [bind_ok, to_u32s_eq, compress_u32_toArray8 _ hH,
    Std.Array.from_val, List.map_map]
  have hw : (List.range 16).map (UScalar.bv ∘ fun k =>
      Aeneas.Std.core.num.U32.from_be_bytes (chunk b k)) = wordsOfBytes (b.val.map UScalar.bv) := by
    rw [← List.map_map, to_u32s_bv]
  rw [← hw]
  simp only [Aeneas.Std.uncurry_apply_pair, bind_ok]

theorem compress_loop_eq (n : ℕ) (s : Slice (Std.Array Std.U8 64#usize)) (hn : s.val.length = n)
    (H : List Word) (hH : H.length = 8) :
    sha2.sha256.soft.compact.compress_loop s (toArray8 H) =
      .ok (toArray8 (compressBlocks H s.val)) := by
  induction n generalizing s H with
  | zero =>
    have hs : s.val = [] := List.eq_nil_of_length_eq_zero hn
    unfold sha2.sha256.soft.compact.compress_loop
    rw [loop]
    dsimp only
    rw [compress_body_nil s hs, bind_ok, hs]
    rfl
  | succ n ih =>
    obtain ⟨b, rest, hs⟩ : ∃ b rest, s.val = b :: rest := by
      cases h : s.val with
      | nil => simp [h] at hn
      | cons b rest => exact ⟨b, rest, rfl⟩
    unfold sha2.sha256.soft.compact.compress_loop
    rw [loop]
    dsimp only
    rw [compress_body_cons s b rest hs H hH, bind_ok, hs]
    have hrest := ih (Slice.from rest (by have := s.property; simp [hs] at this; omega))
      (by simp only [Slice.from_val]; simp [hs] at hn; omega)
      (compress H (wordsOfBytes (b.val.map UScalar.bv))) (length_compress _ _ hH)
    unfold sha2.sha256.soft.compact.compress_loop at hrest
    dsimp only at hrest ⊢
    rw [Slice.from_val] at hrest
    exact hrest

/-- sha2's `compress256` compresses each block in turn, as FIPS 180-4 does. -/
theorem compress256_eq (H : List Word) (hH : H.length = 8)
    (blocks : Slice (Std.Array Std.U8 64#usize)) :
    sha2.sha256.compress256 (toArray8 H) blocks = .ok (toArray8 (compressBlocks H blocks.val)) := by
  simp only [sha2.sha256.compress256, sha2.sha256.compress, sha2.sha256.soft.compact.compress,
    CoreModels.core.slice.Slice.iter, CoreModels.rust_primitives.sequence.seq_from_slice]
  erw [bind_ok, bind_ok]
  exact compress_loop_eq _ blocks rfl H hH

end Plonky3Lean.Proofs.Sha256
