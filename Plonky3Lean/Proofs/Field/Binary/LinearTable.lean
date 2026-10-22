module

public import Plonky3Lean.Proofs.Field.Binary.Linear
public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Lib.Iter

@[expose] public section

/-!
# `unary_table`: the byte tables of a linear map

`linear::unary_table` fills one row of 256 entries per byte of the input.

Row `i` holds the image of every byte placed at byte position `i`. Bit by bit, it sets
`row[v | 2^b] = row[v] ^ image(2^(8 i + b))` for `v < 2^b`.

For a map `img` that is additive on disjoint bits, entry `w` of row `i` is then
`img (w << 8 i)`. The proofs here take any such `img`, so that the squaring and the
square-root tables share them.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Binary

/-- Entry `w` of row `i` of a table, as a natural number (`0` past the end). -/
noncomputable def cell {B : Std.Usize} (t : Std.Array (Std.Array Std.U128 256#usize) B)
    (i w : ℕ) : ℕ :=
  match t.val[i]? with
  | some r => (r.val.getD w 0#u128).val
  | none => 0

/-- Entries `w < n` of row `i` are the images of `w` placed at byte `i`. -/
def RowOK {B : Std.Usize} (img : ℕ → ℕ) (t : Std.Array (Std.Array Std.U128 256#usize) B)
    (i n : ℕ) : Prop :=
  ∀ w < n, cell t i w = img (w <<< (8 * i))

theorem cell_set_row {B : Std.Usize} (t : Std.Array (Std.Array Std.U128 256#usize) B)
    (i : Std.Usize) (r : Std.Array Std.U128 256#usize) (hi : i.val < t.length) (j w : ℕ) :
    cell (t.set i r) j w = if j = i.val then (r.val.getD w 0#u128).val else cell t j w := by
  unfold cell
  rw [Std.Array.set_val_eq]
  by_cases h : j = i.val
  · subst h
    rw [ite_eq_left rfl, List.getElem?_set_self (by simpa using hi)]
  · rw [ite_eq_right h, List.getElem?_set_ne (Ne.symm h)]

theorem getD_set_entry (r : Std.Array Std.U128 256#usize) (u : Std.Usize) (x : Std.U128)
    (hu : u.val < 256) (w : ℕ) :
    ((r.set u x).val.getD w 0#u128).val = if w = u.val then x.val else (r.val.getD w 0#u128).val := by
  rw [Std.Array.set_val_eq]
  by_cases h : w = u.val
  · subst h
    rw [ite_eq_left rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using hu)]
    rfl
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
      ← List.getD_eq_getElem?_getD]

/-- A map additive on disjoint bits below `2^n`, sending `0` to `0`. -/
structure Additive (img : ℕ → ℕ) (n : ℕ) : Prop where
  zero : img 0 = 0
  add : ∀ x y, x < 2 ^ n → y < 2 ^ n → x &&& y = 0 → img (x ||| y) = img x ^^^ img y

/-- A value below `2^b`, shifted by `s`, shares no bit with `2^(s+b)`. -/
theorem shiftLeft_and_two_pow {w b s : ℕ} (hw : w < 2 ^ b) : (w <<< s) &&& 2 ^ (s + b) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases h : s + b = j
  · subst h
    simp [Nat.testBit_lt_two_pow hw]
  · simp [h]

theorem or_two_pow_shiftLeft {w b s : ℕ} : (w ||| 2 ^ b) <<< s = w <<< s ||| 2 ^ (s + b) := by
  rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq (2 ^ b), pow_add, mul_comm]

theorem shiftLeft_lt_two_pow {w b s : ℕ} (hw : w < 2 ^ b) : w <<< s < 2 ^ (s + b) := by
  rw [Nat.shiftLeft_eq, pow_add, mul_comm]
  exact Nat.mul_lt_mul_of_pos_left hw (by positivity)

/-- The innermost loop sets `row[v | 2^b]` for `v < 2^b`. -/
theorem unary_inner_spec {B : Std.Usize} (img : ℕ → ℕ) (hadd : Additive img (8 * B.val))
    (i b : Std.Usize) (hi : i.val < B.val) (hb : b.val < 8) (image : Std.U128)
    (himg : image.val = img (2 ^ (8 * i.val + b.val)))
    (t : Std.Array (Std.Array Std.U128 256#usize) B) (v : Std.Usize) (hv : v.val ≤ 2 ^ b.val)
    (hrow : RowOK img t i.val (2 ^ b.val))
    (hdone : ∀ w < v.val, cell t i.val (w ||| 2 ^ b.val) = img ((w ||| 2 ^ b.val) <<< (8 * i.val))) :
    linear.unary_table_loop0_loop0_loop0 t i b image v ⦃ t' =>
      RowOK img t' i.val (2 ^ (b.val + 1)) ∧ ∀ j, j ≠ i.val → ∀ w, cell t' j w = cell t j w ⦄ := by
  unfold linear.unary_table_loop0_loop0_loop0
  refine loop.spec_decr_nat (fun p => 2 ^ b.val - p.2.val)
    (fun p => p.2.val ≤ 2 ^ b.val ∧ RowOK img p.1 i.val (2 ^ b.val) ∧
      (∀ w < p.2.val,
        cell p.1 i.val (w ||| 2 ^ b.val) = img ((w ||| 2 ^ b.val) <<< (8 * i.val))) ∧
      ∀ j, j ≠ i.val → ∀ w, cell p.1 j w = cell t j w) _ _ _ ?_
    ⟨hv, hrow, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hr, hd, ho⟩
  unfold linear.unary_table_loop0_loop0_loop0.body
  have hb128 : 2 ^ b.val ≤ 128 := by
    calc 2 ^ b.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 128 := by norm_num
  have hbits : b.val < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega
  step*
  · have hi1 : i1.val = 2 ^ b.val := by
      rw [i1_post, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
      rw [show Usize.size = 2 ^ System.Platform.numBits by
        simp [Usize.size_def, Usize.numBits_def]]
      exact Nat.pow_lt_pow_right (by norm_num) hbits
    rename_i hlt
    have hk : k.val < 2 ^ b.val := by have : k.val < i1.val := by scalar_tac
                                      omega
    rw [i3_post, UScalar.val_or, hi1, Nat.or_two_pow_eq_add_of_lt hk]
    simp; omega
  · have hi1 : i1.val = 2 ^ b.val := by
      rw [i1_post, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
      rw [show Usize.size = 2 ^ System.Platform.numBits by
        simp [Usize.size_def, Usize.numBits_def]]
      exact Nat.pow_lt_pow_right (by norm_num) hbits
    rename_i hlt
    simp only at hk hr hd ho
    have hkb : k.val < 2 ^ b.val := by have : k.val < i1.val := by scalar_tac
                                       omega
    have hlen : i.val < tb.length := by simpa using hi
    have hi3 : i3.val = k.val + 2 ^ b.val := by
      rw [i3_post, UScalar.val_or, hi1, Nat.or_two_pow_eq_add_of_lt hkb]
    have hi3lt : i3.val < 256 := by omega
    -- the row as read: `a1` is row `i`
    have hrow_i : ∀ w, (a1.val.getD w 0#u128).val = cell tb i.val w := by
      intro w
      unfold cell
      rw [List.getElem?_eq_getElem hlen, a1_post1]
    have hcell : ∀ j w, cell (index_mut_back a2) j w =
        if j = i.val then (if w = i3.val then i4.val else cell tb i.val w) else cell tb j w := by
      intro j w
      rw [index_mut_back_post, a2_post, cell_set_row _ _ _ hlen,
        getD_set_entry _ _ _ hi3lt, hrow_i]
    have hi2 : i2.val = img (k.val <<< (8 * i.val)) := by
      rw [← hr k.val hkb]
      subst a_post1
      rw [i2_post1]
      simp only [cell, List.getElem?_eq_getElem hlen, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem i2_post, Option.getD_some]
    have hsum : 8 * i.val + b.val < 8 * B.val := by omega
    refine ⟨by omega, ?_, ?_, ?_, by omega⟩
    · intro w hw
      rw [hcell, ite_eq_left rfl, ite_eq_right (by omega)]
      exact hr w hw
    · intro w hw
      rw [hcell, ite_eq_left rfl]
      by_cases hwk : w = k.val
      · subst hwk
        rw [Nat.or_two_pow_eq_add_of_lt hkb, ite_eq_left (by omega), i4_post, UScalar.val_xor, hi2,
          himg, ← Nat.or_two_pow_eq_add_of_lt hkb, or_two_pow_shiftLeft]
        refine (hadd.add _ _ ?_ ?_ (shiftLeft_and_two_pow hkb)).symm
        · exact lt_of_lt_of_le (shiftLeft_lt_two_pow hkb) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · exact Nat.pow_lt_pow_right (by norm_num) hsum
      · have hw' : w < k.val := by omega
        rw [ite_eq_right (by rw [Nat.or_two_pow_eq_add_of_lt (by omega)]; omega)]
        exact hd w hw'
    · intro j hj w
      rw [hcell, ite_eq_right hj]
      exact ho j hj w
  · have hi1 : i1.val = 2 ^ b.val := by
      rw [i1_post, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
      rw [show Usize.size = 2 ^ System.Platform.numBits by
        simp [Usize.size_def, Usize.numBits_def]]
      exact Nat.pow_lt_pow_right (by norm_num) hbits
    rename_i hnk
    simp only at hk hr hd ho
    have hnk' : ¬ k.val < i1.val := fun h => hnk (by scalar_tac)
    have hkb : k.val = 2 ^ b.val := by omega
    refine ⟨?_, ho⟩
    intro w hw
    by_cases hlo : w < 2 ^ b.val
    · exact hr w hlo
    · have hw' : w - 2 ^ b.val < 2 ^ b.val := by rw [pow_succ] at hw; omega
      have := hd (w - 2 ^ b.val) (by omega)
      rwa [Nat.or_two_pow_eq_add_of_lt hw', Nat.sub_add_cancel (by omega)] at this

/-- The middle loop fills row `i`, bit by bit. `himgspec` states that the image the body
computes, by `square` or by `sqrt`, is `img`. -/
theorem unary_middle_spec {B : Std.Usize} (img : ℕ → ℕ) (hadd : Additive img (8 * B.val))
    (hB : 8 * B.val ≤ 128) (inverse : Bool)
    (himgspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * B.val) →
      (if inverse then do
          let i3 ← B * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← B * 8#usize
          linear.square bit i3) ⦃ r => r.val = img bit.val ⦄)
    (i : Std.Usize) (hi : i.val < B.val) (t : Std.Array (Std.Array Std.U128 256#usize) B)
    (b : Std.Usize) (hb : b.val ≤ 8) (hrow : RowOK img t i.val (2 ^ b.val)) :
    linear.unary_table_loop0_loop0 inverse t i b ⦃ t' =>
      RowOK img t' i.val 256 ∧ ∀ j, j ≠ i.val → ∀ w, cell t' j w = cell t j w ⦄ := by
  unfold linear.unary_table_loop0_loop0
  refine loop.spec_decr_nat (fun p => 8 - p.2.val)
    (fun p => p.2.val ≤ 8 ∧ RowOK img p.1 i.val (2 ^ p.2.val) ∧
      ∀ j, j ≠ i.val → ∀ w, cell p.1 j w = cell t j w) _ _ _ ?_ ⟨hb, hrow, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hr, ho⟩
  unfold linear.unary_table_loop0_loop0.body
  step*
  · rw [bit_post, show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) bit_post2)]
    simp only at hk
    rename_i hk8
    have : k.val < 8 := by scalar_tac
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · simp only at hk hr ho
    rename_i hk8
    have hk8' : k.val < 8 := by scalar_tac
    have hbit : bit.val = 2 ^ (8 * i.val + k.val) := by
      rw [bit_post, show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
        Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) bit_post2),
        i2_post, i1_post]
      congr 1
      ring
    refine WP.spec_bind (unary_inner_spec img hadd i k hi hk8' image (by rw [image_post, hbit])
      tb 0#usize (by simp) hr (fun w hw => absurd hw (by simp))) fun t' ⟨hrow', ho'⟩ => ?_
    step*
    refine ⟨by omega, ?_, ?_, by omega⟩
    · rw [b1_post]; exact hrow'
    · intro j hj w
      rw [ho' j hj w, ho j hj w]

/-- Cloning an array whose elements clone to themselves returns the array. -/
theorem array_clone_eq {T : Type} {N : Std.Usize} (inst : CoreModels.core.clone.Clone T)
    (hclone : ∀ x, inst.clone x = .ok x) (a : Std.Array T N) :
    (core.Array.Insts.CoreCloneClone N inst).clone a = .ok a := by
  show core.Array.Insts.CoreCloneClone.clone inst a = .ok a
  unfold core.Array.Insts.CoreCloneClone.clone core.array.Array.map
  rw [array_map_eq _ a () id (by
    intro x
    unfold core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT
      core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut
    simp [hclone])]
  congr 1
  apply Std.Array.ext
  simp

/-- The outer loop fills the rows from `i` on, each starting with a zero entry `0`. -/
theorem unary_outer_spec {B : Std.Usize} (img : ℕ → ℕ) (hadd : Additive img (8 * B.val))
    (hB : 8 * B.val ≤ 128) (inverse : Bool)
    (himgspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * B.val) →
      (if inverse then do
          let i3 ← B * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← B * 8#usize
          linear.square bit i3) ⦃ r => r.val = img bit.val ⦄)
    (t : Std.Array (Std.Array Std.U128 256#usize) B) (i : Std.Usize) (hi : i.val ≤ B.val)
    (hdone : ∀ i' < i.val, RowOK img t i' 256)
    (hzero : ∀ i', i.val ≤ i' → i' < B.val → cell t i' 0 = 0) :
    linear.unary_table_loop0 inverse t i ⦃ t' => ∀ i' < B.val, RowOK img t' i' 256 ⦄ := by
  unfold linear.unary_table_loop0
  refine loop.spec_decr_nat (fun p => B.val - p.2.val)
    (fun p => p.2.val ≤ B.val ∧ (∀ i' < p.2.val, RowOK img p.1 i' 256) ∧
      ∀ i', p.2.val ≤ i' → i' < B.val → cell p.1 i' 0 = 0) _ _ _ ?_ ⟨hi, hdone, hzero⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, hz⟩
  unfold linear.unary_table_loop0.body
  step*
  simp only at hk hd hz
  rename_i hkB
  have hkB' : k.val < B.val := by scalar_tac
  have hrow0 : RowOK img tb k.val (2 ^ (0#usize : Std.Usize).val) := by
    intro w hw
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    rw [hz k.val le_rfl hkB', Nat.zero_shiftLeft, hadd.zero]
  refine WP.spec_bind (unary_middle_spec img hadd hB inverse himgspec k hkB' tb 0#usize
    (by simp) hrow0) fun t' ⟨hrow', ho'⟩ => ?_
  step*
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro i' hi'
    by_cases h : i' = k.val
    · subst h; exact hrow'
    · intro w hw
      rw [ho' i' h w]
      exact hd i' (by omega) w hw
  · intro i' hi' hi'B
    rw [ho' i' (by omega) 0]
    exact hz i' (by omega) hi'B

/-- `unary_table` returns, in row `i`, the image of every byte placed at byte `i`. -/
theorem unary_table_spec {B : Std.Usize} (img : ℕ → ℕ) (hadd : Additive img (8 * B.val))
    (hB : 8 * B.val ≤ 128) (inverse : Bool)
    (himgspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * B.val) →
      (if inverse then do
          let i3 ← B * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← B * 8#usize
          linear.square bit i3) ⦃ r => r.val = img bit.val ⦄) :
    linear.unary_table B inverse ⦃ t => ∀ i' < B.val, RowOK img t i' 256 ⦄ := by
  unfold linear.unary_table
  obtain ⟨a, ha, hall⟩ :=
    Lib.array_repeat_eq 256#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, hallt⟩ := Lib.array_repeat_eq B
    (core.Array.Insts.CoreCloneClone 256#usize core.U128.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine unary_outer_spec img hadd hB inverse himgspec tb 0#usize (by simp)
    (fun _ h => absurd h (by simp)) ?_
  intro i' _ hi'
  have hlen : i' < tb.val.length := by simpa using hi'
  unfold cell
  rw [List.getElem?_eq_getElem hlen, hallt _ (List.getElem_mem hlen)]
  dsimp only
  have ha0 : 0 < a.val.length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha0, Option.getD_some,
    hall _ (List.getElem_mem ha0)]
  rfl

end Plonky3Lean.Proofs.Binary
