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

/-! ## Squaring is additive -/

/-- Disjoint bits: `or` is `xor`. -/
theorem or_eq_xor_of_and_eq_zero {x y : ℕ} (h : x &&& y = 0) : x ||| y = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hi
  simp only [Nat.testBit_or, Nat.testBit_xor]
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

theorem sqNat_xor {K x y : ℕ} (hx : x < 2 ^ 2 ^ K) (hy : y < 2 ^ 2 ^ K) :
    sqNat K (x ^^^ y) = sqNat K x ^^^ sqNat K y := by
  rw [sqNat_eq K (Nat.xor_lt_two_pow hx hy), sqNat_eq K hx, sqNat_eq K hy, towerMul_sq_xor K hx hy]

theorem sqNat_zero (K : ℕ) : sqNat K 0 = 0 := by
  rw [sqNat_eq K (by positivity), ConcreteBinaryTower.towerMul_zero_left]

theorem additive_sqNat (K : ℕ) : Additive (sqNat K) (2 ^ K) where
  zero := sqNat_zero K
  add x y hx hy h := by rw [or_eq_xor_of_and_eq_zero h, sqNat_xor hx hy]

/-! ## The narrowed tables -/

/-- Entry `w` of row `i` of a table of `ty` integers, as a natural number. -/
noncomputable def cellOf {ty : UScalarTy} {B : Std.Usize}
    (t : Std.Array (Std.Array (UScalar ty) 256#usize) B) (i w : ℕ) : ℕ :=
  match t.val[i]? with
  | some r =>
    match r.val[w]? with
    | some x => x.val
    | none => 0
  | none => 0

theorem cellOf_set {ty : UScalarTy} {B : Std.Usize}
    (t : Std.Array (Std.Array (UScalar ty) 256#usize) B) (i : Std.Usize) (j : Std.Usize)
    (x : UScalar ty) (hi : i.val < t.length) (hj : j.val < 256) (i' w : ℕ) :
    cellOf (t.set i ((t.val[i.val]'(by simpa using hi)).set j x)) i' w =
      if i' = i.val ∧ w = j.val then x.val else cellOf t i' w := by
  unfold cellOf
  rw [Std.Array.set_val_eq]
  by_cases h : i' = i.val
  · subst h
    rw [List.getElem?_set_self (by simpa using hi), List.getElem?_eq_getElem (by simpa using hi)]
    dsimp only
    rw [Std.Array.set_val_eq]
    by_cases hw : w = j.val
    · subst hw
      rw [List.getElem?_set_self (by simpa using hj)]
      simp
    · rw [List.getElem?_set_ne (Ne.symm hw)]
      simp [hw]
  · rw [List.getElem?_set_ne (Ne.symm h)]
    simp [h]

/-! ## `square_16` -/

theorem square_16_table_inner (wide : Std.Array (Std.Array Std.U128 256#usize) 2#usize)
    (i : Std.Usize) (hi : i.val < 2) (t : Std.Array (Std.Array Std.U16 256#usize) 2#usize)
    (j : Std.Usize) (hj : j.val ≤ 256) (hdone : ∀ w < j.val, cellOf t i.val w = cell wide i.val w % 2 ^ 16) :
    linear.square_16.TABLE_loop0_loop0 wide t i j ⦃ t' =>
      (∀ w < 256, cellOf t' i.val w = cell wide i.val w % 2 ^ 16) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf t' i' w = cellOf t i' w ⦄ := by
  unfold linear.square_16.TABLE_loop0_loop0
  refine loop.spec_decr_nat (fun p => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ w < p.2.val, cellOf p.1 i.val w = cell wide i.val w % 2 ^ 16) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf p.1 i' w = cellOf t i' w) _ _ _ ?_
    ⟨hj, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, ho⟩
  unfold linear.square_16.TABLE_loop0_loop0.body
  step*
  simp only at hk hd ho
  have hk' : k.val < 256 := by scalar_tac
  have hlen : i.val < tb.length := by simpa using hi
  have hi1 : i1.val = cell wide i.val k.val := by
    subst a_post1
    rw [i1_post1]
    simp only [cell, List.getElem?_eq_getElem a_post, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i1_post, Option.getD_some]
  have hcell : ∀ i' w, cellOf (index_mut_back a2) i' w =
      if i' = i.val ∧ w = k.val then i2.val else cellOf tb i' w := by
    intro i' w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen hk']
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro w hw
    rw [hcell]
    by_cases hwk : w = k.val
    · subst hwk
      rw [ite_eq_left ⟨rfl, rfl⟩, i2_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, hi1]
    · rw [ite_eq_right (fun h => hwk h.2)]
      exact hd w (by omega)
  · intro i' hi' w
    rw [hcell, ite_eq_right (fun h => hi' h.1)]
    exact ho i' hi' w

theorem square_16_table_outer (wide : Std.Array (Std.Array Std.U128 256#usize) 2#usize)
    (t : Std.Array (Std.Array Std.U16 256#usize) 2#usize) (i : Std.Usize) (hi : i.val ≤ 2)
    (hdone : ∀ i' < i.val, ∀ w < 256, cellOf t i' w = cell wide i' w % 2 ^ 16) :
    linear.square_16.TABLE_loop0 wide t i ⦃ t' =>
      ∀ i' < 2, ∀ w < 256, cellOf t' i' w = cell wide i' w % 2 ^ 16 ⦄ := by
  unfold linear.square_16.TABLE_loop0
  refine loop.spec_decr_nat (fun p => 2 - p.2.val)
    (fun p => p.2.val ≤ 2 ∧ ∀ i' < p.2.val, ∀ w < 256, cellOf p.1 i' w = cell wide i' w % 2 ^ 16)
    _ _ _ ?_ ⟨hi, hdone⟩
  rintro ⟨tb, k⟩ ⟨hk, hd⟩
  unfold linear.square_16.TABLE_loop0.body
  step*
  simp only at hk hd
  have hk' : k.val < 2 := by scalar_tac
  refine WP.spec_bind (square_16_table_inner wide k hk' tb 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun t' ⟨hrow, ho⟩ => ?_
  step*
  refine ⟨by omega, ?_, by omega⟩
  intro i' hi' w hw
  by_cases h : i' = k.val
  · subst h; exact hrow w hw
  · rw [ho i' h w]; exact hd i' (by omega) w hw

/-- `square_16`'s table: entry `w` of row `i` is the square of `w` placed at byte `i`. -/
theorem square_16_TABLE_spec :
    linear.square_16.TABLE ⦃ T => ∀ i < 2, ∀ w < 256, cellOf T i w = sqNat 4 (w <<< (8 * i)) ⦄ := by
  unfold linear.square_16.TABLE
  have hspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * (2#usize : Std.Usize).val) →
      (if false then do
          let i3 ← (2#usize : Std.Usize) * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← (2#usize : Std.Usize) * 8#usize
          linear.square bit i3) ⦃ r => r.val = sqNat 4 bit.val ⦄ := by
    intro bit hbit
    rw [ite_eq_right (by decide)]
    step*
    have h16 : i3 = widthUsize 4 :=
      UScalar.eq_of_val_eq (by rw [i3_post, widthUsize_val (by norm_num)]; rfl)
    subst h16
    exact square_spec 4 (by norm_num) bit (by simpa using hbit)
  refine WP.spec_bind (unary_table_spec (B := 2#usize) (sqNat 4) (by simpa using additive_sqNat 4)
    (by simp) false hspec) fun wide hwide => ?_
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq 256#usize core.U16.Insts.CoreCloneClone (fun _ => rfl) 0#u16
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, -⟩ := Lib.array_repeat_eq 2#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U16.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine WP.spec_mono (square_16_table_outer wide tb 0#usize (by simp)
    (fun _ h => absurd h (by simp))) fun T hT => ?_
  intro i hi w hw
  have hi2 : i < (2#usize : Std.Usize).val := by simpa using hi
  rw [hT i hi w hw, hwide i hi2 w hw, Nat.mod_eq_of_lt]
  have hlt : w <<< (8 * i) < 2 ^ 2 ^ 4 := by
    calc w <<< (8 * i) < 2 ^ (8 * i + 8) := shiftLeft_lt_two_pow (by omega)
      _ ≤ 2 ^ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sqNat_lt hlt

/-! ## Iterating over rows -/

/-- The elements a slice iterator has left. -/
def iterList {T : Type} (s : CoreModels.core.slice.iter.Iter T) : List T := Slice.val s

theorem slice_iter_next_cons {T : Type} (s : CoreModels.core.slice.iter.Iter T) {x : T} {xs : List T}
    (h : iterList s = x :: xs) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s =
      .ok (.Some x, Slice.from xs (by have := s.property; simp [iterList] at h; simp [h] at this; omega)) := by
  unfold iterList at h
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    rust_primitives.sequence.seq_len rust_primitives.sequence.seq_remove
  have hne : Slice.len s ≠ 0#usize := by
    intro h0
    have := congrArg UScalar.val h0
    simp [h] at this
  simp [hne, h]
  rfl

theorem slice_iter_next_nil {T : Type} (s : CoreModels.core.slice.iter.Iter T) (h : iterList s = []) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s = .ok (.None, s) := by
  unfold iterList at h
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    rust_primitives.sequence.seq_len
  have h0 : Slice.len s = 0#usize := UScalar.eq_of_val_eq (by simp [h])
  simp [h0]

/-- A slice iterator over a list, typed as the iterator. -/
def iterOf {T : Type} (l : List T) (h : l.length ≤ Usize.max) : CoreModels.core.slice.iter.Iter T :=
  Slice.from l h

theorem iterList_iterOf {T : Type} (l : List T) (h : l.length ≤ Usize.max) :
    iterList (iterOf l h) = l := by
  simp [iterList, iterOf]

theorem array_as_slice_eq {T : Type} {N : Std.Usize} (a : Std.Array T N) :
    CoreModels.core.array.Array.as_slice a = .ok (Std.Array.to_slice a) := rfl

/-- A slice, typed as its iterator. -/
def iterOfSlice {T : Type} (s : Slice T) : CoreModels.core.slice.iter.Iter T := s

theorem iterList_iterOfSlice {T : Type} (s : Slice T) : iterList (iterOfSlice s) = s.val := rfl

/-- `slice.iter()`, as the iterator over the slice's elements. -/
theorem slice_iter_eq {T : Type} (s : Slice T) :
    CoreModels.core.slice.Slice.iter s = .ok (iterOfSlice s) := by
  unfold CoreModels.core.slice.Slice.iter CoreModels.rust_primitives.sequence.seq_from_slice
  exact Aeneas.Std.bind_ok _ _

theorem enumerate_default_eq {T : Type} (s : CoreModels.core.slice.iter.Iter T) :
    CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T) s =
    .ok { iter := s, count := 0#usize } := rfl

/-- One step of `enumerate` over a slice iterator with an element left. -/
theorem enumerate_next_cons {T : Type}
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter T))
    {x : T} {xs : List T} (h : iterList it.iter = x :: xs) (hc : it.count.val + 1 ≤ Usize.max) :
    ∃ c' : Std.Usize, c'.val = it.count.val + 1 ∧
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T) it =
      .ok (.Some (it.count, x),
        { iter := iterOf xs (by have := it.iter.property; simp [iterList] at h; simp [h] at this; omega),
          count := c' }) := by
  obtain ⟨c', hc', hcv⟩ := WP.spec_imp_exists
    (show (it.count + 1#usize) ⦃ r => r.val = it.count.val + 1 ⦄ by step*)
  refine ⟨c', hcv, ?_⟩
  unfold CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  show (do
    let (o, t) ← CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next it.iter
    _) = _
  rw [slice_iter_next_cons it.iter h]
  simp [hc']
  rfl

/-- The low `n + 8` bits are the low `n` bits and the next byte. -/
theorem mod_two_pow_add_byte (x n : ℕ) :
    x % 2 ^ (n + 8) = x % 2 ^ n ^^^ ((x >>> n) % 2 ^ 8) <<< n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h1 : i < n
  · simp [h1, show i < n + 8 by omega, show ¬ n ≤ i by omega]
  · by_cases h2 : i < n + 8
    · simp [h1, h2, show n ≤ i by omega, show i - n < 8 by omega, show n + (i - n) = i by omega]
    · simp [h1, h2, show ¬ i - n < 8 by omega]

theorem square_16_loop_spec (T : Std.Array (Std.Array Std.U16 256#usize) 2#usize)
    (hT : ∀ i < 2, ∀ w < 256, cellOf T i w = sqNat 4 (w <<< (8 * i))) (value : Std.U16)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U16 256#usize)))
    (result : Std.U16) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 2)
    (hres : result.val = sqNat 4 (value.val % 2 ^ (8 * it.count.val))) :
    linear.square_16_loop it value result ⦃ r => r.val = sqNat 4 value.val ⦄ := by
  unfold linear.square_16_loop
  refine loop.spec_decr_nat (fun p => 2 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 2 ∧
      p.2.val = sqNat 4 (value.val % 2 ^ (8 * p.1.count.val))) _ _ _ ?_ ⟨hit, hc, hres⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold linear.square_16_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 2 := by simp
  by_cases hc2 : it.count.val < 2
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (2 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    have hc8 : (8 * it.count.val) < 16 := by omega
    step*
    · have h3 : i3.val ≤ 255 := by
        rw [i3_post, UScalar.val_and]; exact Nat.and_le_right
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      simp; omega
    · have hbyte : i3.val = (value.val >>> (8 * it.count.val)) % 2 ^ 8 := by
        rw [i3_post, UScalar.val_and, i2_post, i1_post, show (255#u16).val = 2 ^ 8 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h3 : i3.val < 256 := hbyte ▸ Nat.mod_lt _ (by norm_num)
      have hi4 : i4.val = i3.val := by
        rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
          rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      have hi5 : i5.val = sqNat 4 (i3.val <<< (8 * it.count.val)) := by
        rw [← hi4, ← hT it.count.val hc2 i4.val (by omega)]
        unfold cellOf
        rw [List.getElem?_eq_getElem (by omega)]
        dsimp only
        rw [List.getElem?_eq_getElem i5_post, i5_post1]
      have hv16 : value.val < 2 ^ 16 := by have := value.hBounds; simpa using this
      have hx : value.val % 2 ^ (8 * it.count.val) < 2 ^ 2 ^ 4 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : i3.val <<< (8 * it.count.val) < 2 ^ 2 ^ 4 :=
        lt_of_lt_of_le (shiftLeft_lt_two_pow (b := 8) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
      rw [result1_post, UScalar.val_xor, hres, hi5, hc', ← sqNat_xor hx hy, hbyte, mul_add, mul_one,
        mod_two_pow_add_byte value.val (8 * it.count.val)]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc2' : it.count.val = 2 := by omega
    have hv16 : value.val < 2 ^ 16 := by have := value.hBounds; simpa using this
    step*
    rw [hres, hc2', Nat.mod_eq_of_lt hv16]

/-- `square_16` squares in the tower's `GF(2^16)`: it is `towerMul 4 v v`. -/
theorem square_16_spec (value : Std.U16) :
    linear.square_16 value ⦃ r => r.val = ConcreteBinaryTower.towerMul 4 value.val value.val ⦄ := by
  have hv16 : value.val < 2 ^ 2 ^ 4 := by have := value.hBounds; simpa using this
  rw [← sqNat_eq 4 hv16]
  unfold linear.square_16
  refine WP.spec_bind square_16_TABLE_spec fun T hT => ?_
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply square_16_loop_spec T hT value
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rw [show (0#u16 : Std.U16).val = 0 from rfl, show (0#usize : Std.Usize).val = 0 from rfl,
      mul_zero, pow_zero, Nat.mod_one, sqNat_zero]

end Plonky3Lean.Proofs.Binary
