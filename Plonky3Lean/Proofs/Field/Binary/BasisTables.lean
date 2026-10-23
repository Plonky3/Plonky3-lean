module

public import Plonky3Lean.Proofs.Field.Binary.BasisInvert

@[expose] public section

/-!
# Applying the change of basis a byte at a time

`byte_tables` turns the columns of a `GF(2)`-linear map into one table per input byte: entry
`w` of table `b` is the map applied to `w` placed at byte `b` (`linB`). `apply_128`,
`apply_64` and `apply_32` xor one entry per byte, which is the map applied to the whole word
(`lin_add`).
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The map with columns `cols` applied to the byte `w` placed at byte `b`. -/
def linB (cols : ℕ → ℕ) (b w : ℕ) : ℕ := lin (fun j => cols (8 * b + j)) 8 w

theorem lin_add (c : ℕ → ℕ) (k : ℕ) : ∀ m v,
    lin c (k + m) v = lin c k v ^^^ lin (fun j => c (k + j)) m (v >>> k)
  | 0, v => by simp [lin]
  | m + 1, v => by
    rw [← Nat.add_assoc, lin, lin_add c k m v, lin, Nat.testBit_shiftRight, Nat.xor_assoc]

/-- Flipping bit `t` of `v` adds column `t` to the image. -/
theorem lin_flip (c : ℕ → ℕ) {k t : ℕ} (ht : t < k) (v : ℕ) :
    lin c k v = lin c k (v ^^^ 2 ^ t) ^^^ c t := by
  rw [lin_xor, lin_two_pow c ht, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ## `byte_tables` -/

theorem byte_inner_spec (cols : Std.Array Std.U128 128#usize) (byte : Std.Usize)
    (hb : byte.val < 16) (T : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (value : Std.Usize) (hv1 : 1 ≤ value.val) (hv : value.val ≤ 256)
    (hdone : ∀ w < value.val, cellOf T byte.val w = linB (aval cols) byte.val w) :
    clmul.basis.byte_tables_loop0_loop0 cols T byte value ⦃ r =>
      (∀ w < 256, cellOf r byte.val w = linB (aval cols) byte.val w) ∧
      ∀ k, k ≠ byte.val → ∀ w, cellOf r k w = cellOf T k w ⦄ := by
  unfold clmul.basis.byte_tables_loop0_loop0
  refine loop.spec_decr_nat (fun s => 256 - s.2.val)
    (fun s => 1 ≤ s.2.val ∧ s.2.val ≤ 256 ∧
      (∀ w < s.2.val, cellOf s.1 byte.val w = linB (aval cols) byte.val w) ∧
      ∀ k, k ≠ byte.val → ∀ w, cellOf s.1 k w = cellOf T k w) _ _ _ ?_ ?_
  rotate_left
  · exact ⟨hv1, hv, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, n⟩ ⟨hn1, hn, hd, ho⟩
  dsimp only at hn1 hn hd ho ⊢
  unfold clmul.basis.byte_tables_loop0_loop0.body
  step*
  have hnb : n.val < 256 := by scalar_tac
  have hn0 : n.val ≠ 0 := by omega
  have hnb2 : n.val < 2 ^ System.Platform.numBits := by
    have := n.hBounds; simpa [UScalarTy.numBits] using this
  obtain ⟨t, hfind, htn, htb, hlow⟩ := find_lowest_bit hn0 hnb2
  have ht8 : t < 8 := by
    by_contra h
    have hlt : n.val < 2 ^ t :=
      lt_of_lt_of_le hnb (by
        have : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this)
    rw [Nat.testBit_lt_two_pow hlt] at htb
    exact absurd htb (by simp)
  have hnum := System.Platform.numBits_eq
  have hts : 2 ^ t < Usize.size := by
    rw [Usize.size_def]
    exact Nat.pow_lt_pow_right (by norm_num) (by simpa [Usize.numBits] using htn)
  have hx : n.val ^^^ 2 ^ t < n.val := by
    rw [← and_sub_one_eq_xor htb hlow]
    exact lt_of_le_of_lt Nat.and_le_right (by omega)
  have hfind' : List.find? (fun i => (n.val).testBit i) (List.range UScalarTy.Usize.numBits) =
      some t := by simpa [UScalarTy.numBits] using hfind
  simp only [core.num.Usize.trailing_zeros, hfind', Option.getD_some]
  have hcast : (UScalar.cast UScalarTy.Usize (⟨BitVec.ofNat 32 t⟩ : Std.U32)).val = t := by
    rw [UScalar.cast_val_eq]
    show (BitVec.ofNat 32 t).toNat % _ = t
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t < 2 ^ 32 by omega)]
    apply Nat.mod_eq_of_lt
    simp only [UScalarTy.numBits]
    rcases hnum with e | e <;> rw [e] <;> omega
  step*
  all_goals have hlowv : low.val = t := by rw [low_post, hcast]
  all_goals have hi1 : i1.val = 2 ^ t := by rw [i1_post, hlowv, Nat.one_shiftLeft, Nat.mod_eq_of_lt hts]
  all_goals have hi2 : i2.val = n.val ^^^ 2 ^ t := by rw [i2_post, UScalar.val_xor, hi1]
  case h_fail => rw [hi2]; scalar_tac
  have hlen : byte.val < tb.val.length := by simpa using a_post
  have hi3 : i3.val = cellOf tb byte.val (n.val ^^^ 2 ^ t) := by
    rw [i3_post1]
    simp only [cellOf, List.getElem?_eq_getElem hlen, ← a_post1, ← hi2,
      List.getElem?_eq_getElem i3_post]
  have hi6 : i6.val = aval cols (8 * byte.val + t) := by
    have hi5 : i5.val = 8 * byte.val + t := by rw [i5_post, i4_post, hlowv]; ring
    rw [i6_post1, aval_eq_getElem _ _ (by rw [← hi5]; simpa using i6_post)]
    simp only [hi5]
  have hcell : ∀ k w, cellOf (index_mut_back a2) k w =
      if k = byte.val ∧ w = n.val then i7.val else cellOf tb k w := by
    intro k w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen (by scalar_tac)]
  refine ⟨by scalar_tac, by scalar_tac, fun w hw => ?_, fun k hk w => ?_, by scalar_tac⟩
  · rw [hcell]
    by_cases hwn : w = n.val
    · rw [ite_eq_left ⟨rfl, hwn⟩, i7_post, UScalar.val_xor, hi3, hi6, hd _ hx, hwn, linB, linB,
        lin_flip (fun j => aval cols (8 * byte.val + j)) ht8 n.val]
    · rw [ite_eq_right (fun h => hwn h.2)]
      exact hd w (by scalar_tac)
  · rw [hcell, ite_eq_right (fun h => hk h.1)]
    exact ho k hk w

theorem byte_outer_spec (cols : Std.Array Std.U128 128#usize) (bits : Std.Usize)
    (h128 : bits.val ≤ 128) (T : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (byte : Std.Usize) (hbyte : byte.val ≤ bits.val / 8)
    (hdone : ∀ k < byte.val, ∀ w < 256, cellOf T k w = linB (aval cols) k w)
    (hzero : ∀ k, byte.val ≤ k → cellOf T k 0 = 0) :
    clmul.basis.byte_tables_loop0 cols bits T byte ⦃ r =>
      ∀ k < bits.val / 8, ∀ w < 256, cellOf r k w = linB (aval cols) k w ⦄ := by
  unfold clmul.basis.byte_tables_loop0
  refine loop.spec_decr_nat (fun s => bits.val / 8 - s.2.val)
    (fun s => s.2.val ≤ bits.val / 8 ∧
      (∀ k < s.2.val, ∀ w < 256, cellOf s.1 k w = linB (aval cols) k w) ∧
      ∀ k, s.2.val ≤ k → cellOf s.1 k 0 = 0) _ _ _ ?_ ?_
  rotate_left
  · exact ⟨hbyte, hdone, hzero⟩
  rintro ⟨tb, n⟩ ⟨hn, hd, hz⟩
  dsimp only at hn hd hz ⊢
  unfold clmul.basis.byte_tables_loop0.body
  step*
  · have hn' : n.val < bits.val / 8 := by scalar_tac
    apply WP.spec_bind (byte_inner_spec cols n (by omega) tb 1#usize (by simp) (by simp)
      (fun w hw => by
        have : w = 0 := by simpa using hw
        rw [this, hz n.val le_rfl]
        simp [linB, lin_zero]))
    rintro t' ⟨hrow, ho⟩
    step*
    refine ⟨by scalar_tac, fun k hk w hw => ?_, fun k hk => ?_, by scalar_tac⟩
    · by_cases h : k = n.val
      · rw [h]; exact hrow w hw
      · rw [ho k h w]; exact hd k (by scalar_tac) w hw
    · rw [ho k (by scalar_tac) 0]; exact hz k (by scalar_tac)

theorem byte_tables_spec (cols : Std.Array Std.U128 128#usize) (bits : Std.Usize)
    (h128 : bits.val ≤ 128) :
    clmul.basis.byte_tables cols bits ⦃ r =>
      ∀ k < bits.val / 8, ∀ w < 256, cellOf r k w = linB (aval cols) k w ⦄ := by
  unfold clmul.basis.byte_tables
  obtain ⟨a, ha, hall⟩ :=
    Lib.array_repeat_eq 256#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, hallt⟩ := Lib.array_repeat_eq 16#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U128.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine byte_outer_spec cols bits h128 tb 0#usize (by simp)
    (fun _ h => absurd h (by simp)) (fun k _ => ?_)
  unfold cellOf
  split
  · rename_i r hr
    rw [hallt r (List.mem_of_getElem? hr)]
    have ha0 : 0 < a.val.length := by simp
    rw [List.getElem?_eq_getElem ha0, hall _ (List.getElem_mem ha0)]
    rfl
  · rfl

/-! ## `apply_128` -/

theorem linB_byte (cols : ℕ → ℕ) (v c : ℕ) :
    linB cols c ((v >>> (8 * c)) % 256) = lin (fun j => cols (8 * c + j)) 8 (v >>> (8 * c)) := by
  unfold linB
  apply lin_congr
  intro i hi
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [hi]

theorem apply_128_loop_spec (T : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (cols : ℕ → ℕ) (hT : ∀ k < 16, ∀ w < 256, cellOf T k w = linB cols k w) (v : Std.U128)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U128 256#usize)))
    (acc : Std.U128) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 16)
    (hacc : acc.val = lin cols (8 * it.count.val) v.val) :
    clmul.basis.apply_128_loop it v acc ⦃ r => r.val = lin cols 128 v.val ⦄ := by
  unfold clmul.basis.apply_128_loop
  refine loop.spec_decr_nat (fun p => 16 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 16 ∧
      p.2.val = lin cols (8 * p.1.count.val) v.val) _ _ _ ?_ ⟨hit, hc, hacc⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold clmul.basis.apply_128_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 16 := by simp
  by_cases hc16 : it.count.val < 16
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (16 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    step*
    have hi3 : i3.val = (v.val >>> (8 * it.count.val)) % 256 := by
      rw [i3_post, UScalar.cast_val_eq, i2_post, UScalar.cast_val_eq, i1_post, i_post]
      have h8 : (v.val >>> (8 * it.count.val)) % 2 ^ 8 < 256 := Nat.mod_lt _ (by norm_num)
      rw [UScalarTy.U8_numBits_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;>
          simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      rfl
    have hi4 : i4.val = linB cols it.count.val ((v.val >>> (8 * it.count.val)) % 256) := by
      rw [← hi3, ← hT it.count.val hc16 i3.val (by rw [hi3]; exact Nat.mod_lt _ (by norm_num))]
      unfold cellOf
      rw [List.getElem?_eq_getElem (by omega)]
      dsimp only
      rw [List.getElem?_eq_getElem i4_post, i4_post1]
    refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
    rw [acc1_post, UScalar.val_xor, hres, hi4, linB_byte, hc', mul_add, mul_one, lin_add]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc16' : it.count.val = 16 := by omega
    step*

/-- `apply_128` applies the map whose byte tables it is given. -/
theorem apply_128_spec (T : Std.Array (Std.Array Std.U128 256#usize) 16#usize) (cols : ℕ → ℕ)
    (hT : ∀ k < 16, ∀ w < 256, cellOf T k w = linB cols k w) (v : Std.U128) :
    clmul.basis.apply_128 T v ⦃ r => r.val = lin cols 128 v.val ⦄ := by
  unfold clmul.basis.apply_128
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply apply_128_loop_spec T cols hT v
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rfl

end Plonky3Lean.Proofs.Binary
