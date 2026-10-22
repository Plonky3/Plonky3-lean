module

public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Proofs.Field.Goldilocks.Inverse
public import ToCompPoly.Fields.Goldilocks

@[expose] public section

/-!
# Goldilocks: constructors and constants

`new_array`, the `TWO_ADIC_GENERATORS` table, `two_adic_generator`, `GENERATOR` and `NEG_ONE`.

The table is checked against CompPoly's primitive `2^32`-th root of unity.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.P3Goldilocks


/-- `new_array` stores each input unchanged. -/
theorem new_array.spec {N : Std.Usize} (input : Array Std.U64 N) :
    goldilocks.Goldilocks.new_array input ⦃ r =>
      r.val = input.val.map (fun v => ({ value := v } : goldilocks.Goldilocks)) ⦄ := by
  unfold goldilocks.Goldilocks.new_array goldilocks.Goldilocks.new_array_loop
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  have hin : input.val.length = N.val := input.property
  step*
  obtain ⟨arr, harr⟩ := array_repeat_ok N goldilocks.Goldilocks.Insts.CoreCloneClone
    (fun x => ⟨x, rfl⟩) g
  rw [harr, bind_ok]
  apply loop.spec_decr_nat (fun (x : Array goldilocks.Goldilocks N × Std.Usize) => N.val - x.2.val)
    (fun x => x.2.val ≤ N.val ∧ ∀ j < x.2.val,
      x.1.val[j]? = (input.val[j]?).map (fun v => ({ value := v } : goldilocks.Goldilocks)))
  · rintro ⟨out, k⟩ ⟨hk, hinv⟩
    have hout : out.val.length = N.val := out.property
    unfold goldilocks.Goldilocks.new_array_loop.body
    simp only at hk hinv ⊢
    split
    · rename_i hlt
      have hlt' : k.val < N.val := by simpa using hlt
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro j hj
      rw [a_post, Array.set_val_eq, List.getElem?_set]
      by_cases hjk : k.val = j
      · subst hjk
        rw [ite_eq_left rfl, ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)]
        rw [i1_post1]; rfl
      · rw [ite_eq_right hjk]; exact hinv j (by omega)
    · rename_i hge
      have hk' : k.val = N.val := by simp at hge; omega
      simp only [WP.spec_ok]
      apply List.ext_getElem?
      intro j
      by_cases hj : j < N.val
      · rw [hinv j (by omega), List.getElem?_map]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_map, List.getElem?_eq_none (by omega)]
        rfl
  · refine ⟨by simp, ?_⟩
    intro j hj; simp at hj

/-- The table `TWO_ADIC_GENERATORS`, as natural numbers. -/
def twoAdicTable : List ℕ :=
  [1, 18446744069414584320, 281474976710656,
  18446744069397807105, 17293822564807737345, 70368744161280,
  549755813888, 17870292113338400769, 13797081185216407910,
  1803076106186727246, 11353340290879379826, 455906449640507599,
  17492915097719143606, 1532612707718625687, 16207902636198568418,
  17776499369601055404, 6115771955107415310, 12380578893860276750,
  9306717745644682924, 18146160046829613826, 3511170319078647661,
  17654865857378133588, 5416168637041100469, 16905767614792059275,
  9713644485405565297, 5456943929260765144, 17096174751763063430,
  1213594585890690845, 6414415596519834757, 16116352524544190054,
  9123114210336311365, 4614640910117430873, 1753635133440165772]

/-- Entry `i` of the table is `twoAdicGenerator ^ (2^(32 - i))`. -/
theorem twoAdicTable_eq :
    twoAdicTable = (List.range 33).map (fun i => Nat.powMod 0x185629dcda58878c (2 ^ (32 - i))
      18446744069414584321) := by
  decide

/-- `TWO_ADIC_GENERATORS[i] = twoAdicGenerator ^ (2^(32 - i))`. -/
theorem TWO_ADIC_GENERATORS.spec :
    goldilocks.Goldilocks.TWO_ADIC_GENERATORS ⦃ r => ∀ i (h : i < r.val.length),
      r.val.length = 33 ∧ toField r.val[i] = Goldilocks.twoAdicGenerator ^ (2 ^ (32 - i)) ⦄ := by
  unfold goldilocks.Goldilocks.TWO_ADIC_GENERATORS
  apply WP.spec_mono (new_array.spec _)
  intro r hr i hi
  have hlen : r.val.length = 33 := r.property
  refine ⟨hlen, ?_⟩
  have hv : (r.val[i]).value.val = twoAdicTable[i]'(by simp [twoAdicTable]; omega) := by
    simp only [hr, List.getElem_map]
    simp only [Array.make, twoAdicTable]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
  unfold toField
  rw [hv]
  have hpow : (Goldilocks.twoAdicGenerator) ^ (2 ^ (32 - i)) =
      ((Nat.powMod 0x185629dcda58878c (2 ^ (32 - i)) 18446744069414584321 : ℕ) : Goldilocks.Field) := by
    show ((0x185629dcda58878c : ℕ) : Goldilocks.Field) ^ (2 ^ (32 - i)) = _
    rw [ZMod.natCast_pow_eq_powMod]; rfl
  rw [hpow]
  congr 1
  have := congrArg (fun l => l[i]?) twoAdicTable_eq
  simp only [List.getElem?_map, List.getElem?_range (by simp [hlen] at hi; omega : i < 33)] at this
  rw [List.getElem?_eq_getElem] at this
  simpa using this

/-- `twoAdicGenerator ^ (2^(32 - i))` has order `2^i`, for `i ≤ 32`. -/
theorem orderOf_twoAdic_pow (i : ℕ) (hi : i ≤ 32) :
    orderOf (Goldilocks.twoAdicGenerator ^ (2 ^ (32 - i))) = 2 ^ i := by
  have hd : 2 ^ (32 - i) ∣ orderOf Goldilocks.twoAdicGenerator := by
    rw [Goldilocks.orderOf_twoAdicGenerator]; exact Nat.pow_dvd_pow 2 (by simp)
  rw [orderOf_pow_of_dvd (by positivity) hd, Goldilocks.orderOf_twoAdicGenerator]
  show 2 ^ 32 / 2 ^ (32 - i) = 2 ^ i
  rw [Nat.pow_div (by omega) (by norm_num)]
  congr 1; omega

/-- Each entry of `TWO_ADIC_GENERATORS` has order `2^i`, and squares to the previous one. -/
theorem TWO_ADIC_GENERATORS.order :
    goldilocks.Goldilocks.TWO_ADIC_GENERATORS ⦃ r => r.val.length = 33 ∧
      (∀ i (h : i < r.val.length), orderOf (toField r.val[i]) = 2 ^ i) ∧
      (∀ i (h : i + 1 < r.val.length), toField r.val[i + 1] ^ 2 = toField r.val[i]) ⦄ := by
  apply WP.spec_mono TWO_ADIC_GENERATORS.spec
  intro r hr
  have hlen : r.val.length = 33 := r.property
  refine ⟨hlen, fun i h => ?_, fun i h => ?_⟩
  · rw [(hr i h).2]; exact orderOf_twoAdic_pow i (by omega)
  · rw [(hr (i + 1) h).2, (hr i (by omega)).2, ← pow_mul]
    congr 1
    rw [← pow_succ]; congr 1; omega

/-- `two_adic_generator(bits)` returns an element of order `2^bits`, for `bits <= 32`. -/
theorem two_adic_generator.spec (bits : Std.Usize) (h : bits.val ≤ 32) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator bits ⦃ r =>
      orderOf (toField r) = 2 ^ bits.val ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator
  have ht : goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.TWO_ADICITY = 32#usize := by
    unfold goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.TWO_ADICITY; rfl
  rw [ht]
  simp only [massert, UScalar.le_equiv, show (32#usize).val = 32 from rfl, h, ite_true, bind_ok]
  apply WP.spec_bind TWO_ADIC_GENERATORS.order
  rintro a ⟨hlen, hord, -⟩
  unfold Array.index_usize
  have hb : bits.val < a.val.length := by rw [hlen]; omega
  rw [show a[bits]? = some (a.val[bits.val]) from List.getElem?_eq_getElem hb]
  simp only [WP.spec_ok]
  exact hord _ hb

/-- `two_adic_generator(bits)` panics for `bits > 32`. -/
theorem two_adic_generator.panics (bits : Std.Usize) (h : 32 < bits.val) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator bits = .fail .panic := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.two_adic_generator
  have ht : goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.TWO_ADICITY = 32#usize := by
    unfold goldilocks.Goldilocks.Insts.P3_fieldFieldTwoAdicField.TWO_ADICITY; rfl
  rw [ht]
  simp only [massert, UScalar.le_equiv, show (32#usize).val = 32 from rfl]
  rw [ite_eq_right (by omega), bind_fail]

/-- `GENERATOR` is CompPoly's `generator`, `7`. -/
theorem GENERATOR.spec :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.GENERATOR ⦃ r =>
      toField r = Goldilocks.generator ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldField.GENERATOR
  step*
  unfold toField; rw [r_post]; rfl

/-- `NEG_ONE` is `-1`, stored canonically. -/
theorem NEG_ONE.spec :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE ⦃ r =>
      toField r = -1 ∧ Canonical r ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE
  rw [ORDER_U64.eq]
  step*
  rename r.value = _ => r_post
  unfold toField Canonical
  rw [r_post, i_post]
  refine ⟨?_, by decide⟩
  rw [eq_neg_iff_add_eq_zero]
  exact_mod_cast p_eq_zero

end Plonky3Lean.Proofs.P3Goldilocks
