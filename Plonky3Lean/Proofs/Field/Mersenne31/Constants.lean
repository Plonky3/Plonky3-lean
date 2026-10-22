module

public import Plonky3Lean.Proofs.Field.Mersenne31.Field

@[expose] public section

/-!
# Mersenne31: the constants, as field elements
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib
open Polynomial

namespace Plonky3Lean.Proofs.P3Mersenne31

/-- A stored value, for writing tables. -/
def e (v : Std.U32) : Element := ⟨v⟩

/-! ## Base-field constants -/

/-- `new v` on a literal below `p` stores it unchanged. -/
theorem new_eq (v : Std.U32) (h : v.val < 2147483647) : mersenne_31.Mersenne31.new v = .ok (e v) :=
  eq_ok_of_spec (WP.spec_mono (new.spec v) fun r hr => by
    obtain ⟨w⟩ := r
    unfold e; congr 1; apply UScalar.eq_of_val_eq; rw [show w.val = _ from hr, Nat.mod_eq_of_lt h])

/-- `new_reduced v` on a literal below `2^31` stores it unchanged. -/
theorem new_reduced_eq (v : Std.U32) (h : v.val < 2 ^ 31) :
    mersenne_31.Mersenne31.new_reduced v = .ok (e v) :=
  eq_ok_of_spec (WP.spec_mono (new_reduced.spec v h) fun r hr => by unfold e; rw [← hr])


theorem ORDER_U32.eq_fieldSize : (2147483647#u32).val = Mersenne31.fieldSize := rfl

theorem GENERATOR.eq :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.GENERATOR = .ok (e 7#u32) := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldField.GENERATOR
  simp (config := { decide := true }) only [new_eq]

theorem GENERATOR.toField :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.GENERATOR ⦃ g =>
      Canonical g ∧ orderOf (Spec.Mersenne31.toField g) = Mersenne31.fieldSize - 1 ⦄ := by
  rw [GENERATOR.eq, WP.spec_ok]
  exact ⟨by unfold Canonical e; decide, Mersenne31.orderOf_generator⟩

theorem NEG_ONE.toField :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.NEG_ONE ⦃ g =>
      Canonical g ∧ Spec.Mersenne31.toField g = -1 ⦄ := by
  rw [NEG_ONE.eq, WP.spec_ok]
  exact ⟨by unfold Canonical; decide, by unfold Spec.Mersenne31.toField; decide⟩

theorem ZERO.toField :
    Canonical mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO ∧
      Spec.Mersenne31.toField mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO = 0 := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO Canonical
    Spec.Mersenne31.toField
  decide

theorem ONE.toField :
    Canonical mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE ∧
      Spec.Mersenne31.toField mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE = 1 := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE Canonical
    Spec.Mersenne31.toField
  decide

theorem TWO.toField :
    Canonical mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.TWO ∧
      Spec.Mersenne31.toField mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.TWO = 2 := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.TWO Canonical
    Spec.Mersenne31.toField
  decide

/-! ## Tables of complex elements -/

/-- A table of stored pairs reads as the complex elements with the same coefficients. -/
theorem toComplex_of_vals {n : Std.Usize} (t : Array (Array Element 2#usize) n)
    (cs : List (Mersenne31.Field × Mersenne31.Field))
    (h : t.val.map (fun c => ((c.val.getD 0 ⟨0#u32⟩).value.val, (c.val.getD 1 ⟨0#u32⟩).value.val)) =
      cs.map (fun c => (c.1.val, c.2.val)))
    (k : ℕ) (hk : k < n.val) (hk' : k < cs.length) :
    toComplex (t.val[k]'(by rw [t.property]; exact hk)) =
      Mersenne31.Complex.mk (cs[k]'hk').1 (cs[k]'hk').2 := by
  have hl : k < (t.val.map (fun c => ((c.val.getD 0 ⟨0#u32⟩).value.val,
      (c.val.getD 1 ⟨0#u32⟩).value.val))).length := by simp [t.property, hk]
  have := List.getElem_of_eq h hl
  simp only [List.getElem_map, Prod.mk.injEq] at this
  unfold toComplex Spec.Mersenne31.toField
  rw [this.1, this.2, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

def extTable : Array (Array Element 2#usize) 33#usize :=
  Array.make 33#usize [
    Array.make 2#usize [e 1#u32, e 0#u32],
    Array.make 2#usize [e 2147483646#u32, e 0#u32],
    Array.make 2#usize [e 0#u32, e 2147483646#u32],
    Array.make 2#usize [e 32768#u32, e 2147450879#u32],
    Array.make 2#usize [e 590768354#u32, e 978592373#u32],
    Array.make 2#usize [e 1179735656#u32, e 1241207368#u32],
    Array.make 2#usize [e 1567857810#u32, e 456695729#u32],
    Array.make 2#usize [e 1774253895#u32, e 1309288441#u32],
    Array.make 2#usize [e 736262640#u32, e 1553669210#u32],
    Array.make 2#usize [e 1819216575#u32, e 1662816114#u32],
    Array.make 2#usize [e 1323191254#u32, e 1936974060#u32],
    Array.make 2#usize [e 605622498#u32, e 1964232216#u32],
    Array.make 2#usize [e 343674985#u32, e 501786993#u32],
    Array.make 2#usize [e 1995316534#u32, e 149306621#u32],
    Array.make 2#usize [e 2107600913#u32, e 1378821388#u32],
    Array.make 2#usize [e 541476169#u32, e 2101081972#u32],
    Array.make 2#usize [e 2135874973#u32, e 483411332#u32],
    Array.make 2#usize [e 2097144245#u32, e 1684033590#u32],
    Array.make 2#usize [e 1662322247#u32, e 670236780#u32],
    Array.make 2#usize [e 1172215635#u32, e 595888646#u32],
    Array.make 2#usize [e 241940101#u32, e 323856519#u32],
    Array.make 2#usize [e 1957194259#u32, e 2139647100#u32],
    Array.make 2#usize [e 1957419629#u32, e 1541039442#u32],
    Array.make 2#usize [e 1062045235#u32, e 1824580421#u32],
    Array.make 2#usize [e 1929382196#u32, e 1664698822#u32],
    Array.make 2#usize [e 1889294251#u32, e 331248939#u32],
    Array.make 2#usize [e 1214231414#u32, e 1646302518#u32],
    Array.make 2#usize [e 1765392370#u32, e 461136547#u32],
    Array.make 2#usize [e 1629751483#u32, e 66485474#u32],
    Array.make 2#usize [e 1501355827#u32, e 1439063420#u32],
    Array.make 2#usize [e 509778402#u32, e 800467507#u32],
    Array.make 2#usize [e 311014874#u32, e 1584694829#u32],
    Array.make 2#usize [e 1166849849#u32, e 1117296306#u32]]

def circleTable : Array (Array Element 2#usize) 32#usize :=
  Array.make 32#usize [
    Array.make 2#usize [e 1#u32, e 0#u32],
    Array.make 2#usize [e 2147483646#u32, e 0#u32],
    Array.make 2#usize [e 0#u32, e 2147483646#u32],
    Array.make 2#usize [e 32768#u32, e 2147450879#u32],
    Array.make 2#usize [e 590768354#u32, e 978592373#u32],
    Array.make 2#usize [e 1179735656#u32, e 1241207368#u32],
    Array.make 2#usize [e 1567857810#u32, e 456695729#u32],
    Array.make 2#usize [e 1774253895#u32, e 1309288441#u32],
    Array.make 2#usize [e 736262640#u32, e 1553669210#u32],
    Array.make 2#usize [e 1819216575#u32, e 1662816114#u32],
    Array.make 2#usize [e 1323191254#u32, e 1936974060#u32],
    Array.make 2#usize [e 605622498#u32, e 1964232216#u32],
    Array.make 2#usize [e 343674985#u32, e 501786993#u32],
    Array.make 2#usize [e 1995316534#u32, e 149306621#u32],
    Array.make 2#usize [e 2107600913#u32, e 1378821388#u32],
    Array.make 2#usize [e 541476169#u32, e 2101081972#u32],
    Array.make 2#usize [e 2135874973#u32, e 483411332#u32],
    Array.make 2#usize [e 2097144245#u32, e 1684033590#u32],
    Array.make 2#usize [e 1662322247#u32, e 670236780#u32],
    Array.make 2#usize [e 1172215635#u32, e 595888646#u32],
    Array.make 2#usize [e 241940101#u32, e 323856519#u32],
    Array.make 2#usize [e 1957194259#u32, e 2139647100#u32],
    Array.make 2#usize [e 1957419629#u32, e 1541039442#u32],
    Array.make 2#usize [e 1062045235#u32, e 1824580421#u32],
    Array.make 2#usize [e 1929382196#u32, e 1664698822#u32],
    Array.make 2#usize [e 1889294251#u32, e 331248939#u32],
    Array.make 2#usize [e 1214231414#u32, e 1646302518#u32],
    Array.make 2#usize [e 1765392370#u32, e 461136547#u32],
    Array.make 2#usize [e 1629751483#u32, e 66485474#u32],
    Array.make 2#usize [e 1501355827#u32, e 1439063420#u32],
    Array.make 2#usize [e 509778402#u32, e 800467507#u32],
    Array.make 2#usize [e 311014874#u32, e 1584694829#u32]]

theorem EXT_TWO_ADIC_GENERATORS.eq :
    mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS = .ok extTable := by
  unfold mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  simp (config := { decide := true }) only [new_eq, bind_ok]
  rfl

theorem CIRCLE_TWO_ADIC_GENERATORS.eq :
    complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS = .ok circleTable := by
  unfold complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS complex.new_complex_new
  simp (config := { decide := true }) only [new_eq, bind_ok, bind_tc_ok, pure_tc_eq,
    List.mapM_cons, List.mapM_nil]
  rfl

theorem extTable_vals :
    extTable.val.map (fun c => ((c.val.getD 0 ⟨0#u32⟩).value.val, (c.val.getD 1 ⟨0#u32⟩).value.val)) =
      Mersenne31.twoAdicGeneratorCoeffs.map (fun c => (c.1.val, c.2.val)) := by
  decide

theorem circleTable_vals :
    circleTable.val.map (fun c => ((c.val.getD 0 ⟨0#u32⟩).value.val, (c.val.getD 1 ⟨0#u32⟩).value.val)) =
      (Mersenne31.twoAdicGeneratorCoeffs.take 32).map (fun c => (c.1.val, c.2.val)) := by
  decide

theorem coeffs_length : Mersenne31.twoAdicGeneratorCoeffs.length = 33 := rfl

/-- The complex element with the coefficients of entry `k` has order `2^k`. -/
theorem coeffs_order (k : ℕ) (hk : k < 33) :
    orderOf (Mersenne31.Complex.mk (Mersenne31.twoAdicGeneratorCoeffs[k]'(by rw [coeffs_length]; exact hk)).1
      (Mersenne31.twoAdicGeneratorCoeffs[k]'(by rw [coeffs_length]; exact hk)).2) = 2 ^ k := by
  have := Mersenne31.twoAdicGenerators_order k (by rw [Mersenne31.twoAdicGenerators_length]; exact hk)
  simpa [Mersenne31.twoAdicGenerators] using this

theorem extTable_order (k : ℕ) (hk : k < 33) :
    orderOf (toComplex (extTable.val[k]'(by rw [extTable.property]; exact hk))) = 2 ^ k := by
  rw [toComplex_of_vals extTable _ extTable_vals k hk (by rw [coeffs_length]; exact hk)]
  exact coeffs_order k hk

/-- Entry `k` of `EXT_TWO_ADIC_GENERATORS` has order `2^k` in `F[i]`. -/
theorem EXT_TWO_ADIC_GENERATORS.order :
    mersenne_31.Mersenne31.EXT_TWO_ADIC_GENERATORS ⦃ t =>
      ∀ k (hk : k < 33), orderOf (toComplex (t.val[k]'(by rw [t.property]; exact hk))) = 2 ^ k ⦄ := by
  rw [EXT_TWO_ADIC_GENERATORS.eq, WP.spec_ok]
  exact extTable_order

/-- Entry `k` of `CIRCLE_TWO_ADIC_GENERATORS` has order `2^k` and norm `1`. -/
theorem CIRCLE_TWO_ADIC_GENERATORS.order :
    complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS ⦃ t =>
      ∀ k (hk : k < 32),
        orderOf (toComplex (t.val[k]'(by rw [t.property]; exact hk))) = 2 ^ k ∧
        toComplex (t.val[k]'(by rw [t.property]; exact hk)) ^ (Mersenne31.fieldSize + 1) = 1 ⦄ := by
  rw [CIRCLE_TWO_ADIC_GENERATORS.eq, WP.spec_ok]
  intro k hk
  have hk' : k < (Mersenne31.twoAdicGeneratorCoeffs.take 32).length := by
    rw [List.length_take, coeffs_length]; omega
  rw [toComplex_of_vals circleTable _ circleTable_vals k hk hk']
  have hc : (Mersenne31.twoAdicGeneratorCoeffs.take 32)[k] =
      Mersenne31.twoAdicGeneratorCoeffs[k]'(by rw [coeffs_length]; omega) := List.getElem_take
  refine ⟨?_, ?_⟩
  · rw [hc]; exact coeffs_order k (by omega)
  · have hn := Mersenne31.twoAdicGeneratorCoeffs_norm _ (List.getElem_mem hk')
    rw [Mersenne31.Complex.mk_pow_fieldSize_succ, hn, map_one]

/-- `ext_two_adic_generator(bits)` returns an element of order `2^bits` for `bits ≤ 32`, and panics otherwise. -/
theorem ext_two_adic_generator.order (bits : Std.Usize) :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.ext_two_adic_generator bits
      ⦃ c => bits.val ≤ 32 ∧ orderOf (toComplex c) = 2 ^ bits.val ⦄ ∨
    (32 < bits.val ∧
      mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.ext_two_adic_generator
        bits = .fail .panic) := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.ext_two_adic_generator
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionHasTwoAdicBinomialExtension2.EXT_TWO_ADICITY
  rw [EXT_TWO_ADIC_GENERATORS.eq]
  by_cases h : bits.val ≤ 32
  · left
    have hb : bits ≤ 32#usize := by scalar_tac
    simp only [hb, massert, ite_true, bind_ok]
    step*
    refine ⟨h, ?_⟩
    rw [c_post1]
    exact extTable_order bits.val (by omega)
  · right
    refine ⟨by omega, ?_⟩
    have hb : ¬ bits ≤ 32#usize := by scalar_tac
    simp [hb, massert]

theorem circleTable_order (k : ℕ) (hk : k < 32) :
    orderOf (toComplex (circleTable.val[k]'(by rw [circleTable.property]; exact hk))) = 2 ^ k := by
  have hk' : k < (Mersenne31.twoAdicGeneratorCoeffs.take 32).length := by
    rw [List.length_take, coeffs_length]; omega
  rw [toComplex_of_vals circleTable _ circleTable_vals k hk hk']
  have hc : (Mersenne31.twoAdicGeneratorCoeffs.take 32)[k] =
      Mersenne31.twoAdicGeneratorCoeffs[k]'(by rw [coeffs_length]; omega) := List.getElem_take
  rw [hc]; exact coeffs_order k (by omega)

/-- `circle_two_adic_generator(bits)` returns an element of order `2^bits` for `bits ≤ 31`, and panics otherwise. -/
theorem circle_two_adic_generator.order (bits : Std.Usize) :
    complex.Mersenne31.circle_two_adic_generator bits
      ⦃ c => bits.val ≤ 31 ∧ orderOf (toComplex c) = 2 ^ bits.val ⦄ ∨
    (31 < bits.val ∧ complex.Mersenne31.circle_two_adic_generator bits = .fail .panic) := by
  unfold complex.Mersenne31.circle_two_adic_generator
  rw [CIRCLE_TWO_ADIC_GENERATORS.eq]
  by_cases h : bits.val ≤ 31
  · left
    have hb : bits ≤ 31#usize := by scalar_tac
    simp only [hb, massert, ite_true, bind_ok]
    step*
    refine ⟨h, ?_⟩
    rw [c_post1]
    exact circleTable_order bits.val (by omega)
  · right
    refine ⟨by omega, ?_⟩
    have hb : ¬ bits ≤ 31#usize := by scalar_tac
    simp [hb, massert]

theorem toComplex_pair (a b : Std.U32) :
    toComplex (Array.make 2#usize [e a, e b]) =
      Mersenne31.Complex.mk (a.val : Mersenne31.Field) (b.val : Mersenne31.Field) := rfl

theorem COMPLEX_GENERATOR.eq :
    complex.Mersenne31.COMPLEX_GENERATOR = .ok (Array.make 2#usize [e 12#u32, e 1#u32]) := by
  unfold complex.Mersenne31.COMPLEX_GENERATOR
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  simp (config := { decide := true }) only [new_eq, bind_ok]
  all_goals rfl

/-- `COMPLEX_GENERATOR` is `12 + i`, which generates the multiplicative group of `F[i]`. -/
theorem COMPLEX_GENERATOR.order :
    complex.Mersenne31.COMPLEX_GENERATOR ⦃ c =>
      orderOf (toComplex c) = Mersenne31.fieldSize ^ 2 - 1 ⦄ := by
  rw [COMPLEX_GENERATOR.eq, WP.spec_ok, toComplex_pair]
  exact Mersenne31.orderOf_mk_twelve_one

/-! ## Binomial extensions of `F[i]` -/

theorem QUADRATIC_W.toComplex :
    Spec.Mersenne31.toComplex extension.Mersenne31.QUADRATIC_W = Mersenne31.Complex.mk 2 1 := by
  unfold extension.Mersenne31.QUADRATIC_W
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.TWO
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  rfl

/-- `W = 2 + i` of the QM31 extension is not a square, so `Y^2 - W` is irreducible. -/
theorem QUADRATIC_W.irreducible :
    Irreducible (X ^ 2 - C (Spec.Mersenne31.toComplex extension.Mersenne31.QUADRATIC_W)) := by
  rw [QUADRATIC_W.toComplex]; exact Mersenne31.irreducible_qm31

/-- `DTH_ROOT` of the QM31 extension is `W^((p^2 - 1) / 2)`. -/
theorem QUADRATIC_DTH_ROOT.toComplex :
    extension.Mersenne31.QUADRATIC_DTH_ROOT ⦃ c => Spec.Mersenne31.toComplex c =
      Spec.Mersenne31.toComplex extension.Mersenne31.QUADRATIC_W ^
        ((Mersenne31.fieldSize ^ 2 - 1) / 2) ⦄ := by
  have h : extension.Mersenne31.QUADRATIC_DTH_ROOT =
      .ok (Array.make 2#usize [e 2147483646#u32, e 0#u32]) := by
    unfold extension.Mersenne31.QUADRATIC_DTH_ROOT
      mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    simp (config := { decide := true }) only [new_eq, bind_ok]
    all_goals rfl
  rw [h, WP.spec_ok, toComplex_pair, QUADRATIC_W.toComplex, Mersenne31.mk_two_one_pow_dth,
    ← Mersenne31.Complex.mk_neg_one]
  congr 1

theorem CUBIC_W.eq :
    extension.Mersenne31.CUBIC_W = .ok (Array.make 2#usize [e 0#u32, e 5#u32]) := by
  unfold extension.Mersenne31.CUBIC_W
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  simp (config := { decide := true }) only [new_eq, bind_ok]
  all_goals rfl

/-- `W = 5i` of the cubic extension of `F[i]` is not a cube, so `Y^3 - W` is irreducible. -/
theorem CUBIC_W.irreducible :
    extension.Mersenne31.CUBIC_W ⦃ w => Irreducible (X ^ 3 - C (Spec.Mersenne31.toComplex w)) ⦄ := by
  rw [CUBIC_W.eq, WP.spec_ok, toComplex_pair]
  exact Mersenne31.irreducible_complexExt3

/-- `DTH_ROOT` of the cubic extension of `F[i]` is `W^((p^2 - 1) / 3)`. -/
theorem CUBIC_DTH_ROOT.toComplex :
    extension.Mersenne31.CUBIC_DTH_ROOT ⦃ c => Spec.Mersenne31.toComplex c =
      Mersenne31.Complex.mk 0 5 ^ ((Mersenne31.fieldSize ^ 2 - 1) / 3) ⦄ := by
  have h : extension.Mersenne31.CUBIC_DTH_ROOT =
      .ok (Array.make 2#usize [e 634005911#u32, e 0#u32]) := by
    unfold extension.Mersenne31.CUBIC_DTH_ROOT
      mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    simp (config := { decide := true }) only [new_eq, bind_ok]
    all_goals rfl
  rw [h, WP.spec_ok, toComplex_pair, Mersenne31.mk_zero_five_pow_dth, Mersenne31.Complex.of_eq_mk]
  rfl

/-- `complex_ext_two_adic_generator(33)` has order `2^33` in QM31, and squares to the order-`2^32` generator of `F[i]`. -/
theorem QUADRATIC_EXT_TWO_ADIC_GENERATOR_33.order :
    extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33 ⦃ c =>
      orderOf (toQM31 c) = 2 ^ 33 ⦄ := by
  have h : extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33 =
      .ok (Array.make 2#usize [Array.make 2#usize [e 0#u32, e 0#u32],
        Array.make 2#usize [e 1437746044#u32, e 946469285#u32]]) := by
    unfold extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33
      mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    simp (config := { decide := true }) only [new_reduced_eq, bind_ok]
    all_goals rfl
  rw [h, WP.spec_ok]
  have hq : toQM31 (Array.make 2#usize [Array.make 2#usize [e 0#u32, e 0#u32],
      Array.make 2#usize [e 1437746044#u32, e 946469285#u32]]) = Mersenne31.qm31TwoAdicGenerator := by
    have h0 : Spec.Mersenne31.toComplex (Array.make 2#usize [e 0#u32, e 0#u32]) = 0 := by
      rw [toComplex_pair]; simp [Mersenne31.Complex.mk]
    unfold toQM31 Mersenne31.qm31TwoAdicGenerator
    rw [show (Array.make 2#usize [Array.make 2#usize [e 0#u32, e 0#u32],
        Array.make 2#usize [e 1437746044#u32, e 946469285#u32]]).val.getD 0
        (Array.repeat 2#usize ⟨0#u32⟩) = Array.make 2#usize [e 0#u32, e 0#u32] from rfl,
      show (Array.make 2#usize [Array.make 2#usize [e 0#u32, e 0#u32],
        Array.make 2#usize [e 1437746044#u32, e 946469285#u32]]).val.getD 1
        (Array.repeat 2#usize ⟨0#u32⟩) = Array.make 2#usize [e 1437746044#u32, e 946469285#u32] from rfl,
      h0, toComplex_pair, map_zero, zero_add]
    rfl
  rw [hq]; exact Mersenne31.orderOf_qm31TwoAdicGenerator

/-! ## The cubic extension of `F` -/

/-- `W = 5` of `BinomiallyExtendable<3>`: `5` is not a cube, so `X^3 - W` is irreducible. -/
theorem CUBIC_BASE_W.irreducible :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.W ⦃ w =>
      Canonical w ∧ Spec.Mersenne31.toField w = 5 ∧
        Irreducible (X ^ 3 - C (Spec.Mersenne31.toField w)) ⦄ := by
  have h : mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.W = .ok (e 5#u32) := by
    unfold mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.W
    simp (config := { decide := true }) only [new_eq]
  rw [h, WP.spec_ok]
  have h5 : Spec.Mersenne31.toField (e 5#u32) = 5 := by unfold Spec.Mersenne31.toField e; decide
  exact ⟨by unfold Canonical e; decide, h5, h5 ▸ Mersenne31.irreducible_ext3⟩

/-- `DTH_ROOT` of `BinomiallyExtendable<3>` is `W^((p - 1) / 3)`, a primitive cube root of unity. -/
theorem CUBIC_BASE_DTH_ROOT.toField :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.DTH_ROOT ⦃ d =>
      Canonical d ∧ Spec.Mersenne31.toField d = 5 ^ ((Mersenne31.fieldSize - 1) / 3) ∧
        Spec.Mersenne31.toField d ^ 3 = 1 ∧ Spec.Mersenne31.toField d ≠ 1 ⦄ := by
  have h : mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.DTH_ROOT =
      .ok (e 1513477735#u32) := by
    unfold mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.DTH_ROOT
    simp (config := { decide := true }) only [new_eq]
  rw [h, WP.spec_ok, Mersenne31.five_pow_div_three]
  have hd : Spec.Mersenne31.toField (e 1513477735#u32) = 1513477735 := by
    unfold Spec.Mersenne31.toField e; decide
  rw [hd]
  exact ⟨by unfold Canonical e; decide, rfl, Mersenne31.dthRoot3_cube⟩

/-- `EXT_GENERATOR` of `BinomiallyExtendable<3>` is `10 + X`, which generates the multiplicative group of `F[X] / (X^3 - 5)`. -/
theorem CUBIC_BASE_EXT_GENERATOR.order :
    mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.EXT_GENERATOR ⦃ g =>
      orderOf (toCubic g) = Mersenne31.fieldSize ^ 3 - 1 ⦄ := by
  have h : mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.EXT_GENERATOR =
      .ok (Array.make 3#usize [e 10#u32, e 1#u32, e 0#u32]) := by
    unfold mersenne_31.Mersenne31.Insts.P3_fieldExtensionBinomiallyExtendable3.EXT_GENERATOR
      mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
      mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    simp (config := { decide := true }) only [new_eq, bind_ok]
    all_goals rfl
  rw [h, WP.spec_ok]
  have hc : toCubic (Array.make 3#usize [e 10#u32, e 1#u32, e 0#u32]) =
      AdjoinRoot.mk (X ^ 3 - C (5 : Mersenne31.Field)) (CoeffList.toPoly [10, 1, 0]) := by
    unfold toCubic
    congr 2
  rw [hc]; exact Mersenne31.orderOf_ext3Generator

end Plonky3Lean.Proofs.P3Mersenne31
