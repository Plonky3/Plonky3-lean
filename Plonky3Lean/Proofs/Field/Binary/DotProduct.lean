module

public import Plonky3Lean.Proofs.Field.Binary.CantorSpec

@[expose] public section

/-!
# Dot products

Without a carry-less multiply, `dot_product` sums `u[i] * v[i]` with `iter().zip(v).map(mul)`
and `Sum`, which reduces the mapped iterator with `+`. `reduce_mapzip_spec` follows that
reduction through the model's `Map`, `Zip` and slice iterators, for any multiplication and
addition closures that compute a product and a sum in some ring.
-/

open Aeneas Aeneas.Std CoreModels
open ConcreteBinaryTower
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

variable {T M : Type} [CommRing M]

/-- The iterator `slice.iter().zip(other).map(f)`. -/
abbrev MapZip (T F : Type) :=
  CoreModels.core.iter.adapters.map.Map
    (CoreModels.core.iter.adapters.zip.Zip (CoreModels.core.slice.iter.Iter T) (CoreModels.core.slice.iter.Iter T)) F

/-- Its `Iterator` dictionary. -/
abbrev mapZipInst {F : Type} (mulInst : CoreModels.core.ops.function.FnMut F (T × T) T) :
    CoreModels.core.iter.traits.iterator.Iterator (MapZip T F) T :=
  CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)) mulInst

/-- The sum of the products of matching entries. -/
def dotList (φ : T → M) : List T → List T → M
  | a :: us, b :: vs => φ a * φ b + dotList φ us vs
  | _, _ => 0

theorem slice_next_cons {T : Type} (s : CoreModels.core.slice.iter.Iter T) {x : T} {xs : List T}
    (h : iterList s = x :: xs) :
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s =
      .ok (.Some x, iterOf xs (by
        have := s.property; simp [iterList] at h; simp [h] at this; omega)) :=
  slice_iter_next_cons s h

theorem slice_inst_next_cons {T : Type} (s : CoreModels.core.slice.iter.Iter T) {x : T}
    {xs : List T} (h : iterList s = x :: xs) (hl : xs.length ≤ Usize.max) :
    (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T).next s =
      .ok (.Some x, iterOf xs hl) :=
  slice_iter_next_cons s h

theorem mapZip_next_cons (φ : T → M) {F : Type} (mulInst : CoreModels.core.ops.function.FnMut F (T × T) T)
    (f : F) (hmul : ∀ a b, mulInst.call_mut f (a, b) ⦃ p => p.2 = f ∧ φ p.1 = φ a * φ b ⦄)
    (it : MapZip T F) (hf : it.f = f) {a b : T} {us vs : List T}
    (h1 : iterList it.iter.it1 = a :: us) (h2 : iterList it.iter.it2 = b :: vs) :
    (mapZipInst mulInst).next it ⦃ p => ∃ c, p.1 = .Some c ∧ φ c = φ a * φ b ∧
      iterList p.2.iter.it1 = us ∧ iterList p.2.iter.it2 = vs ∧ p.2.f = f ⦄ := by
  have hl1 : us.length ≤ Usize.max := by
    have := it.iter.it1.property; simp [iterList] at h1; simp [h1] at this; omega
  have hl2 : vs.length ≤ Usize.max := by
    have := it.iter.it2.property; simp [iterList] at h2; simp [h2] at this; omega
  have e : (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)).next it.iter =
      .ok (.Some (a, b), { it1 := iterOf us hl1, it2 := iterOf vs hl2 }) := by
    show CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next _ _ _ = _
    unfold CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    rw [slice_inst_next_cons _ h1 hl1, slice_inst_next_cons _ h2 hl2]
    simp only [Aeneas.Std.bind_ok]
    rfl
  show CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next _ _ it ⦃ _ ⦄
  unfold CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  rw [e, hf]
  simp only [Aeneas.Std.bind_ok]
  apply WP.spec_bind (hmul a b)
  rintro ⟨c, f'⟩ ⟨hf', hc⟩
  simp only at hf' hc
  show RustM.ok (CoreModels.core.option.Option.Some c,
    ({ iter := { it1 := iterOf us hl1, it2 := iterOf vs hl2 }, f := f' } : MapZip T F)) ⦃ _ ⦄
  rw [WP.spec_ok]
  exact ⟨c, rfl, hc, iterList_iterOf _ _, iterList_iterOf _ _, hf'⟩

theorem mapZip_next_nil {F : Type} (mulInst : CoreModels.core.ops.function.FnMut F (T × T) T)
    (it : MapZip T F) (h1 : iterList it.iter.it1 = []) :
    (mapZipInst mulInst).next it ⦃ p => p.1 = .None ⦄ := by
  show CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next _ _ it ⦃ _ ⦄
  unfold CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  have e : (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)).next it.iter =
      .ok (.None, { it1 := it.iter.it1, it2 := it.iter.it2 }) := by
    show CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next _ _ _ = _
    unfold CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    rw [show (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T).next
      it.iter.it1 = .ok (.None, it.iter.it1) from slice_iter_next_nil _ h1]
    simp only [Aeneas.Std.bind_ok]
    rfl
  rw [e]
  simp only [Aeneas.Std.bind_ok]
  exact (WP.spec_ok _).mpr rfl

variable (φ : T → M) {F G : Type} (mulInst : CoreModels.core.ops.function.FnMut F (T × T) T)
  (f : F) (hmul : ∀ a b, mulInst.call_mut f (a, b) ⦃ p => p.2 = f ∧ φ p.1 = φ a * φ b ⦄)
  (addInst : CoreModels.core.ops.function.FnMut G (T × T) T) (g : G)
  (hadd : ∀ a b, addInst.call_mut g (a, b) ⦃ p => p.2 = g ∧ φ p.1 = φ a + φ b ⦄)

include hmul hadd in
theorem reduce_mapzip_loop_spec (it : MapZip T F) (acc : T) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    CoreModels.core.iter.traits.iterator.iter_reduce_loop (mapZipInst mulInst) addInst it g acc
      ⦃ r => φ r = φ acc + dotList φ (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold CoreModels.core.iter.traits.iterator.iter_reduce_loop
  refine loop.spec_decr_nat (fun s => (iterList s.1.iter.it1).length)
    (fun s => s.1.f = f ∧ s.2.1 = g ∧
      (iterList s.1.iter.it1).length = (iterList s.1.iter.it2).length ∧
      φ acc + dotList φ (iterList it.iter.it1) (iterList it.iter.it2) =
        φ s.2.2 + dotList φ (iterList s.1.iter.it1) (iterList s.1.iter.it2)) _ _ _ ?_
    ⟨hf, rfl, hlen, rfl⟩
  rintro ⟨it', g', acc'⟩ ⟨hf', hg', hl', hsum⟩
  dsimp only at hf' hg' hl' hsum ⊢
  subst hg'
  unfold CoreModels.core.iter.traits.iterator.iter_reduce_loop.body
  rcases h1 : iterList it'.iter.it1 with _ | ⟨a, us⟩
  · apply WP.spec_bind (mapZip_next_nil mulInst it' h1)
    rintro ⟨o, it''⟩ ho
    dsimp only at ho ⊢
    subst ho
    refine (WP.spec_ok _).mpr ?_
    show φ acc' = _
    rw [hsum, h1]
    simp [dotList]
  · rcases h2 : iterList it'.iter.it2 with _ | ⟨b, vs⟩
    · rw [h1, h2] at hl'; simp at hl'
    · apply WP.spec_bind (mapZip_next_cons φ mulInst f hmul it' hf' h1 h2)
      rintro ⟨o, it''⟩ ⟨c, hc, hφc, hu, hv, hf''⟩
      dsimp only at hc hu hv hf'' ⊢
      subst hc
      show (do
        let (accum1, f1) ← addInst.call_mut g' (acc', c)
        RustM.ok (ControlFlow.cont (it'', f1, accum1))) ⦃ _ ⦄
      apply WP.spec_bind (hadd acc' c)
      rintro ⟨acc'', g''⟩ ⟨hg'', hacc''⟩
      dsimp only at hg'' hacc''
      refine (WP.spec_ok _).mpr ?_
      refine ⟨⟨hf'', hg'', ?_, ?_⟩, ?_⟩
      · rw [hu, hv]; rw [h1, h2] at hl'; simpa using hl'
      · rw [hsum, h1, h2, hu, hv, hacc'', hφc, dotList]; ring
      · rw [hu]; simp

include hmul hadd in
/-- Reducing `zip(…).map(mul)` with `add` gives the dot product, or `None` for no entries. -/
theorem reduce_mapzip_spec (it : MapZip T F) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    CoreModels.core.iter.traits.iterator.iter_reduce (mapZipInst mulInst) addInst it g ⦃ o =>
      (iterList it.iter.it1 = [] → o = .None) ∧
      (iterList it.iter.it1 ≠ [] →
        ∃ s, o = .Some s ∧ φ s = dotList φ (iterList it.iter.it1) (iterList it.iter.it2)) ⦄ := by
  unfold CoreModels.core.iter.traits.iterator.iter_reduce
  rcases h1 : iterList it.iter.it1 with _ | ⟨a, us⟩
  · apply WP.spec_bind (mapZip_next_nil mulInst it h1)
    rintro ⟨o, it'⟩ ho
    dsimp only at ho
    subst ho
    refine (WP.spec_ok _).mpr ⟨fun _ => rfl, fun h => absurd rfl h⟩
  · rcases h2 : iterList it.iter.it2 with _ | ⟨b, vs⟩
    · rw [h1, h2] at hlen; simp at hlen
    · apply WP.spec_bind (mapZip_next_cons φ mulInst f hmul it hf h1 h2)
      rintro ⟨o, it'⟩ ⟨c, hc, hφc, hu, hv, hf'⟩
      dsimp only at hc hu hv hf'
      subst hc
      show (do
        let accum ← CoreModels.core.iter.traits.iterator.iter_reduce_loop (mapZipInst mulInst)
          addInst it' g c
        RustM.ok (CoreModels.core.option.Option.Some accum)) ⦃ _ ⦄
      apply WP.spec_bind (reduce_mapzip_loop_spec φ mulInst f hmul addInst g hadd it' c hf'
        (by rw [hu, hv]; rw [h1, h2] at hlen; simpa using hlen))
      intro r hr
      refine (WP.spec_ok _).mpr ⟨fun h => absurd h (by simp), fun _ => ⟨r, rfl, ?_⟩⟩
      rw [hr, hu, hv, hφc, dotList]

/-! ## `GF(2^32)` -/

theorem bf32_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField32 N) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 5 r = dotList (towerOf 5) u.val v.val ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField32.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField32.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField32Shared1BinaryField32BinaryField32
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 5 p.1 = towerOf 5 a * towerOf 5 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField32.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField32Shared1BinaryField32BinaryField32.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField32.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField32Shared1BinaryField32BinaryField32.call_mut
    exact WP.spec_bind (bf32_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 5 a * towerOf 5 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField32.Insts.CoreIterTraitsAccumSumBinaryField32.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 5) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField32BinaryField32.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField32BinaryField32BinaryField32.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField32.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField32Shared1BinaryField32BinaryField32
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField32BinaryField32.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField32BinaryField32BinaryField32.call_mut
        exact WP.spec_bind (bf32_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^2)` -/

theorem bf2_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField2 N) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 1 r = dotList (towerOf 1) u.val v.val ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField2.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField2.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField2Shared1BinaryField2BinaryField2
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 1 p.1 = towerOf 1 a * towerOf 1 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField2.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField2Shared1BinaryField2BinaryField2.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField2.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField2Shared1BinaryField2BinaryField2.call_mut
    exact WP.spec_bind (bf2_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 1 a * towerOf 1 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField2.Insts.CoreIterTraitsAccumSumBinaryField2.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 1) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField2BinaryField2.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField2BinaryField2BinaryField2.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField2.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField2Shared1BinaryField2BinaryField2
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField2BinaryField2.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField2BinaryField2BinaryField2.call_mut
        exact WP.spec_bind (bf2_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^4)` -/

theorem bf4_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField4 N) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 2 r = dotList (towerOf 2) u.val v.val ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField4.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField4.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField4Shared1BinaryField4BinaryField4
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 2 p.1 = towerOf 2 a * towerOf 2 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField4.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField4Shared1BinaryField4BinaryField4.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField4.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField4Shared1BinaryField4BinaryField4.call_mut
    exact WP.spec_bind (bf4_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 2 a * towerOf 2 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField4.Insts.CoreIterTraitsAccumSumBinaryField4.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 2) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField4BinaryField4.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField4BinaryField4BinaryField4.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField4.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField4Shared1BinaryField4BinaryField4
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField4BinaryField4.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField4BinaryField4BinaryField4.call_mut
        exact WP.spec_bind (bf4_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^8)` -/

theorem bf8_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField8 N) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 3 r = dotList (towerOf 3) u.val v.val ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField8.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField8.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField8Shared1BinaryField8BinaryField8
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 3 p.1 = towerOf 3 a * towerOf 3 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField8.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField8Shared1BinaryField8BinaryField8.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField8.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField8Shared1BinaryField8BinaryField8.call_mut
    exact WP.spec_bind (bf8_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 3 a * towerOf 3 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField8.Insts.CoreIterTraitsAccumSumBinaryField8.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 3) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField8BinaryField8.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField8BinaryField8BinaryField8.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField8.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField8Shared1BinaryField8BinaryField8
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField8BinaryField8.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField8BinaryField8BinaryField8.call_mut
        exact WP.spec_bind (bf8_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^16)` -/

theorem bf16_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField16 N) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 4 r = dotList (towerOf 4) u.val v.val ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField16.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField16.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField16Shared1BinaryField16BinaryField16
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 4 p.1 = towerOf 4 a * towerOf 4 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField16.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField16Shared1BinaryField16BinaryField16.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField16.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField16Shared1BinaryField16BinaryField16.call_mut
    exact WP.spec_bind (bf16_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 4 a * towerOf 4 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField16.Insts.CoreIterTraitsAccumSumBinaryField16.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 4) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField16BinaryField16.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField16BinaryField16BinaryField16.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField16.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField16Shared1BinaryField16BinaryField16
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField16BinaryField16.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField16BinaryField16BinaryField16.call_mut
        exact WP.spec_bind (bf16_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^64)` -/

theorem bf64_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField64 N) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 6 r = dotList (towerOf 6) u.val v.val ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField64.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField64.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField64Shared1BinaryField64BinaryField64
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 6 p.1 = towerOf 6 a * towerOf 6 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField64.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField64Shared1BinaryField64BinaryField64.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField64.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField64Shared1BinaryField64BinaryField64.call_mut
    exact WP.spec_bind (bf64_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 6 a * towerOf 6 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField64.Insts.CoreIterTraitsAccumSumBinaryField64.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 6) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField64BinaryField64.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField64BinaryField64BinaryField64.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField64.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField64Shared1BinaryField64BinaryField64
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField64BinaryField64.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField64BinaryField64BinaryField64.call_mut
        exact WP.spec_bind (bf64_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `GF(2^128)` -/

theorem bf128_dot_product_spec {N : Std.Usize} (u v : Std.Array tower.BinaryField128 N) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      towerOf 7 r = dotList (towerOf 7) u.val v.val ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte]
  have hmul : ∀ (c : tower.PrimeCharacteristicRingBinaryField128.dot_product.closure_3 N) a b,
      (tower.PrimeCharacteristicRingBinaryField128.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField128Shared1BinaryField128BinaryField128
        N).call_mut c (a, b) ⦃ p => p.2 = c ∧ towerOf 7 p.1 = towerOf 7 a * towerOf 7 b ⦄ := by
    intro c a b
    show tower.PrimeCharacteristicRingBinaryField128.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField128Shared1BinaryField128BinaryField128.call_mut c (a, b) ⦃ _ ⦄
    unfold tower.PrimeCharacteristicRingBinaryField128.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField128Shared1BinaryField128BinaryField128.call_mut
    exact WP.spec_bind (bf128_mul_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_mul h⟩
  have hlu := u.property
  have hlv := v.property
  split
  · rename_i hN
    have hN' : N.val = 0 := by rw [hN]; rfl
    have hu : u.val = [] := List.eq_nil_of_length_eq_zero (by rw [hlu, hN'])
    refine (WP.spec_ok _).mpr ?_
    rw [hu]
    show _ = 0
    unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    apply ConcreteBTField.toNat_injective
    rw [towerOf, ConcreteBTField.toNat_fromNat]
    rfl
  · split
    · rename_i hN0 hN1
      have hN' : N.val = 1 := by rw [hN1]; rfl
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show u.val.length = 1 by rw [hlu, hN'])
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show v.val.length = 1 by rw [hlv, hN'])
      have hua : u.val[0]'(by rw [ha]; simp) = a := by simp [ha]
      have hvb : v.val[0]'(by rw [hb]; simp) = b := by simp [hb]
      step*
      rw [ha, hb]
      show _ = towerOf 7 a * towerOf 7 b + 0
      rw [add_zero, towerOf_mul r_post, bf_post1, bf1_post1]
      simp [ha, hb]
    · rename_i hN0 hN1
      rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
      unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
        core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        CoreModels.core.iter.adapters.zip.Zip.new
        CoreModels.core.iter.traits.iterator.Iterator.map.default
        CoreModels.core.iter.adapters.map.Map.new
        core.iter.traits.iterator.Iterator.sum.default
      simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
      unfold tower.BinaryField128.Insts.CoreIterTraitsAccumSumBinaryField128.sum
        core.iter.traits.iterator.Iterator.reduce
        CoreModels.core.iter.traits.iterator.Iterator.reduce.default
      have hN2 : 2 ≤ N.val := by
        have h0 : N.val ≠ 0 := fun h => hN0 (UScalar.eq_of_val_eq h)
        have h1 : N.val ≠ 1 := fun h => hN1 (UScalar.eq_of_val_eq h)
        omega
      apply WP.spec_bind (reduce_mapzip_spec (towerOf 7) _ () (hmul ()) _ () ?_ _ rfl
        (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
      · rintro o ⟨-, ho⟩
        obtain ⟨s, rfl, hs⟩ := ho (by
          intro h
          have := congrArg List.length h
          simp [iterList_iterOfSlice, Std.Array.to_slice, hlu] at this
          omega)
        refine (WP.spec_ok _).mpr ?_
        simpa [iterList_iterOfSlice, Std.Array.to_slice] using hs
      · intro a b
        show tower.SumBinaryField128BinaryField128.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField128BinaryField128BinaryField128.call_mut
          (mapZipInst (tower.PrimeCharacteristicRingBinaryField128.dot_product.closure_3.Insts.CoreOpsFunctionFnMutTuplePairShared0BinaryField128Shared1BinaryField128BinaryField128
            N)) () (a, b) ⦃ _ ⦄
        unfold tower.SumBinaryField128BinaryField128.sum.closure.Insts.CoreOpsFunctionFnMutPairBinaryField128BinaryField128BinaryField128.call_mut
        exact WP.spec_bind (bf128_add_spec a b) fun r h => (WP.spec_ok _).mpr ⟨rfl, towerOf_add h⟩

/-! ## `Poly64` -/

theorem mapZip_next_cons_pair {F : Type}
    (pairInst : CoreModels.core.ops.function.FnMut F (T × T) (T × T)) (f : F)
    (hpair : ∀ a b, pairInst.call_mut f (a, b) = .ok ((a, b), f))
    (it : MapZip T F) (hf : it.f = f) {a b : T} {us vs : List T}
    (h1 : iterList it.iter.it1 = a :: us) (h2 : iterList it.iter.it2 = b :: vs) :
    ∃ it' : MapZip T F, (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T))
      pairInst).next it = .ok (.Some (a, b), it') ∧
      iterList it'.iter.it1 = us ∧ iterList it'.iter.it2 = vs ∧ it'.f = f := by
  have hl1 : us.length ≤ Usize.max := by
    have := it.iter.it1.property; simp [iterList] at h1; simp [h1] at this; omega
  have hl2 : vs.length ≤ Usize.max := by
    have := it.iter.it2.property; simp [iterList] at h2; simp [h2] at this; omega
  have e : (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)).next it.iter =
      .ok (.Some (a, b), { it1 := iterOf us hl1, it2 := iterOf vs hl2 }) := by
    show CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next _ _ _ = _
    unfold CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    rw [slice_inst_next_cons _ h1 hl1, slice_inst_next_cons _ h2 hl2]
    simp only [Aeneas.Std.bind_ok]
    rfl
  refine ⟨{ iter := { it1 := iterOf us hl1, it2 := iterOf vs hl2 }, f := f }, ?_,
    iterList_iterOf _ _, iterList_iterOf _ _, rfl⟩
  show CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next _ _ it = _
  unfold CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  rw [e, hf]
  simp only [Aeneas.Std.bind_ok]
  show (do
    let (t1, t2) ← pairInst.call_mut f (a, b)
    RustM.ok (CoreModels.core.option.Option.Some t1,
      ({ iter := { it1 := iterOf us hl1, it2 := iterOf vs hl2 }, f := t2 } : MapZip T F))) = _
  rw [hpair]
  simp only [Aeneas.Std.bind_tc_ok]

theorem mapZip_next_nil_pair {F : Type}
    (pairInst : CoreModels.core.ops.function.FnMut F (T × T) (T × T))
    (it : MapZip T F) (h1 : iterList it.iter.it1 = []) :
    (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T))
      pairInst).next it = .ok (.None, it) := by
  show CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next _ _ it = _
  unfold CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  have e : (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)).next it.iter =
      .ok (.None, it.iter) := by
    show CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next _ _ _ = _
    unfold CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    rw [show (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T).next
      it.iter.it1 = .ok (.None, it.iter.it1) from slice_iter_next_nil _ h1]
    simp only [Aeneas.Std.bind_ok]
    rfl
  rw [e]
  simp only [Aeneas.Std.bind_ok]
  rfl

/-- The sum of the carry-less products of matching entries, as a polynomial. -/
noncomputable def polyDot : List Std.U64 → List Std.U64 → Polynomial (ZMod 2)
  | a :: us, b :: vs => natPoly a.val * natPoly b.val + polyDot us vs
  | _, _ => 0

/-- The `Iterator` dictionary of `zip(…).map(|(a, b)| (a, b))` in `Poly64::dot_product`. -/
abbrev poly64PairInst (N : Std.Usize) :
    CoreModels.core.iter.traits.iterator.Iterator
      (MapZip Std.U64 (poly64.PrimeCharacteristicRingPoly64.dot_product.closure N)) (Std.U64 × Std.U64) :=
  CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64)
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64))
    (poly64.PrimeCharacteristicRingPoly64.dot_product.closure.Insts.CoreOpsFunctionFnMutTuplePairShared0Poly64Shared1Poly64PairU64U64
      N)

theorem poly64_dot_fold_spec {N : Std.Usize}
    (it : MapZip Std.U64 (poly64.PrimeCharacteristicRingPoly64.dot_product.closure N))
    (c : clmul.gf64.composed_dot_64.closure
      (MapZip Std.U64 (poly64.PrimeCharacteristicRingPoly64.dot_product.closure N)))
    (acc : Std.U128) (hf : it.f = ())
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    CoreModels.core.iter.traits.iterator.iter_fold_loop (poly64PairInst N)
      (clmul.gf64.composed_dot_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128
        (poly64PairInst N)) it c acc ⦃ r =>
      natPoly r.val = natPoly acc.val + polyDot (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold CoreModels.core.iter.traits.iterator.iter_fold_loop
  refine loop.spec_decr_nat (fun s => (iterList s.1.iter.it1).length)
    (fun s => s.1.f = () ∧
      (iterList s.1.iter.it1).length = (iterList s.1.iter.it2).length ∧
      natPoly acc.val + polyDot (iterList it.iter.it1) (iterList it.iter.it2) =
        natPoly s.2.2.val + polyDot (iterList s.1.iter.it1) (iterList s.1.iter.it2)) _ _ _ ?_
    ⟨hf, hlen, rfl⟩
  rintro ⟨it', c', acc'⟩ ⟨hf', hl', hsum⟩
  dsimp only at hf' hl' hsum ⊢
  unfold CoreModels.core.iter.traits.iterator.iter_fold_loop.body
  rcases h1 : iterList it'.iter.it1 with _ | ⟨a, us⟩
  · rw [mapZip_next_nil_pair _ it' h1]
    simp only [Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).mpr ?_
    show natPoly acc'.val = _
    rw [hsum, h1]
    exact (_root_.add_zero _).symm
  · rcases h2 : iterList it'.iter.it2 with _ | ⟨b, vs⟩
    · rw [h1, h2] at hl'; simp at hl'
    · obtain ⟨it'', e, hu, hv, hf''⟩ := mapZip_next_cons_pair
        (poly64.PrimeCharacteristicRingPoly64.dot_product.closure.Insts.CoreOpsFunctionFnMutTuplePairShared0Poly64Shared1Poly64PairU64U64
          N) () (fun _ _ => rfl) it' hf' h1 h2
      rw [e]
      simp only [Aeneas.Std.bind_ok]
      have hc : clmul.gf64.composed_dot_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128.call_mut
          (poly64PairInst N) c' (acc', (a, b)) = .ok (acc' ^^^ clmulVal a b, c') := by
        unfold clmul.gf64.composed_dot_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128.call_mut
        simp only [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok, lift_eq]
        rfl
      show (do
        let (accum1, f1) ←
          clmul.gf64.composed_dot_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128.call_mut
            (poly64PairInst N) c' (acc', (a, b))
        RustM.ok (ControlFlow.cont (it'', f1, accum1))) ⦃ _ ⦄
      rw [hc]
      simp only [Aeneas.Std.bind_ok]
      refine (WP.spec_ok _).mpr ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · rw [hu, hv]; rw [h1, h2] at hl'; simpa using hl'
      · rw [hsum, h1, h2, hu, hv, UScalar.val_xor, natPoly_xor, natPoly_clmulVal, polyDot]
        ring
      · rw [hu]; simp

theorem mk_polyDot : ∀ us vs : List Std.U64,
    AdjoinRoot.mk BF64.basePoly (polyDot us vs) = dotList toQuot64 us vs
  | a :: us, b :: vs => by
    rw [polyDot, dotList, map_add, map_mul, mk_polyDot us vs, toQuot64_eq, toQuot64_eq]
  | [], _ => by simp [polyDot, dotList]
  | _ :: _, [] => by simp [polyDot, dotList]

theorem toQuot_dotList_bf64 : ∀ us vs : List Std.U64,
    BF64.toQuot (dotList bf64 us vs) = dotList toQuot64 us vs
  | a :: us, b :: vs => by
    rw [dotList, dotList, BF64.toQuot_add, BF64.toQuot_mul, toQuot_dotList_bf64 us vs]; rfl
  | [], _ => by simp [dotList, BF64.toQuot_zero]
  | _ :: _, [] => by simp [dotList, BF64.toQuot_zero]

/-- `Poly64::dot_product` is the dot product in `GF(2^64)`. -/
theorem poly64_dot_product_spec {N : Std.Usize} (u v : Std.Array poly64.Poly64 N) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product u v ⦃ r =>
      bf64 r = dotList bf64 u.val v.val ⦄ := by
  have hlu := u.property
  have hlv := v.property
  unfold poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok]
  unfold CoreModels.core.iter.traits.iterator.Iterator.zip.default
    core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter
    core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    CoreModels.core.iter.adapters.zip.Zip.new
    CoreModels.core.iter.traits.iterator.Iterator.map.default
    CoreModels.core.iter.adapters.map.Map.new
    clmul.gf64.poly_dot_64 clmul.gf64.composed_dot_64
    core.iter.traits.iterator.Iterator.fold
    CoreModels.core.iter.traits.iterator.Iterator.fold.default
    CoreModels.core.iter.traits.iterator.iter_fold
  simp only [Aeneas.Std.bind_ok, array_as_slice_eq, slice_iter_eq]
  rw [Aeneas.Std.bind_assoc]
  apply WP.spec_bind (poly64_dot_fold_spec _ () 0#u128 rfl
    (by simp [iterList_iterOfSlice, Std.Array.to_slice, hlu, hlv]))
  intro p hp
  rw [reduce_64_eq, Aeneas.Std.bind_ok, WP.spec_ok]
  apply BF64.toQuot_injective
  rw [toQuot_dotList_bf64, toQuot_bf64, toQuot64_eq, val_ofNat_64 (reduce64Nat_lt _),
    mk_natPoly_reduce64Nat (u128_val_lt _), hp, ← mk_polyDot]
  simp [iterList_iterOfSlice, Std.Array.to_slice, natPoly_zero]

/-! ## Folding `zip(…).map(pair)` -/

/-- `Σ_i ψ (us i) (vs i)`. -/
def sumList {N : Type} [AddCommMonoid N] (ψ : T → T → N) : List T → List T → N
  | a :: us, b :: vs => ψ a b + sumList ψ us vs
  | _, _ => 0

theorem fold_mapzip_spec {B N F G : Type} [AddCommMonoid N] (φ : B → N) (ψ : T → T → N)
    (pairInst : CoreModels.core.ops.function.FnMut F (T × T) (T × T)) (f : F)
    (hpair : ∀ a b, pairInst.call_mut f (a, b) = .ok ((a, b), f))
    (foldInst : CoreModels.core.ops.function.FnMut G (B × (T × T)) B) (g : G)
    (hfold : ∀ acc a b, foldInst.call_mut g (acc, (a, b)) ⦃ p => p.2 = g ∧ φ p.1 = φ acc + ψ a b ⦄)
    (it : MapZip T F) (acc : B) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    CoreModels.core.iter.traits.iterator.iter_fold_loop
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T))
        pairInst) foldInst it g acc ⦃ r =>
      φ r = φ acc + sumList ψ (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold CoreModels.core.iter.traits.iterator.iter_fold_loop
  refine loop.spec_decr_nat (fun s => (iterList s.1.iter.it1).length)
    (fun s => s.1.f = f ∧ s.2.1 = g ∧
      (iterList s.1.iter.it1).length = (iterList s.1.iter.it2).length ∧
      φ acc + sumList ψ (iterList it.iter.it1) (iterList it.iter.it2) =
        φ s.2.2 + sumList ψ (iterList s.1.iter.it1) (iterList s.1.iter.it2)) _ _ _ ?_
    ⟨hf, rfl, hlen, rfl⟩
  rintro ⟨it', g', acc'⟩ ⟨hf', hg', hl', hsum⟩
  dsimp only at hf' hg' hl' hsum ⊢
  subst hg'
  unfold CoreModels.core.iter.traits.iterator.iter_fold_loop.body
  rcases h1 : iterList it'.iter.it1 with _ | ⟨a, us⟩
  · rw [mapZip_next_nil_pair _ it' h1]
    simp only [Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).mpr ?_
    show φ acc' = _
    rw [hsum, h1]
    exact (_root_.add_zero _).symm
  · rcases h2 : iterList it'.iter.it2 with _ | ⟨b, vs⟩
    · rw [h1, h2] at hl'; simp at hl'
    · obtain ⟨it'', e, hu, hv, hf''⟩ := mapZip_next_cons_pair pairInst f hpair it' hf' h1 h2
      rw [e]
      simp only [Aeneas.Std.bind_ok]
      show (do
        let (accum1, f1) ← foldInst.call_mut g' (acc', (a, b))
        RustM.ok (ControlFlow.cont (it'', f1, accum1))) ⦃ _ ⦄
      apply WP.spec_bind (hfold acc' a b)
      rintro ⟨acc'', g''⟩ ⟨hg'', hacc''⟩
      dsimp only at hg'' hacc''
      refine (WP.spec_ok _).mpr ⟨⟨hf'', hg'', ?_, ?_⟩, ?_⟩
      · rw [hu, hv]; rw [h1, h2] at hl'; simpa using hl'
      · rw [hsum, h1, h2, hu, hv, hacc'', sumList, ← _root_.add_assoc]
      · rw [hu]; simp

theorem hom_dotList {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) (φ : T → R) :
    ∀ us vs : List T, ρ (dotList φ us vs) = sumList (fun a b => ρ (φ a) * ρ (φ b)) us vs
  | a :: us, b :: vs => by rw [dotList, sumList, map_add, map_mul, hom_dotList ρ φ us vs]
  | [], _ => by simp [dotList, sumList]
  | _ :: _, [] => by simp [dotList, sumList]

/-- The carry-less `dot_product_64` on `u.iter().zip(v).map(…)` is the dot product. -/
theorem clmul_dot_product_64_spec {F : Type}
    (pairInst : CoreModels.core.ops.function.FnMut F (Std.U64 × Std.U64) (Std.U64 × Std.U64))
    (f : F) (hpair : ∀ a b, pairInst.call_mut f (a, b) = .ok ((a, b), f))
    (it : MapZip Std.U64 F) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    clmul.dot_product_64
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64))
        pairInst) it ⦃ r =>
      towerOf 6 r = dotList (towerOf 6) (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold clmul.dot_product_64 core.iter.traits.iterator.Iterator.fold
    CoreModels.core.iter.traits.iterator.Iterator.fold.default
    CoreModels.core.iter.traits.iterator.iter_fold
  apply WP.spec_bind (fold_mapzip_spec (fun acc : Std.U128 =>
      AdjoinRoot.mk (modPoly 64 27) (natPoly acc.val))
    (fun a b => N64 (towerOf 6 a) * N64 (towerOf 6 b)) pairInst f hpair _ () ?_ it 0#u128 hf hlen)
  · intro p hp
    rw [reduce_64_eq, Aeneas.Std.bind_ok]
    apply WP.spec_mono (poly_to_tower_64_spec _)
    intro r hr
    apply N64_injective
    rw [N64_apply, hr, val_ofNat_64 (reduce64Nat_lt _), mk_modPoly_64_iff.mpr
      (mk_natPoly_reduce64Nat (u128_val_lt _)), hp, hom_dotList]
    simp [natPoly_zero]
  · intro acc a b
    show clmul.dot_product_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128.call_mut
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U64))
        pairInst) () (acc, (a, b)) ⦃ _ ⦄
    unfold clmul.dot_product_64.closure.Insts.CoreOpsFunctionFnMutPairU128PairU64U64U128.call_mut
    apply WP.spec_bind (tower_to_poly_64_spec a)
    intro pa ha
    apply WP.spec_bind (tower_to_poly_64_spec b)
    intro pb hb
    rw [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok]
    simp only [lift_eq, Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).mpr ⟨trivial, ?_⟩
    show AdjoinRoot.mk _ (natPoly (acc ^^^ clmulVal pa pb).val) = _
    rw [UScalar.val_xor, natPoly_xor, map_add, natPoly_clmulVal, map_mul, ha, hb, N64_apply,
      N64_apply]

/-- The carry-less `dot_product_128` on `u.iter().zip(v).map(…)` is the dot product. -/
theorem clmul_dot_product_128_spec {F : Type}
    (pairInst : CoreModels.core.ops.function.FnMut F (Std.U128 × Std.U128) (Std.U128 × Std.U128))
    (f : F) (hpair : ∀ a b, pairInst.call_mut f (a, b) = .ok ((a, b), f))
    (it : MapZip Std.U128 F) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    clmul.dot_product_128
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U128)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U128))
        pairInst) it ⦃ r =>
      towerOf 7 r = dotList (towerOf 7) (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold clmul.dot_product_128 core.iter.traits.iterator.Iterator.fold
    CoreModels.core.iter.traits.iterator.Iterator.fold.default
    CoreModels.core.iter.traits.iterator.iter_fold
  apply WP.spec_bind (fold_mapzip_spec (fun acc : Std.U128 × Std.U128 =>
      AdjoinRoot.mk (modPoly 128 135) (natPoly acc.1.val + Polynomial.X ^ 128 * natPoly acc.2.val))
    (fun a b => N128 (towerOf 7 a) * N128 (towerOf 7 b)) pairInst f hpair _ () ?_ it
    (0#u128, 0#u128) hf hlen)
  · rintro ⟨low, high⟩ hp
    dsimp only at hp ⊢
    apply WP.spec_bind (reduce_128_toQuot low high)
    intro i hi
    apply WP.spec_mono (poly_to_tower_128_spec i)
    intro r hr
    apply N128_injective
    rw [toQuot_eq_mk, ← mk_modPoly_128_iff] at hi
    rw [N128_apply, hr, hi, hp, hom_dotList]
    simp [natPoly_zero]
  · intro acc a b
    show clmul.dot_product_128.closure.Insts.CoreOpsFunctionFnMutPairPairU128U128PairU128U128PairU128U128.call_mut
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U128)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U128))
        pairInst) () (acc, (a, b)) ⦃ _ ⦄
    unfold clmul.dot_product_128.closure.Insts.CoreOpsFunctionFnMutPairPairU128U128PairU128U128PairU128U128.call_mut
    obtain ⟨low, high⟩ := acc
    apply WP.spec_bind (tower_to_poly_128_spec a)
    intro pa ha
    apply WP.spec_bind (tower_to_poly_128_spec b)
    intro pb hb
    apply WP.spec_bind (clmul_128x128_spec pa pb)
    rintro ⟨lo, hi⟩ hlh
    dsimp only at hlh ⊢
    simp only [lift_eq, Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).mpr ⟨trivial, ?_⟩
    show AdjoinRoot.mk _ (natPoly (low ^^^ lo).val + Polynomial.X ^ 128 * natPoly (high ^^^ hi).val) = _
    rw [UScalar.val_xor, UScalar.val_xor, natPoly_xor, natPoly_xor, N128_apply, N128_apply, ← ha,
      ← hb, ← map_mul, ← map_add, ← hlh]
    ring_nf

theorem clmulVal_lt {x y : Std.U64} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : x.val < 2 ^ a)
    (hy : y.val < 2 ^ b) : (clmulVal x y).val < 2 ^ (a + b - 1) := by
  apply lt_two_pow_of_degree_natPoly_lt
  rw [natPoly_clmulVal]
  have h1 := natDegree_natPoly_le (k := a - 1) (by rw [Nat.sub_add_cancel ha]; exact hx)
  have h2 := natDegree_natPoly_le (k := b - 1) (by rw [Nat.sub_add_cancel hb]; exact hy)
  have h3 := (Polynomial.natDegree_mul_le (p := natPoly x.val) (q := natPoly y.val)).trans
    (Nat.add_le_add h1 h2)
  exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h3) (by exact_mod_cast (by omega))

/-- One fold modulo `x^n + tail`. -/
theorem mk_fold_gen {n tail p c : ℕ}
    (hc : natPoly c = natPoly (p >>> n) * natPoly tail) :
    AdjoinRoot.mk (modPoly n tail) (natPoly (p % 2 ^ n ^^^ c)) =
      AdjoinRoot.mk (modPoly n tail) (natPoly p) := by
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨-natPoly (p >>> n), ?_⟩
  rw [natPoly_xor, hc, natPoly_split p n, modPoly]
  linear_combination (natPoly (p >>> n) * natPoly tail) *
    (CharTwo.two_eq_zero : (2 : Polynomial (ZMod 2)) = 0)

/-- `N` at 32 bits, as a ring homomorphism. -/
noncomputable abbrev N32 : ConcreteBTField 5 →+* AdjoinRoot (modPoly 32 141) :=
  @towerHom _ _ (charP_modPoly (by norm_num) (by norm_num)) xi32 5 xi32_rel

theorem N32_injective : Function.Injective N32 := by
  have := nontrivial_modPoly (n := 32) (tail := 141) (by norm_num) (by norm_num)
  exact N32.injective

theorem clmul_dot_product_32_spec {F : Type}
    (pairInst : CoreModels.core.ops.function.FnMut F (Std.U32 × Std.U32) (Std.U32 × Std.U32))
    (f : F) (hpair : ∀ a b, pairInst.call_mut f (a, b) = .ok ((a, b), f))
    (it : MapZip Std.U32 F) (hf : it.f = f)
    (hlen : (iterList it.iter.it1).length = (iterList it.iter.it2).length) :
    clmul.dot_product_32
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32))
        pairInst) it ⦃ r =>
      towerOf 5 r = dotList (towerOf 5) (iterList it.iter.it1) (iterList it.iter.it2) ⦄ := by
  unfold clmul.dot_product_32 core.iter.traits.iterator.Iterator.fold
    CoreModels.core.iter.traits.iterator.Iterator.fold.default
    CoreModels.core.iter.traits.iterator.iter_fold
  apply WP.spec_bind (fold_mapzip_spec (fun acc : Std.U64 =>
      AdjoinRoot.mk (modPoly 32 141) (natPoly acc.val))
    (fun a b => N32 (towerOf 5 a) * N32 (towerOf 5 b)) pairInst f hpair _ () ?_ it 0#u64 hf hlen)
  · intro p hp
    simp only [clmul_64x64_eq_clmulVal, Aeneas.Std.bind_ok]
    step*
    have ht : (UScalar.cast UScalarTy.U64 clmul.basis.TAIL_32).val = 141 := by
      rw [UScalar.cast_val_eq, TAIL_32_val]; rfl
    have hp64 := u64_val_lt p
    have hi : i.val < 2 ^ 32 := by
      rw [i_post, Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by omega)
    have hcf := clmulVal_lt (x := i) (y := i1) (a := 32) (b := 8) (by norm_num) (by norm_num) hi
      (by rw [i1_post, ht]; norm_num)
    have hf : fold.val = (clmulVal i i1).val := by
      rw [fold_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hcf (by norm_num))
    have hi3 : i3.val < 2 ^ 7 := by
      rw [i3_post, Nat.shiftRight_eq_div_pow, hf]; exact Nat.div_lt_of_lt_mul (by omega)
    have hcs := clmulVal_lt (x := i3) (y := i4) (a := 7) (b := 8) (by norm_num) (by norm_num) hi3
      (by rw [i4_post, ht]; norm_num)
    have hs : spill.val = (clmulVal i3 i4).val := by
      rw [spill_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hcs (by norm_num))
    have h9 : i9.val = p.val % 2 ^ 32 ^^^ (fold.val % 2 ^ 32 ^^^ spill.val) := by
      rw [i9_post, UScalar.val_xor, i8_post, UScalar.val_xor, i6_post, i7_post, UScalar.cast_val_eq,
        UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, Nat.xor_assoc]
    have e1 : AdjoinRoot.mk (modPoly 32 141) (natPoly (fold.val % 2 ^ 32 ^^^ spill.val)) =
        AdjoinRoot.mk (modPoly 32 141) (natPoly fold.val) :=
      mk_fold_gen (by rw [hs, natPoly_clmulVal, i3_post, i4_post, ht])
    have e2 : AdjoinRoot.mk (modPoly 32 141) (natPoly (p.val % 2 ^ 32 ^^^ fold.val)) =
        AdjoinRoot.mk (modPoly 32 141) (natPoly p.val) :=
      mk_fold_gen (by rw [hf, natPoly_clmulVal, i_post, i1_post, ht])
    have e9 : AdjoinRoot.mk (modPoly 32 141) (natPoly i9.val) =
        AdjoinRoot.mk (modPoly 32 141) (natPoly p.val) := by
      rw [h9, natPoly_xor, map_add, e1, ← map_add, ← natPoly_xor, e2]
    apply WP.spec_mono (poly_to_tower_32_spec i9)
    intro r hr
    apply N32_injective
    show towerMap xi32 5 (towerOf 5 r) = _
    rw [hr, e9, hp, hom_dotList]
    simp [natPoly_zero]
  · intro acc a b
    show clmul.dot_product_32.closure.Insts.CoreOpsFunctionFnMutPairU64PairU32U32U64.call_mut
      (CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (CoreModels.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32)
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32))
        pairInst) () (acc, (a, b)) ⦃ _ ⦄
    unfold clmul.dot_product_32.closure.Insts.CoreOpsFunctionFnMutPairU64PairU32U32U64.call_mut
    show (do
      let i ← clmul.basis.tower_to_poly_32 a
      let i1 ← lift (UScalar.cast UScalarTy.U64 i)
      let i2 ← clmul.basis.tower_to_poly_32 b
      let i3 ← lift (UScalar.cast UScalarTy.U64 i2)
      let i4 ← clmul.portable.clmul_64x64 i1 i3
      let i5 ← lift (UScalar.cast UScalarTy.U64 i4)
      let i6 ← lift (acc ^^^ i5)
      RustM.ok (i6, ())) ⦃ _ ⦄
    apply WP.spec_bind (tower_to_poly_32_spec a)
    intro pa ha
    simp only [lift_eq, Aeneas.Std.bind_ok]
    apply WP.spec_bind (tower_to_poly_32_spec b)
    intro pb hb
    simp only [Aeneas.Std.bind_ok, clmul_64x64_eq_clmulVal]
    refine (WP.spec_ok _).mpr ⟨trivial, ?_⟩
    have hca : (UScalar.cast UScalarTy.U64 pa).val = pa.val := by
      rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (u32_val_lt pa) (by norm_num))
    have hcb : (UScalar.cast UScalarTy.U64 pb).val = pb.val := by
      rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (u32_val_lt pb) (by norm_num))
    have hlt := clmulVal_lt (x := UScalar.cast UScalarTy.U64 pa) (y := UScalar.cast UScalarTy.U64 pb)
      (a := 32) (b := 32) (by norm_num) (by norm_num) (by rw [hca]; exact u32_val_lt pa)
      (by rw [hcb]; exact u32_val_lt pb)
    have hc : (UScalar.cast UScalarTy.U64 (clmulVal (UScalar.cast UScalarTy.U64 pa)
        (UScalar.cast UScalarTy.U64 pb))).val = (clmulVal (UScalar.cast UScalarTy.U64 pa)
        (UScalar.cast UScalarTy.U64 pb)).val := by
      rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (by norm_num))
    show AdjoinRoot.mk _ (natPoly (acc ^^^ _).val) = _
    rw [UScalar.val_xor, natPoly_xor, map_add, hc, natPoly_clmulVal, map_mul, hca, hcb, ha, hb]
    rfl

end Plonky3Lean.Proofs.Binary
