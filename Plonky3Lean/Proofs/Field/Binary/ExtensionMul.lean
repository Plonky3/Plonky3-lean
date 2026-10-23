module

public import Plonky3Lean.Proofs.Field.Binary.Extension

@[expose] public section

/-!
# Multiplying a level by a lower level

Level `u` is a vector space over level `l`, with the coefficients stored as consecutive
`2^l`-bit chunks. Multiplying by an element `b` of level `l` multiplies every chunk by `b`
(`toNat_mul_embed`): at each quadratic step, `b (lo + hi X) = b lo + (b hi) X`. `Mul<lower>`
computes exactly that, a chunk at a time.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Chunk `j` of `x`, `2^l` bits wide. -/
def chunk (l x j : ℕ) : ℕ := (x >>> (j * 2 ^ l)) % 2 ^ 2 ^ l

/-- The first `n` chunks of `x`, each multiplied by `b` at level `l`. -/
def chunkMul (l : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, b => chunkMul l n x b ||| towerMul l (chunk l x n) b <<< (n * 2 ^ l)

theorem chunkMul_lt {l b : ℕ} (hb : b < 2 ^ 2 ^ l) :
    ∀ (n : ℕ) (x : ℕ), chunkMul l n x b < 2 ^ (n * 2 ^ l)
  | 0, _ => by simp [chunkMul]
  | n + 1, x => by
    rw [chunkMul]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le (chunkMul_lt hb n x) (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    · rw [Nat.shiftLeft_eq, show (n + 1) * 2 ^ l = n * 2 ^ l + 2 ^ l by ring, pow_add, mul_comm]
      exact Nat.mul_lt_mul_of_pos_left (towerMul_lt l (Nat.mod_lt _ (by positivity)) hb)
        (by positivity)

theorem chunk_shiftRight (l x m n : ℕ) : chunk l (x >>> (m * 2 ^ l)) n = chunk l x (m + n) := by
  unfold chunk
  rw [add_mul, Nat.shiftRight_add]

theorem chunkMul_add {l b : ℕ} (x m : ℕ) : ∀ n : ℕ,
    chunkMul l (m + n) x b = chunkMul l m x b ||| chunkMul l n (x >>> (m * 2 ^ l)) b <<< (m * 2 ^ l)
  | 0 => by simp [chunkMul]
  | n + 1 => by
    rw [← Nat.add_assoc, chunkMul, chunkMul_add x m n, chunkMul, Nat.shiftLeft_or_distrib,
      Nat.or_assoc, chunk_shiftRight, ← Nat.shiftLeft_add, add_mul, Nat.add_comm (n * 2 ^ l)]

theorem chunk_mod {l x m j : ℕ} (hj : j < m) : chunk l (x % 2 ^ (m * 2 ^ l)) j = chunk l x j := by
  unfold chunk
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 2 ^ l
  · have : j * 2 ^ l + i < m * 2 ^ l := by
      have := Nat.mul_le_mul_right (2 ^ l) (show j + 1 ≤ m by omega)
      rw [add_mul, one_mul] at this
      omega
    simp [hi, this]
  · simp [hi]

theorem chunkMul_mod {l b x : ℕ} : ∀ (m : ℕ) (n : ℕ), n ≤ m →
    chunkMul l n (x % 2 ^ (m * 2 ^ l)) b = chunkMul l n x b
  | _, 0, _ => rfl
  | m, n + 1, h => by
    rw [chunkMul, chunkMul, chunkMul_mod m n (by omega), chunk_mod (by omega)]

/-- A value of level `k + 1` is its two halves. -/
theorem fromNat_eq_joinSucc {k x : ℕ} (hx : x < 2 ^ 2 ^ (k + 1)) :
    (fromNat x : ConcreteBTField (k + 1)) =
      joinSucc k (fromNat (x % 2 ^ 2 ^ k)) (fromNat (x >>> 2 ^ k)) := by
  apply ConcreteBTField.toNat_injective
  show _ = (join (k := k + 1) (by omega) _ _).toNat
  rw [toNat_join, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
    ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hx, Nat.add_sub_cancel,
    Nat.mod_eq_of_lt (shiftRight_lt_of_lt hx), Nat.mod_mod_of_dvd _ (by
      exact Nat.pow_dvd_pow 2 (le_refl _)), Nat.lor_comm, mod_or_shiftRight_shiftLeft]

/-- Scaling by an element of level `k` scales both halves. -/
theorem embed_mul_joinSucc (k : ℕ) (a lo hi : ConcreteBTField k) :
    concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) a * joinSucc k lo hi =
      joinSucc k (a * lo) (a * hi) :=
  smul_joinSucc k a lo hi

/-- Multiplying by an element `b` of level `l` multiplies every `2^l`-bit chunk by `b`. -/
theorem toNat_mul_embed (l : ℕ) : ∀ (d : ℕ) {x b : ℕ}, x < 2 ^ 2 ^ (l + d) → b < 2 ^ 2 ^ l →
    ((fromNat x : ConcreteBTField (l + d)) *
      concreteTowerAlgebraMap l (l + d) (by omega) (fromNat b)).toNat = chunkMul l (2 ^ d) x b
  | 0, x, b, hx, hb => by
    rw [show concreteTowerAlgebraMap l (l + 0) (by omega) = RingHom.id _ from
      concreteTowerAlgebraMap_id l, RingHom.id_apply]
    rw [show (fromNat x : ConcreteBTField (l + 0)) * fromNat b = concrete_mul (fromNat x) (fromNat b)
      from rfl, toNat_concrete_mul, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by simpa using hb)]
    simp [chunkMul, chunk, Nat.mod_eq_of_lt (show x < 2 ^ 2 ^ l by simpa using hx)]
  | d + 1, x, b, hx, hb => by
    have hx' : x < 2 ^ 2 ^ (l + d + 1) := hx
    have hlo : x % 2 ^ 2 ^ (l + d) < 2 ^ 2 ^ (l + d) := Nat.mod_lt _ (by positivity)
    have hhi : x >>> 2 ^ (l + d) < 2 ^ 2 ^ (l + d) := shiftRight_lt_of_lt hx'
    have hsplit : 2 ^ d * 2 ^ l = 2 ^ (l + d) := by rw [← pow_add, Nat.add_comm]
    show ((fromNat x : ConcreteBTField (l + d + 1)) *
      concreteTowerAlgebraMap l (l + d + 1) (by omega) (fromNat b)).toNat = _
    rw [fromNat_eq_joinSucc hx', concreteTowerAlgebraMap_succ l (l + d) (by omega),
      RingHom.comp_apply, mul_comm, embed_mul_joinSucc]
    show (join (k := l + d + 1) (by omega) _ _).toNat = _
    rw [toNat_join]
    simp only [Nat.add_sub_cancel]
    rw [mul_comm, toNat_mul_embed l d hhi hb, mul_comm,
      toNat_mul_embed l d hlo hb, pow_succ, mul_two, chunkMul_add, hsplit,
      ← chunkMul_mod (2 ^ d) (2 ^ d) le_rfl (x := x), hsplit, Nat.lor_comm]

/-! ## `GF(2^16)` by `GF(2^8)` -/

theorem bf16_bf8_closure_spec (a : tower.BinaryField16) (b : tower.BinaryField8) (j : Std.Usize)
    (hj : j.val < 2) :
    extension.MulBinaryField16BinaryField8BinaryField16.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField16BinaryField8BinaryField16.mul.closure) ∧ p.1.val = towerMul 3 (chunk 3 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField16BinaryField8BinaryField16.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
  simp only [tower.BinaryField8.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf16_bf8_loop_spec (a : tower.BinaryField16) (b : tower.BinaryField8)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U16)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 2)
    (hrepr : repr.val = chunkMul 3 it.start.val a.val b.val) :
    tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
      extension.MulBinaryField16BinaryField8BinaryField16.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8
      it (a, b) repr ⦃ r => r.val = chunkMul 3 2 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField16BinaryField8BinaryField16.mul.closure) ∧
      p.2.2.val = chunkMul 3 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField16BinaryField8BinaryField16.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U16.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf16_bf8_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U16.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U16.Insts.CoreConvertFromU8.from
    simp only [tower.BinaryField8.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 3 := hbf ▸ towerMul_lt 3 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 3) < 2 ^ 16 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 3 ≤ 8 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 3) < 2 ^ 2 ^ 3 * 2 ^ 8 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 16 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 3) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U16.size = 2 ^ 16 by simp [U16.size_def, U16.numBits_def], show s.val * 8 = s.val * 2 ^ 3 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 2 by omega]

/-- Multiplying by an element of `GF(2^8)` is multiplying by its embedding. -/
theorem bf16_bf8_mul_spec (a : tower.BinaryField16) (b : tower.BinaryField8) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField8BinaryField16.mul a b ⦃ r =>
      towerOf 4 r = towerOf 4 a * concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.CoreOpsArithMulBinaryField8BinaryField16.mul
    tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn
    tower.BinaryField16.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField16.BITS,
    tower.BinaryField8.BITS]
  step*
  refine WP.spec_bind (bf16_bf8_loop_spec a b { start := 0#usize, «end» := i } 0#u16 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf16_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 3 2 a.val b.val < 2 ^ 2 ^ 4 := chunkMul_lt hb 2 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 3 1 hA hb).symm

/-! ## `GF(2^32)` by `GF(2^8)` -/

theorem bf32_bf8_closure_spec (a : tower.BinaryField32) (b : tower.BinaryField8) (j : Std.Usize)
    (hj : j.val < 4) :
    extension.MulBinaryField32BinaryField8BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField32BinaryField8BinaryField32.mul.closure) ∧ p.1.val = towerMul 3 (chunk 3 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField32BinaryField8BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
  simp only [tower.BinaryField8.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf32_bf8_loop_spec (a : tower.BinaryField32) (b : tower.BinaryField8)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U32)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 4)
    (hrepr : repr.val = chunkMul 3 it.start.val a.val b.val) :
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
      extension.MulBinaryField32BinaryField8BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8
      it (a, b) repr ⦃ r => r.val = chunkMul 3 4 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField32BinaryField8BinaryField32.mul.closure) ∧
      p.2.2.val = chunkMul 3 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField32BinaryField8BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U32.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf32_bf8_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U32.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U32.Insts.CoreConvertFromU8.from
    simp only [tower.BinaryField8.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 3 := hbf ▸ towerMul_lt 3 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 3) < 2 ^ 32 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 3 ≤ 24 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 3) < 2 ^ 2 ^ 3 * 2 ^ 24 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 32 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 3) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U32.size = 2 ^ 32 by simp [U32.size_def, U32.numBits_def], show s.val * 8 = s.val * 2 ^ 3 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 4 by omega]

/-- Multiplying by an element of `GF(2^8)` is multiplying by its embedding. -/
theorem bf32_bf8_mul_spec (a : tower.BinaryField32) (b : tower.BinaryField8) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField8BinaryField32.mul a b ⦃ r =>
      towerOf 5 r = towerOf 5 a * concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreOpsArithMulBinaryField8BinaryField32.mul
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField32.BITS,
    tower.BinaryField8.BITS]
  step*
  refine WP.spec_bind (bf32_bf8_loop_spec a b { start := 0#usize, «end» := i } 0#u32 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf32_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 3 4 a.val b.val < 2 ^ 2 ^ 5 := chunkMul_lt hb 4 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 3 2 hA hb).symm

/-! ## `GF(2^64)` by `GF(2^8)` -/

theorem bf64_bf8_closure_spec (a : tower.BinaryField64) (b : tower.BinaryField8) (j : Std.Usize)
    (hj : j.val < 8) :
    extension.MulBinaryField64BinaryField8BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField64BinaryField8BinaryField64.mul.closure) ∧ p.1.val = towerMul 3 (chunk 3 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField64BinaryField8BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
  simp only [tower.BinaryField8.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf64_bf8_loop_spec (a : tower.BinaryField64) (b : tower.BinaryField8)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U64)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 8)
    (hrepr : repr.val = chunkMul 3 it.start.val a.val b.val) :
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
      extension.MulBinaryField64BinaryField8BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8
      it (a, b) repr ⦃ r => r.val = chunkMul 3 8 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField64BinaryField8BinaryField64.mul.closure) ∧
      p.2.2.val = chunkMul 3 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField64BinaryField8BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf64_bf8_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U64.Insts.CoreConvertFromU8.from
    simp only [tower.BinaryField8.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 3 := hbf ▸ towerMul_lt 3 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 3) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 3 ≤ 56 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 3) < 2 ^ 2 ^ 3 * 2 ^ 56 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 64 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 3) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U64.size = 2 ^ 64 by simp [U64.size_def, U64.numBits_def], show s.val * 8 = s.val * 2 ^ 3 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 8 by omega]

/-- Multiplying by an element of `GF(2^8)` is multiplying by its embedding. -/
theorem bf64_bf8_mul_spec (a : tower.BinaryField64) (b : tower.BinaryField8) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField8BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = towerOf 6 a * concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreOpsArithMulBinaryField8BinaryField64.mul
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField64.BITS,
    tower.BinaryField8.BITS]
  step*
  refine WP.spec_bind (bf64_bf8_loop_spec a b { start := 0#usize, «end» := i } 0#u64 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf64_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 3 8 a.val b.val < 2 ^ 2 ^ 6 := chunkMul_lt hb 8 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 3 3 hA hb).symm

/-! ## `GF(2^128)` by `GF(2^8)` -/

theorem bf128_bf8_closure_spec (a : tower.BinaryField128) (b : tower.BinaryField8) (j : Std.Usize)
    (hj : j.val < 16) :
    extension.MulBinaryField128BinaryField8BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField128BinaryField8BinaryField128.mul.closure) ∧ p.1.val = towerMul 3 (chunk 3 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField128BinaryField8BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
  simp only [tower.BinaryField8.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf128_bf8_loop_spec (a : tower.BinaryField128) (b : tower.BinaryField8)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U128)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 16)
    (hrepr : repr.val = chunkMul 3 it.start.val a.val b.val) :
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
      extension.MulBinaryField128BinaryField8BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8
      it (a, b) repr ⦃ r => r.val = chunkMul 3 16 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField128BinaryField8BinaryField128.mul.closure) ∧
      p.2.2.val = chunkMul 3 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField128BinaryField8BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField8.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf128_bf8_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU8.from i1
      let i3 ← s * tower.BinaryField8.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U128.Insts.CoreConvertFromU8.from
    simp only [tower.BinaryField8.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 3 := hbf ▸ towerMul_lt 3 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 3) < 2 ^ 128 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 3 ≤ 120 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 3) < 2 ^ 2 ^ 3 * 2 ^ 120 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 128 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 3) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def], show s.val * 8 = s.val * 2 ^ 3 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 16 by omega]

/-- Multiplying by an element of `GF(2^8)` is multiplying by its embedding. -/
theorem bf128_bf8_mul_spec (a : tower.BinaryField128) (b : tower.BinaryField8) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField8BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 3 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreOpsArithMulBinaryField8BinaryField128.mul
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.from_basis_coefficients_fn
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField8.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField128.BITS,
    tower.BinaryField8.BITS]
  step*
  refine WP.spec_bind (bf128_bf8_loop_spec a b { start := 0#usize, «end» := i } 0#u128 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf128_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 3 16 a.val b.val < 2 ^ 2 ^ 7 := chunkMul_lt hb 16 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 3 4 hA hb).symm

/-! ## `GF(2^32)` by `GF(2^16)` -/

theorem bf32_bf16_closure_spec (a : tower.BinaryField32) (b : tower.BinaryField16) (j : Std.Usize)
    (hj : j.val < 2) :
    extension.MulBinaryField32BinaryField16BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField32BinaryField16BinaryField32.mul.closure) ∧ p.1.val = towerMul 4 (chunk 4 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField32BinaryField16BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
  simp only [tower.BinaryField16.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf32_bf16_loop_spec (a : tower.BinaryField32) (b : tower.BinaryField16)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U32)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 2)
    (hrepr : repr.val = chunkMul 4 it.start.val a.val b.val) :
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
      extension.MulBinaryField32BinaryField16BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16
      it (a, b) repr ⦃ r => r.val = chunkMul 4 2 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField32BinaryField16BinaryField32.mul.closure) ∧
      p.2.2.val = chunkMul 4 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField32BinaryField16BinaryField32.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U32.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf32_bf16_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U32.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U32.Insts.CoreConvertFromU16.from
    simp only [tower.BinaryField16.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 4 := hbf ▸ towerMul_lt 4 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 4) < 2 ^ 32 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 4 ≤ 16 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 4) < 2 ^ 2 ^ 4 * 2 ^ 16 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 32 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 4) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U32.size = 2 ^ 32 by simp [U32.size_def, U32.numBits_def], show s.val * 16 = s.val * 2 ^ 4 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 2 by omega]

/-- Multiplying by an element of `GF(2^16)` is multiplying by its embedding. -/
theorem bf32_bf16_mul_spec (a : tower.BinaryField32) (b : tower.BinaryField16) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField16BinaryField32.mul a b ⦃ r =>
      towerOf 5 r = towerOf 5 a * concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.CoreOpsArithMulBinaryField16BinaryField32.mul
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn
    tower.BinaryField32.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField32.BITS,
    tower.BinaryField16.BITS]
  step*
  refine WP.spec_bind (bf32_bf16_loop_spec a b { start := 0#usize, «end» := i } 0#u32 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf32_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 4 2 a.val b.val < 2 ^ 2 ^ 5 := chunkMul_lt hb 2 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 4 1 hA hb).symm

/-! ## `GF(2^64)` by `GF(2^16)` -/

theorem bf64_bf16_closure_spec (a : tower.BinaryField64) (b : tower.BinaryField16) (j : Std.Usize)
    (hj : j.val < 4) :
    extension.MulBinaryField64BinaryField16BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField64BinaryField16BinaryField64.mul.closure) ∧ p.1.val = towerMul 4 (chunk 4 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField64BinaryField16BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
  simp only [tower.BinaryField16.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf64_bf16_loop_spec (a : tower.BinaryField64) (b : tower.BinaryField16)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U64)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 4)
    (hrepr : repr.val = chunkMul 4 it.start.val a.val b.val) :
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
      extension.MulBinaryField64BinaryField16BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16
      it (a, b) repr ⦃ r => r.val = chunkMul 4 4 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField64BinaryField16BinaryField64.mul.closure) ∧
      p.2.2.val = chunkMul 4 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField64BinaryField16BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf64_bf16_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U64.Insts.CoreConvertFromU16.from
    simp only [tower.BinaryField16.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 4 := hbf ▸ towerMul_lt 4 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 4) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 4 ≤ 48 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 4) < 2 ^ 2 ^ 4 * 2 ^ 48 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 64 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 4) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U64.size = 2 ^ 64 by simp [U64.size_def, U64.numBits_def], show s.val * 16 = s.val * 2 ^ 4 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 4 by omega]

/-- Multiplying by an element of `GF(2^16)` is multiplying by its embedding. -/
theorem bf64_bf16_mul_spec (a : tower.BinaryField64) (b : tower.BinaryField16) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField16BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = towerOf 6 a * concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreOpsArithMulBinaryField16BinaryField64.mul
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField64.BITS,
    tower.BinaryField16.BITS]
  step*
  refine WP.spec_bind (bf64_bf16_loop_spec a b { start := 0#usize, «end» := i } 0#u64 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf64_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 4 4 a.val b.val < 2 ^ 2 ^ 6 := chunkMul_lt hb 4 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 4 2 hA hb).symm

/-! ## `GF(2^128)` by `GF(2^16)` -/

theorem bf128_bf16_closure_spec (a : tower.BinaryField128) (b : tower.BinaryField16) (j : Std.Usize)
    (hj : j.val < 8) :
    extension.MulBinaryField128BinaryField16BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField128BinaryField16BinaryField128.mul.closure) ∧ p.1.val = towerMul 4 (chunk 4 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField128BinaryField16BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
  simp only [tower.BinaryField16.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf128_bf16_loop_spec (a : tower.BinaryField128) (b : tower.BinaryField16)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U128)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 8)
    (hrepr : repr.val = chunkMul 4 it.start.val a.val b.val) :
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
      extension.MulBinaryField128BinaryField16BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16
      it (a, b) repr ⦃ r => r.val = chunkMul 4 8 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField128BinaryField16BinaryField128.mul.closure) ∧
      p.2.2.val = chunkMul 4 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField128BinaryField16BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField16.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf128_bf16_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU16.from i1
      let i3 ← s * tower.BinaryField16.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U128.Insts.CoreConvertFromU16.from
    simp only [tower.BinaryField16.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 4 := hbf ▸ towerMul_lt 4 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 4) < 2 ^ 128 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 4 ≤ 112 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 4) < 2 ^ 2 ^ 4 * 2 ^ 112 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 128 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 4) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def], show s.val * 16 = s.val * 2 ^ 4 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 8 by omega]

/-- Multiplying by an element of `GF(2^16)` is multiplying by its embedding. -/
theorem bf128_bf16_mul_spec (a : tower.BinaryField128) (b : tower.BinaryField16) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField16BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 4 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreOpsArithMulBinaryField16BinaryField128.mul
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.from_basis_coefficients_fn
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField16.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField128.BITS,
    tower.BinaryField16.BITS]
  step*
  refine WP.spec_bind (bf128_bf16_loop_spec a b { start := 0#usize, «end» := i } 0#u128 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf128_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 4 8 a.val b.val < 2 ^ 2 ^ 7 := chunkMul_lt hb 8 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 4 3 hA hb).symm

/-! ## `GF(2^64)` by `GF(2^32)` -/

theorem bf64_bf32_closure_spec (a : tower.BinaryField64) (b : tower.BinaryField32) (j : Std.Usize)
    (hj : j.val < 2) :
    extension.MulBinaryField64BinaryField32BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField64BinaryField32BinaryField64.mul.closure) ∧ p.1.val = towerMul 5 (chunk 5 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField64BinaryField32BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
  simp only [tower.BinaryField32.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf64_bf32_loop_spec (a : tower.BinaryField64) (b : tower.BinaryField32)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U64)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 2)
    (hrepr : repr.val = chunkMul 5 it.start.val a.val b.val) :
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop
      extension.MulBinaryField64BinaryField32BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32
      it (a, b) repr ⦃ r => r.val = chunkMul 5 2 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 5 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField64BinaryField32BinaryField64.mul.closure) ∧
      p.2.2.val = chunkMul 5 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField64BinaryField32BinaryField64.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU32.from i1
      let i3 ← s * tower.BinaryField32.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf64_bf32_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U64.Insts.CoreConvertFromU32.from i1
      let i3 ← s * tower.BinaryField32.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U64.Insts.CoreConvertFromU32.from
    simp only [tower.BinaryField32.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 5 := hbf ▸ towerMul_lt 5 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 5) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 5 ≤ 32 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 5) < 2 ^ 2 ^ 5 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 64 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 5) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U64.size = 2 ^ 64 by simp [U64.size_def, U64.numBits_def], show s.val * 32 = s.val * 2 ^ 5 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 2 by omega]

/-- Multiplying by an element of `GF(2^32)` is multiplying by its embedding. -/
theorem bf64_bf32_mul_spec (a : tower.BinaryField64) (b : tower.BinaryField32) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField32BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = towerOf 6 a * concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 5 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.CoreOpsArithMulBinaryField32BinaryField64.mul
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn
    tower.BinaryField64.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField64.BITS,
    tower.BinaryField32.BITS]
  step*
  refine WP.spec_bind (bf64_bf32_loop_spec a b { start := 0#usize, «end» := i } 0#u64 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf64_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 5 2 a.val b.val < 2 ^ 2 ^ 6 := chunkMul_lt hb 2 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 5 1 hA hb).symm

/-! ## `GF(2^128)` by `GF(2^32)` -/

theorem bf128_bf32_closure_spec (a : tower.BinaryField128) (b : tower.BinaryField32) (j : Std.Usize)
    (hj : j.val < 4) :
    extension.MulBinaryField128BinaryField32BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField128BinaryField32BinaryField128.mul.closure) ∧ p.1.val = towerMul 5 (chunk 5 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField128BinaryField32BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
  simp only [tower.BinaryField32.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf128_bf32_loop_spec (a : tower.BinaryField128) (b : tower.BinaryField32)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U128)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 4)
    (hrepr : repr.val = chunkMul 5 it.start.val a.val b.val) :
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop
      extension.MulBinaryField128BinaryField32BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32
      it (a, b) repr ⦃ r => r.val = chunkMul 5 4 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 5 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField128BinaryField32BinaryField128.mul.closure) ∧
      p.2.2.val = chunkMul 5 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField128BinaryField32BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField32.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU32.from i1
      let i3 ← s * tower.BinaryField32.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf128_bf32_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU32.from i1
      let i3 ← s * tower.BinaryField32.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U128.Insts.CoreConvertFromU32.from
    simp only [tower.BinaryField32.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 5 := hbf ▸ towerMul_lt 5 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 5) < 2 ^ 128 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 5 ≤ 96 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 5) < 2 ^ 2 ^ 5 * 2 ^ 96 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 128 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 5) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def], show s.val * 32 = s.val * 2 ^ 5 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 4 by omega]

/-- Multiplying by an element of `GF(2^32)` is multiplying by its embedding. -/
theorem bf128_bf32_mul_spec (a : tower.BinaryField128) (b : tower.BinaryField32) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField32BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 5 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreOpsArithMulBinaryField32BinaryField128.mul
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.from_basis_coefficients_fn
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField32.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField128.BITS,
    tower.BinaryField32.BITS]
  step*
  refine WP.spec_bind (bf128_bf32_loop_spec a b { start := 0#usize, «end» := i } 0#u128 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf128_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 5 4 a.val b.val < 2 ^ 2 ^ 7 := chunkMul_lt hb 4 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 5 2 hA hb).symm

/-! ## `GF(2^128)` by `GF(2^64)` -/

theorem bf128_bf64_closure_spec (a : tower.BinaryField128) (b : tower.BinaryField64) (j : Std.Usize)
    (hj : j.val < 2) :
    extension.MulBinaryField128BinaryField64BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField64.call_mut
      (a, b) j ⦃ p => p.2 = ((a, b) : extension.MulBinaryField128BinaryField64BinaryField128.mul.closure) ∧ p.1.val = towerMul 6 (chunk 6 a.val j.val) b.val ⦄ := by
  unfold extension.MulBinaryField128BinaryField64BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField64.call_mut
  simp only [tower.BinaryField64.BITS]
  step*
  refine ⟨rfl, ?_⟩
  rw [bf3_post, bf2_post, i3_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, i2_post, i_post,
    i1_post]
  simp only [chunk]
  norm_num [Nat.mod_mod]

theorem bf128_bf64_loop_spec (a : tower.BinaryField128) (b : tower.BinaryField64)
    (it : CoreModels.core.ops.range.Range Std.Usize) (repr : Std.U128)
    (hs : it.start.val ≤ it.«end».val) (he : it.«end».val = 2)
    (hrepr : repr.val = chunkMul 6 it.start.val a.val b.val) :
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.from_basis_coefficients_fn_loop
      extension.MulBinaryField128BinaryField64BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField64
      it (a, b) repr ⦃ r => r.val = chunkMul 6 2 a.val b.val ⦄ := by
  have hb : b.val < 2 ^ 2 ^ 6 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.from_basis_coefficients_fn_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ p.1.start.val ≤ it.«end».val ∧ p.2.1 = ((a, b) : extension.MulBinaryField128BinaryField64BinaryField128.mul.closure) ∧
      p.2.2.val = chunkMul 6 p.1.start.val a.val b.val) _ _ _ ?_ ⟨rfl, hs, rfl, hrepr⟩
  rintro ⟨⟨s, e⟩, f, rp⟩ ⟨he', h1, hf, hr⟩
  dsimp only at he' h1 hf hr ⊢
  subst he' hf
  unfold tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.from_basis_coefficients_fn_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    show (do
      let (bf, f1) ←
        extension.MulBinaryField128BinaryField64BinaryField128.mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBinaryField64.call_mut
          (a, b) s
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU64.from i1
      let i3 ← s * tower.BinaryField64.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    refine WP.spec_bind (bf128_bf64_closure_spec a b s (by omega)) fun ⟨bf, f1⟩ ⟨hf, hbf⟩ => ?_
    dsimp only at hf hbf ⊢
    show (do
      let i1 ← bf.to_repr
      let i2 ← core.U128.Insts.CoreConvertFromU64.from i1
      let i3 ← s * tower.BinaryField64.BITS
      let i4 ← i2 <<< i3
      let repr1 ← lift (rp ||| i4)
      RustM.ok (ControlFlow.cont (({ start := s', «end» := it.«end» } :
        CoreModels.core.ops.range.Range Std.Usize), f1, repr1))) ⦃ _ ⦄
    subst hf
    unfold CoreModels.core.U128.Insts.CoreConvertFromU64.from
    simp only [tower.BinaryField64.BITS]
    step*
    have hbf8 : bf.val < 2 ^ 2 ^ 6 := hbf ▸ towerMul_lt 6 (Nat.mod_lt _ (by positivity)) hb
    have hsh : bf.val <<< (s.val * 2 ^ 6) < 2 ^ 128 := by
      rw [Nat.shiftLeft_eq]
      have : s.val * 2 ^ 6 ≤ 64 := by omega
      calc bf.val * 2 ^ (s.val * 2 ^ 6) < 2 ^ 2 ^ 6 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le hbf8 (Nat.pow_le_pow_right (by norm_num) this) (by positivity)
        _ = 2 ^ 128 := by norm_num
    have hi4 : i4.val = bf.val <<< (s.val * 2 ^ 6) := by
      rw [i4_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq, i1_post,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hbf8 (by norm_num)), i3_post,
        show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def], show s.val * 64 = s.val * 2 ^ 6 by norm_num,
        Nat.mod_eq_of_lt hsh]
    refine ⟨by omega, ?_, by omega⟩
    rw [repr1_post, UScalar.val_or, hr, hi4, hbf, hs', chunkMul]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    show WP.spec (RustM.ok (ControlFlow.done rp)) _
    rw [WP.spec_ok]
    show rp.val = _
    rw [hr, show s.val = 2 by omega]

/-- Multiplying by an element of `GF(2^64)` is multiplying by its embedding. -/
theorem bf128_bf64_mul_spec (a : tower.BinaryField128) (b : tower.BinaryField64) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField64BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 b) ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 2 ^ 6 := by have := b.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.CoreOpsArithMulBinaryField64BinaryField128.mul
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.from_basis_coefficients_fn
    tower.BinaryField128.Insts.P3_fieldFieldBasedVectorSpaceBinaryField64.DIMENSION
  simp only [clmul.HAS_HARDWARE_CLMUL, Bool.false_eq_true, ↓reduceIte, tower.BinaryField128.BITS,
    tower.BinaryField64.BITS]
  step*
  refine WP.spec_bind (bf128_bf64_loop_spec a b { start := 0#usize, «end» := i } 0#u128 (by simp)
    (by simp only [i_post]) (by rfl)) fun r0 hr0 => ?_
  refine WP.spec_mono (bf128_from_repr_spec r0) fun r hr => ?_
  have hlt : chunkMul 6 2 a.val b.val < 2 ^ 2 ^ 7 := chunkMul_lt hb 2 a.val
  rw [hr0, Nat.mod_eq_of_lt hlt] at hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, hr, Nat.mod_eq_of_lt hlt]
  exact (toNat_mul_embed 6 1 hA hb).symm

/-! ## The lower level on the left -/

theorem bf8_bf16_mul_spec (a : tower.BinaryField8) (b : tower.BinaryField16) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul a b ⦃ r =>
      towerOf 4 r = concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 a) * towerOf 4 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul
  exact WP.spec_mono (bf16_bf8_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf8_bf32_mul_spec (a : tower.BinaryField8) (b : tower.BinaryField32) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ r =>
      towerOf 5 r = concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 a) * towerOf 5 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul
  exact WP.spec_mono (bf32_bf8_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf8_bf64_mul_spec (a : tower.BinaryField8) (b : tower.BinaryField64) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 a) * towerOf 6 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul
  exact WP.spec_mono (bf64_bf8_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf8_bf128_mul_spec (a : tower.BinaryField8) (b : tower.BinaryField128) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 a) * towerOf 7 b ⦄ := by
  unfold tower.BinaryField8.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul
  exact WP.spec_mono (bf128_bf8_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf16_bf32_mul_spec (a : tower.BinaryField16) (b : tower.BinaryField32) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ r =>
      towerOf 5 r = concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 a) * towerOf 5 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul
  exact WP.spec_mono (bf32_bf16_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf16_bf64_mul_spec (a : tower.BinaryField16) (b : tower.BinaryField64) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 a) * towerOf 6 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul
  exact WP.spec_mono (bf64_bf16_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf16_bf128_mul_spec (a : tower.BinaryField16) (b : tower.BinaryField128) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 a) * towerOf 7 b ⦄ := by
  unfold tower.BinaryField16.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul
  exact WP.spec_mono (bf128_bf16_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf32_bf64_mul_spec (a : tower.BinaryField32) (b : tower.BinaryField64) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r = concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 a) * towerOf 6 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul
  exact WP.spec_mono (bf64_bf32_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf32_bf128_mul_spec (a : tower.BinaryField32) (b : tower.BinaryField128) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 a) * towerOf 7 b ⦄ := by
  unfold tower.BinaryField32.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul
  exact WP.spec_mono (bf128_bf32_mul_spec b a) fun r h => by rw [h, mul_comm]

theorem bf64_bf128_mul_spec (a : tower.BinaryField64) (b : tower.BinaryField128) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r = concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 a) * towerOf 7 b ⦄ := by
  unfold tower.BinaryField64.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul
  exact WP.spec_mono (bf128_bf64_mul_spec b a) fun r h => by rw [h, mul_comm]

end Plonky3Lean.Proofs.Binary
