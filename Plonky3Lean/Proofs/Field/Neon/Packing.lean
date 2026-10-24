module

public import Plonky3Lean.Spec.Packed
public import Plonky3Lean.Proofs.Field.Neon.Kernels
public import Plonky3Lean.Proofs.Field.Monty31.Arith
public import Plonky3Lean.Proofs.Field.Monty31.PowersOfTwo

@[expose] public section

/-!
# NEON: `PackedMontyField31Neon`'s arithmetic is lane-wise `MontyField31` arithmetic

For any parameters that are `Spec.Packed.Neon.Valid` (valid `MontyParameters`, and `PACKED_P`,
`PACKED_MU` the broadcasts of `PRIME`, `MONTY_MU`), and packed inputs whose lanes are canonical:

* `add`, `sub`, `neg` and `mul` never fail; each ends in a call `from_vector(v)` whose `v` has
  canonical lanes, the safety condition `from_vector` states (`*.from_vector_arg`);
* every lane of the result is canonical, and lane `i` is what the portable scalar operator
  returns on lane `i` of the inputs (`*.lanewise`).

`halve_neon`, which the packed `halve` wraps, is stated on `uint32x4_t` lanes.

`mul` reads its inputs with `to_signed_vector`, as `int32x4_t`s; a canonical lane is below
`2^31`, so it is the same integer either way.

The scalar operators are P3Monty31's, at the parameters `toPortable` reads from the variant's
dictionary; `neg` and `halve` take a portable `FieldParameters` dictionary with the same prime.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib Plonky3Lean.Spec.Packed.Neon
open Plonky3Lean.Spec.Monty31 (Element)

namespace Plonky3Lean.Proofs.Neon

/-! ## Reading packed values -/

/-- The `uint32x4_t` of a packed value's stored `u32`s, as `to_vector` transmutes it. -/
def vec {MP : Type} (x : PackedNeon MP) : U :=
  Aeneas.Std.Array.make 4#usize (x.val.map (·.value)) (by simp)

/-- The packed value of a `uint32x4_t`'s lanes, as `from_vector` transmutes it. -/
def unvec {MP : Type} (v : U) : PackedNeon MP :=
  Aeneas.Std.Array.make 4#usize (v.val.map fun u => { value := u, _phantom := () }) (by simp)

/-- The `int32x4_t` of a packed value's stored `u32`s, as `to_signed_vector` transmutes it. -/
def svec {MP : Type} (x : PackedNeon MP) : S :=
  Aeneas.Std.Array.make 4#usize (x.val.map fun u => ⟨u.value.bv⟩) (by simp)

theorem toVector_get {MP : Type} (x : PackedNeon MP) (i : Fin 4) :
    (toVector x)[i] = x.val[i.val]'(by simp) := by
  simp [toVector]

theorem ln_vec {MP : Type} (x : PackedNeon MP) (i : Fin 4) :
    ln (vec x) i = ((toVector x)[i]).value.val := by
  rw [toVector_get]
  simp [ln, vec, Aeneas.Std.Array.make_val]

/-- A stored value below `2^31` is the same integer read as an `i32`. -/
theorem sn_svec {MP : Type} (x : PackedNeon MP) (i : Fin 4)
    (h : ((toVector x)[i]).value.val < 2 ^ 31) :
    sn (svec x) i = ((toVector x)[i]).value.val := by
  have hget : (svec x).val[i.val]! = ⟨((toVector x)[i]).value.bv⟩ := by
    rw [toVector_get]
    simp [svec, Aeneas.Std.Array.make_val]
  rw [sn, hget]
  show (((toVector x)[i]).value.bv).toInt = _
  have h2 : 2 * ((toVector x)[i]).value.bv.toNat < 2 ^ 32 := by
    have : ((toVector x)[i]).value.bv.toNat < 2 ^ 31 := h
    omega
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [h2, ↓reduceIte]
  rfl

theorem unvec_value {MP : Type} (v : U) (i : Fin 4) :
    ((toVector (unvec (MP := MP) v))[i]).value = lane v i := by
  rw [toVector_get]
  simp [unvec, lane, Aeneas.Std.Array.make_val]

theorem ln_lane (v : U) (i : Fin 4) : ln v i = (lane v i).val := rfl

open p3_monty_31_neon in
theorem to_vector_eq {PMP : Type} (inst : data_traits.PackedMontyParameters PMP)
    (x : PackedNeon PMP) : aarch64_neon.packing.PackedMontyField31Neon.to_vector inst x =
      .ok (vec x) := rfl

open p3_monty_31_neon in
theorem from_vector_eq {PMP : Type} (inst : data_traits.PackedMontyParameters PMP) (v : U) :
    aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v = .ok (unvec v) := rfl

open p3_monty_31_neon in
theorem to_signed_vector_eq {PMP : Type} (inst : data_traits.PackedMontyParameters PMP)
    (x : PackedNeon PMP) : aarch64_neon.packing.PackedMontyField31Neon.to_signed_vector inst x =
      .ok (svec x) := rfl

/-- Two elements with the same stored value are equal. -/
theorem element_ext {MP : Type} {a b : Element MP} (h : a.value = b.value) : a = b := by
  cases a; cases b; cases h; rfl

/-! ## Parameters -/

section
variable {PMP : Type} {inst : p3_monty_31_neon.data_traits.PackedMontyParameters PMP}
  {p mu : Std.U32}

theorem valid_p_pos (hv : Valid inst p mu) : 0 < p.val := by
  have := hv.monty.odd; omega

theorem valid_lnP (hv : Valid inst p mu) :
    ∃ P, inst.aarch64_neonpackingMontyParametersNeonInst.PACKED_P = .ok P ∧
      ∀ i < 4, ln P i = p.val := by
  obtain ⟨P, hP, hl⟩ := hv.packed_p
  exact ⟨P, hP, fun i hi => by rw [show ln P i = (lane P ⟨i, hi⟩).val from rfl, hl]⟩

theorem valid_snM (hv : Valid inst p mu) :
    ∃ M, inst.aarch64_neonpackingMontyParametersNeonInst.PACKED_MU = .ok M ∧
      ∀ i < 4, sn M i % 2 ^ 32 = mu.val := by
  obtain ⟨M, hM, hl⟩ := hv.packed_mu
  refine ⟨M, hM, fun i hi => ?_⟩
  have h := congrArg UScalar.val (hl ⟨i, hi⟩)
  rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq] at h
  have h0 : (0 : ℤ) ≤ (slane M ⟨i, hi⟩).val % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  rw [sn, show M.val[i]! = slane M ⟨i, hi⟩ from rfl, ← Int.toNat_of_nonneg h0, h]

theorem canonical_ln {x : PackedNeon PMP} (hx : Canonical p.val x) : ∀ i < 4, ln (vec x) i < p.val :=
  fun i hi => by rw [show i = (⟨i, hi⟩ : Fin 4).val from rfl, ln_vec]; exact hx ⟨i, hi⟩

/-- A packed value from a vector whose lanes are below `p` is canonical. -/
theorem canonical_unvec {v : U} (hv : FromVectorSafe p.val v) :
    Canonical p.val (unvec (MP := PMP) v) := fun i => by
  show ((toVector _)[i]).value.val < p.val
  rw [unvec_value]; exact hv i

end

/-! ## The operators -/

section
open p3_monty_31_neon
variable {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}

/-- `Add`: the `from_vector` argument has canonical lanes, `(x_i + y_i) mod p`. -/
theorem add.from_vector_arg (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    ∃ v, FromVectorSafe p.val v ∧
      (∀ i : Fin 4, (lane v i).val =
        (((toVector x)[i]).value.val + ((toVector y)[i]).value.val) % p.val) ∧
      aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add
        inst x y = aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v := by
  obtain ⟨P, hPP, hP⟩ := valid_lnP hv
  obtain ⟨r, hr, hrl⟩ := mod_add (vec x) (vec y) P p.val hv.monty.lt (canonical_ln hx)
    (canonical_ln hy) hP
  refine ⟨r, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← ln_lane, hrl i i.isLt]; exact Nat.mod_lt _ (valid_p_pos hv)
  · rw [← ln_lane, hrl i i.isLt, ln_vec, ln_vec]
  · unfold aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add
    rw [to_vector_eq, bind_ok, to_vector_eq, bind_ok, hPP, bind_ok, hr, bind_ok]

/-- `Sub`: the `from_vector` argument has canonical lanes, `(x_i + p - y_i) mod p`. -/
theorem sub.from_vector_arg (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    ∃ v, FromVectorSafe p.val v ∧
      (∀ i : Fin 4, (lane v i).val =
        (((toVector x)[i]).value.val + p.val - ((toVector y)[i]).value.val) % p.val) ∧
      aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub
        inst x y = aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v := by
  obtain ⟨P, hPP, hP⟩ := valid_lnP hv
  obtain ⟨r, hr, hrl⟩ := mod_sub (vec x) (vec y) P p.val hv.monty.lt (canonical_ln hx)
    (canonical_ln hy) hP
  refine ⟨r, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← ln_lane, hrl i i.isLt]; exact Nat.mod_lt _ (valid_p_pos hv)
  · rw [← ln_lane, hrl i i.isLt, ln_vec, ln_vec]
  · unfold aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub
    rw [to_vector_eq, bind_ok, to_vector_eq, bind_ok, hPP, bind_ok, hr, bind_ok]

/-- `Neg`: the `from_vector` argument has canonical lanes, `(p - x_i) mod p`. -/
theorem neg.from_vector_arg (hv : Valid inst p mu) (x : PackedNeon PMP)
    (hx : Canonical p.val x) :
    ∃ v, FromVectorSafe p.val v ∧
      (∀ i : Fin 4, (lane v i).val = (p.val - ((toVector x)[i]).value.val) % p.val) ∧
      aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithNegPackedMontyField31Neon.neg
        inst x = aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v := by
  obtain ⟨P, hPP, hP⟩ := valid_lnP hv
  obtain ⟨r, hr, hrl⟩ := Neon.neg inst.aarch64_neonpackingMontyParametersNeonInst P (vec x) p.val
    hv.monty.lt hPP hP (canonical_ln hx)
  refine ⟨r, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← ln_lane, hrl i i.isLt]; exact Nat.mod_lt _ (valid_p_pos hv)
  · rw [← ln_lane, hrl i i.isLt, ln_vec]
  · unfold aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithNegPackedMontyField31Neon.neg
    rw [to_vector_eq, bind_ok, hr, bind_ok]

/-- `Mul`: the `from_vector` argument has canonical lanes, the Montgomery products
`r_i · 2^32 ≡ x_i · y_i (mod p)`. -/
theorem mul.from_vector_arg (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    ∃ v, FromVectorSafe p.val v ∧
      (∀ i : Fin 4, (lane v i).val * 2 ^ 32 % p.val =
        ((toVector x)[i]).value.val * ((toVector y)[i]).value.val % p.val) ∧
      aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul
        inst x y = aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v := by
  obtain ⟨P, hPP, hP⟩ := valid_lnP hv
  obtain ⟨M, hMM, hM⟩ := valid_snM hv
  have hlt := hv.monty.lt
  have hsx : ∀ i : Fin 4, sn (svec x) i = ((toVector x)[i]).value.val := fun i =>
    sn_svec x i (by have := hx i; unfold Spec.Monty31.Canonical at this; omega)
  have hsy : ∀ i : Fin 4, sn (svec y) i = ((toVector y)[i]).value.val := fun i =>
    sn_svec y i (by have := hy i; unfold Spec.Monty31.Canonical at this; omega)
  have habs : ∀ (z : PackedNeon PMP), Canonical p.val z →
      (∀ i : Fin 4, sn (svec z) i = ((toVector z)[i]).value.val) →
      ∀ i < 4, |sn (svec z) i| ≤ (p.val : ℤ) := by
    intro z hz hs i hi
    rw [show i = (⟨i, hi⟩ : Fin 4).val from rfl, hs ⟨i, hi⟩, abs_of_nonneg (by positivity)]
    have := hz ⟨i, hi⟩
    unfold Spec.Monty31.Canonical at this
    exact_mod_cast this.le
  obtain ⟨r, hr, hrl⟩ := Neon.mul inst.aarch64_neonpackingMontyParametersNeonInst P M
    (svec x) (svec y) p.val mu.val hlt (valid_p_pos hv) hv.monty.inv hPP hP hMM hM
    (habs x hx hsx) (habs y hy hsy)
  refine ⟨r, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← ln_lane]; exact (hrl i i.isLt).1
  · rw [← ln_lane]
    have h := (hrl i i.isLt).2
    rw [hsx i, hsy i] at h
    exact_mod_cast h
  · unfold aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul
    rw [to_signed_vector_eq, bind_ok, to_signed_vector_eq, bind_ok, hr, bind_ok]

end

/-! ## Lane `i` is the scalar operator on lane `i` -/

section
open p3_monty_31_neon
variable {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}

/-- An op that ends in `from_vector(v)` returns `unvec v`. -/
theorem spec_of_from_vector {m : RustM (PackedNeon PMP)} {v : U}
    (h : m = aarch64_neon.packing.PackedMontyField31Neon.from_vector inst v)
    {Q : PackedNeon PMP → Prop} (hq : Q (unvec v)) : m ⦃ z => Q z ⦄ := by
  rw [h, from_vector_eq]; simp only [WP.spec_ok]; exact hq

/-- Packed `x + y` is lane-wise `MontyField31` addition. -/
theorem add.lanewise (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add
      inst x y ⦃ z => Canonical p.val z ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
          (toPortable inst.MontyParametersInst) (toVector x)[i] (toVector y)[i] =
            .ok (toVector z)[i] ⦄ := by
  obtain ⟨v, hsafe, hval, heq⟩ := add.from_vector_arg hv x y hx hy
  refine spec_of_from_vector heq ⟨canonical_unvec hsafe, fun i => ?_⟩
  unfold p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
  obtain ⟨s, hs, hsv⟩ := spec_imp_exists (Monty31.utils.add.spec hv.monty _ _ (hx i) (hy i))
  rw [hs, bind_ok]
  obtain ⟨c, hc, hcv⟩ := spec_imp_exists (Monty31.monty_31.MontyField31.new_monty.spec
    (inst := toPortable inst.MontyParametersInst) s)
  rw [hc]; congr 1
  apply element_ext
  rw [hcv, unvec_value]
  apply UScalar.eq_of_val_eq
  rw [hsv, hval i]

/-- Packed `x - y` is lane-wise `MontyField31` subtraction. -/
theorem sub.lanewise (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub
      inst x y ⦃ z => Canonical p.val z ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
          (toPortable inst.MontyParametersInst) (toVector x)[i] (toVector y)[i] =
            .ok (toVector z)[i] ⦄ := by
  obtain ⟨v, hsafe, hval, heq⟩ := sub.from_vector_arg hv x y hx hy
  refine spec_of_from_vector heq ⟨canonical_unvec hsafe, fun i => ?_⟩
  unfold p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
  obtain ⟨s, hs, hsv⟩ := spec_imp_exists (Monty31.utils.sub.spec hv.monty _ _ (hx i) (hy i))
  rw [hs, bind_ok]
  obtain ⟨c, hc, hcv⟩ := spec_imp_exists (Monty31.monty_31.MontyField31.new_monty.spec
    (inst := toPortable inst.MontyParametersInst) s)
  rw [hc]; congr 1
  apply element_ext
  rw [hcv, unvec_value]
  apply UScalar.eq_of_val_eq
  rw [hsv, hval i]

/-- Packed `x * y` is lane-wise `MontyField31` multiplication. -/
theorem mul.lanewise (hv : Valid inst p mu) (x y : PackedNeon PMP)
    (hx : Canonical p.val x) (hy : Canonical p.val y) :
    aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul
      inst x y ⦃ z => Canonical p.val z ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
          (toPortable inst.MontyParametersInst) (toVector x)[i] (toVector y)[i] =
            .ok (toVector z)[i] ⦄ := by
  obtain ⟨v, hsafe, hval, heq⟩ := mul.from_vector_arg hv x y hx hy
  refine spec_of_from_vector heq ⟨canonical_unvec hsafe, fun i => ?_⟩
  obtain ⟨c, hc, hcv⟩ := spec_imp_exists
    (Monty31.monty_31.MontyField31.mul.spec hv.monty _ _ (hx i) (hy i))
  rw [hc]; congr 1
  apply element_ext
  rw [unvec_value]
  apply UScalar.eq_of_val_eq
  have h := Monty31.cancel_monty (p := p.val) hv.monty.odd
    (show c.value.val * 2 ^ 32 % p.val = (lane v i).val * 2 ^ 32 % p.val by rw [hcv.2, hval i])
  rw [Nat.ModEq, Nat.mod_eq_of_lt hcv.1, Nat.mod_eq_of_lt (hsafe i)] at h
  exact h

/-- Two canonical elements standing for the same field element are equal (`p` odd). -/
theorem eq_of_toField {MP : Type} {P : ℕ} (hodd : P % 2 = 1) {a b : Element MP}
    (ha : Spec.Monty31.Canonical P a) (hb : Spec.Monty31.Canonical P b)
    (h : Spec.Monty31.toField P a = Spec.Monty31.toField P b) : a = b := by
  unfold Spec.Monty31.toField at h
  have hu := Monty31.two_pow_32_isUnit (P := P) hodd
  have h' : (a.value.val : ZMod P) = b.value.val := by
    have := congrArg (· * (2 ^ 32 : ZMod P)) h
    simp only [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one] at this
    exact this
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact element_ext (UScalar.eq_of_val_eq h')

/-- Packed `-x` is lane-wise `MontyField31` negation, for a portable `FieldParameters` with the
same prime whose `MONTY_ZERO` stands for `0` (which the scalar `neg` subtracts from). -/
theorem neg.lanewise (hv : Valid inst p mu) {mu' : Std.U32}
    (finst : p3_monty_31.data_traits.FieldParameters PMP) (hf : Spec.Monty31.FieldValid finst p mu')
    (hz : finst.MONTY_ZERO ⦃ z => Spec.Monty31.Canonical p.val z ∧ Spec.Monty31.toField p.val z = 0 ⦄)
    (x : PackedNeon PMP) (hx : Canonical p.val x) :
    aarch64_neon.packing.PackedMontyField31Neon.Insts.CoreOpsArithNegPackedMontyField31Neon.neg
      inst x ⦃ z => Canonical p.val z ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg finst
          (toVector x)[i] = .ok (toVector z)[i] ⦄ := by
  obtain ⟨v, hsafe, hval, heq⟩ := neg.from_vector_arg hv x hx
  refine spec_of_from_vector heq ⟨canonical_unvec hsafe, fun i => ?_⟩
  obtain ⟨c, hc, hcv⟩ := spec_imp_exists
    (Monty31.monty_31.MontyField31.neg.toField hf rfl hz _ (hx i))
  rw [hc]; congr 1
  apply eq_of_toField hv.monty.odd hcv.1 (canonical_unvec hsafe i)
  rw [hcv.2]
  unfold Spec.Monty31.toField
  rw [unvec_value, hval i, ← neg_mul]
  congr 1
  have hxi := hx i
  unfold Spec.Monty31.Canonical at hxi
  rw [ZMod.natCast_mod, Nat.cast_sub hxi.le, ZMod.natCast_self, zero_sub]

end

/-! ## `halve_neon` -/

section
open p3_monty_31_neon

/-- `halve_neon(v)`, for `v` with canonical lanes, has canonical lanes, and lane `i` is the
portable scalar `halve` of lane `i`, for a portable `FieldParameters` with the same prime. -/
theorem halve_neon.lanewise {PMP : Type} {inst : data_traits.PackedMontyParameters PMP}
    {p mu mu' : Std.U32} (hv : Valid inst p mu)
    (finst : p3_monty_31.data_traits.FieldParameters PMP) (hf : Spec.Monty31.FieldValid finst p mu')
    (v : U32x4) (hvs : FromVectorSafe p.val v) :
    aarch64_neon.utils.halve_neon inst v ⦃ r => FromVectorSafe p.val r ∧ ∀ i : Fin 4,
      p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve finst
        ⟨lane v i, ()⟩ = .ok ⟨lane r i, ()⟩ ⦄ := by
  obtain ⟨P, hPP, hP⟩ := valid_lnP hv
  obtain ⟨r, hr, hrl⟩ := Neon.halve_neon inst P v p.val hv.monty.lt hv.monty.odd hPP hP
    (fun i hi => hvs ⟨i, hi⟩)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨fun i => (hrl i i.isLt).1, fun i => ?_⟩
  unfold p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
  obtain ⟨s, hs, hsv⟩ := spec_imp_exists (Monty31.utils.halve_u32.spec hf (lane v i) (hvs i))
  rw [hs, bind_ok]
  obtain ⟨c, hc, hcv⟩ := spec_imp_exists (Monty31.monty_31.MontyField31.new_monty.spec
    (inst := finst.PackedMontyParametersInst.MontyParametersInst) s)
  rw [hc]; congr 1
  apply element_ext
  rw [hcv]
  apply UScalar.eq_of_val_eq
  have h2 : s.val * 2 ≡ (lane r i).val * 2 [MOD p.val] := by
    show s.val * 2 % p.val = (lane r i).val * 2 % p.val
    rw [hsv.2, ← ln_lane v i, ← ln_lane r i, (hrl i i.isLt).2]
  have h := Nat.ModEq.cancel_right_of_coprime (c := 2)
    (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hv.monty.odd))) h2
  rw [Nat.ModEq, Nat.mod_eq_of_lt hsv.1, ← ln_lane r i, Nat.mod_eq_of_lt (hrl i i.isLt).1] at h
  exact h

end

end Plonky3Lean.Proofs.Neon
