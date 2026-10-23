module

public import Plonky3Lean.Proofs.Field.Binary.TowerReference
public import Plonky3Lean.Proofs.Field.Binary.ClmulPaths
public import Plonky3Lean.Proofs.Field.Binary.TowerApi

@[expose] public section

/-!
# The remaining field methods

Byte decoding (`from_le_bytes`), the embedding of `GF(2)` (`from_prime_subfield`), the masking
`from_repr` of the tower levels, and the small `Ghash128` and `Poly64` methods.
-/

open Aeneas Aeneas.Std CoreModels
open ConcreteBinaryTower
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## Little-endian bytes -/

/-- The number whose little-endian bytes are `l`. -/
def leNat : List Std.U8 → ℕ
  | [] => 0
  | b :: l => b.val + 256 * leNat l

theorem leNat_lt : ∀ l : List Std.U8, leNat l < 2 ^ (8 * l.length)
  | [] => by simp [leNat]
  | b :: l => by
    have hb : b.val < 2 ^ 8 := by have := b.hBounds; simpa using this
    have := leNat_lt l
    simp only [leNat, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 + 8 * l.length by ring, pow_add]
    nlinarith

theorem toNat_fromLEBytes : ∀ l : List Std.U8,
    (BitVec.fromLEBytes (l.map U8.bv)).toNat = leNat l
  | [] => by
    show (BitVec.ofNat _ 0).toNat = 0
    simp
  | b :: l => by
    have hb : b.val < 2 ^ 8 := by have := b.hBounds; simpa using this
    have hl := leNat_lt l
    rw [List.map_cons, BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, BitVec.toNat_setWidth, toNat_fromLEBytes l, leNat]
    simp only [List.length_cons, List.length_map]
    have hM : 2 ^ (8 * (l.length + 1)) = 2 ^ 8 * 2 ^ (8 * l.length) := by
      rw [← pow_add]; ring_nf
    have hbv : b.bv.toNat = b.val := rfl
    have h0 : b.val % 2 ^ (8 * (l.length + 1)) = b.val :=
      Nat.mod_eq_of_lt (by rw [hM]; nlinarith [Nat.two_pow_pos (8 * l.length)])
    have h1 : leNat l % 2 ^ (8 * (l.length + 1)) = leNat l :=
      Nat.mod_eq_of_lt (by rw [hM]; nlinarith [Nat.two_pow_pos 8])
    have h2 : (leNat l <<< 8) % 2 ^ (8 * (l.length + 1)) = leNat l <<< 8 :=
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, hM]; nlinarith)
    rw [hbv, h0, h1, h2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
    ring

theorem u8_from_le_bytes_val (a : Std.Array Std.U8 1#usize) :
    (Aeneas.Std.core.num.U8.from_le_bytes a).val = leNat a.val := by
  unfold Aeneas.Std.core.num.U8.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromLEBytes _

theorem u16_from_le_bytes_val (a : Std.Array Std.U8 2#usize) :
    (Aeneas.Std.core.num.U16.from_le_bytes a).val = leNat a.val := by
  unfold Aeneas.Std.core.num.U16.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromLEBytes _

theorem u32_from_le_bytes_val (a : Std.Array Std.U8 4#usize) :
    (Aeneas.Std.core.num.U32.from_le_bytes a).val = leNat a.val := by
  unfold Aeneas.Std.core.num.U32.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromLEBytes _

theorem u64_from_le_bytes_val (a : Std.Array Std.U8 8#usize) :
    (Aeneas.Std.core.num.U64.from_le_bytes a).val = leNat a.val := by
  unfold Aeneas.Std.core.num.U64.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromLEBytes _

theorem u128_from_le_bytes_val (a : Std.Array Std.U8 16#usize) :
    (Aeneas.Std.core.num.U128.from_le_bytes a).val = leNat a.val := by
  unfold Aeneas.Std.core.num.U128.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromLEBytes _

theorem bf2_from_repr_level_spec (x : Std.U8) :
    tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 1 ⦄ := by
  unfold tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr
  step*
  rw [i1_post, UScalar.val_and, i_post, Nat.and_two_pow_sub_one_eq_mod]

theorem bf2_from_le_bytes_spec (bytes : Std.Array Std.U8 1#usize) :
    tower.BinaryField2.from_le_bytes bytes ⦃ r => towerOf 1 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField2.from_le_bytes
  simp only [CoreModels.core.num.U8.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u8, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf2_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u8_from_le_bytes_val, Nat.mod_mod]

theorem bf4_from_repr_level_spec (x : Std.U8) :
    tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 2 ⦄ := by
  unfold tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr
  step*
  rw [i1_post, UScalar.val_and, i_post, Nat.and_two_pow_sub_one_eq_mod]

theorem bf4_from_le_bytes_spec (bytes : Std.Array Std.U8 1#usize) :
    tower.BinaryField4.from_le_bytes bytes ⦃ r => towerOf 2 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField4.from_le_bytes
  simp only [CoreModels.core.num.U8.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u8, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf4_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u8_from_le_bytes_val, Nat.mod_mod]

theorem bf8_from_repr_level_spec (x : Std.U8) :
    tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 3 ⦄ := by
  unfold tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.from_repr
  step*

theorem bf8_from_le_bytes_spec (bytes : Std.Array Std.U8 1#usize) :
    tower.BinaryField8.from_le_bytes bytes ⦃ r => towerOf 3 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField8.from_le_bytes
  simp only [CoreModels.core.num.U8.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u8, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf8_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u8_from_le_bytes_val, Nat.mod_mod]

theorem bf16_from_repr_level_spec (x : Std.U16) :
    tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 4 ⦄ := by
  unfold tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.from_repr
  step*

theorem bf16_from_le_bytes_spec (bytes : Std.Array Std.U8 2#usize) :
    tower.BinaryField16.from_le_bytes bytes ⦃ r => towerOf 4 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField16.from_le_bytes
  simp only [CoreModels.core.num.U16.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u16, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf16_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u16_from_le_bytes_val, Nat.mod_mod]

theorem bf32_from_repr_level_spec (x : Std.U32) :
    tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 5 ⦄ := by
  unfold tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.from_repr
  step*

theorem bf32_from_le_bytes_spec (bytes : Std.Array Std.U8 4#usize) :
    tower.BinaryField32.from_le_bytes bytes ⦃ r => towerOf 5 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField32.from_le_bytes
  simp only [CoreModels.core.num.U32.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u32, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf32_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u32_from_le_bytes_val, Nat.mod_mod]

theorem bf64_from_repr_level_spec (x : Std.U64) :
    tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 6 ⦄ := by
  unfold tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.from_repr
  step*

theorem bf64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    tower.BinaryField64.from_le_bytes bytes ⦃ r => towerOf 6 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField64.from_le_bytes
  simp only [CoreModels.core.num.U64.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u64, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf64_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u64_from_le_bytes_val, Nat.mod_mod]

theorem bf128_from_repr_level_spec (x : Std.U128) :
    tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.from_repr x ⦃ r =>
      r.val = x.val % 2 ^ 2 ^ 7 ⦄ := by
  unfold tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.from_repr
  step*

theorem bf128_from_le_bytes_spec (bytes : Std.Array Std.U8 16#usize) :
    tower.BinaryField128.from_le_bytes bytes ⦃ r => towerOf 7 r = fromNat (leNat bytes.val) ⦄ := by
  unfold tower.BinaryField128.from_le_bytes
  simp only [CoreModels.core.num.U128.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u128, Aeneas.Std.bind_ok]
  apply WP.spec_mono (bf128_from_repr_level_spec _)
  intro r hr
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat, hr,
    u128_from_le_bytes_val, Nat.mod_mod]

theorem ghash128_from_le_bytes_spec (bytes : Std.Array Std.U8 16#usize) :
    ghash.Ghash128.from_le_bytes bytes ⦃ r => r.val = leNat bytes.val ⦄ := by
  unfold ghash.Ghash128.from_le_bytes
  simp only [CoreModels.core.num.U128.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u128, Aeneas.Std.bind_ok, WP.spec_ok]
  exact u128_from_le_bytes_val bytes

theorem poly64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    poly64.Poly64.from_le_bytes bytes ⦃ r => r.val = leNat bytes.val ⦄ := by
  unfold poly64.Poly64.from_le_bytes
  simp only [CoreModels.core.num.U64.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u64, Aeneas.Std.bind_ok, WP.spec_ok]
  exact u64_from_le_bytes_val bytes

theorem gf2_from_le_bytes_spec (bytes : Std.Array Std.U8 1#usize) :
    gf2.Gf2.from_le_bytes bytes ⦃ r => r.val = leNat bytes.val % 2 ⦄ := by
  unfold gf2.Gf2.from_le_bytes
  step*
  apply WP.spec_mono (gf2_new_spec i)
  intro r hr
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (show bytes.val.length = 1 by simp)
  rw [hr, i_post1]
  simp [hb, leNat]

/-! ## `GF(2)` inside every field -/

theorem gf2_is_one_spec (f : gf2.Gf2) :
    field_defaults.Gf2.is_one f ⦃ b => b = decide (f.val = 1) ⦄ := by
  unfold field_defaults.Gf2.is_one field_defaults.Gf2.raw_is_one gf2.Gf2.Insts.CoreCmpPartialEqGf2.eq
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  rw [WP.spec_ok]
  by_cases h : f.val = 1
  · have : f = 1#u8 := UScalar.eq_of_val_eq h
    simp [this]
  · have : f ≠ 1#u8 := fun e => h (by rw [e]; rfl)
    simp [this, h]

theorem gf2_from_prime_subfield_spec (f : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r => r = f ⦄ := by
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  rw [WP.spec_ok]

theorem bf2_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf2_from_bool_spec c

theorem bf4_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf4_from_bool_spec c

theorem bf8_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf8_from_bool_spec c

theorem bf16_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf16_from_bool_spec c

theorem bf32_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf32_from_bool_spec c

theorem bf64_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf64_from_bool_spec c

theorem bf128_from_prime_subfield_spec (f : gf2.Gf2) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ bf128_from_bool_spec c

theorem poly64_from_prime_subfield_spec (f : gf2.Gf2) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ poly64_from_bool_spec c

/-! ## `Ghash128` and `Poly64` -/

theorem ghash128_from_bool_spec (b : Bool) :
    ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r => r.val = b.toNat ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool
  cases b <;> simp [CoreModels.core.U128.Insts.CoreConvertFromBool.from]

theorem ghash128_from_prime_subfield_spec (f : gf2.Gf2) :
    ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield f ⦃ r =>
      r.val = (decide (f.val = 1)).toNat ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_prime_subfield
  exact WP.spec_bind (gf2_is_one_spec f) fun c hc => hc ▸ ghash128_from_bool_spec c

theorem ghash128_eq_spec (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreCmpPartialEqGhash128.eq a b ⦃ r => (r = true ↔ ghash a = ghash b) ⦄ := by
  unfold ghash.Ghash128.Insts.CoreCmpPartialEqGhash128.eq
  rw [WP.spec_ok, decide_eq_true_iff]
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  apply UScalar.eq_of_val_eq
  have hq := congrArg toQuot h
  rw [toQuot_eq_mk, toQuot_eq_mk, ← mk_modPoly_128_iff, AdjoinRoot.mk_eq_mk] at hq
  have h0 : a.val ^^^ b.val = 0 := by
    apply mk_natPoly_eq_zero (n := 128) (tail := 135) (by norm_num)
      (Nat.xor_lt_two_pow (u128_val_lt a) (u128_val_lt b))
    rw [natPoly_xor, AdjoinRoot.mk_eq_zero, ← CharTwo.sub_eq_add]
    exact hq
  exact Nat.xor_eq_zero_iff.mp h0

theorem ghash128_bool_check_spec (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      ghash r = ghash a * ghash a + ghash a ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check
  refine WP.spec_bind (ghash128_square_ghash a) fun g hg => ?_
  refine WP.spec_mono (ghash128_add_ghash g a) fun r hr => ?_
  rw [hr, hg]

theorem ghash128_bits_spec : ghash.Ghash128.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 128 ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldField.bits ghash.Ghash128.BITS
  rw [WP.spec_ok]; rfl

theorem poly64_bits_spec : poly64.Poly64.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 64 ⦄ := by
  unfold poly64.Poly64.Insts.P3_fieldFieldField.bits poly64.Poly64.BITS
  rw [WP.spec_ok]; rfl

end Plonky3Lean.Proofs.Binary
