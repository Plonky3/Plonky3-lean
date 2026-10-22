import Mathlib.Data.ZMod.Units
import Plonky3Lean.Lib.RustM
import Plonky3Lean.Proofs.Field.Monty31.Element

/-!
# Monty31: constructors and scalar arithmetic as field operations, for any valid parameters

`MontyField31::new`, `new_array` and `new_2d_array`, and the `MontyField31` operators `Add`, `Sub`, `Mul`, `Neg` and `PrimeCharacteristicRing::halve`, and `from_monty`, read through `Plonky3Lean.Spec.Monty31.toField`.

The operators are transcribed in `P3Monty31.Assumptions.Mirror`.
The `u32` arithmetic they wrap is extracted.

Each operator, on canonical inputs, is the field operation and returns a canonical value.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-! ## Decoding Montgomery form -/

/-- `2^32` is a unit modulo any odd `P`. -/
theorem two_pow_32_isUnit {P : ℕ} (hodd : P % 2 = 1) : IsUnit (2 ^ 32 : ZMod P) := by
  have h : Nat.Coprime (2 ^ 32) P :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd))
  have := (ZMod.isUnit_iff_coprime (2 ^ 32) P).mpr h
  rwa [Nat.cast_pow, Nat.cast_ofNat] at this

/-- A stored value `n · 2^32 mod P` stands for the field element `n`. -/
theorem toField_eq_of_value {P : ℕ} (hodd : P % 2 = 1) {x : Element MP} {n : ℕ}
    (h : x.value.val = n * 2 ^ 32 % P) : toField P x = n := by
  unfold toField
  rw [h, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
    ZMod.mul_inv_of_unit _ (two_pow_32_isUnit hodd), mul_one]

/-- A stored value reduced mod a positive `P` is canonical. -/
theorem canonical_of_value {P : ℕ} (hP : 0 < P) {x : Element MP} {n : ℕ}
    (h : x.value.val = n * 2 ^ 32 % P) : Canonical P x := by
  unfold Canonical; rw [h]; exact Nat.mod_lt _ hP

/-! ## `MontyField31::new` -/

/-- `MontyField31::new` never panics on valid parameters. -/
theorem monty_31.MontyField31.new.ok (hv : Valid inst p mu) (x : Std.U32) :
    ∃ v, monty_31.MontyField31.new inst x = .ok v := by
  obtain ⟨v, hv, -⟩ := WP.spec_imp_exists (monty_31.MontyField31.new.spec hv x)
  exact ⟨v, hv⟩

/-! ## As field elements

The statements take the modulus as a natural number `P` with `p.val = P`.
This lets a field state them at its own spelling of the modulus, such as CompPoly's `fieldSize`. -/

/-- `MontyField31::new x` stands for `x mod p` and is canonical. -/
theorem monty_31.MontyField31.new.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (x : Std.U32) :
    monty_31.MontyField31.new inst x
      ⦃ r => Canonical P r ∧ toField P r = (x.val : ZMod P) ⦄ := by
  have hodd : P % 2 = 1 := hP ▸ hv.odd
  have hp0 : 0 < P := by omega
  exact WP.spec_mono (monty_31.MontyField31.new.spec hv x) fun _ hr =>
    ⟨canonical_of_value hp0 (hP ▸ hr), toField_eq_of_value hodd (hP ▸ hr)⟩

/-- What `new` does to one input, as a relation between input and output. -/
def NewRel (P : ℕ) (x : Std.U32) (r : Element MP) : Prop :=
  Canonical P r ∧ toField P r = (x.val : ZMod P)

theorem forall₂_newRel {P : ℕ} {l : List Std.U32} {l' : List (Element MP)}
    (h : List.Forall₂ (NewRel P) l l') :
    (∀ y ∈ l', Canonical P y) ∧
      l'.map (toField P) = l.map (fun x => (x.val : ZMod P)) := by
  induction h with
  | nil => simp
  | cons hxy _ ih =>
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxy.1
      · exact ih.1 y hy
    · simp [hxy.2, ih.2]

/-- `MontyField31::new_array` applies `new` elementwise: every output is canonical, and the outputs stand for the inputs mod `p`.

About the hand-written transcription of `new_array`. -/
theorem monty_31.MontyField31.new_array.toField (hv : Valid inst p mu) {P : ℕ}
    (hP : p.val = P) {N : Std.Usize} (input : Array Std.U32 N) :
    monty_31.MontyField31.new_array inst input
      ⦃ r => (∀ y ∈ r.val, Canonical P y) ∧
        r.val.map (toField P) = input.val.map (fun x => (x.val : ZMod P)) ⦄ := by
  obtain ⟨l', hl', hall⟩ :=
    mapM_forall₂ _ (NewRel P) (monty_31.MontyField31.new.toField hv hP) input.val
  have hlen : l'.length = N.val := by rw [← hall.length_eq]; exact input.property
  unfold monty_31.MontyField31.new_array
  rw [hl']
  simp only [bind_tc_ok, hlen, _root_.dite_true]
  exact (WP.spec_ok _).mpr (forall₂_newRel hall)

/-- What `new_array` does to one row, as a relation between input and output. -/
def NewArrayRel (P : ℕ) {N : Std.Usize} (x : Array Std.U32 N) (r : Array (Element MP) N) :
    Prop :=
  (∀ y ∈ r.val, Canonical P y) ∧ r.val.map (toField P) = x.val.map (fun x => (x.val : ZMod P))

theorem forall₂_newArrayRel {P : ℕ} {N : Std.Usize} {l : List (Array Std.U32 N)}
    {l' : List (Array (Element MP) N)} (h : List.Forall₂ (NewArrayRel P) l l') :
    (∀ row ∈ l', ∀ y ∈ row.val, Canonical P y) ∧
      l'.map (fun row => row.val.map (toField P)) =
        l.map (fun row => row.val.map (fun x => (x.val : ZMod P))) := by
  induction h with
  | nil => simp
  | cons hxy _ ih =>
    refine ⟨?_, ?_⟩
    · intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · exact hxy.1
      · exact ih.1 row hrow
    · simp [hxy.2, ih.2]

/-- `MontyField31::new_2d_array` applies `new_array` to each row: every output is canonical, and the outputs stand for the inputs mod `p`.

About the hand-written transcription of `new_2d_array`. -/
theorem monty_31.MontyField31.new_2d_array.toField (hv : Valid inst p mu) {P : ℕ}
    (hP : p.val = P) {N M : Std.Usize} (input : Array (Array Std.U32 N) M) :
    monty_31.MontyField31.new_2d_array inst input
      ⦃ r => (∀ row ∈ r.val, ∀ y ∈ row.val, Canonical P y) ∧
        r.val.map (fun row => row.val.map (toField P)) =
          input.val.map (fun row => row.val.map (fun x => (x.val : ZMod P))) ⦄ := by
  obtain ⟨l', hl', hall⟩ :=
    mapM_forall₂ _ (NewArrayRel P) (monty_31.MontyField31.new_array.toField hv hP) input.val
  have hlen : l'.length = M.val := by rw [← hall.length_eq]; exact input.property
  unfold monty_31.MontyField31.new_2d_array
  rw [hl']
  simp only [bind_tc_ok, hlen, _root_.dite_true]
  exact (WP.spec_ok _).mpr (forall₂_newArrayRel hall)

/-- `MontyField31::new_array` never panics on valid parameters. -/
theorem monty_31.MontyField31.new_array.ok (hv : Valid inst p mu) {N : Std.Usize}
    (input : Array Std.U32 N) :
    ∃ r, monty_31.MontyField31.new_array inst input = .ok r := by
  obtain ⟨r, hr, -⟩ :=
    WP.spec_imp_exists (monty_31.MontyField31.new_array.toField hv rfl input)
  exact ⟨r, hr⟩

/-- `MontyField31::new_2d_array` never panics on valid parameters. -/
theorem monty_31.MontyField31.new_2d_array.ok (hv : Valid inst p mu) {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    ∃ r, monty_31.MontyField31.new_2d_array inst input = .ok r := by
  obtain ⟨r, hr, -⟩ :=
    WP.spec_imp_exists (monty_31.MontyField31.new_2d_array.toField hv rfl input)
  exact ⟨r, hr⟩

/-- `x · 2^(-32)` is determined by `x mod P`. -/
theorem toField_congr {P : ℕ} {x y : Element MP} (h : (x.value.val : ZMod P) = y.value.val) :
    toField P x = toField P y := by
  unfold toField; rw [h]

/-- `a + b`, for canonical `a` and `b`, is canonical and stands for `toField a + toField b`. -/
theorem monty_31.MontyField31.add.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.add inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a + toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  unfold monty_31.MontyField31.add
  refine WP.spec_bind (utils.add.spec hv _ _ ha hb) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  have hp0 : 0 < p.val := by have := hv.odd; omega
  refine ⟨by rw [← hP, hc, hv']; exact Nat.mod_lt _ hp0, ?_⟩
  unfold Spec.Monty31.toField
  rw [hc, hv', ← add_mul, ← Nat.cast_add, hP, ZMod.natCast_mod]

/-- `a - b`, for canonical `a` and `b`, is canonical and stands for `toField a - toField b`. -/
theorem monty_31.MontyField31.sub.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.sub inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a - toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  unfold monty_31.MontyField31.sub
  refine WP.spec_bind (utils.sub.spec hv _ _ ha hb) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  have hp0 : 0 < p.val := by have := hv.odd; omega
  refine ⟨by rw [← hP, hc, hv']; exact Nat.mod_lt _ hp0, ?_⟩
  unfold Spec.Monty31.toField
  rw [hc, hv', ← sub_mul, hP, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ← hP,
    ZMod.natCast_self, add_zero]

/-- `a · b`, for canonical `a` and `b`, is canonical and stands for `toField a · toField b`.

The `u64` product is below `p^2 < 2^32 p`, which is `monty_reduce`'s precondition. -/
theorem monty_31.MontyField31.mul.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P)
    (a b : Element MP) (ha : Canonical P a) (hb : Canonical P b) :
    monty_31.MontyField31.mul inst a b
      ⦃ c => Canonical P c ∧ toField P c = toField P a * toField P b ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha hb
  refine WP.spec_mono (monty_31.MontyField31.mul.spec hv a b ha hb) fun c hc => ?_
  refine ⟨hP ▸ hc.1, ?_⟩
  have h : ((c.value.val * 2 ^ 32 : ℕ) : ZMod P) = ((a.value.val * b.value.val : ℕ) : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hc.2, ZMod.natCast_mod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hu := ZMod.mul_inv_of_unit _ (two_pow_32_isUnit (P := P) (hP ▸ hv.odd))
  unfold Spec.Monty31.toField
  calc (c.value.val : ZMod P) * (2 ^ 32)⁻¹
      = (c.value.val : ZMod P) * 2 ^ 32 * (2 ^ 32)⁻¹ * (2 ^ 32)⁻¹ := by rw [mul_assoc _ (2 ^ 32), hu,
        mul_one]
    _ = _ := by rw [h]; ring

/-- `from_monty(a.value)`, the body of `as_canonical_u32`, is the canonical `u32` for the field element `a` stands for.

Every `a` is accepted, canonical or not. -/
theorem from_monty.toField (hv : Valid inst p mu) {P : ℕ} (hP : p.val = P) (a : Element MP) :
    utils.from_monty inst a.value
      ⦃ r => r.val < P ∧ (r.val : ZMod P) = toField P a ⦄ := by
  refine WP.spec_mono (utils.from_monty.spec hv a.value) fun r hr => ?_
  refine ⟨hP ▸ hr.1, ?_⟩
  have h : ((r.val * 2 ^ 32 : ℕ) : ZMod P) = (a.value.val : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hr.2, ZMod.natCast_mod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hu := ZMod.mul_inv_of_unit _ (two_pow_32_isUnit (P := P) (hP ▸ hv.odd))
  unfold Spec.Monty31.toField
  rw [← h, mul_assoc, hu, mul_one]

variable {FP : Type} {finst : data_traits.FieldParameters FP}

/-- `-a`, for canonical `a`, is canonical and stands for `-toField a`.

It is `MONTY_ZERO - a`, so it needs `MONTY_ZERO` to stand for `0`, which `hz` states. -/
theorem monty_31.MontyField31.neg.toField (hv : FieldValid finst p mu) {P : ℕ}
    (hP : p.val = P)
    (hz : finst.MONTY_ZERO ⦃ z => Canonical P z ∧ toField P z = 0 ⦄)
    (a : Element FP) (ha : Canonical P a) :
    monty_31.MontyField31.neg finst a ⦃ c => Canonical P c ∧ toField P c = -toField P a ⦄ := by
  unfold monty_31.MontyField31.neg
  refine WP.spec_bind hz fun z hz' => ?_
  refine WP.spec_mono (monty_31.MontyField31.sub.toField hv.monty hP z a hz'.1 ha) fun c hc => ?_
  rw [hc.2, hz'.2, zero_sub]
  exact ⟨hc.1, rfl⟩

/-- `a.halve()`, for canonical `a`, is canonical and stands for `toField a / 2`. -/
theorem monty_31.MontyField31.halve.toField (hv : FieldValid finst p mu) {P : ℕ}
    (hP : p.val = P) (a : Element FP) (ha : Canonical P a) :
    monty_31.MontyField31.halve finst a ⦃ c => Canonical P c ∧ toField P c * 2 = toField P a ⦄ := by
  unfold Canonical at *
  rw [← hP] at ha
  unfold monty_31.MontyField31.halve
  refine WP.spec_bind (utils.halve_u32.spec hv _ ha) fun v hv' => ?_
  refine WP.spec_mono (monty_31.MontyField31.new_monty.spec v) fun c hc => ?_
  refine ⟨by rw [← hP, hc]; exact hv'.1, ?_⟩
  have h : ((v.val * 2 : ℕ) : ZMod P) = (a.value.val : ZMod P) := by
    rw [← hP, ← ZMod.natCast_mod, hv'.2]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold Spec.Monty31.toField
  rw [hc, ← h]
  ring

end Plonky3Lean.Proofs.Monty31
