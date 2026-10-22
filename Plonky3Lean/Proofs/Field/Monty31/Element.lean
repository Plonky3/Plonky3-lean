import Mathlib.Data.ZMod.Units
import Plonky3Lean.Lib.RustM
import Plonky3Lean.Proofs.Field.Monty31.Utils

/-!
# Monty31: what the constructors produce, for any valid parameters

`MontyField31::new`, `new_array` and `new_2d_array`, read through `Plonky3Lean.Spec.Monty31.toField`.

Each input `x` becomes the field element `x mod p`, stored canonically.
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

/-- `MontyField31::new x` never panics on valid parameters and returns the Montgomery form `x · 2^32 mod p`.

The four `const` assertions of `new` are exactly the fields of `Valid`. -/
theorem monty_31.MontyField31.new.spec (hv : Valid inst p mu) (x : Std.U32) :
    monty_31.MontyField31.new inst x ⦃ r => r.value.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold monty_31.MontyField31.new
  rw [hv.prime, hv.bits, hv.monty_mu]
  have hp := hv.lt
  have hodd := hv.odd
  have hinv := hv.inv
  step*
  exact WP.spec_bind (utils.to_monty.spec hv x) fun r hr => (WP.spec_ok _).mpr hr

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

end Plonky3Lean.Proofs.Monty31
