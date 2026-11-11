module

public import Plonky3Lean.Proofs.Blake2sAir.Sound
public import Plonky3Lean.Proofs.Sha256Air.Binary.GenAdd

@[expose] public section

/-!
# An honest G step meets its constraints

Take the words G computes in characteristic 2:

- the stored carries of `a + b` and of `a_1 + b_1` are the ripple carries
- the witness words `d_1`, `b_1`, `d_2`, `b_2` are the words G computes.

Then the step's four additions hold.

The generator's witness of a step is that one: its carry words are `(x + y) ^ x ^ y` above bit 0.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds rotr_bit)
open Plonky3Lean.Proofs.Sha256Air.Binary (step_holds step_ok final_ok)

variable {F : Type} [Field F]

theorem rotl_rotr (x : Word) {n : ℕ} (hn : n < 32) : (x.rotateRight n).rotateLeft n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [rotl_bit _ hn hi, rotr_bit _ hn (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

theorem xor_xor_rotl (d a : Word) {n : ℕ} (hn : n < 32) :
    d ^^^ ((d ^^^ a).rotateRight n).rotateLeft n = a := by
  rw [rotl_rotr _ hn, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The generator's carry cells of `x + y` are the ripple carries. -/
theorem carries_bits (x y : Word) {i : ℕ} (hi : i < 31) :
    (word_to_bits_le (carries_word x y (x + y)) i : F) = bitF (BitVec.carry (i + 1) x y false) := by
  rw [← Plonky3Lean.Proofs.Sha256Air.Binary.xor_add_bit x y (by omega : i + 1 < 32)]
  unfold word_to_bits_le carries_word
  have e : ((x + y ^^^ x ^^^ y) >>> 1 >>> i) = (x + y ^^^ x ^^^ y) >>> (i + 1) := by
    rw [← BitVec.shiftRight_add, Nat.add_comm]
  rw [e]
  by_cases h : ((x + y) ^^^ x ^^^ y).getLsbD (i + 1) = true
  · rw [ite_t ((Plonky3Lean.Proofs.Sha256Air.Binary.shift_and_one _ _).mpr h), h]; simp [bitF]
  · rw [ite_f (fun h' => h ((Plonky3Lean.Proofs.Sha256Air.Binary.shift_and_one _ _).mp h')),
      Bool.eq_false_iff.mpr h]
    simp [bitF]

variable (h2 : (2 : F) = 0)
include h2

/-- A three-word addition with ripple carries and an honest sum meets its constraints. -/
theorem add3_ok {x y z c s : ℕ → F} {X Y Z : Word} (hx : Holds x X) (hy : Holds y Y) (hz : Holds z Z)
    (hc : ∀ i < 31, c i = bitF (BitVec.carry (i + 1) X Y false)) (hs : Holds s (X + Y + Z)) :
    Add3Ok x y z c s := by
  obtain ⟨o0, oi⟩ := step_ok h2 hx hy hc
  exact ⟨⟨o0, oi⟩, final_ok h2 (step_holds h2 hx hy o0 oi) hz hs⟩

/-- A two-word addition with an honest sum meets its constraints. -/
theorem add2_ok {x y s : ℕ → F} {X Y : Word} (hx : Holds x X) (hy : Holds y Y) (hs : Holds s (X + Y)) :
    Add2Ok x y s :=
  final_ok h2 hx hy hs

/-- A G step whose witness holds the words G computes meets its constraints. -/
theorem step_complete {st : State F} {v : List Word} (hs : StateHolds st v) {slots : List ℕ}
    (hsl : ∀ j < 4, slots.getD j 0 < 4) {mx my : ℕ → F} {X Y : Word} (hx : Holds mx X)
    (hy : Holds my Y) {g : Blake2sBinaryGCols F} :
    let A := v.getD (slots.getD 0 0) 0
    let B := v.getD (4 + slots.getD 1 0) 0
    let C := v.getD (8 + slots.getD 2 0) 0
    let D := v.getD (12 + slots.getD 3 0) 0
    let a1 := A + B + X
    let d1 := (D ^^^ a1).rotateRight 16
    let c1 := C + d1
    let b1 := (B ^^^ c1).rotateRight 12
    let a2 := a1 + b1 + Y
    let d2 := (d1 ^^^ a2).rotateRight 8
    let c2 := c1 + d2
    (∀ i < 31, g.add1_carries i = bitF (BitVec.carry (i + 1) A B false)) → Holds g.d1 d1 →
      Holds g.b1 b1 → (∀ i < 31, g.add2_carries i = bitF (BitVec.carry (i + 1) a1 b1 false)) →
      Holds g.d2 d2 → Holds g.b2 ((b1 ^^^ c2).rotateRight 7) → GOk st slots mx my g := by
  intro A B C D a1 d1 c1 b1 a2 d2 c2 hc1 hd1 hb1 hc2 hd2 hb2
  obtain ⟨-, hst⟩ := hs
  have ha := (hst _ (hsl 0 (by norm_num))).1
  have hb := (hst _ (hsl 1 (by norm_num))).2.1
  have hc := (hst _ (hsl 2 (by norm_num))).2.2.1
  have hd := (hst _ (hsl 3 (by norm_num))).2.2.2
  have ea1 : Holds (xor_rotl fieldOps (st.d (slots.getD 3 0)) g.d1 16) a1 := by
    have := xor_rotl_holds h2 (n := 16) (by norm_num) hd hd1
    rwa [xor_xor_rotl _ _ (by norm_num)] at this
  have ec1 : Holds (xor_rotl_var fieldOps (st.b (slots.getD 1 0)) g.b1 12) c1 := by
    have := xor_rotl_holds h2 (n := 12) (by norm_num) hb hb1
    rwa [xor_xor_rotl _ _ (by norm_num)] at this
  have ea2 : Holds (xor_rotl_var fieldOps g.d1 g.d2 8) a2 := by
    have := xor_rotl_holds h2 (n := 8) (by norm_num) hd1 hd2
    rwa [xor_xor_rotl _ _ (by norm_num)] at this
  have ec2 : Holds (xor_rotl_var fieldOps g.b1 g.b2 7) c2 := by
    have := xor_rotl_holds h2 (n := 7) (by norm_num) hb1 hb2
    rwa [xor_xor_rotl _ _ (by norm_num)] at this
  exact ⟨add3_ok h2 ha hb hx hc1 ea1, add2_ok h2 hc hd1 ec1, add3_ok h2 ea1 hb1 hy hc2 ea2,
    add2_ok h2 ec1 hd2 ec2⟩

end Plonky3Lean.Proofs.Blake2sAir
