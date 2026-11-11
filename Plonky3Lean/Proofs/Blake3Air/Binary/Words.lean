module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Parametric
public import Plonky3Lean.Proofs.Blake3Air.Words

@[expose] public section

/-!
# Words over a field of characteristic 2

In characteristic 2, the sum of two bits is their xor, and (x + z) (y + z) + z is their majority.

So a sum constraint on bits forces the carries of a binary addition, bit by bit.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F] (h2 : (2 : F) = 0)
include h2

theorem add_bit (a b : Bool) : (bitF a : F) + bitF b = bitF (a ^^ b) := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  cases a <;> cases b <;> simp [bitF, h11]

theorem neg_eq (x : F) : -x = x := by
  have : (2 : F) * x = 0 := by rw [h2, zero_mul]
  linear_combination -this

theorem eq_of_add_eq_zero {x y : F} (h : x + y = 0) : x = y := by
  have := eq_neg_of_add_eq_zero_left h
  rwa [neg_eq h2] at this

theorem maj_bit (a b c : Bool) :
    maj fieldOps (bitF a : F) (bitF b) (bitF c) = bitF (Bool.atLeastTwo a b c) := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  cases a <;> cases b <;> cases c <;> simp [maj, fieldOps, bitF, Bool.atLeastTwo, h11]

theorem mul_bit (a b : Bool) : (bitF a : F) * bitF b = bitF (a && b) := by
  cases a <;> cases b <;> simp [bitF]

/-- The constraints of sum = x + y mod 2^32 on bits. -/
def Add2B (x y sum : ℕ → F) : Prop :=
  sum 0 + x 0 + y 0 = 0 ∧ ∀ i ∈ List.range 31,
    maj fieldOps (x i) (y i) (sum i + x i + y i) + (sum (i + 1) + x (i + 1) + y (i + 1)) = 0

/-- The sum of x and y with the carries, the operand the three-operand addition adds to z. -/
def tOf (x y c : ℕ → F) : ℕ → F := fun i => if i = 0 then x 0 + y 0 else x i + y i + c (i - 1)

/-- The constraints of sum = x + y + z mod 2^32 on bits, with the carries of x + y as columns. -/
def Add3B (x y z c sum : ℕ → F) : Prop :=
  x 0 * y 0 + c 0 = 0 ∧ (∀ i ∈ List.range 30, maj fieldOps (x (i + 1)) (y (i + 1)) (c i) + c (i + 1) = 0) ∧
    Add2B (tOf x y c) z sum

omit h2 in
theorem prop_add2 (env : Plonky3Lean.Spec.Air.Var → F) (L : p3_air.air.mirror.AirLayout) (s : Prop)
    (x y sum : ℕ → F) : binary.add2 (propBuilder env L) s x y sum = (s ∧ Add2B x y sum) := by
  simp [binary.add2, Add2B, foldl_and, and_assoc, pb_ops, fo_add]

omit h2 in
theorem prop_add3 (env : Plonky3Lean.Spec.Air.Var → F) (L : p3_air.air.mirror.AirLayout) (s : Prop)
    (x y z c sum : ℕ → F) : binary.add3 (propBuilder env L) s x y z c sum = (s ∧ Add3B x y z c sum) := by
  simp only [binary.add3, prop_add2, pb_assert_zero, pb_add, pb_mul, foldl_and, Add3B]
  simp only [and_assoc]
  rfl

/-! ## Sums of bits -/

/-- The two-operand constraints on the bits of x and y force the bits of x + y. -/
theorem add2B_sound {x y sum : ℕ → F} {wx wy : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (h : Add2B x y sum) : BitsRep sum (wx + wy) := by
  obtain ⟨h0, hs⟩ := h
  -- The carry into bit i is the carry of the binary addition.
  have hc : ∀ i ≤ 31, sum i + x i + y i = bitF (BitVec.carry i wx wy false) := by
    intro i hi
    induction i with
    | zero => rw [h0]; simp [BitVec.carry, bitF, Nat.mod_one]
    | succ i ih =>
      have := hs i (List.mem_range.mpr (by omega))
      rw [ih (by omega), hx i (by omega), hy i (by omega), maj_bit h2] at this
      rw [← eq_of_add_eq_zero h2 this, BitVec.carry_succ]
  intro i hi
  have e := hc i (by omega)
  rw [hx i hi, hy i hi] at e
  have : sum i = bitF (BitVec.carry i wx wy false) + bitF (wx.getLsbD i) + bitF (wy.getLsbD i) := by
    linear_combination e + (neg_eq h2 (bitF (wx.getLsbD i) + bitF (wy.getLsbD i)) : _)
  rw [this, add_bit h2, add_bit h2, BitVec.getLsbD_add (by omega)]
  cases BitVec.carry i wx wy false <;> cases wx.getLsbD i <;> cases wy.getLsbD i <;> rfl

/-- The three-operand constraints on the bits of x, y and z force the carries of x + y and the bits of x + y + z. -/
theorem add3B_sound {x y z c sum : ℕ → F} {wx wy wz : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (hz : BitsRep z wz) (h : Add3B x y z c sum) :
    BitsRep sum (wx + wy + wz) ∧ ∀ i < 31, c i = bitF (BitVec.carry (i + 1) wx wy false) := by
  obtain ⟨h0, hs, hadd⟩ := h
  have hc : ∀ i < 31, c i = bitF (BitVec.carry (i + 1) wx wy false) := by
    intro i hi
    induction i with
    | zero =>
      rw [hx 0 (by omega), hy 0 (by omega), mul_bit h2] at h0
      rw [(eq_of_add_eq_zero h2 h0).symm, BitVec.carry_succ]
      simp [BitVec.carry, Bool.atLeastTwo, Nat.mod_one]
    | succ i ih =>
      have := hs i (List.mem_range.mpr (by omega))
      rw [ih (by omega), hx (i + 1) (by omega), hy (i + 1) (by omega), maj_bit h2] at this
      rw [← eq_of_add_eq_zero h2 this, BitVec.carry_succ (i + 1)]
  refine ⟨add2B_sound h2 (fun i hi => ?_) hz hadd, hc⟩
  rw [tOf, BitVec.getLsbD_add (by omega)]
  split_ifs with h0'
  · subst h0'
    rw [hx 0 (by omega), hy 0 (by omega), add_bit h2]
    simp [BitVec.carry, Nat.mod_one]
  · rw [hx i hi, hy i hi, hc (i - 1) (by omega), Nat.sub_add_cancel (by omega), add_bit h2, add_bit h2,
      Bool.xor_assoc]

/-- The bits of x xor (y <<< sh). -/
theorem xorRotl_rep {x y : ℕ → F} {wx wy : Word} {sh : ℕ} (hsh : sh < 32) (hx : BitsRep x wx)
    (hy : BitsRep y wy) : BitsRep (xor_rotl fieldOps x y sh) (wx ^^^ wy.rotateLeft sh) := by
  intro i hi
  simp only [xor_rotl, fieldOps]
  rw [hx i hi, hy _ (Nat.mod_lt _ (by norm_num)), add_bit h2, BitVec.getLsbD_xor,
    getLsbD_rotateLeft' _ hsh hi, show i + 32 - sh = 32 + i - sh by omega]

/-- From the bits of x and of x xor (y <<< sh), the cells y hold (x xor that) >>> sh. -/
theorem xorRotl_decode {x y : ℕ → F} {wx W : Word} {sh : ℕ} (hsh : sh < 32) (hx : BitsRep x wx)
    (hw : BitsRep (xor_rotl fieldOps x y sh) W) : BitsRep y ((wx ^^^ W).rotateRight sh) := by
  intro j hj
  have hi : (j + sh) % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have e := hw _ hi
  simp only [xor_rotl, fieldOps] at e
  rw [show ((j + sh) % 32 + 32 - sh) % 32 = j by omega, hx _ hi] at e
  rw [getLsbD_rotateRight' _ hsh hj, BitVec.getLsbD_xor, ← add_bit h2, ← e]
  linear_combination (-(bitF (wx.getLsbD ((j + sh) % 32)) : F)) * h2

/-! ## The constraints of correct words -/

/-- The bits of x, y and x + y satisfy the two-operand constraints. -/
theorem add2B_complete {x y sum : ℕ → F} {wx wy : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (hs : BitsRep sum (wx + wy)) : Add2B x y sum := by
  have hc : ∀ i < 32, sum i + x i + y i = bitF (BitVec.carry i wx wy false) := by
    intro i hi
    rw [hs i hi, hx i hi, hy i hi, BitVec.getLsbD_add hi, add_bit h2, add_bit h2]
    cases BitVec.carry i wx wy false <;> cases wx.getLsbD i <;> cases wy.getLsbD i <;> rfl
  refine ⟨by rw [hc 0 (by norm_num)]; simp [BitVec.carry, bitF, Nat.mod_one], fun i hi => ?_⟩
  rw [List.mem_range] at hi
  rw [hc i (by omega), hc (i + 1) (by omega), hx i (by omega), hy i (by omega), maj_bit h2,
    ← BitVec.carry_succ, add_bit h2, Bool.xor_self]
  simp [bitF]

/-- The bits of x, y, z, x + y + z and the carries of x + y satisfy the three-operand constraints. -/
theorem add3B_complete {x y z c sum : ℕ → F} {wx wy wz : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (hz : BitsRep z wz) (hc : ∀ i < 31, c i = bitF (BitVec.carry (i + 1) wx wy false))
    (hs : BitsRep sum (wx + wy + wz)) : Add3B x y z c sum := by
  have ht : BitsRep (tOf x y c) (wx + wy) := by
    intro i hi
    rw [tOf, BitVec.getLsbD_add hi]
    split_ifs with h0
    · subst h0
      rw [hx 0 (by omega), hy 0 (by omega), add_bit h2]
      simp [BitVec.carry, Nat.mod_one]
    · rw [hx i hi, hy i hi, hc (i - 1) (by omega), Nat.sub_add_cancel (by omega), add_bit h2, add_bit h2,
        Bool.xor_assoc]
  refine ⟨?_, fun i hi => ?_, add2B_complete h2 ht hz hs⟩
  · rw [hx 0 (by norm_num), hy 0 (by norm_num), hc 0 (by norm_num), mul_bit h2, BitVec.carry_succ]
    have h0 : BitVec.carry 0 wx wy false = false := by simp [BitVec.carry, Nat.mod_one]
    rw [h0, add_bit h2]
    cases wx.getLsbD 0 <;> cases wy.getLsbD 0 <;> simp [Bool.atLeastTwo, bitF]
  · rw [List.mem_range] at hi
    rw [hx (i + 1) (by omega), hy (i + 1) (by omega), hc i (by omega), hc (i + 1) (by omega), maj_bit h2,
      ← BitVec.carry_succ, add_bit h2, Bool.xor_self]
    simp [bitF]

/-- The constraints of one G step. -/
def GB (a b c d mx my c1 d1 b1 c2 d2 b2 : ℕ → F) : Prop :=
  Add3B a b mx c1 (xor_rotl fieldOps d d1 16) ∧ Add2B c d1 (xor_rotl fieldOps b b1 12) ∧
    Add3B (xor_rotl fieldOps d d1 16) b1 my c2 (xor_rotl fieldOps d1 d2 8) ∧
    Add2B (xor_rotl fieldOps b b1 12) d2 (xor_rotl fieldOps b1 b2 7)

/-- The constraints of a G step force the words of the generator's two half quarter rounds. -/
theorem gB_sound {a b c d mx my c1 d1 b1 c2 d2 b2 : ℕ → F} {wa wb wc wd wx wy : Word}
    (ha : BitsRep a wa) (hb : BitsRep b wb) (hc : BitsRep c wc) (hd : BitsRep d wd)
    (hx : BitsRep mx wx) (hy : BitsRep my wy) (h : GB a b c d mx my c1 d1 b1 c2 d2 b2) :
    let r := verifiable_half_round wa wb wc wd wx false
    let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 wy true
    BitsRep d1 r.2.2.2 ∧ BitsRep b1 r.2.1 ∧ BitsRep d2 r'.2.2.2 ∧ BitsRep b2 r'.2.1 ∧
      BitsRep (xor_rotl fieldOps d1 d2 8) r'.1 ∧ BitsRep (xor_rotl fieldOps b1 b2 7) r'.2.2.1 := by
  obtain ⟨h1, h2', h3, h4⟩ := h
  have hA1 := (add3B_sound h2 ha hb hx h1).1
  have hd1 := xorRotl_decode h2 (by norm_num) hd hA1
  have hC1 := add2B_sound h2 hc hd1 h2'
  have hb1 := xorRotl_decode h2 (by norm_num) hb hC1
  have hA2 := (add3B_sound h2 hA1 hb1 hy h3).1
  have hd2 := xorRotl_decode h2 (by norm_num) hd1 hA2
  have hC2 := add2B_sound h2 hC1 hd2 h4
  have hb2 := xorRotl_decode h2 (by norm_num) hb1 hC2
  exact ⟨hd1, hb1, hd2, hb2, hA2, hC2⟩

end Plonky3Lean.Proofs.Blake3Air.Binary

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F] (h2 : (2 : F) = 0)
include h2

/-- Witness columns holding the generator's words and carries satisfy the constraints of a G step. -/
theorem gB_complete {a b c d mx my c1 d1 b1 c2 d2 b2 : ℕ → F} {wa wb wc wd wx wy : Word}
    (ha : BitsRep a wa) (hb : BitsRep b wb) (hc : BitsRep c wc) (hd : BitsRep d wd)
    (hx : BitsRep mx wx) (hy : BitsRep my wy) :
    let r := verifiable_half_round wa wb wc wd wx false
    let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 wy true
    (∀ i < 31, c1 i = bitF (BitVec.carry (i + 1) wa wb false)) → BitsRep d1 r.2.2.2 → BitsRep b1 r.2.1 →
    (∀ i < 31, c2 i = bitF (BitVec.carry (i + 1) r.1 r.2.1 false)) → BitsRep d2 r'.2.2.2 →
    BitsRep b2 r'.2.1 → GB a b c d mx my c1 d1 b1 c2 d2 b2 := by
  intro r r' hc1 hd1 hb1 hc2 hd2 hb2
  have hA1 : BitsRep (xor_rotl fieldOps d d1 16) r.1 := by
    have := xorRotl_rep h2 (sh := 16) (by norm_num) hd hd1
    rwa [show r.2.2.2 = (wd ^^^ r.1).rotateRight 16 from rfl, xor_rotl_rotr _ _ (by norm_num)] at this
  have hC1 : BitsRep (xor_rotl fieldOps b b1 12) r.2.2.1 := by
    have := xorRotl_rep h2 (sh := 12) (by norm_num) hb hb1
    rwa [show r.2.1 = (wb ^^^ r.2.2.1).rotateRight 12 from rfl, xor_rotl_rotr _ _ (by norm_num)] at this
  have hA2 : BitsRep (xor_rotl fieldOps d1 d2 8) r'.1 := by
    have := xorRotl_rep h2 (sh := 8) (by norm_num) hd1 hd2
    rwa [show r'.2.2.2 = (r.2.2.2 ^^^ r'.1).rotateRight 8 from rfl, xor_rotl_rotr _ _ (by norm_num)] at this
  have hC2 : BitsRep (xor_rotl fieldOps b1 b2 7) r'.2.2.1 := by
    have := xorRotl_rep h2 (sh := 7) (by norm_num) hb1 hb2
    rwa [show r'.2.1 = (r.2.1 ^^^ r'.2.2.1).rotateRight 7 from rfl, xor_rotl_rotr _ _ (by norm_num)] at this
  exact ⟨add3B_complete h2 ha hb hx hc1 hA1, add2B_complete h2 hc hd1 hC1,
    add3B_complete h2 hA1 hb1 hy hc2 hA2, add2B_complete h2 hC1 hd2 hC2⟩

end Plonky3Lean.Proofs.Blake3Air.Binary
