module

public import Plonky3Lean.Proofs.Blake3Air.Row
public import Plonky3Lean.Proofs.KeccakAir.Words
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Words as cells

The AIR holds a 32-bit word either as its 32 bits or as its two 16-bit limbs.

Over a field of characteristic above 3 * 2^16:

- packed bits give the limbs of the word they hold,
- the xor constraints decode their bit cells and fix the limbs of a xor with a rotation,
- the addition constraints on limbs hold exactly when the words add modulo 2^32.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

/-- The cells hold the bits of the word. -/
def BitsRep (f : ℕ → F) (w : Word) : Prop := ∀ k < 32, f k = bitF (w.getLsbD k)

/-- The cells hold the low and high 16-bit limbs of the word. -/
def LimbsRep (f : ℕ → F) (w : Word) : Prop :=
  f 0 = ((w.toNat % 2 ^ 16 : ℕ) : F) ∧ f 1 = ((w.toNat / 2 ^ 16 : ℕ) : F)

/-! ## Packing bits -/

theorem foldl_start (l : List F) (x : F) :
    l.foldl (fun acc e => fieldOps.add (p3_keccak_air.mirror.double fieldOps acc) e) x =
      l.foldl (fun acc e => fieldOps.add (p3_keccak_air.mirror.double fieldOps acc) e)
        (fieldOps.add (p3_keccak_air.mirror.double fieldOps 0) x) := by
  congr 1
  simp [fieldOps, p3_keccak_air.mirror.double]

/-- Packing folds acc <- 2 acc + bit from 0, from the most significant entry. -/
theorem pack_eq (l : List F) : pack_bits_le fieldOps l =
    l.reverse.foldl (fun acc e => fieldOps.add (p3_keccak_air.mirror.double fieldOps acc) e) 0 := by
  unfold pack_bits_le
  cases h : l.reverse with
  | nil => rfl
  | cons x xs => rw [List.foldl_cons, ← foldl_start]

/-- Packed bits from position s are their bit sum. -/
theorem pack_bits (s : ℕ) (g : ℕ → Bool) :
    pack_bits_le fieldOps ((List.range' s 16).map fun z => (bitF (g z) : F)) =
      ((bitsum (fun j => g (s + j)) 16 : ℕ) : F) := by
  rw [pack_eq, ← List.map_reverse, List.foldl_map, foldl_bits, mul_zero, zero_add]

/-- Limb l of a word is the bit sum of its bits 16 l to 16 l + 15. -/
theorem shift_mod_eq_bitsum' {n : ℕ} (w : BitVec n) (l : ℕ) :
    (w >>> (16 * l)).toNat % 2 ^ 16 = bitsum (fun j => w.getLsbD (l * 16 + j)) 16 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitsum_testBit, Nat.testBit_mod_two_pow, ← BitVec.getLsbD, BitVec.getLsbD_ushiftRight]
  by_cases hj : j < 16
  · simp [hj, Nat.mul_comm, Nat.add_comm]
  · simp [hj]

theorem low_eq (w : Word) : w.toNat % 2 ^ 16 = bitsum (fun j => w.getLsbD (0 + j)) 16 := by
  rw [← shift_mod_eq_bitsum' w 0]; simp

theorem high_eq (w : Word) : w.toNat / 2 ^ 16 = bitsum (fun j => w.getLsbD (16 + j)) 16 := by
  have := shift_mod_eq_bitsum' w 1
  simp only [Nat.mul_one, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.one_mul] at this
  rw [← this, Nat.mod_eq_of_lt]
  have := w.isLt
  omega

theorem map_range'_congr {s : ℕ} {f g : ℕ → F} (h : ∀ k, s ≤ k → k < s + 16 → f k = g k) :
    (List.range' s 16).map f = (List.range' s 16).map g :=
  List.map_congr_left fun k hk => by rw [List.mem_range'_1] at hk; exact h k hk.1 hk.2

/-- The limbs packed from the bits of a word are its limbs. -/
theorem limbsRep_limbs {f : ℕ → F} {w : Word} (h : BitsRep f w) : LimbsRep (limbs f) w := by
  constructor
  · simp only [limbs, ite_true, low16, BITS_PER_LIMB, List.range_eq_range']
    rw [map_range'_congr (g := fun z => bitF (w.getLsbD z)) fun k _ hk => h k (by omega),
      pack_bits, low_eq]
  · simp only [limbs, one_ne_zero, ite_false, high16, BITS_PER_LIMB]
    rw [map_range'_congr (g := fun z => bitF (w.getLsbD z)) fun k _ hk => h k (by omega),
      pack_bits, high_eq]

theorem map_range_shift {α : Type} (G : ℕ → α) :
    (List.range 16).map (fun i => G (16 + i)) = (List.range' 16 16).map G := by
  rw [List.range'_eq_map_range, List.map_map]; rfl

/-- Bit i of a word rotated left by sh is bit (32 + i - sh) mod 32 of the word. -/
theorem getLsbD_rotateLeft' (w : Word) {sh i : ℕ} (hsh : sh < 32) (hi : i < 32) :
    (w.rotateLeft sh).getLsbD i = w.getLsbD ((32 + i - sh) % 32) := by
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hsh]
  split_ifs with h
  · congr 1; omega
  · rw [decide_eq_true hi, Bool.true_and]; congr 1; omega

/-- Bit i of a word rotated right by sh is bit (i + sh) mod 32 of the word. -/
theorem getLsbD_rotateRight' (w : Word) {sh i : ℕ} (hsh : sh < 32) (hi : i < 32) :
    (w.rotateRight sh).getLsbD i = w.getLsbD ((i + sh) % 32) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hsh]
  split_ifs with h
  · congr 1; omega
  · rw [decide_eq_true hi, Bool.true_and]; congr 1; omega

/-- From x xor (y <<< sh) = z, the word y is (x xor z) >>> sh. -/
theorem eq_of_xor_rotl {x y z : Word} {sh : ℕ} (hsh : sh < 32) (h : x ^^^ y.rotateLeft sh = z) :
    y = (x ^^^ z).rotateRight sh := by
  subst h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotateRight' _ hsh hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
    getLsbD_rotateLeft' _ hsh (Nat.mod_lt _ (by norm_num)), ← Bool.xor_assoc, Bool.xor_self,
    Bool.false_xor]
  congr 1; omega

theorem rotateLeft_rotateRight' (x : Word) {sh : ℕ} (hsh : sh < 32) :
    (x.rotateRight sh).rotateLeft sh = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotateLeft' _ hsh hi, getLsbD_rotateRight' _ hsh (Nat.mod_lt _ (by norm_num))]
  congr 1; omega

/-- x xor (((x xor z) >>> sh) <<< sh) is z. -/
theorem xor_rotl_rotr (x z : Word) {sh : ℕ} (hsh : sh < 32) :
    x ^^^ ((x ^^^ z).rotateRight sh).rotateLeft sh = z := by
  rw [rotateLeft_rotateRight' _ hsh, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-! ## Decoding bits -/

variable [DecidableEq F]

/-- The word whose bit k is set when cell k is 1. -/
def decodeWord (c : ℕ → F) : Word := BitVec.ofNat 32 (bitsum (fun k => decide (c k = 1)) 32)

/-- Cells that are roots of x (x - 1) hold the bits of the word they decode to. -/
theorem bitsRep_decode {c : ℕ → F} (h : ∀ k < 32, c k * (c k - 1) = 0) : BitsRep c (decodeWord c) := by
  intro k hk
  rw [decodeWord, BitVec.getLsbD_ofNat, bitsum_testBit]
  simpa [hk] using eq_bitF (h k hk)

/-- Cells that are roots of x (x - 1) hold the bits of a word. -/
theorem exists_bitsRep {c : ℕ → F} (h : ∀ k < 32, c k * (c k - 1) = 0) : ∃ w : Word, BitsRep c w :=
  ⟨_, bitsRep_decode h⟩

/-- Cells hold the bits of at most one word. -/
theorem BitsRep.unique {c : ℕ → F} {w w' : Word} (h : BitsRep c w) (h' : BitsRep c w') : w = w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have := (h k hk).symm.trans (h' k hk)
  cases hb : w.getLsbD k <;> cases hb' : w'.getLsbD k <;> simp_all [bitF]

/-- The xor constraints decode c and fix the limbs of a as those of b xor (c <<< sh). -/
theorem xorC_sound {a b c : ℕ → F} {sh : ℕ} (hsh : sh < 32) {wb : Word} (hb : BitsRep b wb)
    (h : XorC a b c sh) : ∃ wc, BitsRep c wc ∧ LimbsRep a (wb ^^^ wc.rotateLeft sh) := by
  obtain ⟨hc, h0, h1⟩ := h
  obtain ⟨wc, hwc⟩ := exists_bitsRep hc
  have hx : ∀ i < 32, p3_keccak_air.mirror.xor fieldOps (b i) (c ((32 + i - sh) % 32)) =
      bitF ((wb ^^^ wc.rotateLeft sh).getLsbD i) := by
    intro i hi
    rw [hb i hi, hwc _ (Nat.mod_lt _ (by norm_num)), xor_bit, BitVec.getLsbD_xor,
      getLsbD_rotateLeft' wc hsh hi]
  refine ⟨wc, hwc, ?_, ?_⟩
  · rw [sub_eq_zero.mp h0, List.range_eq_range',
      map_range'_congr (g := fun z => bitF ((wb ^^^ wc.rotateLeft sh).getLsbD z)) fun k _ hk =>
        hx k (by omega), pack_bits, low_eq]
  · rw [sub_eq_zero.mp h1]
    have e : ∀ i, (32 + (i + 16) - sh) % 32 = (32 + (16 + i) - sh) % 32 := fun i => by rw [Nat.add_comm i]
    simp only [e]
    rw [map_range_shift (fun z => p3_keccak_air.mirror.xor fieldOps (b z) (c ((32 + z - sh) % 32))),
      map_range'_congr (g := fun z => bitF ((wb ^^^ wc.rotateLeft sh).getLsbD z)) fun k _ hk =>
        hx k (by omega), pack_bits, high_eq]

/-! ## The constraints of correct words, in every field -/

section complete

omit [DecidableEq F]

theorem cast_limbs (A : ℕ) : ((A % 2 ^ 16 : ℕ) : F) + ((A / 2 ^ 16 : ℕ) : F) * 2 ^ 16 = (A : F) := by
  have := Nat.mod_add_div A (2 ^ 16)
  have h := congrArg (Nat.cast : ℕ → F) this
  push_cast at h
  linear_combination h

/-- Words that add up satisfy the three-operand addition constraints on their limbs. -/
theorem add3C_complete {a b c d : ℕ → F} {wa wb wc wd : Word} (ha : LimbsRep a wa) (hb : LimbsRep b wb)
    (hc : LimbsRep c wc) (hd : LimbsRep d wd) (h : wa = wb + wc + wd) : Add3C a b c d := by
  have hA : wa.toNat = (wb.toNat + wc.toNat + wd.toNat) % 2 ^ 32 := by
    rw [h, BitVec.toNat_add, BitVec.toNat_add]; omega
  have hb' := wb.isLt
  have hc' := wc.isLt
  have hd' := wd.isLt
  simp only [Add3C, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1, hd.2]
  have e : ∀ x : Word, ((x.toNat % 2 ^ 16 : ℕ) : F) + ((x.toNat / 2 ^ 16 : ℕ) : F) * 2 ^ 16 = x.toNat :=
    fun x => cast_limbs _
  have key : ∀ (X Y : ℕ), X = Y → (X : F) = Y := fun _ _ h => by rw [h]
  constructor
  · have hk : wb.toNat + wc.toNat + wd.toNat = wa.toNat ∨
        wb.toNat + wc.toNat + wd.toNat = wa.toNat + 2 ^ 32 ∨
        wb.toNat + wc.toNat + wd.toNat = wa.toNat + 2 * 2 ^ 32 := by omega
    have ea := e wa; have eb := e wb; have ec := e wc; have ed := e wd
    rcases hk with hk | hk | hk <;> have hk' := key _ _ hk <;> push_cast at hk'
    · left; left; linear_combination ea - eb - ec - ed - hk'
    · left; right; linear_combination ea - eb - ec - ed - hk'
    · right; linear_combination ea - eb - ec - ed - hk'
  · have hk : wb.toNat % 2 ^ 16 + wc.toNat % 2 ^ 16 + wd.toNat % 2 ^ 16 = wa.toNat % 2 ^ 16 ∨
        wb.toNat % 2 ^ 16 + wc.toNat % 2 ^ 16 + wd.toNat % 2 ^ 16 = wa.toNat % 2 ^ 16 + 2 ^ 16 ∨
        wb.toNat % 2 ^ 16 + wc.toNat % 2 ^ 16 + wd.toNat % 2 ^ 16 = wa.toNat % 2 ^ 16 + 2 * 2 ^ 16 := by
      omega
    rcases hk with hk | hk | hk <;> have hk' := key _ _ hk <;> push_cast at hk'
    · left; left; linear_combination -hk'
    · left; right; linear_combination -hk'
    · right; linear_combination -hk'

/-- Words that add up satisfy the two-operand addition constraints on their limbs. -/
theorem add2C_complete {a b c : ℕ → F} {wa wb wc : Word} (ha : LimbsRep a wa) (hb : LimbsRep b wb)
    (hc : LimbsRep c wc) (h : wa = wb + wc) : Add2C a b c := by
  have hA : wa.toNat = (wb.toNat + wc.toNat) % 2 ^ 32 := by rw [h, BitVec.toNat_add]
  have hb' := wb.isLt
  have hc' := wc.isLt
  simp only [Add2C, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
  have e : ∀ x : Word, ((x.toNat % 2 ^ 16 : ℕ) : F) + ((x.toNat / 2 ^ 16 : ℕ) : F) * 2 ^ 16 = x.toNat :=
    fun x => cast_limbs _
  have key : ∀ (X Y : ℕ), X = Y → (X : F) = Y := fun _ _ h => by rw [h]
  constructor
  · have hk : wb.toNat + wc.toNat = wa.toNat ∨ wb.toNat + wc.toNat = wa.toNat + 2 ^ 32 := by omega
    have ea := e wa; have eb := e wb; have ec := e wc
    rcases hk with hk | hk <;> have hk' := key _ _ hk <;> push_cast at hk'
    · left; linear_combination ea - eb - ec - hk'
    · right; linear_combination ea - eb - ec - hk'
  · have hk : wb.toNat % 2 ^ 16 + wc.toNat % 2 ^ 16 = wa.toNat % 2 ^ 16 ∨
        wb.toNat % 2 ^ 16 + wc.toNat % 2 ^ 16 = wa.toNat % 2 ^ 16 + 2 ^ 16 := by omega
    rcases hk with hk | hk <;> have hk' := key _ _ hk <;> push_cast at hk'
    · left; linear_combination -hk'
    · right; linear_combination -hk'

/-- Bits of b and c and limbs of b xor (c <<< sh) satisfy the xor constraints. -/
theorem xorC_complete {a b c : ℕ → F} {wb wc : Word} {sh : ℕ} (hsh : sh < 32) (hb : BitsRep b wb)
    (hc : BitsRep c wc) (ha : LimbsRep a (wb ^^^ wc.rotateLeft sh)) : XorC a b c sh := by
  have hx : ∀ i < 32, p3_keccak_air.mirror.xor fieldOps (b i) (c ((32 + i - sh) % 32)) =
      bitF ((wb ^^^ wc.rotateLeft sh).getLsbD i) := by
    intro i hi
    rw [hb i hi, hc _ (Nat.mod_lt _ (by norm_num)), xor_bit, BitVec.getLsbD_xor,
      getLsbD_rotateLeft' wc hsh hi]
  refine ⟨fun k hk => by rw [hc k hk]; cases wc.getLsbD k <;> simp [bitF], ?_, ?_⟩
  · rw [sub_eq_zero, ha.1, List.range_eq_range',
      map_range'_congr (g := fun z => bitF ((wb ^^^ wc.rotateLeft sh).getLsbD z)) fun k _ hk =>
        hx k (by omega), pack_bits, low_eq]
  · rw [sub_eq_zero, ha.2]
    have e : ∀ i, (32 + (i + 16) - sh) % 32 = (32 + (16 + i) - sh) % 32 := fun i => by rw [Nat.add_comm i]
    simp only [e]
    rw [map_range_shift (fun z => p3_keccak_air.mirror.xor fieldOps (b z) (c ((32 + z - sh) % 32))),
      map_range'_congr (g := fun z => bitF ((wb ^^^ wc.rotateLeft sh).getLsbD z)) fun k _ hk =>
        hx k (by omega), pack_bits, high_eq]

end complete

/-! ## Additions on limbs -/

section add

variable (hp : 3 * 2 ^ 16 < ringChar F)
include hp

/-- An integer of absolute value below the characteristic maps to 0 only if it is 0. -/
theorem int_eq_zero {z : ℤ} (hz : |z| < ringChar F) (h : (z : F) = 0) : z = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((CharP.intCast_eq_zero_iff F (ringChar F) z).mp h) hz

theorem ringChar_prime : (ringChar F).Prime := by
  rcases CharP.char_is_prime_or_zero F (ringChar F) with h | h
  · exact h
  · omega

/-- An integer that both 2^16 and the characteristic divide, of absolute value below their product, is 0. -/
theorem int_eq_zero' {z : ℤ} (hz : |z| < 2 ^ 16 * ringChar F) (h16 : (2 ^ 16 : ℤ) ∣ z) (h : (z : F) = 0) :
    z = 0 := by
  have hpz := (CharP.intCast_eq_zero_iff F (ringChar F) z).mp h
  have hcop : IsCoprime (2 ^ 16 : ℤ) (ringChar F : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hodd : Odd (ringChar F) := (ringChar_prime hp).odd_of_ne_two (by omega)
    have : Nat.Coprime (2 ^ 16) (ringChar F) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast this
  exact Int.eq_zero_of_abs_lt_dvd (hcop.mul_dvd h16 hpz) (by exact_mod_cast hz)

/-- The addition constraints on limbs below 2^16 force the integer equation of a + b + c + d with carry 0, 1 or 2. -/
theorem add3_nat {A0 A1 B0 B1 C0 C1 D0 D1 : ℕ} (hA0 : A0 < 2 ^ 16) (hA1 : A1 < 2 ^ 16)
    (hB0 : B0 < 2 ^ 16) (hB1 : B1 < 2 ^ 16) (hC0 : C0 < 2 ^ 16) (hC1 : C1 < 2 ^ 16)
    (hD0 : D0 < 2 ^ 16) (hD1 : D1 < 2 ^ 16)
    (h : Add3C (F := F) (fun l => if l = 0 then (A0 : F) else A1) (fun l => if l = 0 then (B0 : F) else B1)
      (fun l => if l = 0 then (C0 : F) else C1) (fun l => if l = 0 then (D0 : F) else D1)) :
    (A0 + 2 ^ 16 * A1) % 2 ^ 32 = (B0 + 2 ^ 16 * B1 + (C0 + 2 ^ 16 * C1) + (D0 + 2 ^ 16 * D1)) % 2 ^ 32 := by
  simp only [Add3C, one_ne_zero, ite_false, ite_true] at h
  obtain ⟨h1, h2⟩ := h
  have hp' := hp
  -- The low limbs: their difference is exactly 0, -2^16 or -2^17.
  have h16 : (2 ^ 16 : ℤ) ∣ ((A0 : ℤ) - B0 - C0 - D0) := by
    rcases h2 with (h2 | h2) | h2
    · have := int_eq_zero hp (z := (A0 : ℤ) - B0 - C0 - D0)
        (abs_lt.mpr ⟨by omega, by omega⟩) (by push_cast; linear_combination h2)
      exact ⟨0, by omega⟩
    · have := int_eq_zero hp (z := (A0 : ℤ) - B0 - C0 - D0 + 65536)
        (abs_lt.mpr ⟨by omega, by omega⟩) (by push_cast; linear_combination h2)
      exact ⟨-1, by omega⟩
    · have := int_eq_zero hp (z := (A0 : ℤ) - B0 - C0 - D0 + 131072)
        (abs_lt.mpr ⟨by omega, by omega⟩) (by push_cast; linear_combination h2)
      exact ⟨-2, by omega⟩
  obtain ⟨q, hq⟩ := h16
  -- The words: their difference is exactly 0, -2^32 or -2^33.
  have hP : (3 * 2 ^ 32 : ℤ) < 2 ^ 16 * ringChar F := by
    have : (3 * 2 ^ 16 : ℤ) < ringChar F := by exact_mod_cast hp
    nlinarith
  rcases h1 with (h1 | h1) | h1
  · have := int_eq_zero' hp (z := (A0 : ℤ) - B0 - C0 - D0 + (A1 - B1 - C1 - D1) * 2 ^ 16)
      (abs_lt.mpr ⟨by omega, by omega⟩) ⟨q + (A1 - B1 - C1 - D1), by rw [hq]; ring⟩
      (by push_cast; linear_combination h1)
    omega
  · have := int_eq_zero' hp (z := (A0 : ℤ) - B0 - C0 - D0 + (A1 - B1 - C1 - D1) * 2 ^ 16 + 2 ^ 32)
      (abs_lt.mpr ⟨by omega, by omega⟩) ⟨q + (A1 - B1 - C1 - D1) + 2 ^ 16, by rw [hq]; ring⟩
      (by push_cast; linear_combination h1)
    omega
  · have := int_eq_zero' hp (z := (A0 : ℤ) - B0 - C0 - D0 + (A1 - B1 - C1 - D1) * 2 ^ 16 + 2 ^ 33)
      (abs_lt.mpr ⟨by omega, by omega⟩) ⟨q + (A1 - B1 - C1 - D1) + 2 ^ 17, by rw [hq]; ring⟩
      (by push_cast; linear_combination h1)
    omega

/-- The addition constraints of two operands force the integer equation of a + b + c with carry 0 or 1. -/
theorem add2_nat {A0 A1 B0 B1 C0 C1 : ℕ} (hA0 : A0 < 2 ^ 16) (hA1 : A1 < 2 ^ 16)
    (hB0 : B0 < 2 ^ 16) (hB1 : B1 < 2 ^ 16) (hC0 : C0 < 2 ^ 16) (hC1 : C1 < 2 ^ 16)
    (h : Add2C (F := F) (fun l => if l = 0 then (A0 : F) else A1) (fun l => if l = 0 then (B0 : F) else B1)
      (fun l => if l = 0 then (C0 : F) else C1)) :
    (A0 + 2 ^ 16 * A1) % 2 ^ 32 = (B0 + 2 ^ 16 * B1 + (C0 + 2 ^ 16 * C1)) % 2 ^ 32 := by
  simp only [Add2C, one_ne_zero, ite_false, ite_true] at h
  obtain ⟨h1, h2⟩ := h
  have hp' := hp
  have h16 : (2 ^ 16 : ℤ) ∣ ((A0 : ℤ) - B0 - C0) := by
    rcases h2 with h2 | h2
    · have := int_eq_zero hp (z := (A0 : ℤ) - B0 - C0)
        (abs_lt.mpr ⟨by omega, by omega⟩) (by push_cast; linear_combination h2)
      exact ⟨0, by omega⟩
    · have := int_eq_zero hp (z := (A0 : ℤ) - B0 - C0 + 65536)
        (abs_lt.mpr ⟨by omega, by omega⟩) (by push_cast; linear_combination h2)
      exact ⟨-1, by omega⟩
  obtain ⟨q, hq⟩ := h16
  have hP : (3 * 2 ^ 32 : ℤ) < 2 ^ 16 * ringChar F := by
    have : (3 * 2 ^ 16 : ℤ) < ringChar F := by exact_mod_cast hp
    nlinarith
  rcases h1 with h1 | h1
  · have := int_eq_zero' hp (z := (A0 : ℤ) - B0 - C0 + (A1 - B1 - C1) * 2 ^ 16)
      (abs_lt.mpr ⟨by omega, by omega⟩) ⟨q + (A1 - B1 - C1), by rw [hq]; ring⟩
      (by push_cast; linear_combination h1)
    omega
  · have := int_eq_zero' hp (z := (A0 : ℤ) - B0 - C0 + (A1 - B1 - C1) * 2 ^ 16 + 2 ^ 32)
      (abs_lt.mpr ⟨by omega, by omega⟩) ⟨q + (A1 - B1 - C1) + 2 ^ 16, by rw [hq]; ring⟩
      (by push_cast; linear_combination h1)
    omega

omit hp in
theorem limbs_lt (w : Word) : w.toNat % 2 ^ 16 < 2 ^ 16 ∧ w.toNat / 2 ^ 16 < 2 ^ 16 := by
  have := w.isLt; constructor <;> omega

omit hp in
theorem limbs_sum (w : Word) : w.toNat % 2 ^ 16 + 2 ^ 16 * (w.toNat / 2 ^ 16) = w.toNat :=
  Nat.mod_add_div _ _

/-- The constraints of a = b + c + d mod 2^32 on the limbs of words give the sum of words. -/
theorem add3C_sound {a b c d : ℕ → F} {wa wb wc wd : Word} (ha : LimbsRep a wa) (hb : LimbsRep b wb)
    (hc : LimbsRep c wc) (hd : LimbsRep d wd) (h : Add3C a b c d) : wa = wb + wc + wd := by
  have h' := add3_nat hp (limbs_lt wa).1 (limbs_lt wa).2 (limbs_lt wb).1 (limbs_lt wb).2
    (limbs_lt wc).1 (limbs_lt wc).2 (limbs_lt wd).1 (limbs_lt wd).2
    (by simpa only [Add3C, one_ne_zero, ite_false, ite_true, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1,
      hd.2] using h)
  rw [limbs_sum, limbs_sum, limbs_sum, limbs_sum] at h'
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add]
  have := wa.isLt
  omega

/-- The constraints of a = b + c mod 2^32 on the limbs of words give the sum of words. -/
theorem add2C_sound {a b c : ℕ → F} {wa wb wc : Word} (ha : LimbsRep a wa) (hb : LimbsRep b wb)
    (hc : LimbsRep c wc) (h : Add2C a b c) : wa = wb + wc := by
  have h' := add2_nat hp (limbs_lt wa).1 (limbs_lt wa).2 (limbs_lt wb).1 (limbs_lt wb).2
    (limbs_lt wc).1 (limbs_lt wc).2
    (by simpa only [Add2C, one_ne_zero, ite_false, ite_true, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2] using h)
  rw [limbs_sum, limbs_sum, limbs_sum] at h'
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add]
  have := wa.isLt
  omega

/-- Limb cells hold at most one word. -/
theorem LimbsRep.unique {f : ℕ → F} {w w' : Word} (h : LimbsRep f w) (h' : LimbsRep f w') : w = w' := by
  have hp16 : 2 ^ 16 ≤ ringChar F := by omega
  have e0 := cast_inj hp16 (limbs_lt w).1 (limbs_lt w').1 (h.1.symm.trans h'.1)
  have e1 := cast_inj hp16 (limbs_lt w).2 (limbs_lt w').2 (h.2.symm.trans h'.2)
  apply BitVec.eq_of_toNat_eq
  rw [← limbs_sum w, ← limbs_sum w', e0, e1]

end add

end Plonky3Lean.Proofs.Blake3Air
