module

public import Plonky3Lean.Proofs.Blake3Air.Words

@[expose] public section

/-!
# The quarter round

Over a field of characteristic above 3 * 2^16, the constraints of a quarter round fix its outputs.

The inputs a and c are given as limbs, b and d as bits, and so are the outputs.

Each half computes, with rotations 16 and 12, then 8 and 7:

```text
    a <- a + b + m
    d <- (d xor a) >>> r_1
    c <- c + d
    b <- (b xor c) >>> r_2
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

/-- Half a quarter round, stored as limbs and bits, satisfies its constraints in every field. -/
theorem half_complete {a b c d m a' b' c' d' : ℕ → F} {wa wb wc wd wm : Word} {r₁ r₂ : ℕ}
    (h₁ : r₁ < 32) (h₂ : r₂ < 32) (ha : LimbsRep a wa) (hb : BitsRep b wb) (hc : LimbsRep c wc)
    (hd : BitsRep d wd) (hm : LimbsRep m wm) (ha' : LimbsRep a' (wa + wb + wm))
    (hd' : BitsRep d' ((wd ^^^ (wa + wb + wm)).rotateRight r₁))
    (hc' : LimbsRep c' (wc + (wd ^^^ (wa + wb + wm)).rotateRight r₁))
    (hb' : BitsRep b' ((wb ^^^ (wc + (wd ^^^ (wa + wb + wm)).rotateRight r₁)).rotateRight r₂)) :
    Add3C a' a (limbs b) m ∧ XorC a' d d' r₁ ∧ Add2C c' c (limbs d') ∧ XorC c' b b' r₂ :=
  ⟨add3C_complete ha' ha (limbsRep_limbs hb) hm rfl,
    xorC_complete h₁ hd hd' (by rw [xor_rotl_rotr _ _ h₁]; exact ha'),
    add2C_complete hc' hc (limbsRep_limbs hd') rfl,
    xorC_complete h₂ hb hb' (by rw [xor_rotl_rotr _ _ h₂]; exact hc')⟩

/-- A quarter round whose cells hold the generator's words satisfies its constraints in every field. -/
theorem qrc_complete {t : QuarterRound F F} {wa wb wc wd mx my : Word} (ha : LimbsRep t.a wa)
    (hb : BitsRep t.b wb) (hc : LimbsRep t.c wc) (hd : BitsRep t.d wd) (hmx : LimbsRep t.m_two_i mx)
    (hmy : LimbsRep t.m_two_i_plus_one my)
    (h' : let r := verifiable_half_round wa wb wc wd mx false
      LimbsRep t.a_prime r.1 ∧ BitsRep t.b_prime r.2.1 ∧ LimbsRep t.c_prime r.2.2.1 ∧
        BitsRep t.d_prime r.2.2.2)
    (h'' : let r := verifiable_half_round wa wb wc wd mx false
      let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 my true
      LimbsRep t.a_output r'.1 ∧ BitsRep t.b_output r'.2.1 ∧ LimbsRep t.c_output r'.2.2.1 ∧
        BitsRep t.d_output r'.2.2.2) : QRC t := by
  obtain ⟨a1, b1, c1, d1⟩ := h'
  obtain ⟨a2, b2, c2, d2⟩ := h''
  obtain ⟨e1, e2, e3, e4⟩ := half_complete (by norm_num) (by norm_num) ha hb hc hd hmx a1 d1 c1 b1
  obtain ⟨e5, e6, e7, e8⟩ := half_complete (by norm_num) (by norm_num) a1 b1 c1 d1 hmy a2 d2 c2 b2
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

variable (hp : 3 * 2 ^ 16 < ringChar F)
include hp

/-- The constraints of half a quarter round fix its outputs. -/
theorem half_sound {a b c d m a' b' c' d' : ℕ → F} {wa wb wc wd wm : Word} {r₁ r₂ : ℕ}
    (h₁ : r₁ < 32) (h₂ : r₂ < 32) (ha : LimbsRep a wa) (hb : BitsRep b wb) (hc : LimbsRep c wc)
    (hd : BitsRep d wd) (hm : LimbsRep m wm) (hadd1 : Add3C a' a (limbs b) m) (hxor1 : XorC a' d d' r₁)
    (hadd2 : Add2C c' c (limbs d')) (hxor2 : XorC c' b b' r₂) :
    LimbsRep a' (wa + wb + wm) ∧ BitsRep d' ((wd ^^^ (wa + wb + wm)).rotateRight r₁) ∧
      LimbsRep c' (wc + (wd ^^^ (wa + wb + wm)).rotateRight r₁) ∧
      BitsRep b' ((wb ^^^ (wc + (wd ^^^ (wa + wb + wm)).rotateRight r₁)).rotateRight r₂) := by
  obtain ⟨wd', hd', ha'⟩ := xorC_sound h₁ hd hxor1
  have e₁ := add3C_sound hp ha' ha (limbsRep_limbs hb) hm hadd1
  obtain rfl := eq_of_xor_rotl h₁ e₁
  obtain ⟨wb', hb', hc'⟩ := xorC_sound h₂ hb hxor2
  have e₂ := add2C_sound hp hc' hc (limbsRep_limbs hd') hadd2
  obtain rfl := eq_of_xor_rotl h₂ e₂
  exact ⟨e₁ ▸ ha', hd', e₂ ▸ hc', hb'⟩

/-- The constraints of a quarter round fix its middle words and its outputs: the two halves of the generator. -/
theorem qrc_sound {t : QuarterRound F F} {wa wb wc wd mx my : Word} (ha : LimbsRep t.a wa)
    (hb : BitsRep t.b wb) (hc : LimbsRep t.c wc) (hd : BitsRep t.d wd) (hmx : LimbsRep t.m_two_i mx)
    (hmy : LimbsRep t.m_two_i_plus_one my) (h : QRC t) :
    let r := verifiable_half_round wa wb wc wd mx false
    let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 my true
    LimbsRep t.a_output r'.1 ∧ BitsRep t.b_output r'.2.1 ∧ LimbsRep t.c_output r'.2.2.1 ∧
      BitsRep t.d_output r'.2.2.2 := by
  obtain ⟨a1, d1, c1, b1⟩ := half_sound hp (by norm_num) (by norm_num) ha hb hc hd hmx h.add1 h.xor1
    h.add2 h.xor2
  obtain ⟨a2, d2, c2, b2⟩ := half_sound hp (by norm_num) (by norm_num) a1 b1 c1 d1 hmy h.add3 h.xor3
    h.add4 h.xor4
  exact ⟨a2, b2, c2, d2⟩

end Plonky3Lean.Proofs.Blake3Air
