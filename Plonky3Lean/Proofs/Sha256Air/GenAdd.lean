module

public import Plonky3Lean.Proofs.Sha256Air.Words

@[expose] public section

/-!
# Honest additions meet their checks

When the output limbs are those of the sum modulo `2^32`, the two checks of an addition vanish.

This holds in every field, since the differences are integer multiples of `2^16` and `2^32`:

```text
    low limbs:   lo(x + y + z) - lo x - lo y - lo z = -c 2^16,    c in {0, 1, 2}
    words:       (x + y + z mod 2^32) - x - y - z   = -d 2^32,    d in {0, 1, 2}
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

variable {F : Type} [Field F]

/-- The two cells hold the word's limbs. -/
def IsLimbs (a : ℕ → F) (w : BitVec 32) : Prop := a 0 = (lo w : F) ∧ a 1 = (hi w : F)

theorem toNat_split (w : BitVec 32) : (lo w : ℤ) + (hi w : ℤ) * 65536 = w.toNat := by
  simp only [lo, hi]; omega

theorem gen_add2 {o x y : BitVec 32} (ho : o = x + y) {a b c : ℕ → F} (ha : IsLimbs a o)
    (hb : IsLimbs b x) (hc : IsLimbs c y) : Add2P a b c := by
  obtain ⟨a0, a1⟩ := ha; obtain ⟨b0, b1⟩ := hb; obtain ⟨c0, c1⟩ := hc
  have so := toNat_split o; have sx := toNat_split x; have sy := toNat_split y
  have hn : o.toNat = (x.toNat + y.toNat) % 4294967296 := by rw [ho, BitVec.toNat_add]
  have hl : lo o = (lo x + lo y) % 65536 := by simp only [lo]; omega
  have hx := x.isLt; have hy := y.isLt
  obtain ⟨d, hd, ed⟩ : ∃ d : ℤ, (0 ≤ d ∧ d ≤ 1) ∧ (o.toNat : ℤ) - x.toNat - y.toNat = -(d * 4294967296) :=
    ⟨(x.toNat + y.toNat) / 4294967296, by omega, by omega⟩
  obtain ⟨k, hk, ek⟩ : ∃ k : ℤ, (0 ≤ k ∧ k ≤ 1) ∧ (lo o : ℤ) - lo x - lo y = -(k * 65536) := by
    have := lo_lt x; have := lo_lt y
    exact ⟨(lo x + lo y) / 65536, by omega, by omega⟩
  have e1 : a 0 - b 0 - c 0 + (a 1 - b 1 - c 1) * 65536 = ((-(d * 4294967296) : ℤ) : F) := by
    rw [← ed, ← so, ← sx, ← sy, a0, a1, b0, b1, c0, c1]; push_cast; ring
  have e2 : a 0 - b 0 - c 0 = ((-(k * 65536) : ℤ) : F) := by
    rw [← ek, a0, b0, c0]; push_cast; ring
  simp only [Add2P]
  rw [e1, e2]
  constructor
  · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals push_cast; ring
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals push_cast; ring

theorem gen_add3 {o x y z : BitVec 32} (ho : o = x + y + z) {a b c d : ℕ → F} (ha : IsLimbs a o)
    (hb : IsLimbs b x) (hc : IsLimbs c y) (hd : IsLimbs d z) : Add3P a b c d := by
  obtain ⟨a0, a1⟩ := ha; obtain ⟨b0, b1⟩ := hb; obtain ⟨c0, c1⟩ := hc; obtain ⟨d0, d1⟩ := hd
  have so := toNat_split o; have sx := toNat_split x; have sy := toNat_split y
  have sz := toNat_split z
  have hn : o.toNat = (x.toNat + y.toNat + z.toNat) % 4294967296 := by
    rw [ho, BitVec.toNat_add, BitVec.toNat_add]; simp only [Nat.mod_add_mod]
  have hl : lo o = (lo x + lo y + lo z) % 65536 := by simp only [lo]; omega
  have hx := x.isLt; have hy := y.isLt; have hz := z.isLt
  obtain ⟨e, he, ee⟩ : ∃ e : ℤ, (0 ≤ e ∧ e ≤ 2) ∧
      (o.toNat : ℤ) - x.toNat - y.toNat - z.toNat = -(e * 4294967296) :=
    ⟨(x.toNat + y.toNat + z.toNat) / 4294967296, by omega, by omega⟩
  obtain ⟨k, hk, ek⟩ : ∃ k : ℤ, (0 ≤ k ∧ k ≤ 2) ∧ (lo o : ℤ) - lo x - lo y - lo z = -(k * 65536) := by
    have := lo_lt x; have := lo_lt y; have := lo_lt z
    exact ⟨(lo x + lo y + lo z) / 65536, by omega, by omega⟩
  have e1 : a 0 - b 0 - c 0 - d 0 + (a 1 - b 1 - c 1 - d 1) * 65536 =
      ((-(e * 4294967296) : ℤ) : F) := by
    rw [← ee, ← so, ← sx, ← sy, ← sz, a0, a1, b0, b1, c0, c1, d0, d1]; push_cast; ring
  have e2 : a 0 - b 0 - c 0 - d 0 = ((-(k * 65536) : ℤ) : F) := by
    rw [← ek, a0, b0, c0, d0]; push_cast; ring
  simp only [Add3P]
  rw [e1, e2]
  constructor
  · obtain rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    all_goals push_cast; ring
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals push_cast; ring

end Plonky3Lean.Proofs.Sha256Air
