module

public import P3Blake2sAir

@[expose] public section

/-!
# The bit-matrix transpose of the packed generator

The transpose runs six passes, on widths 32, 16, 8, 4, 2 and 1.

The pass of width `2^t` swaps bit `t` of the row index with bit `t` of the column index, where they differ.

```text
    pass 2^t:   bit c of row r   <-   bit (c xor 2^t) of row (r xor 2^t),   when bit t of r and c differ
```

After the six passes every bit of the two indices is swapped, so bit `c` of row `r` is bit `r` of row `c`.
-/

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_blake2s_air.mirror

/-- The swap step on rows `row` and `row + w`. -/
abbrev swapStep (w : ℕ) (m : BitVec 64) (rows : ℕ → BitVec 64) (row : ℕ) : ℕ → BitVec 64 :=
  let swap : BitVec 64 := ((rows row >>> w) ^^^ rows (row + w)) &&& m
  let rows : ℕ → BitVec 64 := Function.update rows row (rows row ^^^ swap <<< w)
  Function.update rows (row + w) (rows (row + w) ^^^ swap)

/-- One pass of the transpose, at width `w` with mask `m`. -/
def tpass (w : ℕ) (m : BitVec 64) (rows : ℕ → BitVec 64) : ℕ → BitVec 64 :=
  ((List.range ((64 + 2 * w - 1) / (2 * w))).map (· * (2 * w))).foldl
    (fun (rows : ℕ → BitVec 64) base => (List.range' base w).foldl (swapStep w m) rows) rows

theorem transpose_step_eq {rows : ℕ → BitVec 64} {w w' : ℕ} {m m' : BitVec 64} (hw : w ≠ 0)
    (hw' : w / 2 = w') (hm : m ^^^ m <<< w' = m') (i : ℕ) :
    transpose_step (rows, w, m) i = (tpass w m rows, w', m') := by
  subst hw' hm
  simp only [transpose_step, ne_eq, hw, not_false_eq_true, ↓reduceIte, Prod.mk.injEq, and_true]
  rfl

theorem transpose_eq (rows : ℕ → BitVec 64) :
    transpose_bits rows =
      tpass 1 0x5555555555555555#64 (tpass 2 0x3333333333333333#64 (tpass 4 0x0f0f0f0f0f0f0f0f#64
        (tpass 8 0x00ff00ff00ff00ff#64 (tpass 16 0x0000ffff0000ffff#64
          (tpass 32 0x00000000ffffffff#64 rows))))) := by
  rw [transpose_bits, show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from rfl, List.foldl_cons,
    transpose_step_eq (m' := 0x0000ffff0000ffff#64) (by decide) (show 32 / 2 = 16 from rfl) (by decide), List.foldl_cons,
    transpose_step_eq (m' := 0x00ff00ff00ff00ff#64) (by decide) (show 16 / 2 = 8 from rfl) (by decide), List.foldl_cons,
    transpose_step_eq (m' := 0x0f0f0f0f0f0f0f0f#64) (by decide) (show 8 / 2 = 4 from rfl) (by decide), List.foldl_cons,
    transpose_step_eq (m' := 0x3333333333333333#64) (by decide) (show 4 / 2 = 2 from rfl) (by decide), List.foldl_cons,
    transpose_step_eq (m' := 0x5555555555555555#64) (by decide) (show 2 / 2 = 1 from rfl) (by decide), List.foldl_cons,
    transpose_step_eq (by decide) (show 1 / 2 = 0 from rfl) rfl, List.foldl_cons, List.foldl_nil]
  simp [transpose_step]

/-! ## A pass on disjoint pairs of rows -/

/-- Swapping disjoint pairs of rows, in any order, swaps each pair once. -/
theorem pairs_fold (w : ℕ) (hw : 0 < w) (m : BitVec 64) (L : List ℕ) (hnd : L.Nodup)
    (hdis : ∀ a ∈ L, ∀ b ∈ L, a ≠ b + w) (rows : ℕ → BitVec 64) (p : ℕ) :
    (L.foldl (swapStep w m) rows) p =
      if p ∈ L then rows p ^^^ (((rows p >>> w) ^^^ rows (p + w)) &&& m) <<< w
      else if w ≤ p ∧ p - w ∈ L then rows p ^^^ (((rows (p - w) >>> w) ^^^ rows p) &&& m)
      else rows p := by
  induction L generalizing rows with
  | nil => simp
  | cons a L ih =>
    have hnd' := (List.nodup_cons.mp hnd)
    have hdis' : ∀ x ∈ L, ∀ y ∈ L, x ≠ y + w := fun x hx y hy =>
      hdis x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons, ih hnd'.2 hdis']
    -- The rows the head step writes.
    have hs : ∀ q, q ≠ a → q ≠ a + w → swapStep w m rows a q = rows q := by
      intro q h1 h2
      simp [swapStep, Function.update, h1, h2]
    have hw0 : w ≠ 0 := by omega
    have ha : swapStep w m rows a a = rows a ^^^ (((rows a >>> w) ^^^ rows (a + w)) &&& m) <<< w := by
      simp [swapStep, Function.update, hw0]
    have haw : swapStep w m rows a (a + w) = rows (a + w) ^^^ (((rows a >>> w) ^^^ rows (a + w)) &&& m) := by
      simp [swapStep, Function.update, hw0]
    by_cases hp : p ∈ L
    · have h1 : p ≠ a := fun h => hnd'.1 (h ▸ hp)
      have h2 : p ≠ a + w := hdis p (List.mem_cons_of_mem _ hp) a List.mem_cons_self
      have h3 : p + w ≠ a := fun h => hdis a List.mem_cons_self p (List.mem_cons_of_mem _ hp) h.symm
      simp only [hp, ↓reduceIte, List.mem_cons, or_true, hs p h1 h2, hs (p + w) h3 (by omega)]
    · by_cases hq : w ≤ p ∧ p - w ∈ L
      · have h1 : p ≠ a := fun h =>
          hdis a List.mem_cons_self (p - w) (List.mem_cons_of_mem _ hq.2) (by omega)
        have h2 : p ≠ a + w := by
          intro h
          apply hnd'.1
          rw [show a = p - w by omega]
          exact hq.2
        have h3 : p - w ≠ a := fun h => hnd'.1 (h ▸ hq.2)
        have h4 : p - w ≠ a + w := hdis _ (List.mem_cons_of_mem _ hq.2) a List.mem_cons_self
        simp only [hp, ↓reduceIte, hq, and_self, List.mem_cons, or_true, hs p h1 h2, hs (p - w) h3 h4,
          h1, or_false]
      · simp only [hp, ↓reduceIte, hq]
        by_cases e1 : p = a
        · subst e1; simp [ha]
        · by_cases e2 : p = a + w
          · subst e2
            simp only [List.mem_cons, e1, false_or, hp, ↓reduceIte, haw, show w ≤ a + w by omega,
              Nat.add_sub_cancel, true_or, and_self]
          · have : ¬ (w ≤ p ∧ (p - w = a ∨ p - w ∈ L)) := by
              rintro ⟨h1, h2 | h2⟩
              · exact e2 (by omega)
              · exact hq ⟨h1, h2⟩
            simp only [List.mem_cons, e1, hp, or_self, ↓reduceIte, this, hs p e1 e2]

/-! ## One pass swaps one bit of the two indices -/

/-- The rows a pass of width `w` swaps with the row `w` below. -/
def passRows (w : ℕ) : List ℕ :=
  ((List.range ((64 + 2 * w - 1) / (2 * w))).map (· * (2 * w))).flatMap fun base => List.range' base w

theorem tpass_eq (w : ℕ) (m : BitVec 64) (rows : ℕ → BitVec 64) :
    tpass w m rows = (passRows w).foldl (swapStep w m) rows := by
  rw [tpass, passRows, List.foldl_flatMap]

/-- The index pair a pass of width `2^t` reads bit `c` of row `r` from. -/
def sw (t : ℕ) (rc : ℕ × ℕ) : ℕ × ℕ :=
  if rc.1.testBit t = rc.2.testBit t then rc else (rc.1 ^^^ 2 ^ t, rc.2 ^^^ 2 ^ t)

/-- The index facts a pass of width `2^t` relies on, all checkable below 64. -/
def PassOK (t : ℕ) (m : BitVec 64) : Prop :=
  (∀ p ∈ passRows (2 ^ t), p < 64 ∧ p.testBit t = false) ∧
  (∀ p < 64, p.testBit t = false → p ∈ passRows (2 ^ t)) ∧
  (passRows (2 ^ t)).Nodup ∧
  (∀ a ∈ passRows (2 ^ t), ∀ b ∈ passRows (2 ^ t), a ≠ b + 2 ^ t) ∧
  (∀ i < 64, m.getLsbD i = !(i.testBit t)) ∧
  (∀ x < 64, x.testBit t = false → x ^^^ 2 ^ t = x + 2 ^ t ∧ x + 2 ^ t < 64) ∧
  (∀ x < 64, x.testBit t = true → 2 ^ t ≤ x ∧ x ^^^ 2 ^ t = x - 2 ^ t ∧ (x - 2 ^ t).testBit t = false) ∧
  (∀ x < 64, x.testBit t = false → 2 ^ t ≤ x → (x - 2 ^ t).testBit t = true)

instance (t : ℕ) (m : BitVec 64) : Decidable (PassOK t m) := by unfold PassOK; infer_instance

/-- A pass of width `2^t` reads bit `c` of row `r` from the pair the swap of bit `t` gives. -/
theorem tpass_bit {t : ℕ} {m : BitVec 64} (h : PassOK t m) (rows : ℕ → BitVec 64) {r c : ℕ}
    (hr : r < 64) (hc : c < 64) :
    (tpass (2 ^ t) m rows r).getLsbD c = (rows (sw t (r, c)).1).getLsbD (sw t (r, c)).2 := by
  obtain ⟨hL1, hL2, hnd, hdis, hm, hx1, hx2, hx3⟩ := h
  have hw : 0 < 2 ^ t := Nat.two_pow_pos t
  rw [tpass_eq, pairs_fold _ hw _ _ hnd hdis, sw]
  cases hrt : r.testBit t
  · -- Row `r` is the upper row of its pair.
    have hmem : r ∈ passRows (2 ^ t) := hL2 r hr hrt
    obtain ⟨hxr, -⟩ := hx1 r hr hrt
    simp only [hmem, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, hc, decide_true, Bool.true_and]
    cases hct : c.testBit t
    · simp only [↓reduceIte]
      by_cases hcw : c < 2 ^ t
      · simp [hcw]
      · rw [hm _ (by omega), hx3 c hc hct (by omega)]
        simp [hcw]
    · obtain ⟨hcw, hxc, -⟩ := hx2 c hc hct
      have hm' : m.getLsbD (c - 2 ^ t) = true := by
        rw [hm _ (by omega), (hx2 c hc hct).2.2]; rfl
      simp only [Bool.false_eq_true, ↓reduceIte, hxr, hxc, show ¬ c < 2 ^ t by omega, decide_false,
        Bool.not_false, Bool.true_and, hm', Bool.and_true, show 2 ^ t + (c - 2 ^ t) = c by omega]
      cases (rows r).getLsbD c <;> simp
  · -- Row `r` is the lower row of its pair.
    obtain ⟨hrw, hxr, hrt'⟩ := hx2 r hr hrt
    have hnot : r ∉ passRows (2 ^ t) := fun h => by simp [(hL1 r h).2] at hrt
    have hmem : 2 ^ t ≤ r ∧ r - 2 ^ t ∈ passRows (2 ^ t) := ⟨hrw, hL2 _ (by omega) hrt'⟩
    simp only [hnot, ↓reduceIte, hmem, and_self, BitVec.getLsbD_xor, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, hm c hc]
    cases hct : c.testBit t
    · obtain ⟨hxc, -⟩ := hx1 c hc hct
      simp only [Bool.true_eq_false, ↓reduceIte, hxr, hxc, Bool.not_false, Bool.and_true,
        show 2 ^ t + c = c + 2 ^ t by omega]
      cases (rows r).getLsbD c <;> simp
    · simp

theorem tpass_bit' {w t : ℕ} (hw : 2 ^ t = w) {m : BitVec 64} (h : PassOK t m) (rows : ℕ → BitVec 64)
    {r c : ℕ} (hr : r < 64) (hc : c < 64) :
    (tpass w m rows r).getLsbD c = (rows (sw t (r, c)).1).getLsbD (sw t (r, c)).2 := by
  subst hw
  exact tpass_bit h rows hr hc

theorem passOK_5 : PassOK 5 0x00000000ffffffff#64 := by decide
theorem passOK_4 : PassOK 4 0x0000ffff0000ffff#64 := by decide
theorem passOK_3 : PassOK 3 0x00ff00ff00ff00ff#64 := by decide
theorem passOK_2 : PassOK 2 0x0f0f0f0f0f0f0f0f#64 := by decide
theorem passOK_1 : PassOK 1 0x3333333333333333#64 := by decide
theorem passOK_0 : PassOK 0 0x5555555555555555#64 := by decide

theorem sw_lt {t : ℕ} (ht : t < 6) {r c : ℕ} (hr : r < 64) (hc : c < 64) :
    (sw t (r, c)).1 < 64 ∧ (sw t (r, c)).2 < 64 := by
  have h2 : 2 ^ t < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) ht
  unfold sw
  split_ifs
  · exact ⟨hr, hc⟩
  · exact ⟨Nat.xor_lt_two_pow (n := 6) hr h2, Nat.xor_lt_two_pow (n := 6) hc h2⟩

/-- The six swaps exchange the two indices. -/
theorem sw_all : ∀ r < 64, ∀ c < 64, sw 5 (sw 4 (sw 3 (sw 2 (sw 1 (sw 0 (r, c)))))) = (c, r) := by
  decide +kernel

/-- The transpose moves bit `r` of row `c` to bit `c` of row `r`. -/
theorem transpose_bit (rows : ℕ → BitVec 64) {r c : ℕ} (hr : r < 64) (hc : c < 64) :
    (transpose_bits rows r).getLsbD c = (rows c).getLsbD r := by
  rw [transpose_eq]
  obtain ⟨h1, h1'⟩ := sw_lt (t := 0) (by norm_num) hr hc
  obtain ⟨h2, h2'⟩ := sw_lt (t := 1) (by norm_num) h1 h1'
  obtain ⟨h3, h3'⟩ := sw_lt (t := 2) (by norm_num) h2 h2'
  obtain ⟨h4, h4'⟩ := sw_lt (t := 3) (by norm_num) h3 h3'
  obtain ⟨h5, h5'⟩ := sw_lt (t := 4) (by norm_num) h4 h4'
  rw [tpass_bit' (w := 1) (t := 0) rfl passOK_0 _ hr hc, tpass_bit' (w := 2) (t := 1) rfl passOK_1 _ h1 h1',
    tpass_bit' (w := 4) (t := 2) rfl passOK_2 _ h2 h2', tpass_bit' (w := 8) (t := 3) rfl passOK_3 _ h3 h3',
    tpass_bit' (w := 16) (t := 4) rfl passOK_4 _ h4 h4', tpass_bit' (w := 32) (t := 5) rfl passOK_5 _ h5 h5']
  simp only [Prod.mk.eta, sw_all r hr c hc]

end Plonky3Lean.Proofs.Blake2sAir
