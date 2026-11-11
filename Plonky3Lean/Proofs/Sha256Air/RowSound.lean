module

public import Plonky3Lean.Proofs.Sha256Air.Words
public import Plonky3Lean.Proofs.Hash.Sha256.Schedule

@[expose] public section

/-!
# One row computes the compression function

Let a row meet its constraints, over a field of characteristic above `7 * 2^16`.

- Each schedule word from 16 on is the recurrence of FIPS 180-4 on the earlier words.
- Each round's new `a` and new `e` are those of FIPS 180-4 on the round's working variables.
- Each output word is the input word plus the last working variable, modulo `2^32`.

The packed intermediates `tmp1`, `t1` and the schedule's partial sum carry no range check.

Their limbs may leave `[0, 2^16)`, but the addition that consumes them outputs bits, and that pins the sum.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_sha256_air.mirror Plonky3Lean.Spec.Sha256

variable {F : Type} [Field F] [DecidableEq F]

section row

variable {loc : ℕ → F} (h : RowSpec loc)
include h

/-- Schedule word t. -/
def wW (loc : ℕ → F) (t : ℕ) : BitVec 32 := wordOf fun b => loc (col.w t b)

/-- Entry k of the `a` chain. -/
def wA (loc : ℕ → F) (k : ℕ) : BitVec 32 := wordOf fun b => loc (col.a_chain k b)

/-- Entry k of the `e` chain. -/
def wE (loc : ℕ → F) (k : ℕ) : BitVec 32 := wordOf fun b => loc (col.e_chain k b)

/-- Output word i. -/
def wH (loc : ℕ → F) (i : ℕ) : BitVec 32 := wordOf fun b => loc (col.h_out i b)

theorem holds_w {t : ℕ} (ht : t < 64) : Holds (fun b => loc (col.w t b)) (wW loc t) :=
  holds_wordOf (h.bool_w t ht)

theorem holds_a {k : ℕ} (hk : k < 68) : Holds (fun b => loc (col.a_chain k b)) (wA loc k) :=
  holds_wordOf (h.bool_a k hk)

theorem holds_e {k : ℕ} (hk : k < 68) : Holds (fun b => loc (col.e_chain k b)) (wE loc k) :=
  holds_wordOf (h.bool_e k hk)

theorem holds_h {i : ℕ} (hi : i < 8) : Holds (fun b => loc (col.h_out i b)) (wH loc i) :=
  holds_wordOf (h.bool_h i hi)

omit h in
/-- A packed column pinned to a word's limbs. -/
theorem pw_col {x : ℕ → F} {f : ℕ → F} {w : BitVec 32}
    (h0 : x 0 - f 0 = 0) (h1 : x 1 - f 1 = 0)
    (hf : ∀ limb < 2, f limb = ((if limb = 0 then lo w else hi w : ℕ) : F)) : PW x (lo w) w.toNat :=
  pw_of_holds (by rw [sub_eq_zero.mp h0, hf 0 (by norm_num)]; rfl)
    (by rw [sub_eq_zero.mp h1, hf 1 (by norm_num)]; rfl)

omit h in
theorem pw_k (t : ℕ) :
    PW (fun limb => if limb = 0 then ((kOf t &&& 0xFFFF : ℕ) : F)
      else ((kOf t >>> BITS_PER_LIMB : ℕ) : F)) (kOf t % 65536) (kOf t) := by
  have := PW.of_limbs (x := fun limb => if limb = 0 then ((kOf t &&& 0xFFFF : ℕ) : F)
      else ((kOf t >>> BITS_PER_LIMB : ℕ) : F)) (a0 := kOf t % 65536) (a1 := kOf t / 65536)
    (by simp [show kOf t &&& 0xFFFF = kOf t % 2 ^ 16 from Nat.and_two_pow_sub_one_eq_mod _ 16])
    (by simp [BITS_PER_LIMB, Nat.shiftRight_eq_div_pow])
  rwa [show ((kOf t % 65536 : ℕ) : ℤ) + (kOf t / 65536 : ℕ) * 65536 = kOf t by push_cast; omega] at this

omit h in
/-- The round constants are below 2^32. -/
theorem kOf_lt : ∀ t < 64, kOf t < 4294967296 := by decide

omit h in
theorem toNat_lt (w : BitVec 32) : (w.toNat : ℤ) < 4294967296 := by
  have := w.isLt; omega

/-- Schedule word t, for 16 <= t < 64, is the recurrence of FIPS 180-4. -/
theorem sched_eq (hp : 7 * 65536 < ringChar F) {i : ℕ} (hi : i < 48) :
    wW loc (i + 16) = smallSigma1 (wW loc (i + 14)) + wW loc (i + 9) + smallSigma0 (wW loc (i + 1)) +
      wW loc i := by
  have hs := h.sched i hi
  simp only [SchedP, show i + 16 - 15 = i + 1 by omega, show i + 16 - 2 = i + 14 by omega,
    show i + 16 - 7 = i + 9 by omega, show i + 16 - 16 = i by omega] at hs
  obtain ⟨⟨s00, s01⟩, ⟨s10, s11⟩, hadd2, hadd3⟩ := hs
  have p0 := pw_col (x := fun limb => loc (col.sched_sigma0 i limb)) s00 s01 (sigmaF_eq (holds_w h (t := i + 1) (by omega)) .SmallSigma0)
  have p1 := pw_col (x := fun limb => loc (col.sched_sigma1 i limb)) s10 s11 (sigmaF_eq (holds_w h (t := i + 14) (by omega)) .SmallSigma1)
  obtain ⟨k1, j1, hk1, hj1, ptmp⟩ := PW.of_add2 hadd2 p1 (pw_pack (holds_w h (t := i + 9) (by omega)))
  obtain ⟨k2, j2, hk2, hj2, pw⟩ := PW.of_add3 hadd3 ptmp p0 (pw_pack (holds_w h (t := i) (by omega)))
  have := lo_lt (sigmaWord .SmallSigma0 (wW loc (i + 1)))
  have := lo_lt (sigmaWord .SmallSigma1 (wW loc (i + 14)))
  have := lo_lt (wW loc (i + 9))
  have := lo_lt (wW loc i)
  have := toNat_lt (sigmaWord .SmallSigma0 (wW loc (i + 1)))
  have := toNat_lt (sigmaWord .SmallSigma1 (wW loc (i + 14)))
  have := toNat_lt (wW loc (i + 9))
  have := toNat_lt (wW loc i)
  have e := toNat_of_pin hp (holds_w h (t := i + 16) (by omega)) pw (by omega) (by omega)
  simp only [sigmaWord] at e
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, Nat.mod_add_mod]
  omega

/-- T1 of round t, from the chain entries t to t + 3 and the schedule. -/
def t1Of (loc : ℕ → F) (t : ℕ) : BitVec 32 :=
  wE loc t + bigSigma1 (wE loc (t + 3)) + ch (wE loc (t + 3)) (wE loc (t + 2)) (wE loc (t + 1)) +
    BitVec.ofNat 32 (kOf t) + wW loc t

/-- Round t: new a is T1 + T2 and new e is d + T1, as in FIPS 180-4. -/
theorem round_eq (hp : 7 * 65536 < ringChar F) {t : ℕ} (ht : t < 64) :
    wA loc (t + 4) = t1Of loc t + (bigSigma0 (wA loc (t + 3)) +
      maj (wA loc (t + 3)) (wA loc (t + 2)) (wA loc (t + 1))) ∧
    wE loc (t + 4) = wA loc t + t1Of loc t := by
  obtain ⟨⟨s10, s11⟩, ⟨c0, c1⟩, htmp, ht1, ⟨s00, s01⟩, ⟨m0, m1⟩, hna, hne⟩ := h.round t ht
  have he3 := holds_e h (k := t + 3) (by omega)
  have he2 := holds_e h (k := t + 2) (by omega)
  have he1 := holds_e h (k := t + 1) (by omega)
  have ha3 := holds_a h (k := t + 3) (by omega)
  have ha2 := holds_a h (k := t + 2) (by omega)
  have ha1 := holds_a h (k := t + 1) (by omega)
  have p1 := pw_col (x := fun limb => loc (col.sigma1_e t limb)) s10 s11 (sigmaF_eq he3 .BigSigma1)
  have pc := pw_col (x := fun limb => loc (col.ch t limb)) c0 c1 (chF_eq he3 he2 he1)
  have p0 := pw_col (x := fun limb => loc (col.sigma0_a t limb)) s00 s01 (sigmaF_eq ha3 .BigSigma0)
  have pm := pw_col (x := fun limb => loc (col.maj t limb)) m0 m1 (majF_eq ha3 ha2 ha1)
  obtain ⟨k1, j1, hk1, hj1, ptmp⟩ := PW.of_add3 htmp p1 pc (pw_pack (holds_e h (k := t) (by omega)))
  obtain ⟨k2, j2, hk2, hj2, pt1⟩ := PW.of_add3 ht1 ptmp (pw_k t) (pw_pack (holds_w h (t := t) ht))
  obtain ⟨k3, j3, hk3, hj3, pa⟩ := PW.of_add3 hna pt1 p0 pm
  obtain ⟨k4, j4, hk4, hj4, pe⟩ := PW.of_add2 hne pt1 (pw_pack (holds_a h (k := t) (by omega)))
  have := kOf_lt t ht
  have := lo_lt (sigmaWord .BigSigma1 (wE loc (t + 3)))
  have := lo_lt (ch (wE loc (t + 3)) (wE loc (t + 2)) (wE loc (t + 1)))
  have := lo_lt (sigmaWord .BigSigma0 (wA loc (t + 3)))
  have := lo_lt (maj (wA loc (t + 3)) (wA loc (t + 2)) (wA loc (t + 1)))
  have := lo_lt (wE loc t)
  have := lo_lt (wA loc t)
  have := lo_lt (wW loc t)
  have := toNat_lt (sigmaWord .BigSigma1 (wE loc (t + 3)))
  have := toNat_lt (ch (wE loc (t + 3)) (wE loc (t + 2)) (wE loc (t + 1)))
  have := toNat_lt (sigmaWord .BigSigma0 (wA loc (t + 3)))
  have := toNat_lt (maj (wA loc (t + 3)) (wA loc (t + 2)) (wA loc (t + 1)))
  have := toNat_lt (wE loc t)
  have := toNat_lt (wA loc t)
  have := toNat_lt (wW loc t)
  have ea := toNat_of_pin hp (holds_a h (k := t + 4) (by omega)) pa (by omega) (by omega)
  have ee := toNat_of_pin hp (holds_e h (k := t + 4) (by omega)) pe (by omega) (by omega)
  simp only [sigmaWord] at ea ee
  have hK : (BitVec.ofNat 32 (kOf t)).toNat = kOf t := by
    rw [BitVec.toNat_ofNat]; omega
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [t1Of, BitVec.toNat_add, hK, Nat.mod_add_mod, Nat.add_mod_mod] <;> omega

/-- Output word i is input word i plus the last working variable i. -/
theorem final_eq (hp : 7 * 65536 < ringChar F) {i : ℕ} (hi : i < 4) :
    wH loc i = wA loc (3 - i) + wA loc (67 - i) ∧ wH loc (4 + i) = wE loc (3 - i) + wE loc (67 - i) := by
  obtain ⟨a0, a1⟩ := h.init_a i hi
  obtain ⟨e0, e1⟩ := h.init_e i hi
  have pa := pw_col (x := fun limb => loc (col.h_in i limb)) a0 a1
    (packF_eq (holds_a h (k := 3 - i) (by omega)))
  have pe := pw_col (x := fun limb => loc (col.h_in (4 + i) limb)) e0 e1
    (packF_eq (holds_e h (k := 3 - i) (by omega)))
  obtain ⟨k1, j1, hk1, hj1, qa⟩ := PW.of_add2 (h.final_a i hi) pa
    (pw_pack (holds_a h (k := 67 - i) (by omega)))
  obtain ⟨k2, j2, hk2, hj2, qe⟩ := PW.of_add2 (h.final_e i hi) pe
    (pw_pack (holds_e h (k := 67 - i) (by omega)))
  have := lo_lt (wA loc (3 - i)); have := lo_lt (wA loc (67 - i))
  have := lo_lt (wE loc (3 - i)); have := lo_lt (wE loc (67 - i))
  have := toNat_lt (wA loc (3 - i)); have := toNat_lt (wA loc (67 - i))
  have := toNat_lt (wE loc (3 - i)); have := toNat_lt (wE loc (67 - i))
  have ea := toNat_of_pin hp (holds_h h (i := i) (by omega)) qa (by omega) (by omega)
  have ee := toNat_of_pin hp (holds_h h (i := 4 + i) (by omega)) qe (by omega) (by omega)
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_add] <;> omega

/-- The block the row compresses: schedule words 0 to 15. -/
def blockOf (loc : ℕ → F) : List (BitVec 32) := (List.range 16).map (wW loc)

/-- The chaining value the row compresses: the first four entries of each chain, in reverse. -/
def chainOf (loc : ℕ → F) : List (BitVec 32) :=
  [wA loc 3, wA loc 2, wA loc 1, wA loc 0, wE loc 3, wE loc 2, wE loc 1, wE loc 0]

omit h in
theorem length_blockOf : (blockOf loc).length = 16 := by simp [blockOf]

theorem schedule_eq (hp : 7 * 65536 < ringChar F) :
    ∀ t < 64, (schedule (blockOf loc)).getD t 0 = wW loc t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.lt_or_ge t 16 with h16 | h16
    · rw [Proofs.Sha256.schedule_lt _ _ length_blockOf h16]
      simp [blockOf, h16]
    · rw [Proofs.Sha256.schedule_ge _ _ length_blockOf h16 ht, ih _ (by omega) (by omega),
        ih _ (by omega) (by omega), ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      have := sched_eq h hp (i := t - 16) (by omega)
      rw [show t - 16 + 16 = t by omega, show t - 16 + 14 = t - 2 by omega,
        show t - 16 + 9 = t - 7 by omega, show t - 16 + 1 = t - 15 by omega] at this
      exact this.symm

omit h in
/-- The transcribed round constants are FIPS 180-4's. -/
theorem kOf_eq : ∀ t < 64, BitVec.ofNat 32 (kOf t) = K.getD t 0 := by decide

/-- The working variables after round t are the chain entries t to t + 3. -/
theorem rounds_eq (hp : 7 * 65536 < ringChar F) :
    ∀ t ≤ 64, rounds (schedule (blockOf loc)) (Vars.ofList (chainOf loc)) t =
      ⟨wA loc (t + 3), wA loc (t + 2), wA loc (t + 1), wA loc t,
        wE loc (t + 3), wE loc (t + 2), wE loc (t + 1), wE loc t⟩ := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [Proofs.Sha256.rounds_succ, ih (by omega), schedule_eq h hp t (by omega), ← kOf_eq t (by omega)]
    obtain ⟨ea, ee⟩ := round_eq h hp (t := t) (by omega)
    simp only [round, ea, ee, t1Of]

/-- The row's output words are the compression of its chaining value and block. -/
theorem row_compress (hp : 7 * 65536 < ringChar F) :
    (List.range 8).map (wH loc) = compress (chainOf loc) (blockOf loc) := by
  rw [compress, rounds_eq h hp 64 le_rfl]
  obtain ⟨h0, h4⟩ := final_eq h hp (i := 0) (by omega)
  obtain ⟨h1, h5⟩ := final_eq h hp (i := 1) (by omega)
  obtain ⟨h2, h6⟩ := final_eq h hp (i := 2) (by omega)
  obtain ⟨h3, h7⟩ := final_eq h hp (i := 3) (by omega)
  simp only [List.range_succ, List.range_zero, List.map, chainOf, Vars.toList, List.zipWith,
    List.nil_append, List.cons_append]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

end row

end Plonky3Lean.Proofs.Sha256Air
