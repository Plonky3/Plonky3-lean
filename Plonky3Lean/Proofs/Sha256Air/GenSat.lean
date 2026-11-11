module

public import Plonky3Lean.Proofs.Sha256Air.GenRow

@[expose] public section

/-!
# A generated row meets its constraints

In every field, the row the generator fills from any input meets each row constraint.

Bits are 0 or 1, packings and bitwise formulas match their limbs, and every addition is honest.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_sha256_air.mirror Plonky3Lean.Spec.Sha256
open Plonky3Lean.Proofs.KeccakAir (bitF)

variable {F : Type} [Field F]

/-- Cell c of a row. -/
def getc (r : Sha256Cols F) (c : ℕ) : F := r.cells.getD c 0

theorem u32_bits_eq (w : p3_sha256_air.mirror.Word) {i : ℕ} (hi : i < 32) :
    (u32_to_bits_le w i : F) = bitF (w.getLsbD i) := by
  unfold u32_to_bits_le
  have : (w &&& 1#32 <<< i ≠ 0) ↔ w.getLsbD i = true := by
    constructor
    · intro h
      by_contra hb
      apply h
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
      by_cases hki : k = i
      · subst hki; simp_all
      · simp; omega
    · intro h h0
      have := congrArg (fun v => v.getLsbD i) h0
      rw [BitVec.getLsbD_eq_getElem hi] at h
      simp [hi] at this
      simp_all
  by_cases hb : w.getLsbD i <;> simp_all [bitF]

theorem holds_bits {g : ℕ → F} {w : p3_sha256_air.mirror.Word}
    (h : ∀ b < 32, g b = u32_to_bits_le w b) : Holds g w := fun b hb => by
  rw [h b hb, u32_bits_eq w hb]

theorem bool_bits (w : p3_sha256_air.mirror.Word) {i : ℕ} (hi : i < 32) :
    (u32_to_bits_le w i : F) * (u32_to_bits_le w i - 1) = 0 := by
  rw [u32_bits_eq w hi]; cases w.getLsbD i <;> simp [bitF]

theorem limbsF_isLimbs (w : p3_sha256_air.mirror.Word) : IsLimbs (limbsF (F := F) w) w := by
  refine ⟨?_, ?_⟩ <;> simp only [limbsF, u32_to_limbs, lo, hi, BITS_PER_LIMB, ↓reduceIte, one_ne_zero]
  · rfl
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := w.isLt
    congr 1; omega

theorem isLimbs_packF {g : ℕ → F} {w : p3_sha256_air.mirror.Word} (h : Holds g w) :
    IsLimbs (packF g) w := ⟨packF_eq h 0 (by norm_num), packF_eq h 1 (by norm_num)⟩

theorem limbs_sub {a b : ℕ → F} {w : p3_sha256_air.mirror.Word} (ha : IsLimbs a w)
    (hb : ∀ limb < 2, b limb = ((if limb = 0 then lo w else hi w : ℕ) : F)) :
    a 0 - b 0 = 0 ∧ a 1 - b 1 = 0 := by
  rw [ha.1, ha.2, hb 0 (by norm_num), hb 1 (by norm_num)]; simp

/-- The chains hold the working variables: round t reads them at entries t to t + 3. -/
theorem chain_vars (input : List p3_sha256_air.mirror.Word) : ∀ t ≤ 64,
    chA input (t + 3) = (vs input t).a ∧ chA input (t + 2) = (vs input t).b ∧
    chA input (t + 1) = (vs input t).c ∧ chA input t = (vs input t).d ∧
    chE input (t + 3) = (vs input t).e ∧ chE input (t + 2) = (vs input t).f ∧
    chE input (t + 1) = (vs input t).g ∧ chE input t = (vs input t).h := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [chA, chE, vs, rounds, Vars.ofList, hv]
  | succ t ih =>
    intro ht
    obtain ⟨a, b, c, -, e, f, g, -⟩ := ih (by omega)
    rw [vs_succ input (by omega)]
    simp only [round]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [chA, show ¬ t + 1 + 3 < 4 by omega, ↓reduceIte, show t + 1 + 3 - 3 = t + 1 by omega,
        vs_succ input (show t < 64 by omega), round]
    · rw [show t + 1 + 2 = t + 3 by omega, a]
    · rw [show t + 1 + 1 = t + 2 by omega, b]
    · rw [c]
    · simp only [chE, show ¬ t + 1 + 3 < 4 by omega, ↓reduceIte, show t + 1 + 3 - 3 = t + 1 by omega,
        vs_succ input (show t < 64 by omega), round]
    · rw [show t + 1 + 2 = t + 3 by omega, e]
    · rw [show t + 1 + 1 = t + 2 by omega, f]
    · rw [g]

theorem isLimbs_k (t : ℕ) (ht : t < 64) :
    IsLimbs (F := F) (fun limb => if limb = 0 then ((kOf t &&& 0xFFFF : ℕ) : F)
      else ((kOf t >>> BITS_PER_LIMB : ℕ) : F)) (BitVec.ofNat 32 (kOf t)) := by
  have hk := kOf_lt t ht
  refine ⟨?_, ?_⟩ <;> simp only [↓reduceIte, one_ne_zero, lo, hi, BitVec.toNat_ofNat, BITS_PER_LIMB,
    show kOf t &&& 0xFFFF = kOf t % 2 ^ 16 from Nat.and_two_pow_sub_one_eq_mod _ 16,
    Nat.shiftRight_eq_div_pow] <;> congr 1 <;> omega

section row

variable (input : List p3_sha256_air.mirror.Word)

/-- The generated row. -/
abbrev genRow : Sha256Cols F := generate_trace_row_for_compression Sha256Cols.zero input

theorem getc_w {t b : ℕ} (ht : t < 64) (hb : b < 32) :
    getc (genRow (F := F) input) (col.w t b) = u32_to_bits_le (Ws input t) b := by
  rw [getc, cell_w _ ht hb, (gen_spec input).w t ht]

theorem getc_a {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    getc (genRow (F := F) input) (col.a_chain k b) = u32_to_bits_le (chA input k) b := by
  rw [getc, cell_a _ hk hb, (gen_spec input).a k hk]

theorem getc_e {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    getc (genRow (F := F) input) (col.e_chain k b) = u32_to_bits_le (chE input k) b := by
  rw [getc, cell_e _ hk hb, (gen_spec input).e k hk]

theorem getc_h {i b : ℕ} (hi : i < 8) (hb : b < 32) :
    getc (genRow (F := F) input) (col.h_out i b) =
      u32_to_bits_le (input.getD (16 + i) 0 + (vs input 64).toList.getD i 0) b := by
  rw [getc, cell_h_out _ hi hb, (gen_spec input).h_out i hi]

theorem getc_h_in {i : ℕ} (hi : i < 8) :
    IsLimbs (fun limb => getc (genRow (F := F) input) (col.h_in i limb)) (input.getD (16 + i) 0) := by
  have h := limbsF_isLimbs (F := F) (input.getD (16 + i) 0)
  refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [getc, cell_h_in _ hi (by norm_num), (gen_spec input).h_in]
  exacts [h.1, h.2]

theorem limbs_of_cells {f : ℕ → ℕ → ℕ} {g : Sha256Cols F → ℕ → ℕ → F} {i : ℕ}
    {w : p3_sha256_air.mirror.Word}
    (hc : ∀ l < 2, getc (genRow (F := F) input) (f i l) = g (genRow input) i l)
    (hg : g (genRow input) i = limbsF w) : IsLimbs (fun l => getc (genRow (F := F) input) (f i l)) w := by
  have h := limbsF_isLimbs (F := F) w
  refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [hc _ (by norm_num), hg]
  exacts [h.1, h.2]

theorem getc_round {t : ℕ} (ht : t < 64) {f : ℕ → ℕ → ℕ} {off : ℕ}
    (hf : ∀ l, f t l = 6704 + 12 * t + (off + l)) (ho : off + 1 < 12)
    {w : p3_sha256_air.mirror.Word}
    (hr : ∀ l < 2, roundCell (roundSpec (F := F) input t) (off + l) = limbsF w l) :
    IsLimbs (fun l => getc (genRow (F := F) input) (f t l)) w := by
  have h := limbsF_isLimbs (F := F) w
  refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [getc, hf, cell_round _ ht (by omega), (gen_spec input).rounds t ht,
    hr _ (by norm_num)]
  exacts [h.1, h.2]

theorem hw (t : ℕ) (ht : t < 64) : Holds (fun b => getc (genRow (F := F) input) (col.w t b)) (Ws input t) :=
  holds_bits fun _ hb => getc_w input ht hb

theorem ha (k : ℕ) (hk : k < 68) :
    Holds (fun b => getc (genRow (F := F) input) (col.a_chain k b)) (chA input k) :=
  holds_bits fun _ hb => getc_a input hk hb

theorem he (k : ℕ) (hk : k < 68) :
    Holds (fun b => getc (genRow (F := F) input) (col.e_chain k b)) (chE input k) :=
  holds_bits fun _ hb => getc_e input hk hb

/-- In every field, the generated row meets its row constraints. -/
theorem gen_rowSpec : RowSpec (getc (genRow (F := F) input)) := by
  have G := gen_spec (F := F) input
  have cv := chain_vars input
  refine ⟨fun t ht b hb => ?_, fun k hk b hb => ?_, fun k hk b hb => ?_, fun i hi b hb => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun t ht => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [getc_w input ht hb]; exact bool_bits _ hb
  · rw [getc_a input hk hb]; exact bool_bits _ hb
  · rw [getc_e input hk hb]; exact bool_bits _ hb
  · rw [getc_h input hi hb]; exact bool_bits _ hb
  · have hl : IsLimbs (fun limb => getc (genRow (F := F) input) (col.h_in i limb)) (chA input (3 - i)) := by
      have e : chA input (3 - i) = input.getD (16 + i) 0 := by
        simp only [chA, show 3 - i < 4 by omega, ↓reduceIte, show 3 - (3 - i) = i by omega]
      rw [e]
      exact getc_h_in input (by omega)
    exact limbs_sub hl (packF_eq (ha input (3 - i) (by omega)))
  · have hl : IsLimbs (fun limb => getc (genRow (F := F) input) (col.h_in (4 + i) limb))
        (chE input (3 - i)) := by
      have e : chE input (3 - i) = input.getD (16 + (4 + i)) 0 := by
        simp only [chE, show 3 - i < 4 by omega, ↓reduceIte, show 7 - (3 - i) = 4 + i by omega]
      rw [e]
      exact getc_h_in input (by omega)
    exact limbs_sub hl (packF_eq (he input (3 - i) (by omega)))
  · have h0 := limbs_of_cells input (f := col.sched_sigma0) (fun l hl => cell_s0 _ (i := i) (by omega) hl)
      (G.s0 i (by omega))
    have h1 := limbs_of_cells input (f := col.sched_sigma1) (fun l hl => cell_s1 _ (i := i) (by omega) hl)
      (G.s1 i (by omega))
    have ht := limbs_of_cells input (f := col.sched_tmp) (fun l hl => cell_tmp _ (i := i) (by omega) hl)
      (G.tmp i (by omega))
    simp only [SchedP, show i + 16 - 15 = i + 1 by omega, show i + 16 - 2 = i + 14 by omega,
      show i + 16 - 7 = i + 9 by omega, show i + 16 - 16 = i by omega]
    refine ⟨limbs_sub h0 (sigmaF_eq (hw input _ (by omega)) .SmallSigma0),
      limbs_sub h1 (sigmaF_eq (hw input _ (by omega)) .SmallSigma1),
      gen_add2 rfl ht h1 (isLimbs_packF (hw input _ (by omega))),
      gen_add3 (Ws_ge input (t := i + 16) (by omega) (by omega)) (isLimbs_packF (hw input _ (by omega)))
        ht h0 (isLimbs_packF (hw input _ (by omega)))⟩
  · obtain ⟨ca, cb, cc, cd, ce, cf, cg, ch'⟩ := cv t (by omega)
    have hA := fun k (hk : k < 68) => ha (F := F) input k hk
    have hE := fun k (hk : k < 68) => he (F := F) input k hk
    have e3 := hE (t + 3) (by omega); rw [ce] at e3
    have e2 := hE (t + 2) (by omega); rw [cf] at e2
    have e1 := hE (t + 1) (by omega); rw [cg] at e1
    have e0 := hE t (by omega); rw [ch'] at e0
    have a3 := hA (t + 3) (by omega); rw [ca] at a3
    have a2 := hA (t + 2) (by omega); rw [cb] at a2
    have a1 := hA (t + 1) (by omega); rw [cc] at a1
    have a0 := hA t (by omega); rw [cd] at a0
    have hs1 := getc_round input ht (F := F) (f := col.sigma1_e) (off := 0) (w := bigSigma1 (vs input t).e) (fun l => by simp [col.sigma1_e])
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have hch := getc_round input ht (F := F) (f := col.ch) (off := 2) (w := ch (vs input t).e (vs input t).f (vs input t).g) (fun l => by simp [col.ch]; omega)
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have htmp := getc_round input ht (F := F) (f := col.tmp1) (off := 4)
      (w := (vs input t).h + bigSigma1 (vs input t).e + ch (vs input t).e (vs input t).f (vs input t).g) (fun l => by simp [col.tmp1]; omega)
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have ht1 := getc_round input ht (F := F) (f := col.t1) (off := 6) (w := t1s input t) (fun l => by simp [col.t1]; omega)
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have hs0 := getc_round input ht (F := F) (f := col.sigma0_a) (off := 8) (w := bigSigma0 (vs input t).a) (fun l => by simp [col.sigma0_a]; omega)
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have hmj := getc_round input ht (F := F) (f := col.maj) (off := 10) (w := maj (vs input t).a (vs input t).b (vs input t).c) (fun l => by simp [col.maj]; omega)
      (by norm_num) (fun l hl => by interval_cases l <;> rfl)
    have na : chA input (t + 4) = t1s input t + bigSigma0 (vs input t).a +
        maj (vs input t).a (vs input t).b (vs input t).c := by
      simp only [chA, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega,
        vs_succ input ht, round, t1s, add_assoc]
    have ne : chE input (t + 4) = t1s input t + (vs input t).d := by
      simp only [chE, show ¬ t + 4 < 4 by omega, ↓reduceIte, show t + 4 - 3 = t + 1 by omega,
        vs_succ input ht, round, t1s, BitVec.add_comm (vs input t).d]
    refine ⟨limbs_sub hs1 (sigmaF_eq e3 .BigSigma1), limbs_sub hch (chF_eq e3 e2 e1),
      gen_add3 (by simp only [BitVec.add_comm (vs input t).h, BitVec.add_assoc]) htmp hs1 hch
        (isLimbs_packF e0),
      gen_add3 rfl ht1 htmp (isLimbs_k t ht) (isLimbs_packF (hw input t ht)),
      limbs_sub hs0 (sigmaF_eq a3 .BigSigma0), limbs_sub hmj (majF_eq a3 a2 a1),
      gen_add3 na (isLimbs_packF (hA (t + 4) (by omega))) ht1 hs0 hmj,
      gen_add2 ne (isLimbs_packF (hE (t + 4) (by omega))) ht1 (isLimbs_packF a0)⟩
  · obtain ⟨ca, cb, cc, cd, -⟩ := cv 64 le_rfl
    have hh := holds_bits (F := F) fun _ hb => getc_h input (i := i) (by omega) hb
    have hc : chA input (67 - i) = (vs input 64).toList.getD i 0 := by
      interval_cases i
      · exact ca
      · exact cb
      · exact cc
      · exact cd
    have h2 := ha (F := F) input (67 - i) (by omega)
    rw [hc] at h2
    exact gen_add2 rfl (isLimbs_packF hh) (getc_h_in input (by omega)) (isLimbs_packF h2)
  · obtain ⟨-, -, -, -, ce, cf, cg, ch'⟩ := cv 64 le_rfl
    have hh := holds_bits (F := F) fun _ hb => getc_h input (i := 4 + i) (by omega) hb
    have hc : chE input (67 - i) = (vs input 64).toList.getD (4 + i) 0 := by
      interval_cases i
      · exact ce
      · exact cf
      · exact cg
      · exact ch'
    have h2 := he (F := F) input (67 - i) (by omega)
    rw [hc] at h2
    exact gen_add2 rfl (isLimbs_packF hh) (getc_h_in input (by omega)) (isLimbs_packF h2)

end row

end Plonky3Lean.Proofs.Sha256Air
