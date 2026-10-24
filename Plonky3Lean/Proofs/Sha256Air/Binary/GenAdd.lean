module

public import Plonky3Lean.Proofs.Sha256Air.Binary.Words
public import Plonky3Lean.Proofs.Sha256Air.Binary.Sound

@[expose] public section

/-!
# Honest chained additions in characteristic 2

The generator stores the carries of `x + y` as the bits of `(x + y) ^ x ^ y` above bit 0.

Those are the ripple carries, so every carry constraint of the addition holds.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_sha256_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds)

variable {F : Type} [Field F]

theorem xor_add_bit (x y : BitVec 32) {k : ℕ} (hk : k < 32) :
    ((x + y) ^^^ x ^^^ y).getLsbD k = BitVec.carry k x y false := by
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_add hk]
  cases x.getLsbD k <;> cases y.getLsbD k <;> cases BitVec.carry k x y false <;> rfl

theorem shift_and_one (v : BitVec 32) (n : ℕ) : ((v >>> n) &&& 1 = 1) ↔ v.getLsbD n = true := by
  constructor
  · intro h
    have := congrArg (fun u => u.getLsbD 0) h
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rcases k with _ | k
    · simp [h]
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_one]

/-- The generator's carries of x + y are the ripple carries into bits 1 to 31. -/
theorem carry_bits_eq (x y : BitVec 32) {i : ℕ} (hi : i < 31) :
    carry_bits (F := F) x y (x + y) i = bitF (BitVec.carry (i + 1) x y false) := by
  unfold carry_bits
  rw [← xor_add_bit x y (by omega : i + 1 < 32)]
  by_cases h : ((x + y) ^^^ x ^^^ y).getLsbD (i + 1) = true
  · have e := (shift_and_one _ (i + 1)).mpr h
    simp only [e, ↓reduceIte, h]; simp [bitF]
  · simp only [show ¬ (((x + y) ^^^ x ^^^ y) >>> (i + 1) &&& 1 = 1) from
      fun h' => h ((shift_and_one _ _).mp h'), ↓reduceIte]
    simp [Bool.eq_false_iff.mpr h, bitF]

variable (h2 : (2 : F) = 0)
include h2

/-- The stored-carry constraints of an honest addition hold. -/
theorem step_ok {p w c : ℕ → F} {P W : BitVec 32} (hp : Holds p P) (hw : Holds w W)
    (hc : ∀ i < 31, c i = bitF (BitVec.carry (i + 1) P W false)) :
    p 0 * w 0 + c 0 = 0 ∧ ∀ i ∈ List.range' 1 30, maj fieldOps (p i) (w i) (c (i - 1)) + c i = 0 := by
  have hz : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hp 0 (by omega), hw 0 (by omega), hc 0 (by omega), mul_bitF, BitVec.carry_succ]
    simpa using hz _
  · rw [List.mem_range'_1] at hi
    rw [hp i (by omega), hw i (by omega), hc (i - 1) (by omega), hc i (by omega), maj_bitF h2,
      show i - 1 + 1 = i by omega, BitVec.carry_succ i]
    exact hz _

/-- The constraints of the last addition hold when the sum is honest. -/
theorem final_ok {p l s : ℕ → F} {P L : BitVec 32} (hp : Holds p P) (hl : Holds l L)
    (hs : Holds s (P + L)) :
    s 0 + p 0 + l 0 = 0 ∧ ∀ i ∈ List.range 31, maj fieldOps (p i) (l i) (s i + p i + l i) +
      (s (i + 1) + p (i + 1) + l (i + 1)) = 0 := by
  have hz : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  have hc : ∀ i < 32, s i + p i + l i = bitF (BitVec.carry i P L false) := by
    intro i hi
    rw [hs i hi, hp i hi, hl i hi, add_bitF h2, add_bitF h2, BitVec.getLsbD_add hi]
    cases P.getLsbD i <;> cases L.getLsbD i <;> cases BitVec.carry i P L false <;> rfl
  refine ⟨by rw [hc 0 (by omega)]; simp [bitF], fun i hi => ?_⟩
  rw [List.mem_range] at hi
  rw [hc i (by omega), hc (i + 1) (by omega), hp i (by omega), hl i (by omega), maj_bitF h2,
    ← BitVec.carry_succ]
  exact hz _

omit h2 in
/-- The words and carries of the stored-carry additions, from the partial sum P.

Each carry word holds the ripple carries of its addition. -/
def Chain : BitVec 32 → List ((ℕ → F) × (ℕ → F)) → List (BitVec 32) → Prop
  | _, [], [] => True
  | P, wc :: l, W :: Wl =>
    Holds wc.1 W ∧ (∀ i < 31, wc.2 i = bitF (BitVec.carry (i + 1) P W false)) ∧ Chain (P + W) l Wl
  | _, _, _ => False

theorem fold_ok (l : List ((ℕ → F) × (ℕ → F))) (Wl : List (BitVec 32)) (s : Prop) (p : ℕ → F)
    (P : BitVec 32) (hp : Holds p P) (hs : s) (hc : Chain P l Wl) :
    (l.foldl (add_many_step (pb0 (F := F))) (s, p)).1 ∧
      Holds (l.foldl (add_many_step (pb0 (F := F))) (s, p)).2 (Wl.foldl (· + ·) P) := by
  induction l generalizing Wl s p P with
  | nil => cases Wl with
    | nil => exact ⟨hs, hp⟩
    | cons _ _ => exact hc.elim
  | cons wc l ih => cases Wl with
    | nil => exact hc.elim
    | cons W Wl =>
      obtain ⟨hw, hcar, hc'⟩ := hc
      obtain ⟨o0, oi⟩ := step_ok h2 hp hw hcar
      have hstep : (add_many_step (pb0 (F := F)) (s, p) wc).1 :=
        (step_fst (fun _ => 0) {} (s, p) wc).mpr ⟨⟨hs, o0⟩, oi⟩
      exact ih Wl _ _ (P + W) (step_holds h2 hp hw o0 oi) hstep hc'

/-- An honest chained addition meets its constraints. -/
theorem add_many_ok {w0 : ℕ → F} {rest cs : List (ℕ → F)} {sum : ℕ → F} {W0 : BitVec 32}
    {Wrest : List (BitVec 32)} (hWN : Wrest.length = cs.length + 1)
    (hw0 : Holds w0 W0) (hc : Chain W0 ((rest.take cs.length).zip cs) (Wrest.take cs.length))
    (hl : Holds (rest.getD cs.length fun _ => 0) (Wrest.getD cs.length 0))
    (hs : Holds sum (sumW (W0 :: Wrest))) : add_many (pb0 (F := F)) True (w0 :: rest) cs sum := by
  obtain ⟨hF, hp⟩ := fold_ok h2 _ _ True w0 W0 hw0 trivial hc
  have hsum : sumW (W0 :: Wrest) = (Wrest.take cs.length).foldl (· + ·) W0 + Wrest.getD cs.length 0 := by
    rw [sumW]
    conv_lhs => rw [← List.take_append_drop cs.length Wrest]
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega), List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ (by omega)]
  rw [hsum] at hs
  have hl' : Holds ((w0 :: rest).getD (cs.length + 1) fun _ => (pb0 (F := F)).const 0)
      (Wrest.getD cs.length 0) := hl
  obtain ⟨f0, fi⟩ := final_ok h2 hp hl' hs
  unfold add_many
  simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero]
  exact (Plonky3Lean.Proofs.Sha256Air.foldl_eq_and _ (fun _ _ => rfl) _).mpr ⟨⟨hF, f0⟩, fi⟩

end Plonky3Lean.Proofs.Sha256Air.Binary
