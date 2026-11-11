module

public import Plonky3Lean.Proofs.Sha256Air.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Row

@[expose] public section

/-!
# The constraints of one row of the SHA-256 AIR over a prime field

The row builder evaluates the AIR at one row and conjoins what it asserts.

Here that conjunction is written out helper by helper:

- every bit column is a root of x (x - 1)
- the packed input words are the packings of the first chain entries
- each sigma, Ch and Maj column is the packing of its bitwise formula
- each addition meets its two checks, one on the whole words and one on the low limbs
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf foldl_and)

variable {F : Type} [Field F]

/-! ## The helpers in the field -/

/-- The packing of a word of field elements: limb `limb` folds its 16 bits from the top. -/
abbrev packF (bits : ℕ → F) (limb : ℕ) : F := pack_word fieldOps bits limb

/-- The two checks of an addition of two words: on the whole words, and on the low limbs. -/
def Add2P (a b c : ℕ → F) : Prop :=
  let acc_16 := a 0 - b 0 - c 0
  let acc := acc_16 + (a 1 - b 1 - c 1) * 65536
  acc * (acc + 65536 * 65536) = 0 ∧ acc_16 * (acc_16 + 65536) = 0

/-- The two cubic checks of an addition of three words. -/
def Add3P (a b c d : ℕ → F) : Prop :=
  let acc_16 := a 0 - b 0 - c 0 - d 0
  let acc := acc_16 + (a 1 - b 1 - c 1 - d 1) * 65536
  acc * (acc + 65536 * 65536) * (acc + (65536 * 65536 + 65536 * 65536)) = 0 ∧
    acc_16 * (acc_16 + 65536) * (acc_16 + (65536 + 65536)) = 0

/-- Limb `limb` of sigma of a word of bits, as the AIR builds it. -/
def sigmaF (bits : ℕ → F) (spec : SigmaSpec) (limb : ℕ) : F :=
  let (r1, r2, r3, kind) := sigma_params spec
  let get_shifted_bit : ℕ → F := fun i =>
    match kind with
    | .Rotate => bits ((i + r3) % WORD_BITS)
    | .Logical => if i + r3 < WORD_BITS then bits (i + r3) else (0 : F)
  (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
    acc + acc + xor3 fieldOps (bits ((i + r1) % WORD_BITS)) (bits ((i + r2) % WORD_BITS))
      (get_shifted_bit i)) 0

/-- Limb `limb` of Ch(e, f, g), as the AIR builds it. -/
def chF (e f g : ℕ → F) (limb : ℕ) : F :=
  (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
    acc + acc + (e i * f i + (1 - e i) * g i)) 0

/-- Limb `limb` of Maj(a, b, c), as the AIR builds it. -/
def majF (a b c : ℕ → F) (limb : ℕ) : F :=
  (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
    acc + acc + (a i * b i + c i * xor fieldOps (a i) (b i))) 0

/-! ## The helpers on the row builder -/

section helpers

variable (env : Var → F) (L : AirLayout) (s : Prop)

theorem exp_two_16 : exp_u64 (fieldOps (F := F)) 2 16 = 65536 := by
  simp [exp_u64, fieldOps, Nat.size, Nat.binaryRec, List.range_succ]
  norm_num [show Nat.testBit 16 4 = true by decide, show Nat.testBit 16 3 = false by decide,
    show Nat.testBit 16 2 = false by decide, show Nat.testBit 16 1 = false by decide]

theorem pb_mul_2exp (x : F) : mul_2exp_u64 (propBuilder env L).toExprOps x 16 = x * 65536 := by
  simp only [mul_2exp_u64]
  exact congrArg (x * ·) exp_two_16

theorem pb_assert_zeros2 (x y : F) :
    (propBuilder env L).assert_zeros s [x, y] = (s ∧ x = 0 ∧ y = 0) := by
  simp [AirBuilder.assert_zeros, propBuilder, and_assoc]

theorem prop_add2 (a b c : ℕ → F) : add2 (propBuilder env L) s a b c = (s ∧ Add2P a b c) := by
  simp only [add2, pb_mul_2exp, pb_assert_zeros2, Add2P]; rfl

theorem prop_add2_expr_out (a b c : ℕ → F) :
    add2_expr_out (propBuilder env L) s a b c = (s ∧ Add2P a b c) := by
  simp only [add2_expr_out, BITS_PER_LIMB, pb_mul_2exp, pb_assert_zeros2, Add2P]; rfl

theorem prop_add3 (a b c d : ℕ → F) :
    add3 (propBuilder env L) s a b c d = (s ∧ Add3P a b c d) := by
  simp only [add3, pb_mul_2exp, pb_assert_zeros2, Add3P]; rfl

theorem prop_add3_expr_out (a b c d : ℕ → F) :
    add3_expr_out (propBuilder env L) s a b c d = (s ∧ Add3P a b c d) := by
  simp only [add3_expr_out, BITS_PER_LIMB, pb_mul_2exp, pb_assert_zeros2, Add3P]; rfl

theorem prop_packed (packed bits : ℕ → F) :
    assert_packed_equals_bits (propBuilder env L) s packed bits =
      (s ∧ packed 0 - packF bits 0 = 0 ∧ packed 1 - packF bits 1 = 0) := by
  simp only [assert_packed_equals_bits, pb_assert_zeros2]; rfl

theorem prop_sigma (bits packed : ℕ → F) (spec : SigmaSpec) :
    assert_sigma_matches (propBuilder env L) s bits spec packed =
      (s ∧ packed 0 - sigmaF bits spec 0 = 0 ∧ packed 1 - sigmaF bits spec 1 = 0) := by
  cases spec <;> simp only [assert_sigma_matches, sigma_params, pb_assert_zeros2] <;> rfl

theorem prop_ch (e f g packed : ℕ → F) :
    assert_ch_matches (propBuilder env L) s e f g packed =
      (s ∧ packed 0 - chF e f g 0 = 0 ∧ packed 1 - chF e f g 1 = 0) := by
  simp only [assert_ch_matches, pb_assert_zeros2]; rfl

theorem prop_maj (a b c packed : ℕ → F) :
    assert_maj_matches (propBuilder env L) s a b c packed =
      (s ∧ packed 0 - majF a b c 0 = 0 ∧ packed 1 - majF a b c 1 = 0) := by
  simp only [assert_maj_matches, pb_assert_zeros2]; rfl

end helpers

theorem foldl_eq_and {α : Type _} (l : List α) {f : Prop → α → Prop} {P : α → Prop}
    (hf : ∀ s a, f s a = (s ∧ P a)) (s : Prop) : l.foldl f s = (s ∧ ∀ a ∈ l, P a) := by
  rw [show f = fun s a => s ∧ P a from funext₂ hf, foldl_and]

/-! ## The steps on the row builder -/

section steps

variable (loc : ℕ → F)

/-- The constraints of schedule word i + 16. -/
def SchedP (i : ℕ) : Prop :=
  let t := i + 16
  let w : ℕ → ℕ → F := fun t b => loc (col.w t b)
  let sig0 : ℕ → F := fun limb => loc (col.sched_sigma0 i limb)
  let sig1 : ℕ → F := fun limb => loc (col.sched_sigma1 i limb)
  let tmp : ℕ → F := fun limb => loc (col.sched_tmp i limb)
  (sig0 0 - sigmaF (w (t - 15)) .SmallSigma0 0 = 0 ∧ sig0 1 - sigmaF (w (t - 15)) .SmallSigma0 1 = 0) ∧
  (sig1 0 - sigmaF (w (t - 2)) .SmallSigma1 0 = 0 ∧ sig1 1 - sigmaF (w (t - 2)) .SmallSigma1 1 = 0) ∧
  Add2P tmp sig1 (packF (w (t - 7))) ∧ Add3P (packF (w t)) tmp sig0 (packF (w (t - 16)))

/-- The constraints of round t. -/
def RoundP (t : ℕ) : Prop :=
  let ab : ℕ → ℕ → F := fun k b => loc (col.a_chain k b)
  let eb : ℕ → ℕ → F := fun k b => loc (col.e_chain k b)
  let c : (ℕ → ℕ → ℕ) → ℕ → F := fun f limb => loc (f t limb)
  (c col.sigma1_e 0 - sigmaF (eb (t + 3)) .BigSigma1 0 = 0 ∧
    c col.sigma1_e 1 - sigmaF (eb (t + 3)) .BigSigma1 1 = 0) ∧
  (c col.ch 0 - chF (eb (t + 3)) (eb (t + 2)) (eb (t + 1)) 0 = 0 ∧
    c col.ch 1 - chF (eb (t + 3)) (eb (t + 2)) (eb (t + 1)) 1 = 0) ∧
  Add3P (c col.tmp1) (c col.sigma1_e) (c col.ch) (packF (eb t)) ∧
  Add3P (c col.t1) (c col.tmp1)
    (fun limb => if limb = 0 then ((kOf t &&& 0xFFFF : ℕ) : F) else ((kOf t >>> BITS_PER_LIMB : ℕ) : F))
    (packF fun b => loc (col.w t b)) ∧
  (c col.sigma0_a 0 - sigmaF (ab (t + 3)) .BigSigma0 0 = 0 ∧
    c col.sigma0_a 1 - sigmaF (ab (t + 3)) .BigSigma0 1 = 0) ∧
  (c col.maj 0 - majF (ab (t + 3)) (ab (t + 2)) (ab (t + 1)) 0 = 0 ∧
    c col.maj 1 - majF (ab (t + 3)) (ab (t + 2)) (ab (t + 1)) 1 = 0) ∧
  Add3P (packF (ab (t + 4))) (c col.t1) (c col.sigma0_a) (c col.maj) ∧
  Add2P (packF (eb (t + 4))) (c col.t1) (packF (ab t))

variable (env : Var → F) (L : AirLayout) (s : Prop)

theorem prop_bits : eval_bit_range_checks (propBuilder env L) loc s =
    ((((s ∧ ∀ t ∈ List.range 64, ∀ b ∈ List.range 32, loc (col.w t b) * (loc (col.w t b) - 1) = 0) ∧
      ∀ k ∈ List.range 68, ∀ b ∈ List.range 32, loc (col.a_chain k b) * (loc (col.a_chain k b) - 1) = 0) ∧
      ∀ k ∈ List.range 68, ∀ b ∈ List.range 32, loc (col.e_chain k b) * (loc (col.e_chain k b) - 1) = 0) ∧
      ∀ i ∈ List.range 8, ∀ b ∈ List.range 32, loc (col.h_out i b) * (loc (col.h_out i b) - 1) = 0) := by
  simp only [eval_bit_range_checks, AirBuilder.assert_bools, AirBuilder.assert_zeros, AirBuilder.bool_check,
    List.foldl_map]
  rw [foldl_eq_and _ (fun _ _ => foldl_and _ _ _), foldl_eq_and _ (fun _ _ => foldl_and _ _ _),
    foldl_eq_and _ (fun _ _ => foldl_and _ _ _), foldl_eq_and _ (fun _ _ => foldl_and _ _ _)]
  rfl

theorem prop_initial : eval_initial_state (propBuilder env L) loc s =
    ((s ∧ ∀ i ∈ List.range 4, loc (col.h_in i 0) - packF (fun b => loc (col.a_chain (3 - i) b)) 0 = 0 ∧
        loc (col.h_in i 1) - packF (fun b => loc (col.a_chain (3 - i) b)) 1 = 0) ∧
      ∀ i ∈ List.range 4, loc (col.h_in (4 + i) 0) - packF (fun b => loc (col.e_chain (3 - i) b)) 0 = 0 ∧
        loc (col.h_in (4 + i) 1) - packF (fun b => loc (col.e_chain (3 - i) b)) 1 = 0) := by
  simp only [eval_initial_state, prop_packed, foldl_and]

theorem prop_schedule : eval_message_schedule (propBuilder env L) loc s =
    (s ∧ ∀ i ∈ List.range 48, SchedP loc i) := by
  simp only [eval_message_schedule]
  refine foldl_eq_and _ (fun s i => ?_) s
  simp only [prop_sigma, prop_add2, prop_add3_expr_out, SchedP, BLOCK_WORDS, and_assoc]
  rfl

theorem prop_compression : eval_compression (propBuilder env L) loc s =
    (s ∧ ∀ t ∈ List.range 64, RoundP loc t) := by
  simp only [eval_compression]
  refine foldl_eq_and _ (fun s t => ?_) s
  simp only [prop_sigma, prop_ch, prop_add3, prop_maj, prop_add3_expr_out, prop_add2_expr_out, RoundP,
    and_assoc]
  rfl

theorem prop_finalization : eval_finalization (propBuilder env L) loc s =
    ((s ∧ ∀ i ∈ List.range 4, Add2P (packF fun b => loc (col.h_out i b)) (fun limb => loc (col.h_in i limb))
        (packF fun b => loc (col.a_chain (67 - i) b))) ∧
      ∀ i ∈ List.range 4, Add2P (packF fun b => loc (col.h_out (4 + i) b))
        (fun limb => loc (col.h_in (4 + i) limb)) (packF fun b => loc (col.e_chain (67 - i) b))) := by
  simp only [eval_finalization, prop_add2_expr_out, foldl_and]
  rfl

end steps

/-- The constraints of the SHA-256 AIR on one row. -/
structure RowSpec (loc : ℕ → F) : Prop where
  bool_w : ∀ t < 64, ∀ b < 32, loc (col.w t b) * (loc (col.w t b) - 1) = 0
  bool_a : ∀ k < 68, ∀ b < 32, loc (col.a_chain k b) * (loc (col.a_chain k b) - 1) = 0
  bool_e : ∀ k < 68, ∀ b < 32, loc (col.e_chain k b) * (loc (col.e_chain k b) - 1) = 0
  bool_h : ∀ i < 8, ∀ b < 32, loc (col.h_out i b) * (loc (col.h_out i b) - 1) = 0
  init_a : ∀ i < 4, loc (col.h_in i 0) - packF (fun b => loc (col.a_chain (3 - i) b)) 0 = 0 ∧
    loc (col.h_in i 1) - packF (fun b => loc (col.a_chain (3 - i) b)) 1 = 0
  init_e : ∀ i < 4, loc (col.h_in (4 + i) 0) - packF (fun b => loc (col.e_chain (3 - i) b)) 0 = 0 ∧
    loc (col.h_in (4 + i) 1) - packF (fun b => loc (col.e_chain (3 - i) b)) 1 = 0
  sched : ∀ i < 48, SchedP loc i
  round : ∀ t < 64, RoundP loc t
  final_a : ∀ i < 4, Add2P (packF fun b => loc (col.h_out i b)) (fun limb => loc (col.h_in i limb))
    (packF fun b => loc (col.a_chain (67 - i) b))
  final_e : ∀ i < 4, Add2P (packF fun b => loc (col.h_out (4 + i) b))
    (fun limb => loc (col.h_in (4 + i) limb)) (packF fun b => loc (col.e_chain (67 - i) b))

/-- The row builder accepts a row exactly when its row constraints hold. -/
theorem eval_iff (env : Var → F) (L : AirLayout) :
    eval (propBuilder env L) True ↔ RowSpec (rowOf env L 0) := by
  simp only [eval]
  rw [prop_finalization, prop_compression, prop_schedule, prop_initial, prop_bits]
  simp only [List.mem_range, true_and, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Plonky3Lean.Proofs.Sha256Air
