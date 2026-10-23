module

public import Plonky3Lean.Proofs.KeccakAir.Words
public import Plonky3Lean.Proofs.KeccakAir.Round

@[expose] public section

/-!
# A generated row satisfies the constraints within its row

The generator fills the row of round k from the round's input state S.

Whatever S and k < 24, and in every field, the row meets each constraint that reads only its own row.

This needs the row's input limbs to be those of S and its flags to be one-hot at k, which the generator provides.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_keccak_air.mirror

variable {F : Type} [Field F]

/-! ## The words of a round -/

section words

variable (S : WState)

/-- The column parities C[x]. -/
def stC (x : ℕ) : Word := (List.range 5).foldl (fun acc y => acc ^^^ S x y) 0

/-- C'[x] = C[x] xor C[x - 1] xor ROT(C[x + 1], 1). -/
def stCp (x : ℕ) : Word := stC S x ^^^ stC S ((x + 4) % 5) ^^^ (stC S ((x + 1) % 5)).rotateLeft 1

/-- A'[x, y] = A[x, y] xor C[x] xor C'[x]. -/
def stA (x y : ℕ) : Word := S x y ^^^ stC S x ^^^ stCp S x

/-- B[i, j] = ROT(A'[(i + 3 j) mod 5, i], R[(i + 3 j) mod 5][i]). -/
def stB (i j : ℕ) : Word := (stA S ((i + 3 * j) % 5) i).rotateLeft (rOf ((i + 3 * j) % 5) i)

/-- A''[i, j] = B[i, j] xor (not B[i + 1, j] and B[i + 2, j]). -/
def stChi (i j : ℕ) : Word := stB S i j ^^^ ((~~~stB S ((i + 1) % 5) j) &&& stB S ((i + 2) % 5) j)

theorem stC_getLsbD (x z : ℕ) : (stC S x).getLsbD z =
    ((S x 0).getLsbD z ^^ (S x 1).getLsbD z ^^ (S x 2).getLsbD z ^^ (S x 3).getLsbD z ^^
      (S x 4).getLsbD z) := by
  simp [stC, List.range_succ]

end words

section row

variable (row : KeccakCols F) (k : ℕ) (S : WState)

theorem gen_c : (generate_trace_row_for_round row k S).1.c = fun x => u64_to_bits_le (stC S x) := rfl

theorem gen_c_prime :
    (generate_trace_row_for_round row k S).1.c_prime = fun x => u64_to_bits_le (stCp S x) := rfl

theorem gen_a_prime :
    (generate_trace_row_for_round row k S).1.a_prime = fun y x => u64_to_bits_le (stA S x y) := rfl

theorem gen_a_prime_prime : (generate_trace_row_for_round row k S).1.a_prime_prime =
    fun y x => u64_to_16_bit_limbs (stChi S x y) := rfl

theorem gen_bits : (generate_trace_row_for_round row k S).1.a_prime_prime_0_0_bits =
    u64_to_bits_le (stChi S 0 0) := rfl

theorem gen_limbs : (generate_trace_row_for_round row k S).1.a_prime_prime_prime_0_0_limbs =
    u64_to_16_bit_limbs (stChi S 0 0 ^^^ BitVec.ofNat 64 (RC.getD k 0)) := by
  funext l; simp [generate_trace_row_for_round, stChi, stB, stA, stCp, stC]

theorem gen_step_flags : (generate_trace_row_for_round row k S).1.step_flags =
    Function.update row.step_flags k 1 := rfl

theorem gen_a : (generate_trace_row_for_round row k S).1.a = row.a := rfl

theorem gen_preimage : (generate_trace_row_for_round row k S).1.preimage = row.preimage := rfl

theorem gen_export : (generate_trace_row_for_round row k S).1.export_ = row.export_ := rfl

/-- The output state of a round: A'' with lane (0, 0) xored with the round constant. -/
theorem gen_state (x y : ℕ) : (generate_trace_row_for_round row k S).2 x y =
    if x = 0 ∧ y = 0 then stChi S 0 0 ^^^ BitVec.ofNat 64 (RC.getD k 0) else stChi S x y := by
  simp only [generate_trace_row_for_round, Function.update_apply]
  split_ifs <;> simp_all [stChi, stB, stA, stCp, stC]

end row

theorem getLsbD_rotateLeft_nat (w : Word) {r : ℕ} (hr : r < 64) {z : ℕ} (hz : z < 64) :
    (w.rotateLeft r).getLsbD z = w.getLsbD ((z + 64 - r) % 64) := by
  have := Plonky3Lean.Proofs.Keccak.getLsbD_rotateLeft' w hr ⟨z, hz⟩
  rwa [fin64_sub_ofNat _ hr] at this

/-- A cell of a row. -/
def getc (r : KeccakCols F) (c : ℕ) : F := r.cells.getD c 0

theorem bitF_bool (b : Bool) : (bitF b : F) * (bitF b - 1) = 0 := by cases b <;> simp [bitF]

theorem parity_int : ∀ s0 s1 s2 s3 s4 cp : Bool,
    let c := s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4
    let d : ℤ := ((s0 ^^ c ^^ cp).toNat + (s1 ^^ c ^^ cp).toNat + (s2 ^^ c ^^ cp).toNat +
      (s3 ^^ c ^^ cp).toNat + (s4 ^^ c ^^ cp).toNat : ℕ) - (cp.toNat : ℕ)
    d * (d - 2) * (d - 4) = 0 := by
  decide

theorem parity_field (s0 s1 s2 s3 s4 cp : Bool) :
    (bitF (s0 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s1 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      (bitF (s2 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s3 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      bitF (s4 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp)))) - bitF cp) *
    (bitF (s0 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s1 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      (bitF (s2 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s3 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      bitF (s4 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp)))) - bitF cp - 2) *
    (bitF (s0 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s1 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      (bitF (s2 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) + (bitF (s3 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp) +
      bitF (s4 ^^ (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ cp)))) - bitF cp - (2 + 2)) = (0 : F) := by
  have := congrArg (Int.cast : ℤ → F) (parity_int s0 s1 s2 s3 s4 cp)
  push_cast at this
  simp only [bitF]
  linear_combination this

section intra

variable (row : KeccakCols F) (k : ℕ) (S : WState)

theorem intra_c_prime : ∀ x < 5,
    (∀ z < 64, getc (generate_trace_row_for_round row k S).1 (col.c x z) *
      (getc (generate_trace_row_for_round row k S).1 (col.c x z) - 1) = 0) ∧
    ∀ z < 64, getc (generate_trace_row_for_round row k S).1 (col.c_prime x z) -
      xor3 fieldOps (getc (generate_trace_row_for_round row k S).1 (col.c x z))
        (getc (generate_trace_row_for_round row k S).1 (col.c ((x + 4) % 5) z))
        (getc (generate_trace_row_for_round row k S).1 (col.c ((x + 1) % 5) ((z + 63) % 64))) = 0 := by
  intro x hx
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [getc, cell_c _ hx hz]; simp only [gen_c]; rw [u64_bits_eq _ hz]; exact bitF_bool _
  · simp only [getc]
    rw [cell_c _ hx hz, cell_c _ (by omega) hz, cell_c _ (by omega) (by omega), cell_c_prime _ hx hz]
    simp only [gen_c, gen_c_prime]
    rw [u64_bits_eq _ hz, u64_bits_eq _ hz, u64_bits_eq _ hz,
      u64_bits_eq _ (by omega), xor3_bit, stCp, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
      getLsbD_rotateLeft_nat _ (by omega) hz, show z + 64 - 1 = z + 63 by omega, sub_self]

theorem intra_a_limbs (ha : row.a = fun y x => u64_to_16_bit_limbs (S x y)) : ∀ x < 5, ∀ y < 5,
    (∀ z < 64, getc (generate_trace_row_for_round row k S).1 (col.a_prime y x z) *
      (getc (generate_trace_row_for_round row k S).1 (col.a_prime y x z) - 1) = 0) ∧
    ∀ limb < 4, limbOf fieldOps (fun z =>
      xor fieldOps (getc (generate_trace_row_for_round row k S).1 (col.a_prime y x z))
        (xor fieldOps (getc (generate_trace_row_for_round row k S).1 (col.c x z))
          (getc (generate_trace_row_for_round row k S).1 (col.c_prime x z)))) limb -
      getc (generate_trace_row_for_round row k S).1 (col.a y x limb) = 0 := by
  intro x hx y hy
  refine ⟨fun z hz => ?_, fun limb hl => ?_⟩
  · rw [getc, cell_a_prime _ hy hx hz]; simp only [gen_a_prime]; rw [u64_bits_eq _ hz]
    exact bitF_bool _
  · rw [getc, cell_a _ hy hx hl]
    simp only [gen_a, ha]
    rw [sub_eq_zero, u64_limbs_eq, ← limbOf_bits]
    refine limbOf_congr _ fun j hj => ?_
    simp only [getc]
    rw [cell_a_prime _ hy hx (by omega), cell_c _ hx (by omega), cell_c_prime _ hx (by omega)]
    simp only [gen_a_prime, gen_c, gen_c_prime]
    rw [u64_bits_eq _ (by omega), u64_bits_eq _ (by omega), u64_bits_eq _ (by omega), xor_bit, xor_bit,
      stA, BitVec.getLsbD_xor, BitVec.getLsbD_xor]
    congr 1
    cases (S x y).getLsbD (limb * 16 + j) <;> cases (stC S x).getLsbD (limb * 16 + j) <;>
      cases (stCp S x).getLsbD (limb * 16 + j) <;> rfl

theorem intra_parity : ∀ x < 5, ∀ z < 64,
    let diff := sum fieldOps ((List.range 5).map fun y =>
        getc (generate_trace_row_for_round row k S).1 (col.a_prime y x z)) -
      getc (generate_trace_row_for_round row k S).1 (col.c_prime x z)
    diff * (diff - 2) * (diff - (2 + 2)) = 0 := by
  intro x hx z hz
  simp only [sum_eq, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, getc]
  rw [cell_a_prime _ (by omega) hx hz, cell_a_prime _ (by omega) hx hz, cell_a_prime _ (by omega) hx hz,
    cell_a_prime _ (by omega) hx hz, cell_a_prime _ (by omega) hx hz, cell_c_prime _ hx hz]
  simp only [gen_a_prime, gen_c_prime]
  rw [u64_bits_eq _ hz, u64_bits_eq _ hz, u64_bits_eq _ hz, u64_bits_eq _ hz, u64_bits_eq _ hz,
    u64_bits_eq _ hz]
  simp only [stA, BitVec.getLsbD_xor, stC_getLsbD]
  linear_combination parity_field (F := F) ((S x 0).getLsbD z) ((S x 1).getLsbD z) ((S x 2).getLsbD z)
    ((S x 3).getLsbD z) ((S x 4).getLsbD z) ((stCp S x).getLsbD z)

theorem gen_b {x : ℕ} (y z : ℕ) (hx : x < 5) (hz : z < 64) :
    b (getc (generate_trace_row_for_round row k S).1) x y z = bitF ((stB S x y).getLsbD z) := by
  have hr := rOf_lt _ (Nat.mod_lt (x + 3 * y) (by omega)) x hx
  simp only [b, getc]
  rw [cell_a_prime _ hx (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
  simp only [gen_a_prime]
  rw [u64_bits_eq _ (Nat.mod_lt _ (by omega)), stB, getLsbD_rotateLeft_nat _ hr hz]

theorem intra_chi : ∀ y < 5, ∀ x < 5, ∀ limb < 4,
    limbOf fieldOps (fun z => xor fieldOps
      (andn fieldOps (b (getc (generate_trace_row_for_round row k S).1) ((x + 1) % 5) y z)
        (b (getc (generate_trace_row_for_round row k S).1) ((x + 2) % 5) y z))
      (b (getc (generate_trace_row_for_round row k S).1) x y z)) limb -
      getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime y x limb) = 0 := by
  intro y hy x hx limb hl
  rw [getc, cell_a_prime_prime _ hy hx hl]
  simp only [gen_a_prime_prime]
  rw [sub_eq_zero, u64_limbs_eq, ← limbOf_bits]
  refine limbOf_congr _ fun j hj => ?_
  rw [gen_b _ _ _ _ _ (by omega) (by omega), gen_b _ _ _ _ _ (by omega) (by omega),
    gen_b _ _ _ _ _ hx (by omega), andn_bit, xor_bit, stChi, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, Bool.xor_comm]
  simp [show limb * 16 + j < 64 by omega]

theorem intra_bits :
    (∀ z < 64, getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime_0_0_bits z) *
      (getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime_0_0_bits z) - 1) = 0) ∧
    ∀ limb < 4, limbOf fieldOps
        (fun z => getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime_0_0_bits z)) limb -
      getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime 0 0 limb) = 0 := by
  refine ⟨fun z hz => ?_, fun limb hl => ?_⟩
  · rw [getc, cell_bits _ hz, gen_bits, u64_bits_eq _ hz]; exact bitF_bool _
  · rw [getc, cell_a_prime_prime _ (by omega) (by omega) hl]
    simp only [gen_a_prime_prime]
    rw [sub_eq_zero, u64_limbs_eq, ← limbOf_bits]
    refine limbOf_congr _ fun j hj => ?_
    rw [getc, cell_bits _ (by omega), gen_bits, u64_bits_eq _ (by omega)]

theorem intra_iota (hk : k < 24) (hf : row.step_flags = fun _ => 0) : ∀ limb < 4,
    limbOf fieldOps (fun i => xor fieldOps (sum fieldOps
      (((List.range 24).filter fun r => rcBit r i ≠ 0).map fun r =>
        getc (generate_trace_row_for_round row k S).1 (col.step_flags r)))
      (getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime_0_0_bits i))) limb -
      getc (generate_trace_row_for_round row k S).1 (col.a_prime_prime_prime_0_0_limbs limb) = 0 := by
  intro limb hl
  rw [getc, cell_limbs _ hl, gen_limbs, sub_eq_zero, u64_limbs_eq, ← limbOf_bits]
  refine limbOf_congr _ fun j hj => ?_
  have hflag : ∀ r < 24, getc (generate_trace_row_for_round row k S).1 (col.step_flags r) =
      if r = k then 1 else 0 := by
    intro r hr
    rw [getc, cell_step_flags _ hr, gen_step_flags, hf, Function.update_apply]
  rw [sum_eq, List.map_congr_left (g := fun r => if r = k then (1 : F) else 0)
    (fun r hr => hflag r (by simp at hr; omega)), sum_onehot _ ((List.nodup_range).filter _),
    getc, cell_bits _ (by omega), gen_bits, u64_bits_eq _ (by omega), BitVec.getLsbD_xor,
    rc_getLsbD k hk _ (by omega)]
  have hmem : (if k ∈ (List.range 24).filter (fun r => decide (rcBit r (limb * 16 + j) ≠ 0))
      then (1 : F) else 0) = bitF (decide (rcBit k (limb * 16 + j) ≠ 0)) := by
    by_cases hb : rcBit k (limb * 16 + j) ≠ 0 <;> simp [hb, hk, bitF]
  rw [hmem, xor_bit, Bool.xor_comm]

end intra

end Plonky3Lean.Proofs.KeccakAir
