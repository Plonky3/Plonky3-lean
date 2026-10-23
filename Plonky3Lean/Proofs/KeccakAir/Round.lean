module

public import Plonky3Lean.Proofs.KeccakAir.Bits
public import Plonky3Lean.Proofs.KeccakAir.Tables
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# One row computes one round

Let a row satisfy the row constraints, with its round flag one-hot at round k.

Its bit columns are bits, and its input limbs are the limbs of a state A.

Its output limbs are then the limbs of Rnd(A, k), the round of FIPS 202, 3.3.

This needs a field of characteristic at least 2^16, where a limb determines its bits.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_keccak_air.mirror Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Keccak

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Indices -/

theorem fin5_sub_one (x : Fin 5) : (x - 1).val = (x.val + 4) % 5 := by
  rw [Fin.sub_def]; simp; omega

theorem fin5_add (x y : Fin 5) : (x + y).val = (x.val + y.val) % 5 := Fin.val_add x y

theorem fin64_sub_one (z : Fin 64) : (z - 1).val = (z.val + 63) % 64 := by
  rw [Fin.sub_def]; simp; omega

theorem fin64_sub_ofNat (z : Fin 64) {r : ℕ} (hr : r < 64) :
    (z - Fin.ofNat 64 r).val = (z.val + 64 - r) % 64 := by
  rw [Fin.sub_def]; simp [Nat.mod_eq_of_lt hr]; omega

theorem fin5_x3y (x y : Fin 5) : (x + 3 * y).val = (x.val + 3 * y.val) % 5 := by
  rw [Fin.val_add, Fin.val_mul]; simp

/-- Rho moves bit z of lane (x, y) to bit z + r of the lane, r the lane's offset. -/
theorem rho_apply (A : State) (x y : Fin 5) (z : Fin 64) :
    rho A x y z = A x y (z - Fin.ofNat 64 (rhoOffsets.getD (x.val + 5 * y.val) 0)) := by
  have h := foldl_rhoUpdate A (List.range 24) (fun x y z => (x, y, z)) (1, 0)
  rw [rho, show ((A, (1, 0)) : State × (Fin 5 × Fin 5)) =
    (readAt A fun x y z => (x, y, z), (1, 0)) from rfl, h]
  simp only [readAt, rho_positions]

/-- Pi after rho reads bit z of B[x, y] from A'. -/
theorem pi_rho_apply (A : State) (x y : Fin 5) (z : Fin 64) :
    pi (rho A) x y z = A ⟨(x.val + 3 * y.val) % 5, Nat.mod_lt _ (by omega)⟩ x
      ⟨(z.val + 64 - rOf ((x.val + 3 * y.val) % 5) x.val) % 64, Nat.mod_lt _ (by omega)⟩ := by
  rw [pi, rho_apply]
  congr 1
  · exact Fin.ext (fin5_x3y x y)
  apply Fin.ext
  rw [fin64_sub_ofNat _ (rhoOffsets_lt _), fin5_x3y,
    rOf_eq _ (Nat.mod_lt _ (by omega)) _ x.isLt]

/-! ## Bits of a row -/

/-- The bit a cell holds: whether it is 1. -/
def bv (v : F) : Bool := decide (v = 1)

theorem bv_bitF (b : Bool) : bv (bitF b : F) = b := by cases b <;> simp [bv, bitF]

/-- A state read from bits indexed by naturals. -/
def toState (f : ℕ → ℕ → ℕ → Bool) : State := fun x y z => f x.val y.val z.val

section row

variable (loc : ℕ → F)

/-- Bit z of C[x]. -/
def cB (x z : ℕ) : Bool := bv (loc (col.c x z))

/-- Bit z of C'[x]. -/
def cpB (x z : ℕ) : Bool := bv (loc (col.c_prime x z))

/-- Bit z of A'[x, y], stored y first. -/
def apB (y x z : ℕ) : Bool := bv (loc (col.a_prime y x z))

/-- The input state: A[x, y, z] = xor(A'[x, y, z], C[x, z], C'[x, z]). -/
def inB (x y z : ℕ) : Bool := apB loc y x z ^^ cB loc x z ^^ cpB loc x z

/-- Bit z of B[x, y], read from A'. -/
def bB (x y z : ℕ) : Bool :=
  apB loc x ((x + 3 * y) % 5) ((z + 64 - rOf ((x + 3 * y) % 5) x) % 64)

/-- Bit z of A''[x, y]. -/
def chiB (x y z : ℕ) : Bool :=
  bB loc x y z ^^ (!bB loc ((x + 1) % 5) y z && bB loc ((x + 2) % 5) y z)

/-- Bit z of A'''[x, y] in round k. -/
def outB (k x y z : ℕ) : Bool :=
  if x = 0 ∧ y = 0 then chiB loc 0 0 z ^^ decide (rcBit k z ≠ 0) else chiB loc x y z

end row

/-- Two limb folds agree when their bits do. -/
theorem limbOf_congr {f g : ℕ → F} (limb : ℕ) (h : ∀ j < 16, f (limb * 16 + j) = g (limb * 16 + j)) :
    limbOf fieldOps f limb = limbOf fieldOps g limb := by
  have key : ∀ (l : List ℕ) (a : F), (∀ z ∈ l, f z = g z) →
      l.foldl (fun acc z => fieldOps.add (double fieldOps acc) (f z)) a =
        l.foldl (fun acc z => fieldOps.add (double fieldOps acc) (g z)) a := by
    intro l
    induction l with
    | nil => simp
    | cons z l ih =>
      intro a hl
      simp only [List.foldl_cons, hl z (by simp)]
      exact ih _ fun w hw => hl w (by simp [hw])
  refine key _ _ fun z hz => ?_
  simp only [List.mem_reverse, List.mem_range'_1, BITS_PER_LIMB] at hz
  obtain ⟨j, rfl⟩ : ∃ j, z = limb * 16 + j := ⟨z - limb * 16, by omega⟩
  exact h j (by omega)

/-- A sum of one-hot values over a list without repeats is 1 exactly when the hot index is listed. -/
theorem sum_onehot (l : List ℕ) (hl : l.Nodup) (k : ℕ) :
    (l.map fun r => if r = k then (1 : F) else 0).sum = if k ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2]
    by_cases ha : a = k
    · subst ha; simp [hl.1]
    · simp [ha, Ne.symm ha]

/-! ## The row constraints on bits -/

section facts

variable {loc nxt : ℕ → F} {first trans : F} (hR : RowSpec loc nxt first trans)
include hR

theorem c_eq {x z : ℕ} (hx : x < 5) (hz : z < 64) : loc (col.c x z) = bitF (cB loc x z) :=
  eq_bitF ((hR.c_prime x hx).1 z hz)

theorem a_prime_eq {x y z : ℕ} (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    loc (col.a_prime y x z) = bitF (apB loc y x z) :=
  eq_bitF (((hR.a_limbs x hx y hy).1) z hz)

theorem c_prime_eq {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    loc (col.c_prime x z) =
      bitF (cB loc x z ^^ cB loc ((x + 4) % 5) z ^^ cB loc ((x + 1) % 5) ((z + 63) % 64)) := by
  have h := (hR.c_prime x hx).2 z hz
  rw [c_eq hR hx hz, c_eq hR (by omega : (x + 4) % 5 < 5) hz,
    c_eq hR (by omega : (x + 1) % 5 < 5) (by omega : (z + 63) % 64 < 64), xor3_bit,
    sub_eq_zero] at h
  exact h

theorem cpB_eq {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    cpB loc x z = (cB loc x z ^^ cB loc ((x + 4) % 5) z ^^ cB loc ((x + 1) % 5) ((z + 63) % 64)) := by
  rw [cpB, c_prime_eq hR hx hz, bv_bitF]

theorem c_prime_eq' {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    loc (col.c_prime x z) = bitF (cpB loc x z) := by
  rw [cpB_eq hR hx hz, c_prime_eq hR hx hz]

/-- The limbs of A are those of the input state. -/
theorem a_eq {x y limb : ℕ} (hx : x < 5) (hy : y < 5) (hl : limb < 4) :
    loc (col.a y x limb) = ((bitsum (fun j => inB loc x y (limb * 16 + j)) 16 : ℕ) : F) := by
  have h := ((hR.a_limbs x hx y hy).2) limb hl
  rw [sub_eq_zero] at h
  rw [← h, ← limbOf_bits]
  refine limbOf_congr _ fun j hj => ?_
  rw [a_prime_eq hR hx hy (by omega), c_eq hR hx (by omega), c_prime_eq' hR hx (by omega),
    xor_bit, xor_bit, inB, Bool.xor_assoc]

/-- The five bits of A' in a column xor to C'. -/
theorem parity_eq (hp : 2 ^ 16 ≤ ringChar F) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    (apB loc 0 x z ^^ apB loc 1 x z ^^ apB loc 2 x z ^^ apB loc 3 x z ^^ apB loc 4 x z) =
      cpB loc x z := by
  have h := hR.parity x hx z hz
  simp only [sum_eq, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at h
  rw [a_prime_eq hR hx (by omega) hz, a_prime_eq hR hx (by omega) hz, a_prime_eq hR hx (by omega) hz,
    a_prime_eq hR hx (by omega) hz, a_prime_eq hR hx (by omega) hz, c_prime_eq' hR hx hz] at h
  set a0 := apB loc 0 x z
  set a1 := apB loc 1 x z
  set a2 := apB loc 2 x z
  set a3 := apB loc 3 x z
  set a4 := apB loc 4 x z
  set c := cpB loc x z
  have key : ∀ m n : ℕ, m ≤ 5 → n ≤ 1 →
      ((m : F) - n) * ((m : F) - n - 2) * ((m : F) - n - (2 + 2)) = 0 →
        m = n ∨ m = n + 2 ∨ m = n + 4 := by
    intro m n hm hn h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact cast_inj hp (by omega) (by omega) (sub_eq_zero.mp h)
      · right; left
        refine cast_inj hp (by omega) (by omega) ?_
        push_cast; linear_combination h
    · right; right
      refine cast_inj hp (by omega) (by omega) ?_
      push_cast; linear_combination h
  have hs := key (a0.toNat + a1.toNat + a2.toNat + a3.toNat + a4.toNat) c.toNat
    (by have := Bool.toNat_le a0; have := Bool.toNat_le a1; have := Bool.toNat_le a2
        have := Bool.toNat_le a3; have := Bool.toNat_le a4; omega)
    (Bool.toNat_le c) (by push_cast; simpa [bitF, add_assoc] using h)
  revert hs
  clear_value a0 a1 a2 a3 a4 c
  clear h key
  revert a0 a1 a2 a3 a4 c
  decide

/-- The five bits of the input state in a column xor to C. -/
theorem column_eq (hp : 2 ^ 16 ≤ ringChar F) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    (inB loc x 0 z ^^ inB loc x 1 z ^^ inB loc x 2 z ^^ inB loc x 3 z ^^ inB loc x 4 z) =
      cB loc x z := by
  have h := parity_eq hR hp hx hz
  simp only [inB]
  revert h
  generalize apB loc 0 x z = a0
  generalize apB loc 1 x z = a1
  generalize apB loc 2 x z = a2
  generalize apB loc 3 x z = a3
  generalize apB loc 4 x z = a4
  generalize cpB loc x z = c'
  generalize cB loc x z = c
  revert a0 a1 a2 a3 a4 c c'
  decide

/-- Theta of the input state is A'. -/
theorem theta_eq (hp : 2 ^ 16 ≤ ringChar F) :
    theta (toState (inB loc)) = toState (fun x y z => apB loc y x z) := by
  funext x y z
  have hx := x.isLt
  have hz := z.isLt
  simp only [theta, toState, Fin.val_zero, Fin.val_one, Fin.val_two, fin5_sub_one, fin64_sub_one,
    fin5_add, show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl]
  rw [column_eq hR hp (by omega) hz, column_eq hR hp (by omega) (by omega), inB,
    cpB_eq hR hx hz]
  generalize apB loc y x z = a
  generalize cB loc x z = c
  generalize cB loc ((x + 4) % 5) z = c4
  generalize cB loc ((x + 1) % 5) ((z + 63) % 64) = c1
  revert a c c4 c1
  decide

theorem b_eq {x : ℕ} (y z : ℕ) (hx : x < 5) : b loc x y z = bitF (bB loc x y z) :=
  a_prime_eq hR (by omega) hx (by omega)

/-- The limbs of A'' are those of chi of B. -/
theorem a_prime_prime_eq {x y limb : ℕ} (hx : x < 5) (hy : y < 5) (hl : limb < 4) :
    loc (col.a_prime_prime y x limb) = ((bitsum (fun j => chiB loc x y (limb * 16 + j)) 16 : ℕ) : F) := by
  have h := hR.chi y hy x hx limb hl
  rw [sub_eq_zero] at h
  rw [← h, ← limbOf_bits]
  refine limbOf_congr _ fun j hj => ?_
  rw [b_eq hR _ _ (by omega), b_eq hR _ _ (by omega), b_eq hR _ _ hx, andn_bit, xor_bit, chiB,
    Bool.xor_comm]

/-- The separate bits of A''[0, 0] are those of chi of B. -/
theorem bits_eq (hp : 2 ^ 16 ≤ ringChar F) {z : ℕ} (hz : z < 64) :
    loc (col.a_prime_prime_0_0_bits z) = bitF (chiB loc 0 0 z) := by
  have hbit : ∀ z < 64, loc (col.a_prime_prime_0_0_bits z) =
      bitF (bv (loc (col.a_prime_prime_0_0_bits z))) := fun z hz => eq_bitF (hR.bits_bool z hz)
  have hl := hR.bits_limb (z / 16) (by omega)
  rw [sub_eq_zero, a_prime_prime_eq hR (by omega) (by omega) (by omega),
    limbOf_congr (g := fun z => bitF (bv (loc (col.a_prime_prime_0_0_bits z)))) _
      (fun j hj => hbit _ (by omega)), limbOf_bits] at hl
  have h := bits_of_limb hp hl (z % 16) (by omega)
  rw [show z / 16 * 16 + z % 16 = z by omega] at h
  rw [hbit z hz, h]

/-- With the flags one-hot at round k, the limbs of A'''[x, y] are those of the round's output bits. -/
theorem output_eq (hp : 2 ^ 16 ≤ ringChar F) {k : ℕ} (hk : k < 24)
    (hflag : ∀ r < 24, loc (col.step_flags r) = if r = k then 1 else 0)
    {x y limb : ℕ} (hx : x < 5) (hy : y < 5) (hl : limb < 4) :
    a_prime_prime_prime loc y x limb =
      ((bitsum (fun j => outB loc k x y (limb * 16 + j)) 16 : ℕ) : F) := by
  unfold a_prime_prime_prime
  split_ifs with h0
  · obtain ⟨rfl, rfl⟩ := h0
    have h := hR.iota limb hl
    rw [sub_eq_zero] at h
    rw [← h, ← limbOf_bits]
    refine limbOf_congr _ fun j hj => ?_
    have hsum : sum fieldOps (((List.range 24).filter fun r => rcBit r (limb * 16 + j) ≠ 0).map
        fun r => loc (col.step_flags r)) = bitF (decide (rcBit k (limb * 16 + j) ≠ 0)) := by
      rw [sum_eq, List.map_congr_left (g := fun r => if r = k then (1 : F) else 0)
        (fun r hr => hflag r (by simp at hr; omega)),
        sum_onehot _ ((List.nodup_range).filter _)]
      by_cases hb : rcBit k (limb * 16 + j) ≠ 0 <;> simp [hb, hk, bitF]
    rw [hsum, bits_eq hR hp (by omega), xor_bit, outB, ite_eq_left ⟨rfl, rfl⟩, Bool.xor_comm]
  · rw [a_prime_prime_eq hR hx hy hl]
    congr 2
    funext j
    rw [outB, ite_eq_right (by tauto)]

/-- With the flags one-hot at round k, the output bits are Rnd(A, k) of the input state A. -/
theorem round_eq (hp : 2 ^ 16 ≤ ringChar F) {k : ℕ} (hk : k < 24) :
    toState (outB loc k) = rnd (toState (inB loc)) k := by
  rw [rnd, theta_eq hR hp]
  funext x y z
  simp only [iota, chi, toState, outB, chiB, bB, Fin.ext_iff, Fin.val_zero, Bool.xor_true]
  rw [pi_rho_apply, pi_rho_apply, pi_rho_apply]
  simp only [toState, fin5_add, Fin.val_one, Fin.val_two]
  simp only [rcBit_eq hk z.isLt, Fin.ofNat_val_eq_self]
  split_ifs with h0
  · obtain ⟨hx0, hy0⟩ := h0
    simp [hx0, hy0]
  · rfl

end facts

end Plonky3Lean.Proofs.KeccakAir
