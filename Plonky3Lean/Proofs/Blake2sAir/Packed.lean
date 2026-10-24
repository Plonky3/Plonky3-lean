module

public import P3Blake2sAir
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Proofs.KeccakAir.Words
public import Plonky3Lean.Proofs.Blake2sAir.Extracted
public import Plonky3Lean.Proofs.Sha256Air.Bits

@[expose] public section

/-!
# The bit-sliced adder of the packed generator

The packed generator holds a 32-bit word of 64 trace rows as 32 planes of 64 bits.

Bit `k` of plane `i` is bit `i` of the word of lane `k`.

```text
    plane i   = [ bit i of lane 0, bit i of lane 1, ..., bit i of lane 63 ]
```

The extracted adder on planes never panics.

In every lane, it adds the two words modulo `2^32`, and writes the ripple carries into bits 1 to 31.
-/

namespace Plonky3Lean.Proofs.Blake2sAir

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib
open Plonky3Lean.Proofs.KeccakAir (bitsum bitsum_testBit)

/-- The plane of the carry into bit `j`, in every lane. -/
def carryPlane (x y : Std.Array Std.U64 32#usize) : ℕ → Std.U64
  | 0 => ⟨0⟩
  | j + 1 => (x.val[j]! &&& y.val[j]!) ||| (carryPlane x y j &&& (x.val[j]! ^^^ y.val[j]!))

/-- The carry planes the loop has written after `j` steps. -/
def carriesAt (x y : Std.Array Std.U64 32#usize) (c : Std.Array Std.U64 31#usize) : ℕ → Std.Array Std.U64 31#usize
  | 0 => c
  | j + 1 => (carriesAt x y c j).set (usz j) (carryPlane x y (j + 1))

/-- The sum planes the loop has written after `j` steps. -/
def sumAt (x y s : Std.Array Std.U64 32#usize) : ℕ → Std.Array Std.U64 32#usize
  | 0 => s
  | j + 1 => (sumAt x y s j).set (usz j) ((x.val[j]! ^^^ y.val[j]!) ^^^ carryPlane x y j)

/-- The word of lane `k`. -/
def laneWord (p : Std.Array Std.U64 32#usize) (k : ℕ) : BitVec 32 :=
  BitVec.ofNat 32 (bitsum (fun i => (p.val[i]!).bv.getLsbD k) 32)

theorem laneWord_getLsbD (p : Std.Array Std.U64 32#usize) (k : ℕ) {i : ℕ} (hi : i < 32) :
    (laneWord p k).getLsbD i = (p.val[i]!).bv.getLsbD k := by
  rw [laneWord, BitVec.getLsbD, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Plonky3Lean.Proofs.KeccakAir.bitsum_lt _ _), bitsum_testBit]
  simp [hi]

/-- In lane `k`, the carry plane into bit `j` holds the ripple carry of the two lane words. -/
theorem carryPlane_lane (x y : Std.Array Std.U64 32#usize) {k : ℕ} : ∀ j ≤ 32,
    (carryPlane x y j).bv.getLsbD k = BitVec.carry j (laneWord x k) (laneWord y k) false
  | 0, _ => by
    rw [carryPlane, BitVec.carry_zero]
    exact BitVec.getLsbD_zero
  | j + 1, hj => by
    simp only [carryPlane, BitVec.carry_succ, U64.bv, UScalar.bv_or, UScalar.bv_and, UScalar.bv_xor,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
      laneWord_getLsbD x k (show j < 32 by omega), laneWord_getLsbD y k (show j < 32 by omega)]
    rw [← carryPlane_lane x y j (by omega)]
    cases (x.val[j]!).bv.getLsbD k <;> cases (y.val[j]!).bv.getLsbD k <;>
      cases (carryPlane x y j).bv.getLsbD k <;> rfl

/-! ## The loop -/

theorem index_usz {α : Type} [Inhabited α] {n : Std.Usize} (v : Std.Array α n) {j : ℕ}
    (hj : j < v.val.length) (h32 : j < 2 ^ 32) : v.index_usize (usz j) = .ok v.val[j]! := by
  rw [index_usize_eq v (by rw [usz_val h32]; exact hj)]
  congr 1
  simp only [usz_val h32]
  exact (getElem!_pos v.val j hj).symm

theorem lit0' : (0#usize : Std.Usize) = usz 0 := eq_usz (by norm_num) rfl
theorem lit31 : (31#usize : Std.Usize) = usz 31 := eq_usz (by norm_num) rfl

theorem add_body (x y s0 : Std.Array Std.U64 32#usize) (c0 : Std.Array Std.U64 31#usize) {j : ℕ}
    (hj : j < 31) :
    p3_blake2s_air.binary.generation.add_planes_loop.body x y { start := usz j, «end» := 31#usize }
        (carriesAt x y c0 j) (sumAt x y s0 j) (carryPlane x y j) =
      .ok (.cont ({ start := usz (j + 1), «end» := 31#usize }, carriesAt x y c0 (j + 1),
        sumAt x y s0 (j + 1), carryPlane x y (j + 1))) := by
  have hx : x.val.length = 32 := x.property
  have hy : y.val.length = 32 := y.property
  have hs : ∀ m, (sumAt x y s0 m).val.length = 32 := fun m => (sumAt x y s0 m).property
  have hc : ∀ m, (carriesAt x y c0 m).val.length = 31 := fun m => (carriesAt x y c0 m).property
  unfold p3_blake2s_air.binary.generation.add_planes_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step j 31#usize (by simpa using hj), bind_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [index_usz x (j := j) (by omega) (by omega), index_usz y (j := j) (by omega) (by omega),
    bind_ok, lift, update_eq _ (show (usz j).val < (sumAt x y s0 j).val.length by
      rw [hs, usz_val (by omega)]; omega),
    update_eq _ (show (usz j).val < (carriesAt x y c0 j).val.length by rw [hc, usz_val (by omega)]; omega)]
  rfl

theorem add_done (x y s : Std.Array Std.U64 32#usize) (c : Std.Array Std.U64 31#usize) (carry : Std.U64) :
    p3_blake2s_air.binary.generation.add_planes_loop.body x y { start := usz 31, «end» := 31#usize } c s carry =
      .ok (.done (c, s, carry)) := by
  unfold p3_blake2s_air.binary.generation.add_planes_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz 31) 31#usize (by rw [usz_val (by norm_num)]; rfl), bind_ok]
  rfl

theorem add_loop (x y s0 : Std.Array Std.U64 32#usize) (c0 : Std.Array Std.U64 31#usize) :
    p3_blake2s_air.binary.generation.add_planes_loop { start := 0#usize, «end» := 31#usize } x y c0 s0
        0#u64 = .ok (carriesAt x y c0 31, sumAt x y s0 31, carryPlane x y 31) := by
  unfold p3_blake2s_air.binary.generation.add_planes_loop
  rw [lit0']
  exact loop_of_steps (fun a : CoreModels.core.ops.range.Range Std.Usize × Std.Array Std.U64 31#usize ×
      Std.Array Std.U64 32#usize × Std.U64 =>
      p3_blake2s_air.binary.generation.add_planes_loop.body x y a.1 a.2.1 a.2.2.1 a.2.2.2)
    (fun j => (({ start := usz j, «end» := 31#usize } : CoreModels.core.ops.range.Range Std.Usize),
      carriesAt x y c0 j, sumAt x y s0 j, carryPlane x y j)) 31 _
    (fun j hj => add_body x y s0 c0 hj) (add_done _ _ _ _ _)

/-! ## The adder -/

theorem set_get {n : Std.Usize} (a : Std.Array Std.U64 n) {j : ℕ} (hj : j < a.val.length) (h32 : j < 2 ^ 32)
    (v : Std.U64) (i : ℕ) : (a.set (usz j) v).val[i]! = if i = j then v else a.val[i]! := by
  rw [Std.Array.set_val_eq, usz_val h32]
  split_ifs with h
  · subst h; simp [getElem!_def, List.getElem?_set_self hj]
  · simp [getElem!_def, Ne.symm h]

theorem sumAt_get (x y s0 : Std.Array Std.U64 32#usize) :
    ∀ j ≤ 31, ∀ i < j, (sumAt x y s0 j).val[i]! = (x.val[i]! ^^^ y.val[i]!) ^^^ carryPlane x y i
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, hj, i, hi => by
    have hl : (sumAt x y s0 j).val.length = 32 := (sumAt x y s0 j).property
    rw [sumAt, set_get _ (by omega) (by omega)]
    split_ifs with h
    · subst h; rfl
    · exact sumAt_get x y s0 j (by omega) i (by omega)

theorem carriesAt_get (x y : Std.Array Std.U64 32#usize) (c0 : Std.Array Std.U64 31#usize) :
    ∀ j ≤ 31, ∀ i < j, (carriesAt x y c0 j).val[i]! = carryPlane x y (i + 1)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, hj, i, hi => by
    have hl : (carriesAt x y c0 j).val.length = 31 := (carriesAt x y c0 j).property
    rw [carriesAt, set_get _ (by omega) (by omega)]
    split_ifs with h
    · subst h; rfl
    · exact carriesAt_get x y c0 j (by omega) i (by omega)

theorem lit31' : (31#usize : Std.Usize) = usz 31 := eq_usz (by norm_num) rfl

/-- The extracted adder on planes never panics.

In every lane `k`, it returns:

- the sum of the two lane words modulo `2^32`
- the ripple carries into bits 1 to 31 of that sum, in place of the carry planes it is given -/
theorem add_planes_spec (x y : Std.Array Std.U64 32#usize) (c : Std.Array Std.U64 31#usize) :
    ∃ sum c', p3_blake2s_air.binary.generation.add_planes x y c = .ok (sum, c') ∧
      (∀ k, laneWord sum k = laneWord x k + laneWord y k) ∧
      ∀ k, ∀ i < 31, (c'.val[i]!).bv.getLsbD k = BitVec.carry (i + 1) (laneWord x k) (laneWord y k) false := by
  obtain ⟨s0, hs0, -⟩ := array_repeat_eq 32#usize CoreModels.core.U64.Insts.CoreCloneClone (fun _ => rfl) 0#u64
  have hx : x.val.length = 32 := x.property
  have hy : y.val.length = 32 := y.property
  have hl : (sumAt x y s0 31).val.length = 32 := (sumAt x y s0 31).property
  unfold p3_blake2s_air.binary.generation.add_planes
  simp only [hs0, bind_ok, add_loop, Aeneas.Std.uncurry_apply_pair]
  simp only [lit31', bind_ok, index_usz x (j := 31) (by omega) (by norm_num),
    index_usz y (j := 31) (by omega) (by norm_num), lift,
    update_eq _ (show (usz 31).val < (sumAt x y s0 31).val.length by rw [hl, usz_val (by norm_num)]; omega)]
  refine ⟨_, _, rfl, fun k => ?_, fun k i hi => ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [laneWord_getLsbD _ k hi, BitVec.getLsbD_add hi, set_get _ (by omega) (by norm_num),
      ← carryPlane_lane x y i (by omega)]
    split_ifs with h
    · subst h
      simp only [U64.bv, UScalar.bv_xor, BitVec.getLsbD_xor, laneWord_getLsbD x k hi,
        laneWord_getLsbD y k hi, Bool.xor_assoc]
    · rw [sumAt_get x y s0 31 le_rfl i (by omega)]
      simp only [U64.bv, UScalar.bv_xor, BitVec.getLsbD_xor, laneWord_getLsbD x k hi,
        laneWord_getLsbD y k hi, Bool.xor_assoc]
  · rw [carriesAt_get x y c 31 le_rfl i hi, carryPlane_lane x y (i + 1) (by omega)]

/-! ## The rotation -/

theorem lit32 : (32#usize : Std.Usize) = usz 32 := eq_usz (by norm_num) rfl

/-- The extracted rotation on planes never panics for an amount below 32.

In every lane, it returns `(x ^ y) >>> amount`. -/
theorem xor_rotate_right_spec (x y : Std.Array Std.U64 32#usize) (amount : Std.Usize) (ha : amount.val < 32) :
    ∃ out, p3_blake2s_air.binary.generation.xor_rotate_right x y amount = .ok out ∧
      ∀ k, laneWord out k = (laneWord x k ^^^ laneWord y k).rotateRight amount.val := by
  have hx : x.val.length = 32 := x.property
  have hy : y.val.length = 32 := y.property
  generalize hav : amount.val = a at ha
  have hau : amount = usz a := eq_usz (by omega) hav
  subst hau
  let g : ℕ → Std.U64 := fun k => x.val[(k + a) % 32]! ^^^ y.val[(k + a) % 32]!
  unfold p3_blake2s_air.binary.generation.xor_rotate_right CoreModels.core.array.from_fn
  refine ⟨_, array_from_fn_eq 32#usize
    p3_blake2s_air.binary.generation.xor_rotate_right.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
    ((x, usz a, y) : p3_blake2s_air.binary.generation.xor_rotate_right.closure) g (fun k hk => by
    have hk' : k < 32 := by simpa using hk
    simp only [p3_blake2s_air.binary.generation.xor_rotate_right.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
      Aeneas.Std.uncurry_apply_pair, usz_add (show k + a < 2 ^ 32 by omega), bind_ok, lit32,
      usz_rem (show k + a < 2 ^ 32 by omega) (by norm_num : 32 < 2 ^ 32) (by norm_num),
      index_usz x (show (k + a) % 32 < x.val.length by rw [hx]; exact Nat.mod_lt _ (by norm_num))
        (show (k + a) % 32 < 2 ^ 32 by omega),
      index_usz y (show (k + a) % 32 < y.val.length by rw [hy]; exact Nat.mod_lt _ (by norm_num))
        (show (k + a) % 32 < 2 ^ 32 by omega), lift]
    rfl), fun k => ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (i + a) % 32 < 32 := Nat.mod_lt _ (by norm_num)
  rw [laneWord_getLsbD _ k hi, Plonky3Lean.Proofs.Sha256Air.rotr_bit _ ha hi,
    BitVec.getLsbD_xor, laneWord_getLsbD x k hm, laneWord_getLsbD y k hm]
  have e : ((List.range (32#usize : Std.Usize).val).map g)[i]! = g i := by
    have h32 : (32#usize : Std.Usize).val = 32 := rfl
    rw [h32]
    simp [getElem!_pos, hi]
  simp only [Std.Array.from_val, e, g, U64.bv, UScalar.bv_xor, BitVec.getLsbD_xor]

end Plonky3Lean.Proofs.Blake2sAir
