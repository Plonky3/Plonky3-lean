module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Round
public import Plonky3Lean.Proofs.KeccakAir.Extracted
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Lib.Iter
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Proofs.Hash.Keccak.P3

@[expose] public section

/-!
# The extracted round on words

The extracted round of the characteristic-2 generator never panics for a round below 24.

It computes, word for word, the transcribed round, and so Rnd of FIPS 202.

For a round of 24 or more it panics, reading past the end of the round constants.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib p3_keccak_air.mirror p3_keccak_air.mirror.binary
open Plonky3Lean.Proofs.Keccak (u32k u32k_val eq_u32k u32k_rem u64_shr usz_div rotateLeft_zero
  cast_usz_u32k)

/-- Folding a step that always succeeds over an index range, with the index, folds it over the range. -/
theorem iter_fold_loop_range_idx {B F : Type}
    (inst : CoreModels.core.ops.function.FnMut F (B × Std.Usize) B) (f : F) (g : B → ℕ → B)
    (K : ℕ) (hstep : ∀ b (i : Std.Usize), i.val < K → inst.call_mut f (b, i) = .ok (g b i.val, f)) :
    ∀ (n : ℕ) (i Kz : Std.Usize) (x : B), Kz.val = K → Kz.val - i.val = n →
      core.iter.traits.iterator.iter_fold_loop
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator
          core.Usize.Insts.CoreIterRangeStep) inst { start := i, «end» := Kz } f x =
        .ok ((List.range' i.val n).foldl g x) := by
  intro n
  induction n with
  | zero =>
    intro i Kz x _ hn
    unfold core.iter.traits.iterator.iter_fold_loop
    rw [loop]
    simp [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, range_next_ge i Kz (by omega)]
  | succ n ih =>
    intro i Kz x hK hn
    obtain ⟨i', e, hi'⟩ := range_next_lt i Kz (by omega)
    have h := ih i' Kz (g x i.val) hK (by omega)
    rw [hi'] at h
    rw [List.range'_succ, List.foldl_cons, ← h]
    unfold core.iter.traits.iterator.iter_fold_loop
    rw [loop]
    simp [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, e, hstep x i (by omega)]

theorem usz5 : (5#usize : Std.Usize) = usz 5 := ofNatCore_eq_usz _ _ (by decide)

/-- The inner closure of the parity: acc xor lane 5 y + x. -/
theorem call_parity_step (state : Std.Array Std.U64 25#usize) {x : ℕ} (hx : x < 5) (b : Std.U64)
    {k : ℕ} (hk : k < 5) :
    p3_keccak_air.binary.generation.keccak_round.closure.closure.Insts.CoreOpsFunctionFnMutPairU64UsizeU64.call_mut
        (state, usz x) (b, usz k) = .ok (b ^^^ state.val[5 * k + x]!, (state, usz x)) := by
  have hs := state.property
  unfold p3_keccak_air.binary.generation.keccak_round.closure.closure.Insts.CoreOpsFunctionFnMutPairU64UsizeU64.call_mut
  show (do
    let i1 ← 5#usize * usz k
    let i2 ← i1 + usz x
    let i3 ← Std.Array.index_usize state i2
    let i4 ← lift (b ^^^ i3)
    RustM.ok (i4, ((state, usz x) : p3_keccak_air.binary.generation.keccak_round.closure.closure))) = _
  simp only [usz5, usz_mul (show 5 * k < 2 ^ 32 by omega) (by decide) (show k < 2 ^ 32 by omega),
    usz_add (show 5 * k + x < 2 ^ 32 by omega), bind_tc_ok, lift,
    index_usize_eq state (usz (5 * k + x)) (by rw [usz_val (by omega), hs]; simp; omega)]
  simp only [usz_val (show 5 * k + x < 2 ^ 32 by omega), List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 5 * k + x < state.val.length by rw [hs]; simp; omega),
    Option.getD_some]
  rfl

/-- The column parity closure: C[x] is the xor of lanes x, x + 5, ..., x + 20. -/
theorem call_parity (state : Std.Array Std.U64 25#usize) {x : ℕ} (hx : x < 5) :
    p3_keccak_air.binary.generation.keccak_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        state (usz x) =
      .ok ((List.range 5).foldl (fun acc y => acc ^^^ state.val[5 * y + x]!) 0#u64, state) := by
  have hstep : ∀ (b : Std.U64) (i : Std.Usize), i.val < 5 →
      CoreModels.core.ops.function.FnMut.call_mut
        p3_keccak_air.binary.generation.keccak_round.closure.closure.Insts.CoreOpsFunctionFnMutPairU64UsizeU64
        ((state, usz x) : p3_keccak_air.binary.generation.keccak_round.closure.closure) (b, i) =
        .ok (b ^^^ state.val[5 * i.val + x]!, ((state, usz x) :
          p3_keccak_air.binary.generation.keccak_round.closure.closure)) := by
    intro b i hi
    have h := call_parity_step state hx b hi
    rw [show usz i.val = i from (eq_usz (show i.val < 2 ^ 32 by omega) rfl).symm] at h
    exact h
  unfold p3_keccak_air.binary.generation.keccak_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [CoreModels.core.iter.traits.iterator.Iterator.fold.default,
    CoreModels.core.iter.traits.iterator.iter_fold,
    iter_fold_loop_range_idx _ _ (fun acc y => acc ^^^ state.val[5 * y + x]!) 5 hstep 5 (0#usize)
      (5#usize) 0#u64 rfl rfl, bind_ok]
  rfl

theorem u64_shl (x : Std.U64) (k : ℕ) (hk : k < 64) :
    (x <<< u32k k : RustM Std.U64) = .ok ⟨x.bv <<< k⟩ := by
  show UScalar.shiftLeft_UScalar x _ = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, u32k_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.U64.numBits from hk))]
  rfl

theorem u32k_sub {a b : ℕ} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (u32k a - u32k b : RustM Std.U32) = .ok (u32k (a - b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.sub_bv_spec (x := u32k a) (y := u32k b) (by rw [u32k_val ha, u32k_val (by omega)]; omega))
  rw [hz, eq_u32k (x := z) (k := a - b) (by omega) (by rw [hv.1, u32k_val ha, u32k_val (by omega)])]

theorem lit64 : (64#u32 : Std.U32) = u32k 64 := eq_u32k (by decide) rfl

/-- The modelled rotation is the rotation of the word. -/
theorem cm_rotate_left (x : Std.U64) {r : ℕ} (hr : r < 64) :
    CoreModels.core.num.U64.rotate_left x (u32k r) = .ok ⟨x.bv.rotateLeft r⟩ := by
  unfold CoreModels.core.num.U64.rotate_left
  rw [lit64, u32k_rem (by omega) (by decide) (by decide), bind_ok, Nat.mod_eq_of_lt hr]
  by_cases h0 : r = 0
  · subst h0
    rw [ite_eq_left (by rfl), rotateLeft_zero]
  · rw [ite_eq_right (fun h => h0 (by have := congrArg UScalar.val h; rwa [u32k_val (by omega)] at this)),
      u64_shl x r hr, bind_ok, u32k_sub (by omega) (by decide), bind_ok, u64_shr x (64 - r) (by omega),
      bind_ok]
    congr 1
    show (⟨x.bv <<< r ^^^ x.bv >>> (64 - r)⟩ : Std.U64) = ⟨x.bv.rotateLeft r⟩
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hr, hi, decide_true, Bool.true_and]
    by_cases hir : i < r
    · simp [hir]
    · rw [ite_eq_right hir, BitVec.getLsbD_of_ge x.bv (64 - r + i) (by omega)]
      simp [hir]

theorem usz4 : (4#usize : Std.Usize) = usz 4 := ofNatCore_eq_usz _ _ (by decide)
theorem usz1 : (1#usize : Std.Usize) = usz 1 := ofNatCore_eq_usz _ _ (by decide)
theorem usz2 : (2#usize : Std.Usize) = usz 2 := ofNatCore_eq_usz _ _ (by decide)
theorem lit1 : (1#u32 : Std.U32) = u32k 1 := eq_u32k (by decide) rfl

theorem getElem!_eq {α : Type} [Inhabited α] (l : List α) {i : ℕ} (h : i < l.length) : l[i]! = l[i] := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The closure of D: D[x] = C[x - 1] xor ROT(C[x + 1], 1). -/
theorem call_d (c : Std.Array Std.U64 5#usize) {x : ℕ} (hx : x < 5) :
    p3_keccak_air.binary.generation.keccak_round.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        c (usz x) = .ok (c.val[(x + 4) % 5]! ^^^ ⟨(c.val[(x + 1) % 5]!).bv.rotateLeft 1⟩, c) := by
  have hc := c.property
  unfold p3_keccak_air.binary.generation.keccak_round.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [usz4, usz1, usz5, lit1, usz_add (show x + 4 < 2 ^ 32 by omega),
    usz_add (show x + 1 < 2 ^ 32 by omega), usz_rem (b := 5) (show x + 4 < 2 ^ 32 by omega) (by decide) (by decide),
    usz_rem (b := 5) (show x + 1 < 2 ^ 32 by omega) (by decide) (by decide), bind_ok, lift,
    index_usize_eq c (usz ((x + 4) % 5)) (by rw [usz_val (by omega), hc]; simp; omega),
    index_usize_eq c (usz ((x + 1) % 5)) (by rw [usz_val (by omega), hc]; simp; omega),
    cm_rotate_left _ (show 1 < 64 by omega), usz_val (show (x + 4) % 5 < 2 ^ 32 by omega),
    usz_val (show (x + 1) % 5 < 2 ^ 32 by omega),
    getElem!_eq c.val (show (x + 4) % 5 < c.val.length by rw [hc]; simp; omega),
    getElem!_eq c.val (show (x + 1) % 5 < c.val.length by rw [hc]; simp; omega)]

theorem usz3 : (3#usize : Std.Usize) = usz 3 := ofNatCore_eq_usz _ _ (by decide)

theorem R_length : p3_keccak_air.constants.R.val.length = 5 := by simp

theorem R_row_length (a : ℕ) : (p3_keccak_air.constants.R.val[a]!).val.length = 5 := by simp

/-- Entry [a][b] of the extracted rho table is the transcribed one. -/
theorem R_val {a b : ℕ} (ha : a < 5) (hb : b < 5) :
    ((p3_keccak_air.constants.R.val[a]!).val[b]!).val = rOf a b := by
  have h := congrArg (fun L => (L.getD a []).getD b 0) R_eq
  have ha' : a < p3_keccak_air.constants.R.val.length := by rw [R_length]; exact ha
  have hb' : b < (p3_keccak_air.constants.R.val[a]).val.length := by simp; exact hb
  rw [rOf, ← h, getElem!_eq _ ha', getElem!_eq _ hb']
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha', List.getElem?_eq_getElem hb']

theorem R_val' {a b : ℕ} (ha : a < 5) (hb : b < 5) {h1 : a < p3_keccak_air.constants.R.val.length}
    {h2 : b < (p3_keccak_air.constants.R.val[a]).val.length} :
    ((p3_keccak_air.constants.R.val[a]).val[b]).val = rOf a b := by
  rw [← R_val ha hb, getElem!_eq _ h1, getElem!_eq _ h2]

theorem cast_u8_usz (e : Std.U8) : UScalar.cast .Usize e = usz e.val := by
  have he : e.val < 2 ^ 8 := e.hBounds
  apply eq_usz (by omega)
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have : 8 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  exact lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) this)

/-- The extracted rho-pi table lookup is the transcribed one. -/
theorem rho_pi_source_eq {x y : ℕ} (hx : x < 5) (hy : y < 5) :
    p3_keccak_air.binary.rho_pi_source (usz x) (usz y) =
      .ok (usz x, usz ((x + 3 * y) % 5), usz (rOf ((x + 3 * y) % 5) x)) := by
  have hs : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold p3_keccak_air.binary.rho_pi_source
  simp only [usz3, usz5, usz_mul (show 3 * y < 2 ^ 32 by omega) (by decide) (show y < 2 ^ 32 by omega),
    usz_add (show x + 3 * y < 2 ^ 32 by omega),
    usz_rem (b := 5) (show x + 3 * y < 2 ^ 32 by omega) (by decide) (by decide), bind_ok, lift,
    index_usize_eq _ (usz ((x + 3 * y) % 5)) (by rw [usz_val (by omega), R_length]; exact hs),
    usz_val (show (x + 3 * y) % 5 < 2 ^ 32 by omega)]
  rw [index_usize_eq _ (usz x) (by
    rw [usz_val (by omega), ← getElem!_eq _ (show (x + 3 * y) % 5 < _ by rw [R_length]; exact hs),
      R_row_length]; exact hx), bind_ok, cast_u8_usz]
  simp only [usz_val (show x < 2 ^ 32 by omega), R_val' hs hx]

/-- The closure of B: lane i of B is lane (y', x') of A' rotated, from the rho-pi table. -/
theorem call_b (state : Std.Array Std.U64 25#usize) (d : Std.Array Std.U64 5#usize) {i : ℕ}
    (hi : i < 25) :
    p3_keccak_air.binary.generation.keccak_round.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        ((state, d) : p3_keccak_air.binary.generation.keccak_round.closure_2) (usz i) =
      .ok (⟨(state.val[5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5]! ^^^
          d.val[(i % 5 + 3 * (i / 5)) % 5]!).bv.rotateLeft (rOf ((i % 5 + 3 * (i / 5)) % 5) (i % 5))⟩,
        ((state, d) : p3_keccak_air.binary.generation.keccak_round.closure_2)) := by
  have hs := state.property
  have hd := d.property
  have hx : i % 5 < 5 := Nat.mod_lt _ (by omega)
  have hy : i / 5 < 5 := by omega
  have hsx : (i % 5 + 3 * (i / 5)) % 5 < 5 := Nat.mod_lt _ (by omega)
  have hr := rOf_lt _ hsx _ hx
  unfold p3_keccak_air.binary.generation.keccak_round.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  show (do
    let i0 ← usz i % 5#usize
    let i1 ← usz i / 5#usize
    let (source_y, source_x, rot) ← p3_keccak_air.binary.rho_pi_source i0 i1
    let i2 ← 5#usize * source_y
    let i3 ← i2 + source_x
    let i4 ← Std.Array.index_usize state i3
    let i5 ← Std.Array.index_usize d source_x
    let i6 ← lift (i4 ^^^ i5)
    let i7 ← lift (UScalar.cast .U32 rot)
    let i8 ← CoreModels.core.num.U64.rotate_left i6 i7
    RustM.ok (i8, ((state, d) : p3_keccak_air.binary.generation.keccak_round.closure_2))) = _
  simp only [usz5, usz_rem (b := 5) (show i < 2 ^ 32 by omega) (by decide) (by decide),
    usz_div (b := 5) (show i < 2 ^ 32 by omega) (by decide) (by decide), bind_tc_ok,
    rho_pi_source_eq hx hy, usz_mul (show 5 * (i % 5) < 2 ^ 32 by omega) (by decide) (by omega),
    usz_add (show 5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5 < 2 ^ 32 by omega),
    index_usize_eq state (usz (5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5))
      (by rw [usz_val (by omega), hs]; simp; omega),
    index_usize_eq d (usz ((i % 5 + 3 * (i / 5)) % 5)) (by rw [usz_val (by omega), hd]; simp; omega),
    lift, cast_usz_u32k _ (show rOf ((i % 5 + 3 * (i / 5)) % 5) (i % 5) < 2 ^ 32 by omega),
    cm_rotate_left _ hr, usz_val (show 5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5 < 2 ^ 32 by omega),
    usz_val (show (i % 5 + 3 * (i / 5)) % 5 < 2 ^ 32 by omega),
    getElem!_eq state.val (show 5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5 < state.val.length by
      rw [hs]; simp; omega),
    getElem!_eq d.val (show (i % 5 + 3 * (i / 5)) % 5 < d.val.length by rw [hd]; simp; omega)]
  rfl

/-- The closure of chi. -/
theorem call_chi (b : Std.Array Std.U64 25#usize) {i : ℕ} (hi : i < 25) :
    p3_keccak_air.binary.generation.keccak_round.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        b (usz i) =
      .ok (b.val[i]! ^^^ ((~~~b.val[5 * (i / 5) + (i % 5 + 1) % 5]!) &&&
        b.val[5 * (i / 5) + (i % 5 + 2) % 5]!), b) := by
  have hb := b.property
  unfold p3_keccak_air.binary.generation.keccak_round.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [usz5, usz1, usz2, usz_rem (b := 5) (show i < 2 ^ 32 by omega) (by decide) (by decide),
    usz_div (b := 5) (show i < 2 ^ 32 by omega) (by decide) (by decide), bind_ok, lift,
    index_usize_eq b (usz i) (by rw [usz_val (by omega), hb]; simp; omega),
    usz_mul (show 5 * (i / 5) < 2 ^ 32 by omega) (by decide) (by omega),
    usz_add (show i % 5 + 1 < 2 ^ 32 by omega), usz_add (show i % 5 + 2 < 2 ^ 32 by omega),
    usz_rem (b := 5) (show i % 5 + 1 < 2 ^ 32 by omega) (by decide) (by decide),
    usz_rem (b := 5) (show i % 5 + 2 < 2 ^ 32 by omega) (by decide) (by decide),
    usz_add (show 5 * (i / 5) + (i % 5 + 1) % 5 < 2 ^ 32 by omega),
    usz_add (show 5 * (i / 5) + (i % 5 + 2) % 5 < 2 ^ 32 by omega),
    index_usize_eq b (usz (5 * (i / 5) + (i % 5 + 1) % 5)) (by rw [usz_val (by omega), hb]; simp; omega),
    index_usize_eq b (usz (5 * (i / 5) + (i % 5 + 2) % 5)) (by rw [usz_val (by omega), hb]; simp; omega),
    usz_val (show i < 2 ^ 32 by omega), usz_val (show 5 * (i / 5) + (i % 5 + 1) % 5 < 2 ^ 32 by omega),
    usz_val (show 5 * (i / 5) + (i % 5 + 2) % 5 < 2 ^ 32 by omega),
    getElem!_eq b.val (show i < b.val.length by rw [hb]; simp; omega),
    getElem!_eq b.val (show 5 * (i / 5) + (i % 5 + 1) % 5 < b.val.length by rw [hb]; simp; omega),
    getElem!_eq b.val (show 5 * (i / 5) + (i % 5 + 2) % 5 < b.val.length by rw [hb]; simp; omega)]

/-- The word of lane i of B. -/
def bWord (state : Std.Array Std.U64 25#usize) (d : Std.Array Std.U64 5#usize) (i : ℕ) : Std.U64 :=
  ⟨(state.val[5 * (i % 5) + (i % 5 + 3 * (i / 5)) % 5]! ^^^
    d.val[(i % 5 + 3 * (i / 5)) % 5]!).bv.rotateLeft (rOf ((i % 5 + 3 * (i / 5)) % 5) (i % 5))⟩

theorem from_fn_b (state : Std.Array Std.U64 25#usize) (d : Std.Array Std.U64 5#usize) :
    rust_primitives.slice.array_from_fn 25#usize
        p3_keccak_air.binary.generation.keccak_round.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        ((state, d) : p3_keccak_air.binary.generation.keccak_round.closure_2) =
      .ok (Std.Array.from ((List.range 25).map (bWord state d)) (by simp)) :=
  array_from_fn_eq 25#usize _ _ _ (fun k hk => call_b state d (by simpa using hk))

theorem from_map_get {n : Std.Usize} {α : Type} [Inhabited α] (g : ℕ → α) (m : ℕ)
    (h : ((List.range m).map g).length = n.val) {i : ℕ} (hi : i < m) :
    (Std.Array.from ((List.range m).map g) h).val[i]! = g i := by
  rw [Std.Array.from_val, getElem!_eq _ (by simpa using hi)]
  simp

theorem getElem!_map_range {α : Type} [Inhabited α] (f : ℕ → α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f)[k]! = f k := by
  rw [getElem!_eq _ (by simpa using hk)]; simp

theorem getElem!_set_eq {α : Type} [Inhabited α] (l : List α) (j : ℕ) (v : α) {i : ℕ}
    (hi : i < l.length) : (l.set j v)[i]! = if i = j then v else l[i]! := by
  rw [getElem!_eq _ (by simpa using hi), getElem!_eq _ hi, List.getElem_set]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem u64_mk_bv (x : BitVec 64) : (⟨x⟩ : Std.U64).bv = x := rfl

theorem u64_zero_bv : (0#u64 : Std.U64).bv = 0 := rfl

theorem val5 : (5#usize : Std.Usize).val = 5 := rfl
theorem val25 : (25#usize : Std.Usize).val = 25 := rfl
theorem val0 : (0#usize : Std.Usize).val = 0 := rfl

theorem foldl_xor_bv (l : List ℕ) (w : ℕ → Std.U64) (z : Std.U64) :
    (l.foldl (fun acc y => acc ^^^ w y) z).bv = l.foldl (fun acc y => acc ^^^ (w y).bv) z.bv := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih, xor_bv]

theorem RC_bv {r : ℕ} (h : r < p3_keccak_air.constants.RC.val.length) :
    (p3_keccak_air.constants.RC.val[r]).bv = BitVec.ofNat 64 (RC.getD r 0) := by
  have e := congrArg (fun L => L.getD r 0) RC_eq
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq; simp

/-- The extracted round on an array of words never panics for a round below 24.

It computes the transcribed round, word for word. -/
theorem keccak_round_extracted (state : Std.Array Std.U64 25#usize) (round : Std.Usize)
    (hr : round.val < 24) :
    ∃ out, p3_keccak_air.binary.generation.keccak_round state round = .ok out ∧
      ∀ i < 25, (out.val[i]!).bv = binary.keccak_round (fun j => (state.val[j]!).bv) round.val i := by
  have hs := state.property
  unfold p3_keccak_air.binary.generation.keccak_round
  simp only [CoreModels.core.array.from_fn]
  rw [array_from_fn_eq 5#usize _ state _ (fun k hk => call_parity state (by simpa using hk)), bind_ok,
    array_from_fn_eq 5#usize _ _ _ (fun k hk => call_d _ (by simpa using hk)), bind_ok,
    from_fn_b, bind_ok,
    array_from_fn_eq 25#usize _ _ _ (fun k hk => call_chi _ (by simpa using hk)), bind_ok,
    index_usize_eq p3_keccak_air.constants.RC round (by simpa using hr), bind_ok,
    index_usize_eq _ 0#usize (by simp), bind_ok, lift, bind_ok, update_eq _ 0#usize _ (by simp)]
  refine ⟨_, rfl, fun i hi => ?_⟩
  simp only [Std.Array.from_val, val5, val25, val0]
  simp (disch := ((try simp only [List.length_map, List.length_range]); omega)) only [getElem!_set_eq,
    getElem!_map_range, bWord, Std.Array.from_val, List.getElem_map, List.getElem_range]
  simp only [binary.keccak_round, rho_pi_source, Function.update_apply]
  split_ifs with h0
  · subst h0
    simp only [xor_bv, and_bv, Plonky3Lean.Proofs.Keccak.u64_not_bv, u64_mk_bv, foldl_xor_bv,
      RC_bv (show round.val < _ by simpa using hr), u64_zero_bv]
  · simp only [xor_bv, and_bv, Plonky3Lean.Proofs.Keccak.u64_not_bv, u64_mk_bv, foldl_xor_bv, u64_zero_bv]

/-- For a round of 24 or more, the extracted round panics: it reads past the end of the round constants. -/
theorem keccak_round_panics (state : Std.Array Std.U64 25#usize) (round : Std.Usize)
    (hr : 24 ≤ round.val) :
    p3_keccak_air.binary.generation.keccak_round state round = .fail .panic := by
  unfold p3_keccak_air.binary.generation.keccak_round
  simp only [CoreModels.core.array.from_fn]
  rw [array_from_fn_eq 5#usize _ state _ (fun k hk => call_parity state (by simpa using hk)), bind_ok,
    array_from_fn_eq 5#usize _ _ _ (fun k hk => call_d _ (by simpa using hk)), bind_ok,
    from_fn_b, bind_ok,
    array_from_fn_eq 25#usize _ _ _ (fun k hk => call_chi _ (by simpa using hk)), bind_ok]
  have hn : p3_keccak_air.constants.RC[round]? = none := by
    simp only [Std.Array.getElem?_Usize_eq]
    exact List.getElem?_eq_none (by simp; omega)
  simp [Std.Array.index_usize, hn]

end Plonky3Lean.Proofs.KeccakAir.Binary
