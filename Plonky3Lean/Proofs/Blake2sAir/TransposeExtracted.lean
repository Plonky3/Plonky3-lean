module

public import Plonky3Lean.Proofs.Blake2sAir.Transpose
public import Plonky3Lean.Proofs.Blake2sAir.Packed

@[expose] public section

/-!
# The extracted bit-matrix transpose

The extracted transpose never panics.

Its six passes swap the same pairs of rows as the transcription does, in the same order.

So it moves bit `r` of row `c` to bit `c` of row `r`.
-/

namespace Plonky3Lean.Proofs.Blake2sAir

open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib p3_blake2s_air.mirror

/-! ## Shifts -/

theorem shr_usize (x : Std.U64) (s : Std.Usize) (h : s.val < 64) :
    (x >>> s : RustM Std.U64) = .ok ⟨x.bv >>> s.val⟩ := by
  show UScalar.shiftRight_UScalar x s = _
  simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight]
  rw [ite_eq_left (by simpa using h)]
  rfl

theorem shl_usize (x : Std.U64) (s : Std.Usize) (h : s.val < 64) :
    (x <<< s : RustM Std.U64) = .ok ⟨x.bv <<< s.val⟩ := by
  show UScalar.shiftLeft_UScalar x s = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
  rw [ite_eq_left (by simpa using h)]
  rfl

/-! ## One swap on an array -/

/-- The rows an array holds. -/
def arrF (a : Std.Array Std.U64 64#usize) : ℕ → BitVec 64 := fun i => (a.val[i]!).bv

/-- The swap step on rows `row` and `row + w` of an array. -/
def stepA (w : ℕ) (m : BitVec 64) (a : Std.Array Std.U64 64#usize) (row : ℕ) : Std.Array Std.U64 64#usize :=
  let swap : BitVec 64 := (((a.val[row]!).bv >>> w) ^^^ (a.val[row + w]!).bv) &&& m
  let a1 := a.set (usz row) ⟨(a.val[row]!).bv ^^^ swap <<< w⟩
  a1.set (usz (row + w)) ⟨(a1.val[row + w]!).bv ^^^ swap⟩

/-- On the rows inside the array, the swap step on the array is the swap step on its rows. -/
theorem arrF_stepA {w : ℕ} (hw : 0 < w) (m : BitVec 64) {a : Std.Array Std.U64 64#usize} {f : ℕ → BitVec 64}
    (h : ∀ i < 64, arrF a i = f i) {row : ℕ} (hr : row + w < 64) :
    ∀ i < 64, arrF (stepA w m a row) i = swapStep w m f row i := by
  intro i hi
  have hl : a.val.length = 64 := a.property
  have e1 : (a.val[row]!).bv = f row := h row (by omega)
  have e2 : (a.val[row + w]!).bv = f (row + w) := h (row + w) (by omega)
  have ei : (a.val[i]!).bv = f i := h i hi
  generalize hv : (⟨(a.val[row]!).bv ^^^ ((((a.val[row]!).bv >>> w) ^^^ (a.val[row + w]!).bv) &&& m) <<< w⟩ :
    Std.U64) = v
  have hv' : v.bv = f row ^^^ (((f row >>> w) ^^^ f (row + w)) &&& m) <<< w := by rw [← hv, e1, e2]
  have hl1 : (a.set (usz row) v).val.length = 64 := (a.set (usz row) v).property
  have hset1 : ∀ j, ((a.set (usz row) v).val[j]!) = if j = row then v else a.val[j]! :=
    set_get a (by omega) (by omega) v
  have hw0 : w ≠ 0 := by omega
  have hne : row + w ≠ row := by omega
  simp only [arrF, stepA, hv]
  rw [set_get _ (by omega) (by omega), hset1 (row + w)]
  simp only [hne, ↓reduceIte, e1, e2, swapStep, Function.update_apply]
  by_cases h1 : i = row + w
  · simp only [h1, ↓reduceIte]
  · rw [hset1 i]
    by_cases h2 : i = row
    · subst h2; simp only [h1, ↓reduceIte, hv']
    · simp only [h1, h2, ↓reduceIte, ei]

/-! ## The innermost loop -/

theorem update_set (a : Std.Array Std.U64 64#usize) {j : ℕ} (hj : j < 64) (v : Std.U64) :
    a.update (usz j) v = .ok (a.set (usz j) v) := by
  rw [Plonky3Lean.Lib.update_eq _ _ _ (by rw [a.property, usz_val (by omega)]; exact hj)]
  rfl

theorem inner_body {w : ℕ} (hw : w < 64) (m : BitVec 64) {j e : ℕ} (hj : j < e) (he : e ≤ 64)
    (hjw : j + w < 64) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0.body (usz w) ⟨m⟩
        { start := usz j, «end» := usz e } a =
      .ok (.cont ({ start := usz (j + 1), «end» := usz e }, stepA w m a j)) := by
  have hl : a.val.length = 64 := a.property
  have hwv : (usz w).val = w := usz_val (by omega)
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step j (usz e) (by rw [usz_val (by omega)]; exact hj), bind_ok, Aeneas.Std.uncurry_apply_pair]
  have hs : (usz w).val < 64 := by rw [hwv]; exact hw
  simp only [index_usz a (j := j) (by omega) (by omega), shr_usize _ (usz w) hs, bind_ok,
    usz_add (show j + w < 2 ^ 32 by omega), index_usz a (j := j + w) (by omega) (by omega), lift,
    shl_usize _ (usz w) hs, update_set a (show j < 64 by omega)]
  rw [index_usz _ (j := j + w) (by simp only [Std.Array.set_val_eq, List.length_set, hl]; omega) (by omega), bind_ok, update_set _ (show j + w < 64 by omega),
    bind_ok]
  simp only [hwv]
  rfl

theorem inner_done (w : ℕ) (m : BitVec 64) (e : ℕ) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0.body (usz w) ⟨m⟩
        { start := usz e, «end» := usz e } a = .ok (.done a) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
  rfl

/-- The innermost loop swaps rows `base` to `base + w - 1` with the rows `w` below. -/
theorem inner_loop {w : ℕ} (hw : w < 64) (m : BitVec 64) {base : ℕ} (hb : base + 2 * w ≤ 64)
    (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0
        { start := usz base, «end» := usz (base + w) } a (usz w) ⟨m⟩ =
      .ok ((List.range' base w).foldl (stepA w m) a) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0
  have key := loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize × Std.Array Std.U64 64#usize =>
      p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0.body (usz w) ⟨m⟩ x.1 x.2)
    (fun k => (({ start := usz (base + k), «end» := usz (base + w) } : CoreModels.core.ops.range.Range Std.Usize),
      (List.range' base k).foldl (stepA w m) a)) w ((List.range' base w).foldl (stepA w m) a)
    (fun k hk => by
      simp only
      rw [inner_body hw m (by omega) (by omega) (by omega), List.range'_concat, List.foldl_append,
        List.foldl_cons, List.foldl_nil, show base + k + 1 = base + (k + 1) by omega, Nat.one_mul])
    (by simp only; exact inner_done w m (base + w) _)
  simpa using key

/-! ## The step-by iterator over the bases -/

/-- The range iterator the step-by adapter wraps. -/
abbrev rangeIt := CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator
  CoreModels.core.Usize.Insts.CoreIterRangeStep

theorem lit64 : (64#usize : Std.Usize) = usz 64 := eq_usz (by norm_num) rfl
theorem lit1 : (1#usize : Std.Usize) = usz 1 := eq_usz (by norm_num) rfl

/-- One step of a range that may be exhausted: the start moves up, but not past the end. -/
theorem range_next_min (c : ℕ) (hc : c ≤ 64) :
    ∃ o, CoreModels.core.IteratorRange.next CoreModels.core.Usize.Insts.CoreIterRangeStep
      { start := usz c, «end» := usz 64 } = .ok (o, { start := usz (min (c + 1) 64), «end» := usz 64 }) := by
  rcases Nat.lt_or_ge c 64 with h | h
  · exact ⟨_, by rw [show min (c + 1) 64 = c + 1 by omega]; exact range_step c (usz 64) (by rw [usz_val (by norm_num)]; exact h)⟩
  · have e : c = 64 := by omega
    subst e
    exact ⟨_, range_stop _⟩

/-- The skipping loop of the step-by adapter advances the range `st - 1` times. -/
theorem next_loop_eq {st : ℕ} (hst : 0 < st) (hst' : st < 2 ^ 32) {c : ℕ} (hc : c ≤ 64) :
    CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop rangeIt
        { start := usz 1, «end» := usz st } { start := usz c, «end» := usz 64 } =
      .ok { start := usz (min (c + (st - 1)) 64), «end» := usz 64 } := by
  unfold CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop
  have key := loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize × CoreModels.core.ops.range.Range Std.Usize =>
      CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop.body rangeIt x.1 x.2)
    (fun j => (({ start := usz (1 + j), «end» := usz st } : CoreModels.core.ops.range.Range Std.Usize),
      ({ start := usz (min (c + j) 64), «end» := usz 64 } : CoreModels.core.ops.range.Range Std.Usize))) (st - 1)
    ({ start := usz (min (c + (st - 1)) 64), «end» := usz 64 } : CoreModels.core.ops.range.Range Std.Usize)
    (fun j hj => by
      obtain ⟨o, ho⟩ := range_next_min (min (c + j) 64) (by omega)
      simp only [CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop.body,
        CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next]
      rw [range_step (1 + j) (usz st) (by rw [usz_val hst']; omega), bind_ok]
      have ho' : rangeIt.next { start := usz (min (c + j) 64), «end» := usz 64 } =
          .ok (o, { start := usz (min (min (c + j) 64 + 1) 64), «end» := usz 64 }) := ho
      rw [ho', show min (min (c + j) 64 + 1) 64 = min (c + (j + 1)) 64 by omega,
        show 1 + j + 1 = 1 + (j + 1) by omega]
      simp only [bind_ok]
      rfl)
    (by
      simp only [CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop.body,
        CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next]
      rw [show 1 + (st - 1) = st by omega, range_stop, bind_ok]
      rfl)
  simpa [show min c 64 = c by omega] using key

/-- A step of the step-by adapter: it yields the start, and moves the start up by the step. -/
theorem stepby_next {b st : ℕ} (hb : b + st ≤ 64) (hb' : b < 64) (hst : 0 < st) :
    CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next rangeIt
        { iter := { start := usz b, «end» := usz 64 }, step := usz st } =
      .ok (.Some (usz b), { iter := { start := usz (b + st), «end» := usz 64 }, step := usz st }) := by
  have h1 : rangeIt.next { start := usz b, «end» := usz 64 } =
      .ok (.Some (usz b), { start := usz (b + 1), «end» := usz 64 }) :=
    range_step b (usz 64) (by rw [usz_val (by norm_num)]; exact hb')
  unfold CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next
  rw [h1, bind_ok]
  simp only [lit1]
  change (do
    let t1 ← CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop rangeIt
      { start := usz 1, «end» := usz st } { start := usz (b + 1), «end» := usz 64 }
    RustM.ok (CoreModels.core.option.Option.Some (usz b), ({ iter := t1, step := usz st } :
      CoreModels.core.iter.adapters.step_by.StepBy (CoreModels.core.ops.range.Range Std.Usize)))) = _
  rw [next_loop_eq hst (by omega) (by omega), bind_tc_ok, show min (b + 1 + (st - 1)) 64 = b + st by omega]

/-- An exhausted step-by adapter yields nothing. -/
theorem stepby_none {st : ℕ} (hst : 0 < st) (hst' : st < 2 ^ 32) :
    CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next rangeIt
        { iter := { start := usz 64, «end» := usz 64 }, step := usz st } =
      .ok (.None, { iter := { start := usz 64, «end» := usz 64 }, step := usz st }) := by
  have h1 : rangeIt.next { start := usz 64, «end» := usz 64 } =
      .ok (.None, { start := usz 64, «end» := usz 64 }) := range_stop _
  unfold CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next
  rw [h1, bind_ok]
  simp only [lit1]
  change (do
    let t1 ← CoreModels.core.iter.adapters.step_by.StepBy.Insts.CoreIterTraitsIteratorIterator.next_loop rangeIt
      { start := usz 1, «end» := usz st } { start := usz 64, «end» := usz 64 }
    RustM.ok (CoreModels.core.option.Option.None, ({ iter := t1, step := usz st } :
      CoreModels.core.iter.adapters.step_by.StepBy (CoreModels.core.ops.range.Range Std.Usize)))) = _
  rw [next_loop_eq hst hst' le_rfl, bind_tc_ok, show min (64 + (st - 1)) 64 = 64 by omega]

/-! ## One pass -/

/-- One pass on an array: the swap steps of every aligned square of twice the width. -/
def passA (w : ℕ) (m : BitVec 64) (a : Std.Array Std.U64 64#usize) : Std.Array Std.U64 64#usize :=
  ((List.range ((64 + 2 * w - 1) / (2 * w))).map (· * (2 * w))).foldl
    (fun a base => (List.range' base w).foldl (stepA w m) a) a

theorem middle_body {w : ℕ} (hw : 0 < w) (hw' : w < 64) (m : BitVec 64) {b : ℕ} (hb : b + 2 * w ≤ 64)
    (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0.body (usz w) ⟨m⟩
        { iter := { start := usz b, «end» := usz 64 }, step := usz (2 * w) } a =
      .ok (.cont ({ iter := { start := usz (b + 2 * w), «end» := usz 64 }, step := usz (2 * w) },
        (List.range' b w).foldl (stepA w m) a)) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0.body
  rw [stepby_next hb (by omega) (by omega), bind_ok]
  change (do
    let i ← usz b + usz w
    let rows1 ← p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0_loop0
      { start := usz b, «end» := i } a (usz w) ⟨m⟩
    RustM.ok (ControlFlow.cont (({ iter := { start := usz (b + 2 * w), «end» := usz 64 }, step := usz (2 * w) } :
      CoreModels.core.iter.adapters.step_by.StepBy (CoreModels.core.ops.range.Range Std.Usize)), rows1))) = _
  rw [usz_add (by omega), bind_tc_ok, inner_loop hw' m (by omega), bind_tc_ok]

theorem middle_done (w : ℕ) (hw : 0 < w) (hw' : w < 64) (m : BitVec 64) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0.body (usz w) ⟨m⟩
        { iter := { start := usz 64, «end» := usz 64 }, step := usz (2 * w) } a = .ok (.done a) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0.body
  rw [stepby_none (by omega) (by omega), bind_ok]
  rfl

/-- The step-by loop over the bases runs one pass. -/
theorem middle_loop {w : ℕ} (hw : 0 < w) (hw' : w < 64) (hdiv : (64 + 2 * w - 1) / (2 * w) * (2 * w) = 64)
    (m : BitVec 64) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0
        { iter := { start := usz 0, «end» := usz 64 }, step := usz (2 * w) } a (usz w) ⟨m⟩ =
      .ok (passA w m a) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0 passA
  have key := loop_of_steps
    (fun x : CoreModels.core.iter.adapters.step_by.StepBy (CoreModels.core.ops.range.Range Std.Usize) ×
        Std.Array Std.U64 64#usize =>
      p3_blake2s_air.binary.generation.transpose_bits_loop0_loop0.body (usz w) ⟨m⟩ x.1 x.2)
    (fun k => (({ iter := { start := usz (2 * w * k), «end» := usz 64 }, step := usz (2 * w) } :
        CoreModels.core.iter.adapters.step_by.StepBy (CoreModels.core.ops.range.Range Std.Usize)),
      ((List.range k).map (· * (2 * w))).foldl (fun a base => (List.range' base w).foldl (stepA w m) a) a))
    ((64 + 2 * w - 1) / (2 * w)) _
    (fun k hk => by
      have hk' : 2 * w * k + 2 * w ≤ 64 := by
        have := Nat.mul_le_mul_right (2 * w) (Nat.succ_le_of_lt hk)
        rw [Nat.succ_mul] at this
        rw [Nat.mul_comm (2 * w) k]; omega
      simp only
      rw [middle_body hw hw' m hk', List.range_succ, List.map_append, List.foldl_append, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil, show 2 * w * k + 2 * w = 2 * w * (k + 1) by ring,
        show k * (2 * w) = 2 * w * k by ring])
    (by simp only; rw [show 2 * w * ((64 + 2 * w - 1) / (2 * w)) = 64 by rw [Nat.mul_comm]; exact hdiv];
        exact middle_done w hw hw' m _)
  simpa using key

/-! ## The outer loop -/

theorem lit0u : (0#usize : Std.Usize) = usz 0 := eq_usz (by norm_num) rfl
theorem lit2u : (2#usize : Std.Usize) = usz 2 := eq_usz (by norm_num) rfl

theorem usz_ne_zero {w : ℕ} (hw : 0 < w) (hw' : w < 2 ^ 32) : usz w ≠ usz 0 := fun h => by
  have := congrArg UScalar.val h
  rw [usz_val hw', usz_val (by norm_num)] at this
  omega

theorem usz_shr_one {w : ℕ} (hw : w < 2 ^ 32) : (usz w >>> (1#i32 : Std.I32) : RustM Std.Usize) = .ok (usz (w / 2)) := by
  have hN : 1 < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  rw [shiftRight_i32_eq _ _ (by decide) (by simpa using hN)]
  congr 1
  apply eq_usz (by omega)
  show (BitVec.ushiftRight (usz w).bv (I32.toNat 1#i32)).toNat = w / 2
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have : (usz w).bv.toNat = w := usz_val hw
  rw [this, Nat.shiftRight_eq_div_pow]
  rfl

/-- One iteration of the outer loop runs a pass, halves the width, and moves to the next mask. -/
theorem outer_body {w : ℕ} (hw : 0 < w) (hw' : w < 64) (hdiv : (64 + 2 * w - 1) / (2 * w) * (2 * w) = 64)
    (m : BitVec 64) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0.body a (usz w) ⟨m⟩ =
      .ok (.cont (passA w m a, usz (w / 2), ⟨m ^^^ m <<< (w / 2)⟩)) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0.body
  have hne : (usz w != (0#usize : Std.Usize)) = true := by
    rw [lit0u, bne_iff_ne]; exact usz_ne_zero hw (by omega)
  rw [ite_eq_left hne]
  have h2 : ¬ (usz (2 * w) = usz 0) := usz_ne_zero (by omega) (by omega)
  rw [lit2u, usz_mul (by omega) (by norm_num) (by omega), bind_ok]
  simp only [CoreModels.core.iter.traits.iterator.Iterator.step_by.default,
    CoreModels.core.iter.adapters.step_by.StepBy.new, h2, ↓reduceIte, bind_ok, lit0u, lit64]
  rw [middle_loop hw hw' hdiv m a, bind_ok, usz_shr_one (by omega), bind_ok,
    shl_usize _ _ (by rw [usz_val (by omega)]; omega), bind_ok, lift, bind_ok, usz_val (by omega)]
  rfl

theorem outer_done (m : BitVec 64) (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits_loop0.body a (usz 0) ⟨m⟩ = .ok (.done a) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits_loop0.body
  have hne : (usz 0 != (0#usize : Std.Usize)) = false := by rw [lit0u]; simp
  rw [hne]
  rfl

/-- The widths of the six passes, then zero. -/
def widthAt (k : ℕ) : ℕ := [32, 16, 8, 4, 2, 1, 0].getD k 0

/-- The masks of the six passes, then zero. -/
def maskAt (k : ℕ) : BitVec 64 :=
  [0x00000000ffffffff#64, 0x0000ffff0000ffff#64, 0x00ff00ff00ff00ff#64, 0x0f0f0f0f0f0f0f0f#64,
    0x3333333333333333#64, 0x5555555555555555#64, 0#64].getD k 0

/-- The array after `k` passes. -/
def passesA (a : Std.Array Std.U64 64#usize) : ℕ → Std.Array Std.U64 64#usize
  | 0 => a
  | k + 1 => passA (widthAt k) (maskAt k) (passesA a k)

theorem outer_loop (a : Std.Array Std.U64 64#usize) :
    p3_blake2s_air.binary.generation.transpose_bits a = .ok (passesA a 6) := by
  unfold p3_blake2s_air.binary.generation.transpose_bits p3_blake2s_air.binary.generation.transpose_bits_loop0
  have key := loop_of_steps
    (fun x : Std.Array Std.U64 64#usize × Std.Usize × Std.U64 =>
      p3_blake2s_air.binary.generation.transpose_bits_loop0.body x.1 x.2.1 x.2.2)
    (fun k => (passesA a k, usz (widthAt k), (⟨maskAt k⟩ : Std.U64))) 6 (passesA a 6)
    (fun k hk => by
      simp only
      interval_cases k <;>
        rw [outer_body (by decide) (by decide) (by decide)] <;> congr 3)
    (by simp only; exact outer_done _ _)
  rw [show (32#usize : Std.Usize) = usz (widthAt 0) from eq_usz (by decide) rfl]
  exact key

/-! ## The extracted transpose is the transcribed one -/

/-- On the rows inside the array, a pass on the array is the transcribed pass. -/
theorem arrF_passA {w : ℕ} (hw : 0 < w) (m : BitVec 64) (hrows : ∀ r ∈ passRows w, r + w < 64)
    {a : Std.Array Std.U64 64#usize} {f : ℕ → BitVec 64} (h : ∀ i < 64, arrF a i = f i) :
    ∀ i < 64, arrF (passA w m a) i = tpass w m f i := by
  have e : passA w m a = (passRows w).foldl (stepA w m) a := by rw [passA, passRows, List.foldl_flatMap]
  rw [e, tpass_eq]
  clear e
  generalize passRows w = L at hrows ⊢
  induction L generalizing a f with
  | nil => exact h
  | cons r L ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (arrF_stepA hw m h (hrows r List.mem_cons_self))
      (fun x hx => hrows x (List.mem_cons_of_mem _ hx))

theorem passRows_bound : ∀ w ∈ [32, 16, 8, 4, 2, 1], ∀ r ∈ passRows w, r + w < 64 := by decide

/-- The extracted transpose never panics, and returns the transcribed transpose of its rows. -/
theorem transpose_bits_extracted (rows : Std.Array Std.U64 64#usize) :
    ∃ out, p3_blake2s_air.binary.generation.transpose_bits rows = .ok out ∧
      ∀ i < 64, (out.val[i]!).bv = transpose_bits (arrF rows) i := by
  refine ⟨_, outer_loop rows, fun i hi => ?_⟩
  rw [transpose_eq]
  have p1 := arrF_passA (w := 32) (by decide) (maskAt 0) (passRows_bound 32 (by simp))
    (a := passesA rows 0) (f := arrF rows) (fun _ _ => rfl)
  have p2 := arrF_passA (w := 16) (by decide) (maskAt 1) (passRows_bound 16 (by simp)) p1
  have p3 := arrF_passA (w := 8) (by decide) (maskAt 2) (passRows_bound 8 (by simp)) p2
  have p4 := arrF_passA (w := 4) (by decide) (maskAt 3) (passRows_bound 4 (by simp)) p3
  have p5 := arrF_passA (w := 2) (by decide) (maskAt 4) (passRows_bound 2 (by simp)) p4
  have p6 := arrF_passA (w := 1) (by decide) (maskAt 5) (passRows_bound 1 (by simp)) p5
  exact p6 i hi

/-- The extracted transpose moves bit `r` of row `c` to bit `c` of row `r`. -/
theorem transpose_bits_extracted_bit (rows : Std.Array Std.U64 64#usize) :
    ∃ out, p3_blake2s_air.binary.generation.transpose_bits rows = .ok out ∧
      ∀ r < 64, ∀ c < 64, (out.val[r]!).bv.getLsbD c = (rows.val[c]!).bv.getLsbD r := by
  obtain ⟨out, h, e⟩ := transpose_bits_extracted rows
  exact ⟨out, h, fun r hr c hc => by rw [e r hr, transpose_bit _ hr hc]; rfl⟩

end Plonky3Lean.Proofs.Blake2sAir
