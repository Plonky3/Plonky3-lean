module

public import Plonky3Lean.Proofs.BinaryDft.Extracted
public import Plonky3Lean.Proofs.BinaryDft.Coset
public import Plonky3Lean.Lib.Slice

@[expose] public section

/-!
# The extracted Lin-Chung-Han kernels

hax extracts the forward and inverse transform kernels, generic over the butterfly trait.

A buffer of w columns is read as its rows, each a function from columns to the field.

Each kernel returns the buffer that its transcription computes on those rows.

It panics exactly when the transcription does.

So every theorem about the transcribed transform holds for the shipped kernels.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

/-! ## Words -/

/-- The word of a natural number, wrapped at the word size. -/
abbrev uz (k : ℕ) : Std.Usize := ⟨BitVec.ofNat _ k⟩

theorem uz_val {k : ℕ} (h : k ≤ Usize.max) : (uz k).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
    rw [Usize.max_def]; simp [Usize.numBits]
  have := Nat.two_pow_pos UScalarTy.Usize.numBits
  omega

theorem usz_eq_uz (k : ℕ) : usz k = uz k := rfl

theorem eq_uz (x : Std.Usize) : x = uz x.val := UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)])

theorem uz_add_one {a : ℕ} (h : a + 1 ≤ Usize.max) :
    (uz a + 1#usize : RustM Std.Usize) = .ok (uz (a + 1)) := by
  obtain ⟨z, hz, hv⟩ := usize_add_ok (uz a) 1#usize (by
    rw [uz_val (by omega), show (1#usize : Std.Usize).val = 1 from rfl]; exact h)
  rw [hz, eq_uz z, hv, uz_val (by omega), show (1#usize : Std.Usize).val = 1 from rfl]

theorem uz_add {a b : ℕ} (h : a + b ≤ Usize.max) :
    (uz a + uz b : RustM Std.Usize) = .ok (uz (a + b)) := by
  obtain ⟨z, hz, hv⟩ := usize_add_ok (uz a) (uz b) (by rw [uz_val (by omega), uz_val (by omega)]; exact h)
  rw [hz, eq_uz z, hv, uz_val (by omega), uz_val (by omega)]

theorem uz_sub {a b : ℕ} (hb : b ≤ a) (ha : a ≤ Usize.max) :
    (uz a - uz b : RustM Std.Usize) = .ok (uz (a - b)) := by
  obtain ⟨z, hz, hv⟩ := usize_sub_ok (uz a) (uz b) (by rw [uz_val ha, uz_val (by omega)]; exact hb)
  rw [hz, eq_uz z, hv, uz_val ha, uz_val (by omega)]

theorem uz_mul {a b : ℕ} (h : a * b ≤ Usize.max) (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) :
    (uz a * uz b : RustM Std.Usize) = .ok (uz (a * b)) := by
  have hs := Usize.mul_spec (x := uz a) (y := uz b)
  obtain ⟨z, hz, hv⟩ : ∃ z, (uz a * uz b : RustM Std.Usize) = .ok z ∧ z.val = (uz a).val * (uz b).val := by
    generalize (uz a * uz b : RustM Std.Usize) = m at hs ⊢
    cases m with
    | ret r => exact ⟨r, rfl, by simpa using hs⟩
    | vis i k => cases i with
      | fail e => (cases e <;> simp [WP.partialSpec] at hs; rw [uz_val ha, uz_val hb] at hs; omega)
    | div => simp at hs
  rw [hz, eq_uz z, hv, uz_val ha, uz_val hb]

theorem uz_lt {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) : uz a < uz b ↔ a < b := by
  rw [UScalar.lt_equiv, uz_val ha, uz_val hb]

theorem uz_le {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) : uz a ≤ uz b ↔ a ≤ b := by
  rw [UScalar.le_equiv, uz_val ha, uz_val hb]

/-! ## Loops -/

/-- A loop that follows a fold over an index range, step by step, under an invariant.

At index k the loop state encodes the fold's value.

A step of the fold that fails is a panic of the loop. -/
theorem loop_foldlM_inv {α β γ : Type} (body : α → RustM (ControlFlow α β)) (enc : γ → ℕ → α)
    (out : γ → β) (n : ℕ) (g : γ → ℕ → Option γ) (P : γ → ℕ → Prop)
    (hstep : ∀ k < n, ∀ c, P c k →
      match g c k with
      | some c' => P c' (k + 1) ∧ body (enc c k) = .ok (.cont (enc c' (k + 1)))
      | none => body (enc c k) = .fail .panic)
    (hdone : ∀ c, P c n → body (enc c n) = .ok (.done (out c))) (c : γ) (hc : P c 0) :
    loop body (enc c 0) = ofOption (((List.range n).foldlM g c).map out) := by
  suffices h : ∀ m ≤ n, ∀ c, P c (n - m) → loop body (enc c (n - m)) =
      ofOption ((((List.range' (n - m) m)).foldlM g c).map out) by
    simpa [List.range_eq_range'] using h n le_rfl c (by simpa using hc)
  intro m
  induction m with
  | zero => intro _ c hc; rw [loop, Nat.sub_zero, hdone c (by simpa using hc), bind_ok]; rfl
  | succ m ih =>
    intro hm c hc
    have hs := hstep (n - (m + 1)) (by omega) c hc
    rw [List.range'_succ, List.foldlM_cons]
    revert hs
    cases g c (n - (m + 1)) with
    | none => intro hs; rw [loop, hs]; simp [ofOption]
    | some c' =>
      intro hs
      rw [loop, hs.2, bind_ok]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show n - (m + 1) + 1 = n - m by omega] at hs ⊢
      exact ih (by omega) c' hs.1

/-- A loop that follows a fold over an index range, step by step. -/
theorem loop_foldlM {α β γ : Type} (body : α → RustM (ControlFlow α β)) (enc : γ → ℕ → α)
    (out : γ → β) (n : ℕ) (g : γ → ℕ → Option γ)
    (hstep : ∀ k < n, ∀ c, body (enc c k) =
      match g c k with
      | some c' => .ok (.cont (enc c' (k + 1)))
      | none => .fail .panic)
    (hdone : ∀ c, body (enc c n) = .ok (.done (out c))) (c : γ) :
    loop body (enc c 0) = ofOption (((List.range n).foldlM g c).map out) :=
  loop_foldlM_inv body enc out n g (fun _ _ => True)
    (fun k hk c _ => by rw [hstep k hk c]; cases g c k <;> simp)
    (fun c _ => hdone c) c trivial

/-! ## Lists as slices -/

/-- A list as a slice, or the empty slice if it is too long. -/
def mkSlice {α : Type} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (by simp)

theorem mkSlice_val {α : Type} {l : List α} (h : l.length ≤ Usize.max) : (mkSlice l).val = l := by
  simp [mkSlice, h]

theorem mkSlice_self {α : Type} (s : Slice α) : mkSlice s.val = s :=
  Slice.ext _ _ (mkSlice_val s.property)

/-- A list as a vector, or the empty vector if it is too long. -/
def mkVec {α : Type} (l : List α) : alloc.vec.Vec α := mkSlice l

theorem vec_new_eq {α : Type} : alloc.vec.Vec.new α = .ok (mkVec []) := by
  simp only [alloc.vec.Vec.new, rust_primitives.sequence.seq_empty]
  refine (bind_tc_ok (α := alloc.vec.Vec α) _ _).trans ?_
  congr 1

theorem vec_push_eq {α : Type} (l : List α) (x : α) (h : l.length + 1 ≤ Usize.max) :
    alloc.vec.Vec.push (mkVec l) x = .ok (mkVec (l ++ [x])) := by
  simp only [alloc.vec.Vec.push, rust_primitives.sequence.seq_push]
  rw [dite_eq_left (by rw [mkVec, mkSlice_val (by omega)]; simpa using h)]
  refine (bind_tc_ok (α := alloc.vec.Vec α) _ _).trans ?_
  congr 1; apply Slice.ext
  simp only [Slice.from_val, mkVec, mkSlice_val (show l.length ≤ Usize.max by omega)]
  rw [mkSlice_val (by simpa using h)]

theorem vec_index_eq {α : Type} (l : List α) (hl : l.length ≤ Usize.max) (i : Std.Usize) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT α) (mkVec l) i = ofOption l[i.val]? := by
  have hv : (mkSlice l).val = l := mkSlice_val hl
  simp only [alloc.vec.Vec.Insts.CoreOpsIndexIndex.index, alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref,
    alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_index, bind_ok, mkVec]
  by_cases h : i.val < l.length
  · have : i < (mkSlice l).len := by scalar_tac
    simp only [this, ↓reduceIte]
    rw [slice_index_eq _ i (by rw [hv]; exact h), List.getElem?_eq_getElem h]
    simp [ofOption, hv]
  · have : ¬ i < (mkSlice l).len := by scalar_tac
    simp only [this, ↓reduceIte, bind_ok, List.getElem?_eq_none (by omega : l.length ≤ i.val)]
    rfl

/-! ## The domain steps -/

variable {F R : Type} [Field F] {inst : p3_binary_field.tower.TowerLevel F R} {L : Level F}

/-- The extracted domain steps return what their transcription computes. -/
theorem domain_point_steps_eq_mirror (h : TowerComputes inst L) (count : Std.Usize) :
    p3_binary_dft.domain.domain_point_steps inst count =
      ofOption ((p3_binary_dft.domain.mirror.domain_point_steps L count.val).map mkVec) := by
  have hc := count.hmax
  unfold p3_binary_dft.domain.domain_point_steps p3_binary_dft.hax_reshaped.domain_point_steps
    p3_binary_dft.domain.mirror.domain_point_steps
  rw [vec_new_eq, bind_ok, h.zero, bind_ok]
  unfold p3_binary_dft.hax_reshaped.domain_point_steps_loop
  have := loop_foldlM_inv (fun st => p3_binary_dft.hax_reshaped.domain_point_steps_loop.body inst st.1 st.2.1 st.2.2)
    (fun (c : F × List F) k => (({ start := uz k, «end» := count } : core.ops.range.Range Std.Usize),
      mkVec c.2, c.1))
    (fun c => mkVec c.2) count.val
    (fun acc r => do
      let point := acc.1 + (← L.cantorBasis (r + 1))
      pure (point, acc.2 ++ [point]))
    (fun c k => c.2.length = k) (fun k hk c hck => ?_) (fun c hck => ?_) (0, []) rfl
  · rw [Option.map_map]; exact this
  · simp only [p3_binary_dft.hax_reshaped.domain_point_steps_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz k, «end» := count } = _ from range_step k count hk]
    simp only [bind_ok]
    have hk1 : k + 1 ≤ Usize.max := by scalar_tac
    cases hb : L.cantorBasis (k + 1) with
    | none =>
      simp [usz_eq_uz, uz_add_one hk1, h.cantor, uz_val hk1, hb, ofOption]
    | some b =>
      simp [usz_eq_uz, uz_add_one hk1, h.cantor, uz_val hk1, hb, ofOption, hck,
        h.add_assign, vec_push_eq _ _ (show c.2.length + 1 ≤ Usize.max by scalar_tac)]
  · simp only [p3_binary_dft.hax_reshaped.domain_point_steps_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz count.val, «end» := count } = _ from
      range_next_none _ _ (by rw [uz_val (by scalar_tac)])]
    simp

/-! ## The twiddle state -/

open p3_binary_dft.lch.mirror in
/-- A transcribed twiddle state as the extracted structure. -/
def toTw (tw : Twiddles F) : p3_binary_dft.lch.twiddles.Twiddles F := ⟨mkVec tw.bases, mkVec tw.steps⟩

theorem saturating_sub_exposed_eq (a b : Std.Usize) :
    core.num.Usize.saturating_sub_exposed a b = .ok (uz (a.val - b.val)) := rfl

open p3_binary_dft.lch.mirror in
/-- The extracted twiddle state is the transcribed one. -/
theorem twiddles_new_eq_mirror (h : TowerComputes inst L) (log_n : Std.Usize) (shift : F) :
    p3_binary_dft.lch.twiddles.Twiddles.new inst log_n shift =
      ofOption ((Twiddles.new L log_n.val shift).map toTw) := by
  have hl := log_n.hmax
  unfold p3_binary_dft.lch.twiddles.Twiddles.new p3_binary_dft.lch.twiddles.Twiddles.new_indexed
    Twiddles.new
  rw [vec_new_eq, bind_ok]
  have := loop_foldlM_inv
    (fun st => p3_binary_dft.lch.twiddles.Twiddles.new_indexed_loop.body inst st.1 st.2.1 st.2.2)
    (fun (c : List F × F) k => (({ start := uz k, «end» := log_n } : core.ops.range.Range Std.Usize),
      mkVec c.1, c.2))
    (fun c => mkVec c.1) log_n.val
    (fun acc _ => some (acc.1 ++ [acc.2], acc.2 ^ 2 + acc.2))
    (fun c k => c.1.length = k) (fun k hk c hck => ?_) (fun c hck => ?_) ([], shift) rfl
  · have hloop : p3_binary_dft.lch.twiddles.Twiddles.new_indexed_loop inst
        { start := 0#usize, «end» := log_n } (mkVec []) shift = _ := this
    rw [hloop, foldlM_some _ (fun (acc : List F × F) _ => (acc.1 ++ [acc.2], acc.2 ^ 2 + acc.2)) _
        (fun _ _ _ => rfl)]
    simp only [ofOption, Option.map_some, bind_ok, saturating_sub_exposed_eq,
      show (1#usize : Std.Usize).val = 1 from rfl, domain_point_steps_eq_mirror h,
      uz_val (show log_n.val - 1 ≤ Usize.max by scalar_tac)]
    cases p3_binary_dft.domain.mirror.domain_point_steps L (log_n.val - 1) <;> simp [toTw]
  · simp only [p3_binary_dft.lch.twiddles.Twiddles.new_indexed_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz k, «end» := log_n } = _ from range_step k log_n hk]
    simp [usz_eq_uz, hck, h.square, h.add, vec_push_eq _ _ (show c.1.length + 1 ≤ Usize.max by scalar_tac)]
  · simp only [p3_binary_dft.lch.twiddles.Twiddles.new_indexed_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz log_n.val, «end» := log_n } = _ from
      range_next_none _ _ (by rw [uz_val (by scalar_tac)])]
    simp

/-- The trailing zeros of a nonzero word are those the transcription counts. -/
theorem trailing_zeros_eq (n : Std.Usize) (hn : 0 < n.val) :
    core.num.Usize.trailing_zeros n = .ok ⟨BitVec.ofNat 32 (trailingZeros n.val)⟩ := by
  unfold core.num.Usize.trailing_zeros
  obtain ⟨a, ha⟩ := trailingZeros_spec hn
  generalize trailingZeros n.val = t at ha ⊢
  have hlt : t < UScalarTy.Usize.numBits := by
    by_contra hc
    have := n.hBounds
    have : 2 ^ UScalarTy.Usize.numBits ≤ n.val := by
      rw [ha]; exact le_trans (Nat.pow_le_pow_right two_pos (by omega)) (Nat.le_mul_of_pos_right _ (by omega))
    omega
  have : (List.range UScalarTy.Usize.numBits).find? (fun i => n.val.testBit i) = some t := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, t, by simpa using hlt, by simp, fun j hj => ?_⟩
    · rw [ha, Nat.testBit_two_pow_mul]; simp
    · simp only [List.getElem_range]
      rw [ha, Nat.testBit_two_pow_mul]; simp; omega
  rw [this, Option.getD_some]

open p3_binary_dft.lch.mirror in
/-- The extracted twiddle of a block is the transcribed one, while twice the block fits a word. -/
theorem twiddles_at_eq (h : TowerComputes inst L) (tw : Twiddles F) (hb : tw.bases.length ≤ Usize.max)
    (stage block : Std.Usize) (h2 : block.val * 2 ≤ Usize.max) :
    p3_binary_dft.lch.twiddles.Twiddles.at inst (toTw tw) stage block =
      ofOption (tw.at L stage.val block.val) := by
  unfold p3_binary_dft.lch.twiddles.Twiddles.at Twiddles.at
  have hsh : (block <<< 1#i32 : RustM Std.Usize) = .ok (uz (block.val * 2)) := by
    rw [shiftLeft_i32_eq _ _ (by decide) (by
      simp [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> simp [e])]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [uz_val h2]
    show (block.bv <<< (1#i32 : Std.I32).toNat).toNat = _
    rw [show (1#i32 : Std.I32).toNat = 1 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      pow_one, Nat.mod_eq_of_lt]
    · rfl
    · have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
      have := Nat.two_pow_pos UScalarTy.Usize.numBits
      show block.val * 2 < _
      simp only [UScalarTy.Usize_numBits_eq] at *; omega
  simp only [toTw, vec_index_eq _ hb, hsh, bind_ok, domain_point_eq_mirror h, uz_val h2]
  cases tw.bases[stage.val]? <;> simp [ofOption]
  cases p3_binary_dft.domain.mirror.domain_point L (block.val * 2) <;> simp [h.add]

open p3_binary_dft.lch.mirror in
/-- The extracted step to a nonzero block is the transcribed one. -/
theorem twiddles_step_eq (tw : Twiddles F) (hs : tw.steps.length ≤ Usize.max) (index : Std.Usize)
    (hi : 0 < index.val) :
    p3_binary_dft.lch.twiddles.Twiddles.step inst (toTw tw) index = ofOption (tw.step index.val) := by
  unfold p3_binary_dft.lch.twiddles.Twiddles.step Twiddles.step
  rw [trailing_zeros_eq index hi, bind_ok, lift_eq, bind_ok, toTw, vec_index_eq _ hs]
  have ht := trailingZeros_lt hi index.hBounds
  have h64 : UScalarTy.Usize.numBits ≤ 64 := by
    rcases System.Platform.numBits_eq with e | e <;> simp [UScalarTy.numBits, e]
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
    rcases System.Platform.numBits_eq with e | e <;> simp [UScalarTy.numBits, e])]
  show ofOption tw.steps[(BitVec.ofNat 32 (trailingZeros index.val)).toNat]? = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Buffers as rows -/

/-- The forward or the inverse butterfly with a twiddle. -/
def bop {V : Type _} [AddCommGroup V] [Module F V] (inverse : Bool) (t : F) : V → V → V × V :=
  if inverse then ibutterfly t else butterfly t

theorem bop_apply (inverse : Bool) (t : F) (u v : ℕ → F) (c : ℕ) :
    ((bop inverse t u v).1 c = (bop inverse t (u c) (v c)).1) ∧
      ((bop inverse t u v).2 c = (bop inverse t (u c) (v c)).2) := by
  cases inverse
  · simp [bop, butterfly]
  · simp [bop, ibutterfly]; ring

/-- Row r of a buffer of w columns: its entries r w, ..., r w + w - 1, and zero past the end. -/
def rowsOf (w : ℕ) (s : List F) : ℕ → ℕ → F := fun r c => s.getD (r * w + c) 0

/-- The first n rows of a matrix of w columns, flattened. -/
def flat (w n : ℕ) (x : ℕ → ℕ → F) : List F := (List.range (n * w)).map fun p => x (p / w) (p % w)

theorem length_flat (w n : ℕ) (x : ℕ → ℕ → F) : (flat w n x).length = n * w := by simp [flat]

theorem flat_getElem? {w n : ℕ} (x : ℕ → ℕ → F) (p : ℕ) :
    (flat w n x)[p]? = if p < n * w then some (x (p / w) (p % w)) else none := by
  by_cases hp : p < n * w <;> simp [flat, hp]

theorem flat_rowsOf {w n : ℕ} (s : List F) (hs : s.length = n * w) :
    flat w n (rowsOf w s) = s := by
  apply List.ext_getElem? ; intro p
  rw [flat_getElem?]
  split_ifs with hp
  · simp [rowsOf, Nat.div_add_mod' p w, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show p < s.length by omega)]
  · rw [List.getElem?_eq_none (by omega)]

theorem rowsOf_flat {w n : ℕ} (x : ℕ → ℕ → F) {r c : ℕ} (hr : r < n) (hc : c < w) :
    rowsOf w (flat w n x) r c = x r c := by
  have hp : r * w + c < n * w := by nlinarith
  simp only [rowsOf, List.getD_eq_getElem?_getD, flat_getElem?, hp, ↓reduceIte, Option.getD_some]
  congr 1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-! ## One block of butterflies -/

open p3_binary_dft.butterfly.mirror p3_dft.mirror in
variable [DecidableEq F] in
/-- The packed butterfly of m pairs, the run at lo against the run at hi, element by element. -/
theorem packed_butterfly_apply {V : Type _} [AddCommGroup V] [Module F V] (inverse : Bool)
    {lo hi m : ℕ} (hlh : lo + m ≤ hi) (t : F) (x : ℕ → V) (i : ℕ) :
    packed_butterfly inverse lo hi m t x i =
      if lo ≤ i ∧ i < lo + m then (bop inverse t (x i) (x (i - lo + hi))).1
      else if hi ≤ i ∧ i < hi + m then (bop inverse t (x (i - hi + lo)) (x i)).2
      else x i := by
  unfold packed_butterfly butterfly_values
  rw [Plonky3Lean.Proofs.BinaryDft.pairOp_eq]
  change List.foldl (fun acc s => bfly (bop inverse t) (lo + s) (hi + s) acc) x (List.range m) i = _
  induction m generalizing i with
  | zero => simp only [List.range_zero, List.foldl_nil]; split_ifs <;> first | rfl | omega
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih' := fun j => ih (by omega) j
    simp only [bfly, ih']
    split_ifs <;> first | rfl | omega | (simp_all; done) | (subst_vars; congr 3; omega)

/-- A buffer after the butterflies of one block of 2 H entries from o, as the extracted code writes it back. -/
def blockList (inverse : Bool) (t : F) (g : List F) (o H : ℕ) : List F :=
  let sub := (g.drop o).take (2 * H)
  g.setSlice! o (List.zipWith (fun u v => (bop inverse t u v).1) (sub.take H) (sub.drop H) ++
    List.zipWith (fun u v => (bop inverse t u v).2) (sub.take H) (sub.drop H))

theorem blockList_getElem? (inverse : Bool) (t : F) (g : List F) {o H : ℕ} (h : o + 2 * H ≤ g.length)
    (p : ℕ) :
    (blockList inverse t g o H)[p]? =
      if o ≤ p ∧ p < o + H then some (bop inverse t (g.getD p 0) (g.getD (p + H) 0)).1
      else if o + H ≤ p ∧ p < o + 2 * H then some (bop inverse t (g.getD (p - H) 0) (g.getD p 0)).2
      else g[p]? := by
  unfold blockList
  simp only
  have hz : ∀ f : F → F → F, (List.zipWith f (((g.drop o).take (2 * H)).take H)
      (((g.drop o).take (2 * H)).drop H)).length = H := fun f => by simp; omega
  split_ifs with h1 h2
  · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨h1.1, by simp; omega, by omega⟩,
      List.getElem?_append_left (by rw [hz]; omega), List.getElem?_zipWith]
    simp only [List.getElem?_take, List.getElem?_drop, List.getD_eq_getElem?_getD]
    rw [show o + (p - o) = p by omega, show o + (H + (p - o)) = p + H by omega,
      List.getElem?_eq_getElem (show p < g.length by omega),
      List.getElem?_eq_getElem (show p + H < g.length by omega)]
    split_ifs <;> first | omega | simp
  · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨by omega, by simp; omega, by omega⟩,
      List.getElem?_append_right (by rw [hz]; omega), List.getElem?_zipWith, hz]
    simp only [List.getElem?_take, List.getElem?_drop, List.getD_eq_getElem?_getD]
    rw [show o + (p - o - H) = p - H by omega, show o + (H + (p - o - H)) = p by omega,
      List.getElem?_eq_getElem (show p - H < g.length by omega),
      List.getElem?_eq_getElem (show p < g.length by omega)]
    split_ifs <;> first | omega | simp
  · rw [List.setSlice!_getElem?_same]
    simp; omega

theorem row_le_iff {a r c w : ℕ} (hc : c < w) : a * w ≤ r * w + c ↔ a ≤ r := by
  constructor
  · intro h; by_contra h'; push Not at h'
    have : (r + 1) * w ≤ a * w := Nat.mul_le_mul_right _ h'
    rw [add_mul, one_mul] at this; omega
  · intro h; have := Nat.mul_le_mul_right w h; omega

theorem row_lt_iff {a r c w : ℕ} (hc : c < w) : r * w + c < a * w ↔ r < a := by
  rw [← not_le, ← not_le, not_iff_not]
  constructor
  · intro h; by_contra h'; push Not at h'
    have : (r + 1) * w ≤ a * w := Nat.mul_le_mul_right _ h'
    rw [add_mul, one_mul] at this; omega
  · intro h; have := Nat.mul_le_mul_right w h; omega

theorem div_row {r c w : ℕ} (hc : c < w) : (r * w + c) / w = r := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]

theorem mod_row {r c w : ℕ} (hc : c < w) : (r * w + c) % w = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem flat_getD {w n : ℕ} (x : ℕ → ℕ → F) {r c : ℕ} (hr : r < n) (hc : c < w) :
    (flat w n x).getD (r * w + c) 0 = x r c := rowsOf_flat x hr hc

open p3_binary_dft.butterfly.mirror in
variable [DecidableEq F] in
/-- One full block of the extracted walk is the transcribed block, on the flattened rows. -/
theorem blockList_flat (inverse : Bool) (t : F) {w len half k : ℕ} (hw : 0 < w)
    (hfull : (k + 1) * (2 * half) ≤ len) (y : ℕ → ℕ → F) :
    blockList inverse t (flat w len y) (k * (2 * half) * w) (half * w) =
      flat w len (packed_butterfly inverse (k * (2 * half)) (k * (2 * half) + half) half t y) := by
  apply List.ext_getElem?
  intro p
  have hlen : k * (2 * half) * w + 2 * (half * w) ≤ (flat w len y).length := by
    rw [length_flat]; nlinarith
  rw [blockList_getElem? _ _ _ hlen, flat_getElem?, flat_getElem?]
  obtain ⟨r, c, hc, rfl⟩ : ∃ r c, c < w ∧ p = r * w + c :=
    ⟨p / w, p % w, Nat.mod_lt _ hw, by rw [Nat.mul_comm]; exact (Nat.div_add_mod p w).symm⟩
  rw [div_row hc, mod_row hc, packed_butterfly_apply _ (by omega)]
  have e1 : k * (2 * half) * w + half * w = (k * (2 * half) + half) * w := by ring
  have e2 : k * (2 * half) * w + 2 * (half * w) = (k * (2 * half) + 2 * half) * w := by ring
  simp only [e1, e2, row_le_iff hc, row_lt_iff hc]
  have hA : k * (2 * half) + 2 * half ≤ len := by rw [add_mul, one_mul] at hfull; exact hfull
  clear e1 e2 hlen hfull
  generalize k * (2 * half) = A at *
  have e3 : r * w + c + half * w = (r + half) * w + c := by ring
  rw [e3]
  split_ifs <;> try (first | omega | rfl)
  · rw [flat_getD _ (by omega) hc, flat_getD _ (by omega) hc, (bop_apply _ _ _ _ _).1,
      show r - A + (A + half) = r + half by omega]
  · rw [show r * w + c - half * w = (r - half) * w + c by rw [Nat.sub_mul]; have := Nat.mul_le_mul_right w (show half ≤ r by omega); omega,
      flat_getD _ (by omega) hc, flat_getD _ (by omega) hc, (bop_apply _ _ _ _ _).2,
      show r - (A + half) + A = r - half by omega]

/-! ## Slicing -/

/-- Borrowing the range a .. b of a slice, with the write-back of a borrow of the same length. -/
theorem index_mut_range_eq {α : Type} (s : Slice α) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ s.val.length) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α) s
      { start := uz a, «end» := uz b } =
      .ok (mkSlice ((s.val.drop a).take (b - a)), fun x => mkSlice (s.val.setSlice! a x.val)) := by
  have hbm : b ≤ Usize.max := le_trans hb s.property
  simp only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, uz_val hbm, uz_val (le_trans hab hbm)]
  have hc : a ≤ b ∧ b ≤ s.length := ⟨hab, hb⟩
  simp only [hc, and_self, ↓reduceIte, bind_ok]
  congr 1
  simp only [Prod.mk.injEq]
  refine ⟨Slice.ext _ _ ?_, funext fun x => Slice.ext _ _ ?_⟩
  · rw [Slice.from_val, mkSlice_val (le_trans (by simp) s.property)]; rfl
  · rw [Slice.from_val, mkSlice_val (by simp)]

/-- Splitting a slice at n: its first n entries, the rest, and the write-back of two runs of those lengths. -/
theorem split_at_mut_eq {α : Type} (s : Slice α) {n : ℕ} (hn : n ≤ s.val.length) :
    ∃ back, core.slice.Slice.split_at_mut s (uz n) =
      .ok ((mkSlice (s.val.take n), mkSlice (s.val.drop n)), back) ∧
      ∀ a b : Slice α, a.val.length = n → b.val.length = s.val.length - n →
        back (a, b) = mkSlice (a.val ++ b.val) := by
  have hnm : n ≤ Usize.max := le_trans hn s.property
  unfold core.slice.Slice.split_at_mut rust_primitives.slice.slice_split_at_mut
    Aeneas.Std.core.slice.Slice.split_at_mut
  rw [dite_eq_left_of_eq_true (eq_true (by rw [uz_val hnm]; exact hn))]
  dsimp only
  refine ⟨_, congrArg RustM.ok (Prod.ext (Prod.ext ?_ ?_) rfl), fun a b ha hb => ?_⟩
  · apply Slice.ext; simp [uz_val hnm, List.splitAt_eq, mkSlice_val (show (s.val.take n).length ≤ Usize.max by simp)]
  · apply Slice.ext; simp [uz_val hnm, List.splitAt_eq, mkSlice_val (show (s.val.drop n).length ≤ Usize.max by simp; have := s.property; omega)]
  · simp only
    rw [dite_eq_left_of_eq_true (eq_true ⟨by simp [uz_val hnm, ha]; omega, by simp [uz_val hnm, hb]⟩)]
    apply Slice.ext; rw [Slice.from_val, mkSlice_val (by simp [ha, hb]; have := s.property; omega)]

end Plonky3Lean.Proofs.BinaryDft
