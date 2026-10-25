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

theorem ite_of_pos {c : Prop} [Decidable c] (h : c) {α : Sort _} (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_neg {c : Prop} [Decidable c] (h : ¬c) {α : Sort _} (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem uz_one : (1#usize : Std.Usize) = uz 1 :=
  UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl)

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

theorem ofOption_map_bind {α β γ : Type} (o : Option (α × γ)) (f : α → β) :
    ofOption (o.map fun c => f c.1) = ofOption ((o.bind fun r => pure r.1).map f) := by
  cases o <;> rfl

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

/-- Doubling a word by a shift, while the double fits. -/
theorem shl_one_eq (x : Std.Usize) (h2 : x.val * 2 ≤ Usize.max) :
    (x <<< 1#i32 : RustM Std.Usize) = .ok (uz (x.val * 2)) := by
  rw [shiftLeft_i32_eq _ _ (by decide) (by
    simp [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> simp [e])]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [uz_val h2]
  show (x.bv <<< (1#i32 : Std.I32).toNat).toNat = _
  rw [show (1#i32 : Std.I32).toNat = 1 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    pow_one, Nat.mod_eq_of_lt]
  · rfl
  · have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    have := Nat.two_pow_pos UScalarTy.Usize.numBits
    show x.val * 2 < _
    simp only [UScalarTy.Usize_numBits_eq] at *; omega

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
  have hsh := shl_one_eq block h2
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

/-! ## The butterfly instance -/

/-- The lower outputs of the butterflies of two runs, pair by pair. -/
def bfly1 (inverse : Bool) (t : F) (lo hi : List F) : List F :=
  List.zipWith (fun u v => (bop inverse t u v).1) lo hi

/-- The upper outputs of the butterflies of two runs, pair by pair. -/
def bfly2 (inverse : Bool) (t : F) (lo hi : List F) : List F :=
  List.zipWith (fun u v => (bop inverse t u v).2) lo hi

/-- The members of a butterfly instance that the transform calls compute:

- the tower level's members, as for the domain;
- the bit width 2^b of the level, through b;
- the butterfly of two runs of equal length, pair by pair, which panics on runs of different lengths. -/
structure ButterflyComputes (inst : p3_binary_dft.butterfly.ButterflyField F R) (L : Level F) :
    Prop where
  tower : TowerComputes inst.p3_binary_fieldtowerTowerLevelInst L
  logBits : inst.p3_binary_fieldtowerTowerLevelInst.LOG_BITS = .ok (uz L.logBits)
  butterfly : ∀ (inverse : Bool) (lo hi : Slice F) (t : F), inst.butterfly inverse lo hi t =
    if lo.val.length = hi.val.length then
      .ok (mkSlice (bfly1 inverse t lo.val hi.val), mkSlice (bfly2 inverse t lo.val hi.val))
    else .fail .panic

theorem chunk_end_eq {a z n : ℕ} (han : a ≤ n) (hn : n ≤ Usize.max) (hz : z ≤ Usize.max) :
    p3_binary_dft.lch.schedule.hax_reshaped.chunk_end (uz a) (uz z) (uz n) = .ok (uz (min (a + z) n)) := by
  unfold p3_binary_dft.lch.schedule.hax_reshaped.chunk_end
  rw [uz_sub han hn, bind_ok]
  by_cases h : n - a < z
  · rw [ite_of_pos ((uz_lt (by omega) hz).mpr h), min_eq_right (by omega)]
  · rw [ite_of_neg (fun h' => h ((uz_lt (by omega) hz).mp h')), uz_add (by omega), min_eq_left (by omega)]

theorem grain_eq : p3_binary_dft.lch.schedule.BUTTERFLY_GRAIN = .ok (uz 1024) := by
  unfold p3_binary_dft.lch.schedule.BUTTERFLY_GRAIN
  rw [shiftLeft_i32_eq _ _ (by decide) (by
    simp [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> simp [e])]
  congr 1

/-! ## The butterfly one grain at a time -/

/-- The run base with its first m entries replaced by f of the first m pairs of lo and hi. -/
def stg (f : F → F → F) (m : ℕ) (lo hi base : List F) : List F :=
  List.zipWith f (lo.take m) (hi.take m) ++ base.drop m

theorem stg_drop_take (f : F → F → F) {m H : ℕ} (lo hi base : List F) (hlo : lo.length = H)
    (hhi : hi.length = H) (hm : m ≤ H) (d : ℕ) :
    ((stg f m lo hi base).drop m).take d = (base.drop m).take d := by
  unfold stg
  rw [List.drop_append_of_le_length (by simp; omega)]
  simp [hlo, hhi, hm]

theorem stg_getElem? (f : F → F → F) {m H : ℕ} (lo hi base : List F) (hlo : lo.length = H)
    (hhi : hi.length = H) (hm : m ≤ H) (p : ℕ) :
    (stg f m lo hi base)[p]? = if p < m then Option.map₂ f lo[p]? hi[p]? else base[p]? := by
  unfold stg
  split_ifs with hp
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_zipWith]
    simp only [List.getElem?_take, hp, ite_true]
    cases lo[p]? <;> cases hi[p]? <;> rfl
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_zipWith, List.length_take, hlo, hhi, min_self, min_eq_left hm,
      List.getElem?_drop]
    congr 1; omega

theorem stg_setSlice (f : F → F → F) {m m' H : ℕ} (lo hi base : List F) (hlo : lo.length = H)
    (hhi : hi.length = H) (hb : base.length = H) (hm : m ≤ m') (hm' : m' ≤ H) :
    (stg f m lo hi base).setSlice! m
        (List.zipWith f ((lo.drop m).take (m' - m)) ((hi.drop m).take (m' - m))) =
      stg f m' lo hi base := by
  have hx : (List.zipWith f ((lo.drop m).take (m' - m)) ((hi.drop m).take (m' - m))).length = m' - m := by
    simp; omega
  have hl : (stg f m lo hi base).length = H := by simp [stg]; omega
  apply List.ext_getElem?
  intro p
  rw [stg_getElem? f lo hi base hlo hhi hm']
  by_cases h1 : p < m
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ h1, stg_getElem? f lo hi base hlo hhi (by omega),
      ite_of_pos h1, ite_of_pos (show p < m' by omega)]
  by_cases h2 : p < m'
  · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨by omega, by omega, by omega⟩, ite_of_pos h2,
      List.getElem?_zipWith]
    simp only [List.getElem?_take, List.getElem?_drop, show p - m < m' - m by omega, ite_true,
      show m + (p - m) = p by omega]
    cases lo[p]? <;> cases hi[p]? <;> rfl
  · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by rw [hx]; omega), stg_getElem? f lo hi base hlo hhi (by omega),
      ite_of_neg h1, ite_of_neg h2]

theorem slice_len_eq {α : Type} (s : Slice α) : core.slice.Slice.len s = .ok (uz s.val.length) := by
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [uz_val s.property]; simp

theorem stg_zero (f : F → F → F) (lo hi base : List F) : stg f 0 lo hi base = base := by simp [stg]

theorem stg_full (f : F → F → F) {H : ℕ} (lo hi base : List F) (hlo : lo.length = H)
    (hhi : hi.length = H) (hb : base.length = H) :
    stg f H lo hi base = List.zipWith f lo hi := by
  unfold stg
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
    List.drop_of_length_le (by omega), List.append_nil]

theorem length_stg (f : F → F → F) {m H : ℕ} (lo hi base : List F) (hlo : lo.length = H)
    (hhi : hi.length = H) (hb : base.length = H) (hm : m ≤ H) : (stg f m lo hi base).length = H := by
  simp [stg]; omega

/-- The butterfly of two runs of equal length, one grain at a time, is the butterfly of the runs. -/
theorem grains_eq {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (inverse : Bool) (lo hi : Slice F) (t : F) (h : lo.val.length = hi.val.length)
    (hH : lo.val.length + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.hax_reshaped.grains inverse inst lo hi t =
      .ok (mkSlice (bfly1 inverse t lo.val hi.val), mkSlice (bfly2 inverse t lo.val hi.val)) := by
  set H := lo.val.length with hHdef
  set f1 : F → F → F := fun u v => (bop inverse t u v).1
  set f2 : F → F → F := fun u v => (bop inverse t u v).2
  let m : ℕ → ℕ := fun k => min (k * 1024) H
  have := loop_foldlM_inv
    (fun st => p3_binary_dft.lch.schedule.hax_reshaped.grains_loop.body inverse inst t st.1 st.2.1 st.2.2)
    (fun (_ : Unit) k => (mkSlice (stg f1 (m k) lo.val hi.val lo.val),
      mkSlice (stg f2 (m k) lo.val hi.val hi.val), uz (k * 1024)))
    (fun _ => (mkSlice (stg f1 H lo.val hi.val lo.val), mkSlice (stg f2 H lo.val hi.val hi.val)))
    ((H + 1023) / 1024) (fun _ _ => some ()) (fun _ _ => True) (fun k hk _ _ => ?_) (fun _ _ => ?_) () trivial
  · simp only [m, zero_mul, Nat.zero_min, stg_zero, mkSlice_self] at this
    have hloop : p3_binary_dft.lch.schedule.hax_reshaped.grains inverse inst lo hi t = _ := this
    rw [hloop, foldlM_some _ (fun _ _ => ()) _ (fun _ _ _ => rfl)]
    simp only [ofOption, Option.map_some, bfly1, bfly2]
    rw [stg_full f1 lo.val hi.val lo.val hHdef.symm h.symm hHdef.symm,
      stg_full f2 lo.val hi.val hi.val hHdef.symm h.symm h.symm]
  · refine ⟨trivial, ?_⟩
    have hkH : k * 1024 < H := by omega
    have hmk : m k = k * 1024 := by simp only [m]; omega
    set m' := min (k * 1024 + 1024) H with hm'
    have hmk1 : m (k + 1) = m' := by simp only [m, hm']; ring_nf
    have hlo : lo.val.length = H := rfl
    have hhi : hi.val.length = H := h.symm
    have lL := length_stg f1 lo.val hi.val lo.val hlo hhi hlo (le_of_lt hkH)
    have lH := length_stg f2 lo.val hi.val hi.val hlo hhi hhi (le_of_lt hkH)
    have vL : (mkSlice (stg f1 (m k) lo.val hi.val lo.val)).val = stg f1 (k * 1024) lo.val hi.val lo.val := by
      rw [hmk, mkSlice_val (by rw [lL]; omega)]
    have vH : (mkSlice (stg f2 (m k) lo.val hi.val hi.val)).val = stg f2 (k * 1024) lo.val hi.val hi.val := by
      rw [hmk, mkSlice_val (by rw [lH]; omega)]
    have eL := index_mut_range_eq (mkSlice (stg f1 (m k) lo.val hi.val lo.val)) (a := k * 1024) (b := m')
      (by omega) (by rw [vL, lL]; omega)
    have eH := index_mut_range_eq (mkSlice (stg f2 (m k) lo.val hi.val hi.val)) (a := k * 1024) (b := m')
      (by omega) (by rw [vH, lH]; omega)
    rw [vL, stg_drop_take f1 lo.val hi.val lo.val hlo hhi (le_of_lt hkH)] at eL
    rw [vH, stg_drop_take f2 lo.val hi.val hi.val hlo hhi (le_of_lt hkH)] at eH
    have eB := hb.butterfly inverse (mkSlice ((lo.val.drop (k * 1024)).take (m' - k * 1024)))
      (mkSlice ((hi.val.drop (k * 1024)).take (m' - k * 1024))) t
    rw [mkSlice_val (by simp; omega), mkSlice_val (by simp; omega), ite_of_pos (by simp; omega)] at eB
    simp only [p3_binary_dft.lch.schedule.hax_reshaped.grains_loop.body, slice_len_eq, vL, vH, lL, lH,
      bind_ok, ite_of_pos ((uz_lt (by omega) (by omega)).mpr hkH), grain_eq,
      chunk_end_eq (le_of_lt hkH) (show H ≤ Usize.max by omega) (show 1024 ≤ Usize.max by omega),
      uz_add (show k * 1024 + 1024 ≤ Usize.max by omega)]
    simp only [← hm', eL, eH, bind_ok, hmk1, Aeneas.Std.uncurry]
    rw [eB, bind_ok]
    simp only [Aeneas.Std.uncurry, bfly1, bfly2]
    rw [mkSlice_val (by simp; omega), mkSlice_val (by simp; omega),
      stg_setSlice f1 lo.val hi.val lo.val hlo hhi hlo (by omega) (by omega),
      stg_setSlice f2 lo.val hi.val hi.val hlo hhi hhi (by omega) (by omega), add_mul, one_mul]
  · have hK : H ≤ (H + 1023) / 1024 * 1024 := by omega
    have hmK : m ((H + 1023) / 1024) = H := by simp only [m]; omega
    have lL := length_stg f1 lo.val hi.val lo.val rfl h.symm rfl (le_refl H)
    simp only [p3_binary_dft.lch.schedule.hax_reshaped.grains_loop.body, slice_len_eq, hmK,
      mkSlice_val (show (stg f1 H lo.val hi.val lo.val).length ≤ Usize.max by omega), lL, bind_ok]
    rw [ite_of_neg (fun h' => absurd ((uz_lt (by omega) (by omega)).mp h') (by omega))]

/-! ## The walk over the blocks of a group -/

open p3_binary_dft.lch.mirror p3_binary_dft.butterfly.mirror in
variable [DecidableEq F] in
theorem blockButterfly_full' (inverse : Bool) {len half k : ℕ} (h : (k + 1) * (2 * half) ≤ len)
    (t : F) (y : ℕ → ℕ → F) :
    blockButterfly inverse len half k t y =
      some (packed_butterfly inverse (k * (2 * half)) (k * (2 * half) + half) half t y) := by
  have hb : min (2 * half) (len - k * (2 * half)) = 2 * half := by
    rw [min_eq_left]; rw [add_mul, one_mul] at h; omega
  simp only [blockButterfly, hb, show ¬ 2 * half < half by omega, ↓reduceIte, plain_butterfly,
    show 2 * half - half = half by omega]

theorem bne_uz_zero {k : ℕ} (hk : k ≤ Usize.max) : (uz k != 0#usize) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : uz k ≠ 0#usize := fun e => h (by rw [← uz_val hk, e]; rfl)
    simp [this, h]

/-- The butterfly a block runs, whole or one grain at a time, on two runs of equal length. -/
theorem kernel_eq {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (inverse split : Bool) (H : ℕ) (lo hi : Slice F) (t : F) (hlo : lo.val.length = H)
    (hhi : hi.val.length = H) (hH : H + 1024 ≤ Usize.max) :
    (if split then do
        let i1 ← p3_binary_dft.lch.schedule.BUTTERFLY_GRAIN
        if uz H ≤ i1 then inst.butterfly inverse lo hi t
        else p3_binary_dft.lch.schedule.hax_reshaped.grains inverse inst lo hi t
      else inst.butterfly inverse lo hi t) =
      .ok (mkSlice (bfly1 inverse t lo.val hi.val), mkSlice (bfly2 inverse t lo.val hi.val)) := by
  have hbf : inst.butterfly inverse lo hi t = _ := hb.butterfly inverse lo hi t
  rw [ite_of_pos (by rw [hlo, hhi])] at hbf
  cases split
  · exact hbf
  · simp only [ite_true, grain_eq, bind_ok]
    split_ifs
    · exact hbf
    · exact grains_eq hb inverse lo hi t (by rw [hlo, hhi]) (by omega)

open p3_binary_dft.lch.mirror p3_binary_dft.butterfly.mirror in
variable [DecidableEq F] in
/-- The extracted walk over cnt whole blocks of a group is the transcribed walk, on its rows. -/
theorem walk_blocks_eq {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (tw : Twiddles F) (hbl : tw.bases.length ≤ Usize.max) (hsl : tw.steps.length ≤ Usize.max)
    (inverse split : Bool) {w cnt half : ℕ} (hw : 0 < w) (hh : 0 < half) (s : Slice F)
    (y : ℕ → ℕ → F) (hy : flat w (cnt * (2 * half)) y = s.val) (stage first : Std.Usize)
    (hfirst : (first.val + cnt) * 2 ≤ Usize.max) (hHG : 2 * (half * w) + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks inverse inst s (uz (half * w)) stage first split
        (toTw tw) =
      ofOption ((walkBlocks L tw inverse stage.val first.val (cnt * (2 * half)) half y).map
        fun y => mkSlice (flat w (cnt * (2 * half)) y)) := by
  have hs : s.val.length = cnt * (2 * half) * w := by rw [← hy, length_flat]
  set H := half * w with hH
  set len := cnt * (2 * half) with hlen
  have hsmax := s.property
  have hcount : (len + 2 * half - 1) / (2 * half) = cnt := by
    rw [hlen, show cnt * (2 * half) + 2 * half - 1 = (2 * half - 1) + cnt * (2 * half) by omega,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  unfold p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks walkBlocks
  rw [twiddles_at_eq hb.tower tw hbl stage first (by omega)]
  have hH2 : H * 2 ≤ Usize.max := by omega
  have hlw : len * w ≤ Usize.max := by omega
  -- The block walk, as a loop over the blocks.
  have hloop : ∀ t0 : F, p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks_loop inverse inst s (uz H)
      first split (toTw tw) t0 (uz (H * 2)) (uz (len * w)) 0#usize 0#usize =
      ofOption (((List.range cnt).foldlM (fun (acc : (ℕ → ℕ → F) × F) i => do
        let t ← if i = 0 then pure acc.2 else (do pure (acc.2 + (← tw.step (first.val + i))))
        let y ← blockButterfly inverse len half i t acc.1
        pure (y, t)) (y, t0)).map fun (c : (ℕ → ℕ → F) × F) => mkSlice (flat w len c.1)) := by
    intro t0
    have := loop_foldlM_inv
      (fun st => p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks_loop.body inverse inst (uz H) first
        split (toTw tw) (uz (H * 2)) (uz (len * w)) st.1 st.2.1 st.2.2.1 st.2.2.2)
      (fun (c : (ℕ → ℕ → F) × F) k => (mkSlice (flat w len c.1), c.2, uz (k * (H * 2)), uz k))
      (fun (c : (ℕ → ℕ → F) × F) => mkSlice (flat w len c.1)) cnt
      (fun (acc : (ℕ → ℕ → F) × F) i => do
        let t ← if i = 0 then pure acc.2 else (do pure (acc.2 + (← tw.step (first.val + i))))
        let y ← blockButterfly inverse len half i t acc.1
        pure (y, t)) (fun _ _ => True) (fun k hk c _ => ?_) (fun c _ => ?_)
      (y, t0) trivial
    · rw [show (y, t0).1 = y from rfl, hy, mkSlice_self] at this
      simp only [zero_mul] at this
      unfold p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks_loop
      exact this
    · -- One block.
      have hkc : k + 1 ≤ cnt := hk
      have hHpos : 0 < H := Nat.mul_pos hh hw
      have hlenw : len * w = cnt * (H * 2) := by rw [hlen, hH]; ring
      have hk2 : (k + 1) * (2 * half) ≤ len := by rw [hlen]; exact Nat.mul_le_mul_right _ hkc
      have hko : k * (H * 2) + H * 2 ≤ len * w := by rw [hlenw, ← add_one_mul]; exact Nat.mul_le_mul_right _ hkc
      set g := flat w len c.1 with hg
      have hgl : g.length = len * w := length_flat _ _ _
      have hgv : (mkSlice g).val = g := mkSlice_val (by omega)
      -- The twiddle of the block.
      have ht : ∀ {β : Type} (P : F → RustM β),
          (do let t1 ← (if (uz k != 0#usize) = true then do
                  let i1 ← first + uz k
                  let t2 ← p3_binary_dft.lch.twiddles.Twiddles.step inst.p3_binary_fieldtowerTowerLevelInst (toTw tw) i1
                  inst.p3_binary_fieldtowerTowerLevelInst.p3_fieldfieldFieldInst.AlgebraInst.coreopsarithAddAssignInst.add_assign c.2 t2
                else RustM.ok c.2); P t1) =
            ofOption (if k = 0 then pure c.2 else (do pure (c.2 + (← tw.step (first.val + k))))) >>= P := by
        intro β P
        rw [bne_uz_zero (by omega)]
        by_cases hk0 : k = 0
        · simp [hk0, ofOption]
        · simp only [hk0, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false]
          have e1 : (first + uz k : RustM Std.Usize) = .ok (uz (first.val + k)) := by
            conv_lhs => rw [eq_uz first]
            exact uz_add (by omega)
          rw [e1, bind_ok, twiddles_step_eq tw hsl _ (by rw [uz_val (by omega)]; omega),
            uz_val (by omega)]
          cases tw.step (first.val + k) <;> simp [ofOption, hb.tower.add_assign]
      have hmir : ∀ t : F, blockButterfly inverse len half k t c.1 =
          some (packed_butterfly inverse (k * (2 * half)) (k * (2 * half) + half) half t c.1) :=
        fun t => blockButterfly_full' inverse hk2 t c.1
      simp only [hmir]
      simp only [p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks_loop.body]
      rw [ite_of_pos ((uz_lt (by omega) (by omega)).mpr (by omega)),
        chunk_end_eq (by omega) hlw hH2, min_eq_left hko, bind_ok]
      set o := k * (H * 2) with ho
      set sub := (g.drop o).take (H * 2) with hsub
      have hsubl : sub.length = H * 2 := by simp [hsub, hgl]; omega
      have hidx := index_mut_range_eq (mkSlice g) (a := o) (b := o + H * 2) (by omega) (by rw [hgv]; omega)
      rw [hgv, show o + H * 2 - o = H * 2 by omega, ← hsub] at hidx
      have hsv : (mkSlice sub).val = sub := mkSlice_val (by omega)
      obtain ⟨back2, hsplit, hback2⟩ := split_at_mut_eq (mkSlice sub) (n := H) (by rw [hsv]; omega)
      rw [hsv] at hsplit hback2
      have hlo : (mkSlice (sub.take H)).val = sub.take H := mkSlice_val (by simp; omega)
      have hhi : (mkSlice (sub.drop H)).val = sub.drop H := mkSlice_val (by simp; omega)
      have hker := fun t1 => kernel_eq hb inverse split H (mkSlice (sub.take H)) (mkSlice (sub.drop H)) t1
        (by rw [hlo]; simp; omega) (by rw [hhi]; simp; omega) (by omega)
      have hb2 : ∀ t1 : F, back2 (mkSlice (bfly1 inverse t1 (mkSlice (sub.take H)).val (mkSlice (sub.drop H)).val),
          mkSlice (bfly2 inverse t1 (mkSlice (sub.take H)).val (mkSlice (sub.drop H)).val)) =
          mkSlice (bfly1 inverse t1 (sub.take H) (sub.drop H) ++ bfly2 inverse t1 (sub.take H) (sub.drop H)) := by
        intro t1
        rw [hlo, hhi, hback2 _ _ (by rw [mkSlice_val (by simp [bfly1]; omega)]; simp [bfly1]; omega)
          (by rw [mkSlice_val (by simp [bfly2]; omega)]; simp [bfly2]; omega),
          mkSlice_val (by simp [bfly1]; omega), mkSlice_val (by simp [bfly2]; omega)]
      have hfin : ∀ t1 : F, mkSlice (g.setSlice! o (mkSlice (bfly1 inverse t1 (sub.take H) (sub.drop H) ++
          bfly2 inverse t1 (sub.take H) (sub.drop H))).val) =
          mkSlice (flat w len (packed_butterfly inverse (k * (2 * half)) (k * (2 * half) + half) half t1 c.1)) := by
        intro t1
        rw [mkSlice_val (by simp [bfly1, bfly2]; omega)]
        have := blockList_flat inverse t1 hw hk2 c.1
        rw [show k * (2 * half) * w = o by rw [ho, hH]; ring, ← hH] at this
        rw [← this, ← hg]
        unfold blockList
        rw [show 2 * H = H * 2 by ring, ← hsub]
        rfl
      simp only [hidx, bind_ok, Aeneas.Std.uncurry, hsplit, hker, uz_add_one (show k + 1 ≤ Usize.max by omega),
        hb2, hfin]
      simp only [ht, show o + H * 2 = (k + 1) * (H * 2) by rw [ho]; ring]
      by_cases hk0 : k = 0
      · simp [hk0, ofOption]
      · cases tw.step (first.val + k) <;> simp [hk0, ofOption]
    · have e : c.1 = c.1 := rfl
      simp only [p3_binary_dft.lch.schedule.hax_reshaped.walk_blocks_loop.body,
        show cnt * (H * 2) = len * w by rw [hlen, hH]; ring]
      rw [ite_of_neg (fun h' => absurd ((uz_lt (by omega) (by omega)).mp h') (lt_irrefl _))]
  cases hat : Twiddles.at L tw stage.val first.val with
  | none => simp [ofOption]
  | some t0 =>
    rw [hcount]
    simp only [ofOption, bind_ok, shl_one_eq (uz H) (by rw [uz_val (by omega)]; omega),
      uz_val (show H ≤ Usize.max by omega), slice_len_eq, hs, massert, bne_uz_zero hH2]
    rw [ite_of_pos (by simp only [ne_eq, decide_eq_true_eq]; positivity), bind_ok, hloop t0]
    exact (ofOption_map_bind _ (fun y => mkSlice (flat w len y))).trans rfl

/-! ## Helpers for a stage pass -/

theorem uz_div {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) (h0 : b ≠ 0) :
    (uz a / uz b : RustM Std.Usize) = .ok (uz (a / b)) := by
  obtain ⟨z, hz, hv, -⟩ := UScalar.div_bv_spec (uz a) (y := uz b) (by rw [uz_val hb]; exact h0)
  rw [hz, eq_uz z, hv, uz_val ha, uz_val hb]

theorem max_uz {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) :
    core.Usize.Insts.CoreCmpOrd.max (uz a) (uz b) = .ok (uz (max a b)) := by
  unfold core.Usize.Insts.CoreCmpOrd.max
  congr 1
  by_cases h : b < a
  · rw [ite_of_pos ((uz_lt hb ha).mpr h), max_eq_left (by omega)]
  · rw [ite_of_neg (fun h' => h ((uz_lt hb ha).mp h')), max_eq_right (by omega)]

theorem shl_uz {a j : ℕ} (hj : j < UScalarTy.Usize.numBits) (h : a * 2 ^ j ≤ Usize.max) :
    (uz a <<< uz j : RustM Std.Usize) = .ok (uz (a * 2 ^ j)) := by
  have hjm : j ≤ Usize.max := by
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    have := Nat.lt_two_pow_self (n := UScalarTy.Usize.numBits); omega
  show UScalar.shiftLeft_UScalar (uz a) (uz j) = _
  unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
  rw [uz_val hjm, ite_of_pos hj]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [uz_val h]
  have ha : a ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos j)) h
  show ((uz a).bv <<< j).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change ((uz a).val * 2 ^ j) % _ = _
  rw [uz_val ha, Nat.mod_eq_of_lt]
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
  have := Nat.two_pow_pos UScalarTy.Usize.numBits
  simp only [UScalarTy.Usize_numBits_eq] at *
  omega

open p3_binary_dft.lch.mirror in
theorem flat_slice {w n o len : ℕ} (x : ℕ → ℕ → F) (h : o + len ≤ n) :
    flat w len (slice x o) = ((flat w n x).drop (o * w)).take (len * w) := by
  apply List.ext_getElem?
  intro p
  rw [flat_getElem?, List.getElem?_take, List.getElem?_drop, flat_getElem?]
  by_cases hp : p < len * w
  · have hw : 0 < w := by rcases Nat.eq_zero_or_pos w with h0 | h0 <;> simp_all
    rw [ite_of_pos hp, ite_of_pos hp, ite_of_pos (by nlinarith)]
    obtain ⟨r, c, hc, rfl⟩ : ∃ r c, c < w ∧ p = r * w + c :=
      ⟨p / w, p % w, Nat.mod_lt _ hw, by rw [Nat.mul_comm]; exact (Nat.div_add_mod p w).symm⟩
    rw [div_row hc, mod_row hc, show o * w + (r * w + c) = (o + r) * w + c by ring, div_row hc, mod_row hc]
    rfl
  · rw [ite_of_neg hp, ite_of_neg hp]

open p3_binary_dft.lch.mirror in
theorem flat_writeBack {w n o len : ℕ} (x y : ℕ → ℕ → F) (h : o + len ≤ n) :
    flat w n (writeBack x o len y) = (flat w n x).setSlice! (o * w) (flat w len y) := by
  apply List.ext_getElem?
  intro p
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simp [flat]
  rw [flat_getElem?]
  obtain ⟨r, c, hc, rfl⟩ : ∃ r c, c < w ∧ p = r * w + c :=
    ⟨p / w, p % w, Nat.mod_lt _ hw, by rw [Nat.mul_comm]; exact (Nat.div_add_mod p w).symm⟩
  rw [div_row hc, mod_row hc]
  by_cases h1 : r < o
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ ((row_lt_iff hc).mpr h1), flat_getElem?, div_row hc,
      mod_row hc]
    simp [writeBack, show ¬ o ≤ r by omega]
  by_cases h2 : r < o + len
  · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨(row_le_iff hc).mpr (by omega), by
        rw [length_flat, show r * w + c - o * w = (r - o) * w + c by rw [Nat.sub_mul]; have := Nat.mul_le_mul_right w (show o ≤ r by omega); omega]
        exact (row_lt_iff hc).mpr (by omega), by rw [length_flat]; exact (row_lt_iff hc).mpr (by omega)⟩,
      flat_getElem?, show r * w + c - o * w = (r - o) * w + c by rw [Nat.sub_mul]; have := Nat.mul_le_mul_right w (show o ≤ r by omega); omega,
      div_row hc, mod_row hc]
    simp only [writeBack, show o ≤ r by omega, h2, and_self, ite_true]
    rw [ite_of_pos ((row_lt_iff hc).mpr (by omega)), ite_of_pos ((row_lt_iff hc).mpr (by omega))]
  · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by rw [length_flat]; have := Nat.mul_le_mul_right w (show o + len ≤ r by omega); rw [add_mul] at this; omega),
      flat_getElem?, div_row hc, mod_row hc]
    simp [writeBack, h2]

/-! ## One stage pass -/

open p3_binary_dft.lch.mirror in
variable [DecidableEq F] in
/-- The extracted stage pass over n rows, whole blocks of stage j, is the transcribed pass. -/
theorem stage_pass_eq_mirror {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (tw : Twiddles F) (hbl : tw.bases.length ≤ Usize.max) (hsl : tw.steps.length ≤ Usize.max)
    (inverse : Bool) {w n j : ℕ} (hw : 0 < w) (x : ℕ → ℕ → F) (values : Slice F)
    (hv : flat w n x = values.val) (hdiv : 2 ^ (j + 1) ∣ n) (hn : 0 < n)
    (hbound : n * w + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.stage_pass inverse inst values (uz w) (uz j) (toTw tw) =
      ofOption ((stage_pass L tw inverse w n j x).map fun y => mkSlice (flat w n y)) := by
  have hjn : 2 ^ (j + 1) ≤ n := Nat.le_of_dvd hn hdiv
  have hj2 : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
  have hjb : j < UScalarTy.Usize.numBits := by
    have h1 : 2 ^ (j + 1) ≤ Usize.max := by nlinarith
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    by_contra hc
    have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hnw := values.property
  rw [← hv, length_flat] at hnw
  set H := 2 ^ j * w with hH
  have hHpos : 0 < H := Nat.mul_pos (Nat.two_pow_pos j) hw
  have h2H : 2 * H ≤ n * w := by rw [hH, ← mul_assoc, hj2]; exact Nat.mul_le_mul_right _ hjn
  set per := max (1024 / H) 1 with hper
  have hperpos : 0 < per := by omega
  set TR := per * (2 * 2 ^ j) with hTR
  set TL := per * (H * 2) with hTL
  have hTLR : TL = TR * w := by rw [hTL, hTR, hH]; ring
  have hTLb : TL ≤ Usize.max := by
    -- A task is at most the grain, or one block when a block exceeds the grain.
    by_cases hg : H ≤ 1024
    · have : per * H ≤ 1024 := by
        rw [hper, max_eq_left (Nat.div_pos hg hHpos)]
        exact Nat.div_mul_le_self 1024 H
      have hbig : 2 ^ 32 - 1 ≤ Usize.max := by
        rcases Usize.bounds_eq with e | e <;> rw [e] <;> simp [U32.max_def, U64.max_def, U32.numBits, U64.numBits]
      rw [hTL, show per * (H * 2) = per * H * 2 by ring]
      norm_num at hbig; omega
    · have : per = 1 := by rw [hper]; simp [Nat.div_eq_of_lt (show 1024 < H by omega)]
      rw [hTL, this]; omega
  set K := (n + TR - 1) / TR with hK
  have hTRpos : 0 < TR := by positivity
  have hKTR : n ≤ K * TR := by
    rw [hK, mul_comm]; have := Nat.div_add_mod (n + TR - 1) TR; have := Nat.mod_lt (n + TR - 1) hTRpos
    omega
  have hKlt : ∀ k < K, k * TR < n := fun k hk => by
    by_contra hc; push Not at hc
    have : K < k + 1 := by
      rw [hK]; apply (Nat.div_lt_iff_lt_mul hTRpos).mpr; rw [add_mul, one_mul]; omega
    omega
  have hdivTR : 2 ^ (j + 1) ∣ TR := ⟨per, by rw [hTR, hj2, mul_comm]⟩
  -- The pass, as a loop over the tasks.
  have hloop := loop_foldlM_inv
    (fun st => p3_binary_dft.lch.schedule.hax_reshaped.stage_pass_loop.body inverse inst (uz j) (toTw tw)
      (uz H) (uz per) (uz TL) (uz (n * w)) st.1 st.2.1 st.2.2)
    (fun (x : ℕ → ℕ → F) k => (mkSlice (flat w n x), uz (min (k * TL) (n * w)), uz k))
    (fun x => mkSlice (flat w n x)) K
    (fun x task => do
      let y ← walkBlocks L tw inverse j (task * per) (min TR (n - task * TR)) (2 ^ j) (slice x (task * TR))
      pure (writeBack x (task * TR) (min TR (n - task * TR)) y))
    (fun _ _ => True) (fun k hk c _ => ?_) (fun c _ => ?_) x trivial
  · simp only [zero_mul, Nat.zero_min] at hloop
    rw [hv, mkSlice_self] at hloop
    have hl : p3_binary_dft.lch.schedule.hax_reshaped.stage_pass_loop inverse inst values (uz j) (toTw tw)
        (uz H) (uz per) (uz TL) (uz (n * w)) 0#usize 0#usize = _ := hloop
    have hHm : H ≤ Usize.max := by omega
    have hdl : 1024 / H ≤ 1024 := Nat.div_le_self _ _
    have hwn : w ≤ n * w := Nat.le_mul_of_pos_left w hn
    have hperle : per ≤ 1024 := by rw [hper]; omega
    unfold p3_binary_dft.lch.schedule.stage_pass p3_binary_dft.lch.schedule.hax_reshaped.stage_pass stage_pass
    rw [uz_one, shl_uz hjb (by rw [one_mul]; nlinarith), bind_ok, one_mul,
      uz_mul (by rw [← hH]; omega) (by nlinarith) (by omega), bind_ok, ← hH, grain_eq, bind_ok,
      uz_div (by omega) hHm (by omega), bind_ok, max_uz (by omega) (by omega), bind_ok, ← hper,
      shl_one_eq (uz H) (by rw [uz_val hHm]; omega), bind_ok, uz_val hHm,
      uz_mul (by rw [← hTL]; exact hTLb) (by omega) (by omega), bind_ok, ← hTL]
    simp only [massert, bne_uz_zero hTLb]
    rw [ite_of_pos (by simp only [ne_eq, decide_eq_true_eq]; positivity), bind_ok, slice_len_eq, bind_ok, ← hv,
      length_flat, hl, ite_of_neg (by positivity)]
    simp only [BUTTERFLY_GRAIN, ← hper, ← hTR, ← hK]
  · -- One task.
    set o := k * TR with ho
    set lk := min TR (n - o) with hlk
    have hon : o < n := hKlt k hk
    have holk : o + lk ≤ n := by omega
    have hlkpos : 0 < lk := by omega
    have hdo : 2 ^ (j + 1) ∣ o := Dvd.dvd.mul_left hdivTR k
    have hdlk : 2 ^ (j + 1) ∣ lk := by
      rw [hlk]; rcases le_total TR (n - o) with h | h
      · rw [min_eq_left h]; exact hdivTR
      · rw [min_eq_right h]; exact Nat.dvd_sub hdiv hdo
    obtain ⟨cnt, hcnt⟩ := hdlk
    have hlkc : lk = cnt * (2 * 2 ^ j) := by rw [hcnt, hj2, mul_comm]
    have hkTL : k * TL = o * w := by rw [hTLR, ho]; ring
    have hmin1 : min (k * TL) (n * w) = o * w := by
      rw [hkTL, min_eq_left (Nat.mul_le_mul_right _ hon.le)]
    have hmin2 : min (o * w + TL) (n * w) = (o + lk) * w := by
      rw [hTLR, ← add_mul, hlk]
      rcases le_total TR (n - o) with h | h
      · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right _ (by omega))]
      · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_right _ (by omega)), show o + (n - o) = n by omega]
    have hmin3 : min ((k + 1) * TL) (n * w) = (o + lk) * w := by rw [add_mul, one_mul, hkTL, hmin2]
    have hgl : (flat w n c).length = n * w := length_flat _ _ _
    have hgv : (mkSlice (flat w n c)).val = flat w n c := mkSlice_val (by omega)
    have holw : (o + lk) * w ≤ n * w := Nat.mul_le_mul_right _ holk
    have hidx := index_mut_range_eq (mkSlice (flat w n c)) (a := o * w) (b := (o + lk) * w)
      (Nat.mul_le_mul_right _ (by omega)) (by rw [hgv, hgl]; exact holw)
    rw [hgv, show (o + lk) * w - o * w = lk * w by rw [add_mul]; omega, ← flat_slice c holk] at hidx
    have hsub : (mkSlice (flat w lk (slice c o))).val = flat w lk (slice c o) := mkSlice_val (by
      rw [length_flat]; have := Nat.mul_le_mul_right w (show lk ≤ n by omega); omega)
    have hkper : k * per * 2 ^ (j + 1) = o := by rw [ho, hTR, hj2]; ring
    have hfirst : (k * per + cnt) * 2 ≤ Usize.max := by
      have h1 : (k * per + cnt) * 2 ^ (j + 1) ≤ n := by rw [add_mul, hkper, mul_comm cnt, ← hcnt]; exact holk
      have h2 : (k * per + cnt) * 2 ≤ (k * per + cnt) * 2 ^ (j + 1) :=
        Nat.mul_le_mul_left _ (by have := Nat.one_lt_two_pow_iff.mpr (Nat.succ_ne_zero j); omega)
      have h3 : n ≤ n * w := Nat.le_mul_of_pos_right n hw
      calc (k * per + cnt) * 2 ≤ (k * per + cnt) * 2 ^ (j + 1) := h2
        _ ≤ n := h1
        _ ≤ n * w := h3
        _ ≤ Usize.max := by omega
    have hwalk := walk_blocks_eq hb tw hbl hsl inverse true hw (Nat.two_pow_pos j)
      (mkSlice (flat w lk (slice c o))) (slice c o) (by rw [hsub, hlkc]) (uz j) (uz (k * per))
      (by rw [uz_val (by omega)]; exact hfirst) (by omega)
    have hkp : k * per ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ two_pos) (le_trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ cnt)) hfirst)
    have hkm : k ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right k hperpos) hkp
    have hk1 : k + 1 ≤ Usize.max := by
      have : k * TR + 1 ≤ n := hon
      have : k ≤ k * TR := Nat.le_mul_of_pos_right k hTRpos
      have : n ≤ n * w := Nat.le_mul_of_pos_right n hw
      omega
    have hperm : per ≤ Usize.max := by
      have : 1024 / H ≤ 1024 := Nat.div_le_self _ _
      have : per ≤ 1024 := by rw [hper]; omega
      omega
    have hjm : j ≤ Usize.max := by
      have := Nat.lt_two_pow_self (n := j + 1); have : n ≤ n * w := Nat.le_mul_of_pos_right n hw; omega
    simp only [uz_val hkp, uz_val hjm, ← hlkc, ← hH] at hwalk
    simp only [p3_binary_dft.lch.schedule.hax_reshaped.stage_pass_loop.body, hmin1]
    rw [ite_of_pos ((uz_lt (by omega) (by omega)).mpr (Nat.mul_lt_mul_of_pos_right hon hw)),
      chunk_end_eq (Nat.mul_le_mul_right _ hon.le) (by omega) hTLb, hmin2, bind_ok, hidx, bind_ok]
    simp only [Aeneas.Std.uncurry]
    rw [uz_mul hkp hkm hperm, bind_ok, hwalk, uz_add_one hk1]
    cases walkBlocks L tw inverse j (k * per) lk (2 ^ j) (slice c o) with
    | none => simp [ofOption]
    | some y =>
      simp only [ofOption, bind_ok, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.map]
      refine ⟨trivial, ?_⟩
      rw [mkSlice_val (by rw [length_flat]; have := Nat.mul_le_mul_right w (show lk ≤ n by omega); omega),
        ← flat_writeBack c y holk, hmin3]
  · simp only [p3_binary_dft.lch.schedule.hax_reshaped.stage_pass_loop.body]
    rw [min_eq_right (by rw [hTLR, ← mul_assoc]; exact Nat.mul_le_mul_right _ hKTR),
      ite_of_neg (lt_irrefl _)]

end Plonky3Lean.Proofs.BinaryDft
