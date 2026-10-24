module

public import P3Sumcheck
public import Plonky3Lean.Lib.Slice

@[expose] public section

/-!
# The extracted round arithmetic

hax extracts the round arithmetic of the quadratic verifier, generic over the field trait.

Its theorems assume one thing of the field instance: its one, sum, difference and product are the field's.

Under that assumption each extracted function returns what its transcription computes.

So every theorem about the transcriptions holds for the shipped code.
-/

open CoreModels Aeneas Aeneas.Std

namespace Plonky3Lean.Proofs.Sumcheck

variable {F : Type} [Field F]

/-- The field members the round arithmetic calls compute one, the sum, the difference and the product. -/
structure FieldComputes (inst : p3_field.field.Field F) : Prop where
  one : inst.AlgebraInst.PrimeCharacteristicRingInst.ONE = .ok 1
  add : ∀ a b : F, inst.AlgebraInst.coreopsarithAddInst.add a b = .ok (a + b)
  sub : ∀ a b : F, inst.AlgebraInst.coreopsarithSubInst.sub a b = .ok (a - b)
  mul : ∀ a b : F, inst.AlgebraInst.coreopsarithMulInst.mul a b = .ok (a * b)

variable {inst : p3_field.field.Field F} (h : FieldComputes inst)
include h

theorem lagrange_weights_01inf_eq (r : F) :
    p3_sumcheck.lagrange.lagrange_weights_01inf inst r =
      .ok (Std.Array.make 3#usize [1 - r, r, r * (r - 1)]) := by
  simp [p3_sumcheck.lagrange.lagrange_weights_01inf, h.one, h.sub, h.mul]

theorem extrapolate_01inf_eq (e0 e1 e_inf r : F) :
    p3_sumcheck.lagrange.extrapolate_01inf inst e0 e1 e_inf r =
      .ok (p3_sumcheck.lagrange.mirror.extrapolate_01inf e0 e1 e_inf r) := by
  simp [p3_sumcheck.lagrange.extrapolate_01inf, lagrange_weights_01inf_eq h, h.add, h.mul,
    p3_sumcheck.lagrange.mirror.extrapolate_01inf, p3_sumcheck.lagrange.mirror.lagrange_weights_01inf,
    Plonky3Lean.Lib.index_make]

/-- The basis tag of the transcriptions. -/
def toMirror : p3_sumcheck.strategy.Basis → p3_sumcheck.mirror.Basis
  | .Evaluation => .Evaluation
  | .Projective => .Projective

theorem reduce_claim_eq (b : p3_sumcheck.strategy.Basis) (c_a c_inf r c : F) :
    p3_sumcheck.strategy.Basis.reduce_claim inst b c_a c_inf r c =
      .ok ((toMirror b).reduce_claim c_a c_inf r c) := by
  cases b <;> simp [p3_sumcheck.strategy.Basis.reduce_claim, toMirror, h.sub, extrapolate_01inf_eq h,
    p3_sumcheck.mirror.Basis.reduce_claim]

omit h

/-! ## The tensor product of the weights -/

/-- The entries of a vector. -/
def vlist {T : Type} (v : CoreModels.alloc.vec.Vec T) : List T := Slice.val v

/-- The vector of a list that fits. -/
def mkVec {T : Type} (l : List T) (hl : l.length ≤ Usize.max) : CoreModels.alloc.vec.Vec T := Slice.from l hl

/-- The entries an iterator has left. -/
def ilist {T : Type} (it : CoreModels.core.slice.iter.Iter T) : List T := Slice.val it

@[simp] theorem vlist_mkVec {T : Type} (l : List T) (hl : l.length ≤ Usize.max) : vlist (mkVec l hl) = l := by
  simp [vlist, mkVec]

theorem vlist_length {T : Type} (v : CoreModels.alloc.vec.Vec T) : (vlist v).length ≤ Usize.max :=
  Slice.property v

/-- Appending a list to a vector, which panics past the maximal length. -/
def pushAll {T : Type} (v : CoreModels.alloc.vec.Vec T) (l : List T) : RustM (CoreModels.alloc.vec.Vec T) :=
  if hl : (vlist v ++ l).length ≤ Usize.max then .ok (mkVec (vlist v ++ l) hl) else .fail .panic

theorem push_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) (x : T) :
    CoreModels.alloc.vec.Vec.push v x = pushAll v [x] :=
  (Std.bind_pure _).trans rfl

theorem pushAll_nil {T : Type} (v : CoreModels.alloc.vec.Vec T) : pushAll v [] = .ok v := by
  simp only [pushAll, List.append_nil]
  rw [dite_eq_left (vlist_length v)]
  exact congrArg _ (Slice.val_from _ _)

theorem pushAll_bind {T : Type} (v : CoreModels.alloc.vec.Vec T) (l₁ l₂ : List T) :
    (pushAll v l₁ >>= fun v' => pushAll v' l₂) = pushAll v (l₁ ++ l₂) := by
  unfold pushAll
  by_cases h₁ : (vlist v ++ l₁).length ≤ Usize.max
  · rw [dite_eq_left h₁, bind_tc_ok]
    simp [List.append_assoc]
  · rw [dite_eq_right h₁, bind_tc_fail, dite_eq_right (by simp at h₁ ⊢; omega)]

theorem iter_next_cons {T : Type} (it : CoreModels.core.slice.iter.Iter T) {x : T} {xs : List T}
    (hit : ilist it = x :: xs) :
    ∃ it', ilist it' = xs ∧
      CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next it = .ok (.Some x, it') := by
  unfold ilist at hit
  unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    CoreModels.rust_primitives.sequence.seq_len CoreModels.rust_primitives.sequence.seq_remove
  have hne : Slice.len it ≠ 0#usize := fun h0 => by simpa [hit] using congrArg UScalar.val h0
  simp [hne, hit]
  exact ⟨_, by simp [ilist], rfl⟩

theorem iter_next_nil {T : Type} (it : CoreModels.core.slice.iter.Iter T) (hit : ilist it = []) :
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next it = .ok (.None, it) := by
  unfold ilist at hit
  unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    CoreModels.rust_primitives.sequence.seq_len
  simp [UScalar.eq_of_val_eq (by simp [hit] : (Slice.len it).val = (0#usize).val)]

open p3_sumcheck.lagrange in
include h in
/-- The innermost loop appends each remaining entry of the table, times the weight. -/
theorem multi_inner (li : F) : ∀ (ws : List F) (it : CoreModels.core.slice.iter.Iter F),
    ilist it = ws → ∀ next : CoreModels.alloc.vec.Vec F,
    lagrange_weights_01inf_multi_loop0_loop0_loop0 inst it next li = pushAll next (ws.map (· * li))
  | [], it, hit, next => by
    unfold lagrange_weights_01inf_multi_loop0_loop0_loop0
    rw [loop]
    simp [lagrange_weights_01inf_multi_loop0_loop0_loop0.body, iter_next_nil it hit, pushAll_nil]
  | w :: ws, it, hit, next => by
    obtain ⟨it', hit', hnext⟩ := iter_next_cons it hit
    have ih := multi_inner li ws it' hit'
    have hb : lagrange_weights_01inf_multi_loop0_loop0_loop0.body inst li it next =
        (pushAll next [w * li] >>= fun n => .ok (.cont (it', n))) := by
      simp [lagrange_weights_01inf_multi_loop0_loop0_loop0.body, hnext, h.mul, push_eq]
      rfl
    have hl : List.map (· * li) (w :: ws) = [w * li] ++ List.map (· * li) ws := rfl
    unfold lagrange_weights_01inf_multi_loop0_loop0_loop0 at ih ⊢
    rw [loop]
    dsimp only
    rw [hb, hl, ← pushAll_bind]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    exact congrArg _ (funext fun n => ih n)

theorem into_iter_vec {T : Type} (v : CoreModels.alloc.vec.Vec T) :
    ∃ it, ilist it = vlist v ∧
      CoreModels.alloc.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter v = .ok it :=
  ⟨v, rfl, (bind_tc_ok _ _).trans (bind_tc_ok _ _)⟩

theorem into_iter_slice {T : Type} (s : Slice T) :
    ∃ it, ilist it = s.val ∧
      CoreModels.core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter s = .ok it :=
  ⟨s, rfl, by
    simp [CoreModels.core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
      CoreModels.core.slice.Slice.iter, CoreModels.rust_primitives.sequence.seq_from_slice]⟩

theorem into_iter_array {T : Type} {N : Std.Usize} (l : List T) (hl : l.length = N.val) :
    ∃ it, ilist it = l ∧
      core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter (Std.Array.make N l hl) =
        .ok it :=
  ⟨Std.Array.to_slice (Std.Array.make N l hl), by simp [ilist], (bind_tc_ok _ _).trans (bind_tc_ok _ _)⟩

open p3_sumcheck.lagrange in
include h in
/-- The middle loop appends the table times each remaining weight. -/
theorem multi_middle (cur : CoreModels.alloc.vec.Vec F) : ∀ (us : List F) (it : CoreModels.core.slice.iter.Iter F),
    ilist it = us → ∀ next : CoreModels.alloc.vec.Vec F,
    lagrange_weights_01inf_multi_loop0_loop0 inst it cur next =
      pushAll next (us.flatMap fun li => (vlist cur).map (· * li))
  | [], it, hit, next => by
    unfold lagrange_weights_01inf_multi_loop0_loop0
    rw [loop]
    simp [lagrange_weights_01inf_multi_loop0_loop0.body, iter_next_nil it hit, pushAll_nil]
  | li :: us, it, hit, next => by
    obtain ⟨it', hit', hnext⟩ := iter_next_cons it hit
    obtain ⟨ic, hic, hinto⟩ := into_iter_vec cur
    have ih := multi_middle cur us it' hit'
    have hb : lagrange_weights_01inf_multi_loop0_loop0.body inst cur it next =
        (pushAll next ((vlist cur).map (· * li)) >>= fun n => .ok (.cont (it', n))) := by
      simp [lagrange_weights_01inf_multi_loop0_loop0.body, hnext, hinto, multi_inner h li _ ic hic]
      rfl
    unfold lagrange_weights_01inf_multi_loop0_loop0 at ih ⊢
    rw [loop]
    dsimp only
    rw [hb, List.flatMap_cons, ← pushAll_bind]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    exact congrArg _ (funext fun n => ih n)

/-- One round of the tensor product: the table times each of the three weights at r. -/
def step (cur : List F) (r : F) : List F := [1 - r, r, r * (r - 1)].flatMap fun li => cur.map (· * li)

theorem step_length (cur : List F) (r : F) : (step cur r).length = 3 * cur.length := by
  simp [step]; ring

theorem foldl_step_length : ∀ (rs : List F) (cur : List F),
    (rs.foldl step cur).length = 3 ^ rs.length * cur.length
  | [], cur => by simp
  | r :: rs, cur => by rw [List.foldl_cons, foldl_step_length, step_length]; simp [pow_succ]; ring

/-- The weight of node d at r, for the nodes 0, 1 and infinity. -/
def wt (r : F) : ℕ → F
  | 0 => 1 - r
  | 1 => r
  | _ => r * (r - 1)

theorem step_getD (cur : List F) (r : F) {p d : ℕ} (hp : p < cur.length) (hd : d < 3) :
    (step cur r).getD (p + cur.length * d) 0 = cur.getD p 0 * wt r d := by
  simp only [step, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_eq_getElem?_getD]
  obtain _ | _ | _ | d := d
  · simp [List.getElem?_append_left, hp, wt]
  · rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
    simp [hp, wt]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show p + cur.length * 2 - cur.length - cur.length = p by omega, hp, wt]
  · omega

/-- Entry p + |cur| q of the rounds is entry p of the table times the weights at the base-3 digits of q.

Digit k of q picks the node of point k. -/
theorem foldl_step_getD : ∀ (rs cur : List F) {p q : ℕ}, p < cur.length → q < 3 ^ rs.length →
    (rs.foldl step cur).getD (p + cur.length * q) 0 =
      cur.getD p 0 * ∏ k ∈ Finset.range rs.length, wt (rs.getD k 0) (q / 3 ^ k % 3)
  | [], cur, p, q, hp, hq => by simp_all
  | r :: rs, cur, p, q, hp, hq => by
    have hd : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hq' : q / 3 < 3 ^ rs.length := by
      rw [List.length_cons, pow_succ] at hq; omega
    have hidx : p + cur.length * q = (p + cur.length * (q % 3)) + (step cur r).length * (q / 3) := by
      rw [step_length]; nth_rw 1 [← Nat.mod_add_div q 3]; ring
    have hp' : p + cur.length * (q % 3) < (step cur r).length := by
      rw [step_length]; nlinarith
    have hk : ∀ k, q / 3 ^ (k + 1) % 3 = q / 3 / 3 ^ k % 3 := fun k => by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [List.foldl_cons, hidx, foldl_step_getD rs _ hp' hq', step_getD cur r hp hd,
      List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, Nat.div_one, hk]
    ring

theorem mirror_multi_eq (rs : List F) :
    p3_sumcheck.lagrange.mirror.lagrange_weights_01inf_multi rs = rs.foldl step [1] := rfl

theorem mirror_multi_length (rs : List F) :
    (p3_sumcheck.lagrange.mirror.lagrange_weights_01inf_multi rs).length = 3 ^ rs.length := by
  simp [mirror_multi_eq, foldl_step_length]

theorem mirror_multi_getD (rs : List F) {j : ℕ} (hj : j < 3 ^ rs.length) :
    (p3_sumcheck.lagrange.mirror.lagrange_weights_01inf_multi rs).getD j 0 =
      ∏ k ∈ Finset.range rs.length, wt (rs.getD k 0) (j / 3 ^ k % 3) := by
  simpa [mirror_multi_eq] using foldl_step_getD rs [1] (p := 0) (by simp) hj

/-- The empty vector. -/
def emptyVec {T : Type} : CoreModels.alloc.vec.Vec T := mkVec [] (by simp)

theorem clear_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) : CoreModels.alloc.vec.Vec.clear v = .ok emptyVec := by
  simp only [CoreModels.alloc.vec.Vec.clear, CoreModels.rust_primitives.sequence.seq_empty]
  exact (bind_tc_ok _ _).trans rfl

theorem vlist_emptyVec {T : Type} : vlist (emptyVec : CoreModels.alloc.vec.Vec T) = [] := by simp [emptyVec]

theorem pushAll_empty {T : Type} (v : CoreModels.alloc.vec.Vec T) : pushAll emptyVec (vlist v) = .ok v := by
  unfold pushAll
  rw [dite_eq_left (by simpa [vlist_emptyVec] using vlist_length v)]
  exact congrArg _ (by simp only [vlist_emptyVec, List.nil_append]; exact Slice.val_from _ _)

theorem pushAll_foldl (rs : List F) (L : List F) :
    (pushAll emptyVec L >>= fun c => pushAll emptyVec (rs.foldl step (vlist c))) =
      pushAll emptyVec (rs.foldl step L) := by
  unfold pushAll
  have he := vlist_emptyVec (T := F)
  by_cases hL : (vlist (emptyVec : CoreModels.alloc.vec.Vec F) ++ L).length ≤ Usize.max
  · rw [dite_eq_left hL, bind_tc_ok]
    simp [he]
  · rw [dite_eq_right hL, bind_tc_fail, dite_eq_right]
    simp only [he, List.nil_append, foldl_step_length] at hL ⊢
    have : L.length ≤ 3 ^ rs.length * L.length := Nat.le_mul_of_pos_left _ (by positivity)
    omega

open p3_sumcheck.lagrange in
include h in
/-- The outer loop replaces the table by its round for each remaining point. -/
theorem multi_outer : ∀ (rs : List F) (it : CoreModels.core.slice.iter.Iter F),
    ilist it = rs → ∀ cur next : CoreModels.alloc.vec.Vec F,
    lagrange_weights_01inf_multi_loop0 inst it cur next = pushAll emptyVec (rs.foldl step (vlist cur))
  | [], it, hit, cur, next => by
    unfold lagrange_weights_01inf_multi_loop0
    rw [loop]
    simp [lagrange_weights_01inf_multi_loop0.body, iter_next_nil it hit, pushAll_empty]
  | r :: rs, it, hit, cur, next => by
    obtain ⟨it', hit', hnext⟩ := iter_next_cons it hit
    obtain ⟨iu, hiu, hinto⟩ := into_iter_array (N := 3#usize) [1 - r, r, r * (r - 1)] (by simp)
    have ih := multi_outer rs it' hit'
    have hb : lagrange_weights_01inf_multi_loop0.body inst it cur next =
        (pushAll emptyVec (step (vlist cur) r) >>= fun n => .ok (.cont (it', n, cur))) := by
      simp [lagrange_weights_01inf_multi_loop0.body, hnext, lagrange_weights_01inf_eq h, clear_eq, hinto,
        multi_middle h cur _ iu hiu, step, CoreModels.core.mem.swap, Aeneas.Std.core.mem.swap]
      rfl
    unfold lagrange_weights_01inf_multi_loop0 at ih ⊢
    rw [loop]
    dsimp only
    rw [hb, List.foldl_cons, ← pushAll_foldl]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    exact congrArg _ (funext fun n => ih n cur)

theorem usize_lt_iff (x : ℕ) : x < 2 ^ UScalarTy.Usize.numBits ↔ x ≤ Usize.max := by
  have : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
  simp only [Usize.max_def, Usize.numBits_def]
  omega

theorem tryMk_usize_of_le {x : ℕ} (hx : x ≤ Usize.max) : ∃ y, UScalar.tryMk .Usize x = .ok y := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt]
  rw [dite_eq_left (by simpa using (usize_lt_iff x).mpr hx)]
  exact ⟨_, rfl⟩

theorem tryMk_usize_of_gt {x : ℕ} (hx : Usize.max < x) : UScalar.tryMk .Usize x = .fail .panic := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt]
  have := usize_lt_iff x
  rw [dite_eq_right (by simp at this ⊢; omega)]
  rfl

theorem with_capacity_eq {T : Type} (c : Std.Usize) :
    CoreModels.alloc.vec.Vec.with_capacity T c = .ok emptyVec := by
  simp only [CoreModels.alloc.vec.Vec.with_capacity, CoreModels.alloc.vec.Vec.new,
    CoreModels.rust_primitives.sequence.seq_empty]
  exact (bind_tc_ok _ _).trans rfl

open p3_sumcheck.lagrange in
include h in
/-- The tensor product of the weights at every point, as the transcription computes it.

It panics exactly when its 3^n entries exceed the maximal length of a vector. -/
theorem lagrange_weights_01inf_multi_eq (rs : Slice F) :
    lagrange_weights_01inf_multi inst rs = pushAll emptyVec (mirror.lagrange_weights_01inf_multi rs.val) := by
  obtain ⟨it, hit, hinto⟩ := into_iter_slice rs
  unfold lagrange_weights_01inf_multi
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, lift,
    CoreModels.core.num.Usize.pow, CoreModels.rust_primitives.arithmetic.pow_usize, bind_ok]
  have hc : (UScalar.cast UScalarTy.U32 rs.len).val ≤ rs.val.length := by
    simpa using Nat.mod_le _ _
  by_cases hp : (3#usize).val ^ (UScalar.cast UScalarTy.U32 rs.len).val ≤ Usize.max
  · obtain ⟨y, hy⟩ := tryMk_usize_of_le hp
    simp only [hy, with_capacity_eq, h.one, push_eq, hinto, bind_ok, multi_outer h _ it hit, mirror_multi_eq]
    exact pushAll_foldl rs.val [1]
  · rw [tryMk_usize_of_gt (by omega), bind_fail]
    unfold pushAll
    rw [dite_eq_right]
    simp only [vlist_emptyVec, List.nil_append, mirror_multi_eq, foldl_step_length, List.length_singleton, mul_one]
    have h3 := Nat.pow_le_pow_right (by norm_num : 0 < 3) hc
    rw [show (3#usize).val = 3 from rfl] at hp
    omega

end Plonky3Lean.Proofs.Sumcheck
