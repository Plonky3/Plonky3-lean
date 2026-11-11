module

public import Plonky3Lean.Proofs.MerkleTree.BinaryPlan
public import Plonky3Lean.Proofs.MerkleTree.Accept

@[expose] public section

/-!
# The extracted verifier runs the binary plan

Take arity 2, and dimensions whose heights are all powers of two.

The tallest height is then 2^n.

Every value the verifier reads from the dimensions is the binary tree's:

- the schedule is n binary steps
- the proof walks n - min(c, n) of them, for a cap height c
- the matrix order groups the matrices by height, tallest first
- the leaf group is the tallest matrices
- the plan injects the matrices of height 2^e after the fold to width 2^e.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- The log heights of the dimensions. -/
def logsOf (dims : Slice p3_matrix.Dimensions) : List ℕ :=
  dims.val.map fun d => Nat.log 2 d.height.val

/-- Every height is a power of two. -/
def PowHeights (dims : Slice p3_matrix.Dimensions) : Prop :=
  ∀ d ∈ dims.val, 2 ^ Nat.log 2 d.height.val = d.height.val

theorem logsOf_length (dims : Slice p3_matrix.Dimensions) :
    (logsOf dims).length = dims.val.length := by
  simp [logsOf]

theorem heightOf_pow {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims) :
    ∀ m < (logsOf dims).length, heightOf dims m = 2 ^ (logsOf dims).getD m 0 := by
  intro m hm
  rw [logsOf_length] at hm
  simp only [heightOf, logsOf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hm, Option.map_some, Option.getD_some]
  exact (hpow _ (List.getElem_mem hm)).symm

theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | x :: l, a => by
    rw [List.foldl_cons]
    rcases foldl_max_mem l (max a x) with h | h
    · rw [h]
      rcases max_choice a x with h' | h' <;> rw [h'] <;> simp
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem le_foldl_max_of : ∀ (l : List ℕ) (a x : ℕ), x ∈ l ∨ x ≤ a → x ≤ l.foldl max a
  | [], _, _, hx => by simpa using hx
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    refine le_foldl_max_of l _ x ?_
    rcases hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl hx
    · exact Or.inr (le_max_of_le_left hx)

/-- On power-of-two heights, a positive tallest height is 2^n, and every log height is at most n. -/
theorem maxHeight_pow {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims)
    (hpos : 0 < maxHeight dims) :
    maxHeight dims = 2 ^ Nat.log 2 (maxHeight dims) ∧
      ∀ m < (logsOf dims).length, (logsOf dims).getD m 0 ≤ Nat.log 2 (maxHeight dims) := by
  refine ⟨?_, fun m hm => ?_⟩
  · rcases foldl_max_mem (dims.val.map fun d => d.height.val) 0 with h | h
    · exact absurd h (by unfold maxHeight at hpos; omega)
    · obtain ⟨d, hd, hd'⟩ := List.mem_map.1 h
      rw [maxHeight, ← hd', hpow d hd]
  · rw [logsOf_length] at hm
    simp only [logsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm,
      Option.map_some, Option.getD_some]
    exact Nat.log_mono_right (le_foldl_max_of _ _ _ (Or.inl (List.mem_map_of_mem (List.getElem_mem hm))))

/-- On power-of-two heights, the matrix order is the binary tree's. -/
theorem tallest_first_binary {dims : Slice p3_matrix.Dimensions} {order : alloc.vec.Vec Std.Usize}
    (hpow : PowHeights dims) (hpos : 0 < maxHeight dims)
    (h : mmcs.hax_reshaped.tallest_first dims = RustM.ok order) :
    ordL order = tallOrder (logsOf dims) (Nat.log 2 (maxHeight dims)) := by
  rw [tallest_first_eq h, ← logsOf_length,
    sortTallest_eq _ _ _ (heightOf_pow hpow) (maxHeight_pow hpow hpos).2 _ le_rfl]
  rfl

/-- On power-of-two heights, the leaf group is the block of the tallest matrices. -/
theorem leafEnd_binary (lh : List ℕ) (height : ℕ → ℕ) (n : ℕ)
    (hh : ∀ m < lh.length, height m = 2 ^ lh.getD m 0) :
    leafEnd height (tallOrder lh n) (2 ^ n) 0 = blockEnd lh n n := by
  have hsplit : tallOrder lh n = [] ++ atLog lh n ++ (List.range n).reverse.flatMap (atLog lh) := by
    rw [tallOrder, logsDown_eq_cons n]; simp
  have hnpt : ∀ e, ∀ y ∈ atLog lh e, npt (height y) = 2 ^ e := fun e y hy => by
    obtain ⟨h1, h2⟩ := mem_atLog.1 hy; rw [hh y h1, h2, npt_two_pow]
  rw [leafEnd_eq_advance _ _ _ _ 0 rfl, hsplit]
  refine (advance_block _ _ _ [] _ (hnpt n) ?_).trans (by simp [blockEnd, blockStart])
  · intro y hy
    obtain ⟨e, he, hy⟩ := List.mem_flatMap.1 (List.mem_of_mem_head? hy)
    simp only [List.mem_reverse, List.mem_range] at he
    rw [hnpt e y hy]
    exact (Nat.pow_lt_pow_right (by omega) he).ne

/-- With arity 2 and power-of-two heights, everything the verifier reads from the dimensions is the binary tree's.

The tallest height is 2^n, and c is the cap height.

- The tallest height is 2^n, and so is the padded leaf width.
- The schedule is n binary steps.
- The proof walks n - min(c, n) of them.
- The matrix order is the order of the binary tree.
- The leaf group ends where the tallest matrices end. -/
theorem layout_binary {cap pl val : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched order : alloc.vec.Vec Std.Usize} {curr lnpt pos : Std.Usize}
    (hpow : PowHeights dims)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels 2#usize cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val 2#usize = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos) :
    val.val = 2 ^ Nat.log 2 val.val ∧ curr.val = 2 ^ Nat.log 2 val.val ∧
      sched.val.map (fun s => s.val) = List.replicate (Nat.log 2 val.val) 2 ∧
      pl.val = Nat.log 2 val.val - min cap.val (Nat.log 2 val.val) ∧
      ordL order = tallOrder (logsOf dims) (Nat.log 2 val.val) ∧
      pos.val = blockEnd (logsOf dims) (Nat.log 2 val.val) (Nat.log 2 val.val) := by
  obtain ⟨hvm, hv0⟩ := validate_ok_val hval
  have hmax := maxHeight_pow hpow (hvm ▸ hv0)
  rw [← hvm] at hmax
  set n := Nat.log 2 val.val
  have hcv : curr.val = 2 ^ n := by rw [padded_len_ok hcurr, hmax.1]; exact padded_two_pow n
  have hord : ordL order = tallOrder (logsOf dims) n := by
    rw [tallest_first_binary hpow (hvm ▸ hv0) horder, ← hvm]
  have hlv : lnpt.val = 2 ^ n := by rw [(npt_ok hlnpt).1, hmax.1, npt_two_pow]
  obtain ⟨val', order', curr', lnpt', pos0, f, hval', horder', hcurr', hlnpt', -, hrun, hpl⟩ :=
    arity_eq hsched
  rw [hval] at hval'; cases result_ok_inj (ok_inj hval')
  rw [hcurr] at hcurr'; cases ok_inj hcurr'
  have hs := schedRun_two _ _ _ n f _ _ _ (hcv ▸ hrun)
  have hlen : sched.val.length = n := by simpa using congrArg List.length hs
  refine ⟨hmax.1, hcv, by simpa using hs, by rw [hpl, hlen], hord, ?_⟩
  rw [sched_leaf_loop_ok dims order lnpt 0#usize pos hpos, hord, hlv]
  exact leafEnd_binary _ _ n (heightOf_pow hpow)

/-- With arity 2 and power-of-two heights, the verifier's plan is the binary plan.

The tallest height is 2^n, and c is the cap height.

The plan walks n - min(c, n) levels, from the leaf layer up. -/
theorem plan_eq_bplan {cap pl val : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched sched1 order : alloc.vec.Vec Std.Usize} {curr lnpt pos : Std.Usize}
    (hpow : PowHeights dims)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels 2#usize cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val 2#usize = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos) :
    plan 2 (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val =
      bplan (logsOf dims) (Nat.log 2 val.val) (Nat.log 2 val.val)
        (Nat.log 2 val.val - min cap.val (Nat.log 2 val.val)) := by
  obtain ⟨-, hcv, hs, hpl, hord, hpv⟩ :=
    layout_binary hpow hval hsched horder hcurr hlnpt hpos
  have hs1 : schedFrom sched1 0 =
      List.replicate (Nat.log 2 val.val - min cap.val (Nat.log 2 val.val)) 2 := by
    rw [schedFrom, List.drop_zero, vec_truncate_ok hsched1, List.map_take, hs, hpl,
      List.take_replicate]
    congr 1
    omega
  rw [hs1, hcv, hpv, hord]
  exact plan_binary _ _ _ (heightOf_pow hpow) _ _ (by omega) le_rfl

/-! ## The walk, on binary levels -/

/-- On binary levels, the walk never reads the padding: only its length matters. -/
theorem walk_pad_two {F D : Type _} (h : List (List F) → D) (c : List D → D) (z : D)
    (order : List ℕ) (opened : List (List F)) (proof : List D) (pad : List D) (hpad : pad.length = 2) :
    ∀ (pl : List Level), (∀ l ∈ pl, l.1 = 2) → ∀ i pp d,
      walk h c pad z order opened proof pl i pp d = walk h c [z, z] z order opened proof pl i pp d := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, pad = [a, b] := by
    match pad, hpad with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  intro pl
  induction pl with
  | nil => intro _ i pp d; rfl
  | cons l pl ih =>
    intro hl i pp d
    obtain ⟨s, g⟩ := l
    have hs : s = 2 := hl _ List.mem_cons_self
    subst hs
    have hch : ∀ pg d', children [a, b] 2 pg d' proof pp z = children [z, z] 2 pg d' proof pp z := by
      intro pg d'; simp [children, List.range_succ]
    simp only [walk, hch]
    rcases g with _ | ⟨a', b'⟩
    · exact ih (fun l hl' => hl l (List.mem_cons_of_mem _ hl')) _ _ _
    · simp only [List.set_cons_zero, List.set_cons_succ]
      exact ih (fun l hl' => hl l (List.mem_cons_of_mem _ hl')) _ _ _

/-- A matrix of log height e sits in its block of the binary tree's order. -/
theorem mem_block {lh : List ℕ} {n e m : ℕ} (he : e ≤ n) (hm : m ∈ atLog lh e) :
    ∃ k, blockStart lh n e ≤ k ∧ k < blockEnd lh n e ∧ k < (tallOrder lh n).length ∧
      (tallOrder lh n).getD k 0 = m := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hs := tallOrder_split lh he
  rw [show tallOrder lh e = atLog lh e ++ (List.range e).reverse.flatMap (atLog lh) by
    rw [tallOrder, logsDown_eq_cons e, List.flatMap_cons]] at hs
  refine ⟨blockStart lh n e + i, by omega, by rw [blockEnd]; omega, ?_, ?_⟩
  · rw [hs, blockStart_eq]; simp; omega
  · rw [hs, blockStart_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem mem_injected_bplan_inv (lh : List ℕ) (n : ℕ) :
    ∀ L e g, L ≤ e → g ∈ injected (bplan lh n e L) →
      ∃ e', e - L ≤ e' ∧ e' < e ∧ g = (blockStart lh n e', blockEnd lh n e') := by
  intro L
  induction L with
  | zero => intro e g _ hg; simp [bplan, injected] at hg
  | succ L ih =>
    intro e g hL hg
    have hrest : g ∈ injected (bplan lh n (e - 1) L) →
        ∃ e', e - (L + 1) ≤ e' ∧ e' < e ∧ g = (blockStart lh n e', blockEnd lh n e') := fun hg => by
      obtain ⟨e', h1, h2, rfl⟩ := ih _ _ (by omega) hg
      exact ⟨e', by omega, by omega, rfl⟩
    by_cases hb : atLog lh (e - 1) = []
    · simp only [bplan, hb, ↓reduceIte, injected] at hg
      exact hrest hg
    · simp only [bplan, hb, ↓reduceIte, injected, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨e - 1, by omega, by omega, rfl⟩
      · exact hrest hg

/-- A position inside the block of log height e holds a matrix of log height e. -/
theorem mem_block_inv {lh : List ℕ} {n e k : ℕ} (he : e ≤ n) (h1 : blockStart lh n e ≤ k)
    (h2 : k < blockEnd lh n e) : (tallOrder lh n).getD k 0 ∈ atLog lh e := by
  have hs := tallOrder_split lh he
  rw [show tallOrder lh e = atLog lh e ++ (List.range e).reverse.flatMap (atLog lh) by
    rw [tallOrder, logsDown_eq_cons e, List.flatMap_cons]] at hs
  rw [blockEnd] at h2
  rw [blockStart_eq] at h1 h2
  rw [hs, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
    List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

/-- With arity 2 and power-of-two heights, the verifier reads exactly the matrices at least as tall as the cap.

The tallest height is 2^n, and c is the cap height.

A matrix of height 2^e is read exactly when e is at least min(c, n). -/
theorem reads_binary {cap pl val : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched sched1 order : alloc.vec.Vec Std.Usize} {curr lnpt pos : Std.Usize}
    (hpow : PowHeights dims)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels 2#usize cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val 2#usize = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos) (m : ℕ) :
    Reads 2#usize cap dims m ↔
      m < dims.val.length ∧ min cap.val (Nat.log 2 val.val) ≤ (logsOf dims).getD m 0 := by
  obtain ⟨-, -, -, -, hord, hpv⟩ := layout_binary hpow hval hsched horder hcurr hlnpt hpos
  have hplan := plan_eq_bplan hpow hval hsched hsched1 horder hcurr hlnpt hpos
  obtain ⟨hvm, hv0⟩ := validate_ok_val hval
  have hmax := (maxHeight_pow hpow (hvm ▸ hv0)).2
  rw [← hvm] at hmax
  set n := Nat.log 2 val.val
  set lh := logsOf dims
  have hlen : order.val.length = (tallOrder lh n).length := by rw [← hord, ordL_length]
  have hbs : blockStart lh n n = 0 := by simp [blockStart]
  constructor
  · rintro ⟨val', sched', pl', sched1', order', curr', lnpt', pos', hval', hsched', hsched1',
      horder', hcurr', hlnpt', hpos', k, hk, rfl, hread⟩
    rw [hval] at hval'; cases result_ok_inj (ok_inj hval')
    rw [hsched] at hsched'; cases result_ok_inj (ok_inj hsched')
    rw [hsched1] at hsched1'; cases ok_inj hsched1'
    rw [horder] at horder'; cases ok_inj horder'
    rw [hcurr] at hcurr'; cases ok_inj hcurr'
    rw [hlnpt] at hlnpt'; cases ok_inj hlnpt'
    rw [hpos] at hpos'; cases ok_inj hpos'
    rw [show (2#usize : Std.Usize).val = 2 from rfl, hplan] at hread
    rw [hord]
    rcases hread with hk0 | ⟨g, hg, hgk, hkg⟩
    · have := mem_atLog.1 (mem_block_inv le_rfl (by omega) (hpv ▸ hk0))
      rw [logsOf_length] at this
      exact ⟨this.1, by omega⟩
    · obtain ⟨e', h1, h2, rfl⟩ := mem_injected_bplan_inv lh n _ n g (by omega) hg
      have := mem_atLog.1 (mem_block_inv (by omega) hgk hkg)
      rw [logsOf_length] at this
      exact ⟨this.1, by omega⟩
  · rintro ⟨hm, hcm⟩
    have hml : m < lh.length := by rw [logsOf_length]; exact hm
    have hmem : m ∈ atLog lh (lh.getD m 0) := mem_atLog.2 ⟨hml, rfl⟩
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := mem_block (hmax m hml) hmem
    refine ⟨val, sched, pl, sched1, order, curr, lnpt, pos, hval, hsched, hsched1, horder, hcurr,
      hlnpt, hpos, k, by omega, by rw [hord, hk4], ?_⟩
    rw [show (2#usize : Std.Usize).val = 2 from rfl, hplan]
    rcases Nat.lt_or_ge (lh.getD m 0) n with hlt | hge
    · exact Or.inr ⟨_, mem_injected_bplan lh n _ n _ (by omega) (by omega) hlt
        (List.ne_nil_of_mem hmem), hk1, hk2⟩
    · have he : lh.getD m 0 = n := le_antisymm (hmax m hml) hge
      rw [he] at hk2
      exact Or.inl (by omega)

variable {P PW F W H C : Type} {DIGEST_ELEMS : Std.Usize}

/-- Merkle's binding argument on the binary tree over power-of-two heights.

Take two openings at one index, under one cap and one set of dimensions, that both verify.

The tallest height is 2^n, and c is the cap height.

Then one of these holds:

- the hasher collides
- the compression collides
- the two openings agree on every matrix of height 2^e with e at least min(c, n). -/
theorem verify_binding_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (index : Std.Usize)
    (o1 o2 : Slice (alloc.vec.Vec F)) (p1 p2 : Slice (Std.Array W DIGEST_ELEMS))
    (h1 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o1 p1 =
      RustM.ok (core.result.Result.Ok ()))
    (h2 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o2 p2 =
      RustM.ok (core.result.Result.Ok ())) :
    CCollision c ∨ HCollision h ∨
      ∀ m < dims.val.length, min mt.cap_height.val (Nat.log 2 (maxHeight dims)) ≤ (logsOf dims).getD m 0 →
        (openedL o1).getD m [] = (openedL o2).getD m [] := by
  obtain ⟨val, sched, pl, sched1, order, curr, lnpt, pos, -, -, -, -, -, -, hval, hsched, hsched1, -,
    horder, hcurr, -, hlnpt, hpos, -⟩ := verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims
      index o1 p1 h1
  rcases verify_binding cl cp dfInst eqInst hInst cInst mt h c hH hC hcl heq (by decide) commit dims
    index o1 o2 p1 p2 h1 h2 with hc | hh | hall
  · exact Or.inl hc
  · exact Or.inr (Or.inl hh)
  refine Or.inr (Or.inr fun m hm hcm => hall m ?_)
  rw [reads_binary hpow hval hsched hsched1 horder hcurr hlnpt hpos, (validate_ok_val hval).1]
  exact ⟨hm, hcm⟩

/-- What the verifier accepts on the binary tree over power-of-two heights.

The tallest height is 2^n, c is the cap height, and L = n - min(c, n) is the number of walked levels.

An accepting run had all of these:

- an index below 2^n
- one row per matrix, at its width
- L siblings
- a walk of the binary plan from the hash of the tallest rows that reaches the cap entry at its index.

The walk pads with the default digest z, and binary levels never read the padding. -/
theorem verify_accepts_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y)
    (t : W) (z : Std.Array W DIGEST_ELEMS) (ht : dfInst.default = RustM.ok t)
    (hz : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok z)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS))
    (hacc : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    let n := Nat.log 2 (maxHeight dims)
    let lh := logsOf dims
    let w := walk h c [z, z] z (tallOrder lh n) (openedL opened) proof.val
      (bplan lh n n (n - min mt.cap_height.val n)) index.val 0
      (h (group (tallOrder lh n) (openedL opened) 0 (blockEnd lh n n)))
    index.val < 2 ^ n ∧ opened.val.length = dims.val.length ∧
      (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
        (opened.val[m]).val.length = (dims.val[m]).width.val) ∧
      proof.val.length = n - min mt.cap_height.val n ∧
      commit.cap.val[w.1]? = some w.2 := by
  intro n lh w
  obtain ⟨val, sched, pl, sched1, order, curr, lnpt, pos, t', dflt, d0, ci, df, a, hval, hsched,
    hsched1, hwid, horder, hcurr, hidx, hlnpt, hpos, hd0, ht', hdflt, hloop, ha, heqa, epl, hepl,
    hplen⟩ := verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims index opened proof hacc
  rw [ht] at ht'; cases ok_inj ht'
  rw [hz] at hdflt; cases ok_inj hdflt
  have hvm := (validate_ok_val hval).1
  obtain ⟨hv2, -, hs, hpl, hord, hpv⟩ := layout_binary hpow hval hsched horder hcurr hlnpt hpos
  have hplan := plan_eq_bplan hpow hval hsched hsched1 horder hcurr hlnpt hpos
  rw [hvm] at hv2 hs hpl hord hpv hplan
  obtain ⟨hl, hwd⟩ := check_widths_ok hwid
  have hordO : ∀ i ∈ order.val, i.val < opened.val.length :=
    fun i hi => hl ▸ tallest_first_ok horder i hi
  refine ⟨by rw [← hv2, ← hvm]; exact hidx, hl, hwd, ?_, ?_⟩
  · -- Each walked level is binary, so it takes one sibling.
    rw [hplen, sum_loop_ok hepl, sibSum, List.drop_zero, vec_truncate_ok hsched1,
      show (fun s : Std.Usize => s.val - 1) = (fun x => x - 1) ∘ (fun s : Std.Usize => s.val) from rfl,
      ← List.map_map, List.map_take, hs, hpl, List.take_replicate]
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    show _ = Nat.log 2 (maxHeight dims) - _
    omega
  · -- The run folds the binary plan from the hash of the tallest rows.
    obtain ⟨padA, hpad⟩ := Lib.array_repeat_ok 2#usize
      (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst)
      (Lib.array_clone_ok cp.cloneCloneInst hcl) z
    have hw := walk_ok cl cp hInst cInst mt.hash mt.compress h c hH hC dims opened proof sched1 order
      z padA hpad hordO _ index curr pos d0 0#usize 0#usize ci df rfl hloop
    have hleaf : d0 = h (group (ordL order) (openedL opened) 0 pos.val) := by
      rw [hH _ _ (rowsList opened (vs order) 0 pos.val)
        ⟨_, rfl, rows_yields opened (vs order) (by rw [vs_val]; exact hordO) _ 0#usize pos rfl
          (by rw [vs_val]; exact leaf_pos_le hpos)⟩] at hd0
      rw [← ok_inj hd0, rowsList_val opened order hordO]
    simp only [show (0#usize : Std.Usize).val = 0 from rfl,
      show (2#usize : Std.Usize).val = 2 from rfl] at hw
    rw [hplan, hleaf, hord, hpv,
      walk_pad_two h c z _ _ _ padA.val (by simp) _ (bplan_steps _ _ _ _)] at hw
    simp only [p3_symmetric.hash.MerkleCap.Insts.CoreOpsIndexIndexUsizeDigest.index] at ha
    rw [← congrArg Prod.fst hw, ← congrArg Prod.snd hw, (vec_index_ok ha).2,
      array_eq_true eqInst heq heqa]

/-- The cap size the verifier expects is the product of the arities above the walked levels. -/
theorem cap_loop_ok {sched : alloc.vec.Vec Std.Usize} {pl e : Std.Usize}
    (h : mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok e) :
    e.val = ((sched.val.drop pl.val).map fun s => s.val).prod := by
  unfold mmcs.hax_reshaped.check_cap_size_loop at h
  refine loop_inv _ (fun x : Std.Usize × Std.Usize =>
      x.1.val * ((sched.val.drop x.2.val).map fun s => s.val).prod =
        ((sched.val.drop pl.val).map fun s => s.val).prod)
    (fun e : Std.Usize => e.val = ((sched.val.drop pl.val).map fun s => s.val).prod) ?_ _ _ h
    (by simp)
  rintro ⟨a, l⟩ hinv r hr
  dsimp only at hinv hr
  unfold mmcs.hax_reshaped.check_cap_size_loop.body at hr
  obtain ⟨len, hlen, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hlen
  cases ok_inj hlen
  split at hr
  · rename_i hlt
    have hlt' : l.val < sched.val.length := by simpa using hlt
    obtain ⟨s1, hs1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hs1v⟩ := vec_index_ok hs1
    obtain ⟨a1, ha1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨l1, hl1, hr⟩ := bind_tc_eq_ok hr
    cases ok_inj hr
    rw [List.getElem?_eq_getElem hlt'] at hs1v
    dsimp only
    rw [usize_mul_ok ha1, usize_succ_ok hl1, ← hinv, List.drop_eq_getElem_cons hlt',
      ← Option.some.inj hs1v]
    simp only [List.map_cons, List.prod_cons, mul_assoc]
  · rename_i hlt
    have hlt' : ¬ l.val < sched.val.length := by simpa using hlt
    cases ok_inj hr
    rw [← hinv, List.drop_of_length_le (by omega)]
    simp

end Plonky3Lean.Proofs.MerkleTree
