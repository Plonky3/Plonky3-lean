module

public import Aeneas
public import CoreModels
public import Mathlib.Data.List.Forall2
public import Plonky3Lean.Lib.RustM

@[expose] public section

/-!
# Arrays

Facts about how generated code builds arrays.

* Cloning an array never fails when cloning an element never fails
  (`array_clone_ok`), through `foldlM_ok`.
* `core::array::repeat` never fails when cloning never fails
  (`array_repeat_ok`), and fills the array with its argument when cloning returns
  its argument (`array_repeat_eq`). CoreModels builds the array with `array_from_fn` and a
  closure that pops the head of a sequence of clones, so its own
  `array_from_fn_spec`, which assumes the closure keeps its state, does not apply;
  the proof follows the sequence down instead.
* A `while i < N { output[i] = f(input[i]); i += 1 }` loop, as aeneas emits it with
  the `loop` combinator, relates input and output elementwise by any spec `f`
  meets (`elementwise_loop`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Lib

/-- A `foldlM` whose step never fails never fails. -/
theorem foldlM_ok {α σ : Type} (f : σ → α → RustM σ) (hf : ∀ s x, ∃ s', f s x = .ok s') :
    ∀ (l : List α) (s : σ), ∃ r, l.foldlM f s = .ok r := by
  intro l
  induction l with
  | nil => intro s; exact ⟨s, rfl⟩
  | cons x l ih =>
    intro s
    obtain ⟨s', hs'⟩ := hf s x
    obtain ⟨r, hr⟩ := ih s'
    exact ⟨r, by simp [List.foldlM_cons, hs', hr]⟩

/-- Cloning an array never fails when cloning an element never fails. -/
theorem array_clone_ok {T : Type} {N : Std.Usize} (inst : core.clone.Clone T)
    (hclone : ∀ x, ∃ v, inst.clone x = .ok v) (a : Array T N) :
    ∃ b, (core.Array.Insts.CoreCloneClone N inst).clone a = .ok b := by
  show ∃ b, core.Array.Insts.CoreCloneClone.clone inst a = .ok b
  unfold core.Array.Insts.CoreCloneClone.clone core.array.Array.map
    rust_primitives.slice.array_map
  obtain ⟨r, hr⟩ := foldlM_ok (fun (s : List T × core.array.CloneArray.clone.closure T N) (x : T) => do
      let (v, f') ← (core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT N inst).call_mut s.2 x
      RustM.ok (s.1 ++ [v], f'))
    (by
      intro s x
      obtain ⟨v, hv⟩ := hclone x
      refine ⟨(s.1 ++ [v], s.2), ?_⟩
      show (do
        let (v, f') ← core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut inst s.2 x
        RustM.ok (s.1 ++ [v], f')) = _
      unfold core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut
      simp [hv])
    a.val ([], ())
  split
  · rename_i h
    generalize hm : (List.foldlM (m := RustM) _ _ _ : RustM (List T × core.array.CloneArray.clone.closure T N)) = m at h
    obtain rfl : m = .ok r := hm.symm.trans hr
    simp at h
  · rename_i h
    generalize hm : (List.foldlM (m := RustM) _ _ _ : RustM (List T × core.array.CloneArray.clone.closure T N)) = m at h
    obtain rfl : m = .ok r := hm.symm.trans hr
    simp at h
  · exact ⟨_, rfl⟩

/-- `seq_remove s 0` on a nonempty sequence returns its head and the rest. -/
theorem seq_remove_zero {T : Type} (s : rust_primitives.sequence.Seq T) (h : 0 < s.val.length) :
    ∃ x s', rust_primitives.sequence.seq_remove s 0#usize = .ok (x, s') ∧
      s'.val.length = s.val.length - 1 := by
  unfold rust_primitives.sequence.seq_remove
  split
  · exact ⟨_, _, rfl, by simp⟩
  · rename_i hn; exact absurd (by simpa using h) hn

/-- `repeat`'s closure, called on a nonempty sequence, removes its head, whatever
the index it is called with. -/
theorem repeat_call_mut {T : Type} {N : Std.Usize} (inst : core.clone.Clone T)
    (c : core.array.repeat.closure T N) (h : 0 < c.val.length) :
    ∃ x c', (∀ k, core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
        inst c k = .ok (x, c')) ∧ c'.val.length = c.val.length - 1 := by
  obtain ⟨x, s', hs, hlen⟩ := seq_remove_zero c h
  refine ⟨x, s', fun k => ?_, hlen⟩
  unfold core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  simp [hs]

/-- `array_from_fn_go` with `repeat`'s closure, run `n` times on a sequence of at least
`n` elements, returns `n` values. -/
theorem repeat_go {T : Type} {N : Std.Usize} (inst : core.clone.Clone T) :
    ∀ (n : Nat) (c : core.array.repeat.closure T N), n ≤ c.val.length →
      ∃ l c', rust_primitives.slice.array_from_fn_go
          (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) c n = .ok (l, c') ∧
        l.length = n ∧ c'.val.length = c.val.length - n := by
  intro n
  induction n with
  | zero => intro c _; exact ⟨[], c, rfl, rfl, by simp⟩
  | succ n ih =>
    intro c hn
    obtain ⟨l, c', hgo, hl, hc'⟩ := ih c (by omega)
    obtain ⟨x, c'', hcall, hc''⟩ := repeat_call_mut inst c' (by omega)
    refine ⟨l ++ [x], c'', ?_, by simp [hl], by omega⟩
    unfold rust_primitives.slice.array_from_fn_go
    simp [hgo, hcall]

/-- `seq_create` of a value whose clone never fails returns `n` elements. -/
theorem seq_create_ok {T : Type} (inst : core.clone.Clone T) (hclone : ∀ x, ∃ v, inst.clone x = .ok v)
    (x : T) (n : Std.Usize) :
    ∃ s, rust_primitives.sequence.seq_create inst x n = .ok s ∧ s.val.length = n.val := by
  unfold rust_primitives.sequence.seq_create
  split
  · exact ⟨Slice.new T, rfl, by simp_all⟩
  · obtain ⟨l', hl', hlen⟩ := mapM_total inst.clone hclone (List.replicate (n.val - 1) x)
    have hmax : n.val ≤ Usize.max := by scalar_tac
    have hn : (l' ++ [x]).length ≤ Usize.max := by simp [hlen]; omega
    rw [hl']
    simp only [RustM.match.ok]
    split
    · exact ⟨_, rfl, by simp [hlen]; omega⟩
    · contradiction

/-- `core::array::repeat` never fails when cloning never fails. -/
theorem array_repeat_ok {T : Type} (N : Std.Usize) (inst : core.clone.Clone T)
    (hclone : ∀ x, ∃ v, inst.clone x = .ok v) (x : T) :
    ∃ a, core.array.repeat N inst x = .ok a := by
  obtain ⟨s, hs, hslen⟩ := seq_create_ok inst hclone x N
  obtain ⟨l, c', hgo, hl, -⟩ := repeat_go (N := N) inst N.val s (by omega)
  refine ⟨Array.from l (by rw [hl]), ?_⟩
  unfold core.array.repeat rust_primitives.slice.array_from_fn
  simp [hs, hgo, hl]

/-- `seq_remove s 0` on a nonempty sequence returns an element of `s`, and a rest whose
elements are elements of `s`. -/
theorem seq_remove_zero_mem {T : Type} (s : rust_primitives.sequence.Seq T) (h : 0 < s.val.length) :
    ∃ x s', rust_primitives.sequence.seq_remove s 0#usize = .ok (x, s') ∧
      s'.val.length = s.val.length - 1 ∧ x ∈ s.val ∧ ∀ y ∈ s'.val, y ∈ s.val := by
  unfold rust_primitives.sequence.seq_remove
  split
  · refine ⟨_, _, rfl, by simp, List.get_mem _ _, ?_⟩
    intro y hy
    simp only [Slice.from_val] at hy
    exact List.mem_of_mem_drop hy
  · rename_i hn; exact absurd (by simpa using h) hn

/-- `repeat_go`, keeping track of where the values come from: every value it returns,
and every element left in the sequence, is an element of the sequence it started from. -/
theorem repeat_go_mem {T : Type} {N : Std.Usize} (inst : core.clone.Clone T) :
    ∀ (n : Nat) (c : core.array.repeat.closure T N), n ≤ c.val.length →
      ∃ l c', rust_primitives.slice.array_from_fn_go
          (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) c n = .ok (l, c') ∧
        l.length = n ∧ c'.val.length = c.val.length - n ∧
        (∀ y ∈ l, y ∈ c.val) ∧ ∀ y ∈ c'.val, y ∈ c.val := by
  intro n
  induction n with
  | zero => intro c _; exact ⟨[], c, rfl, rfl, by simp, by simp, fun _ h => h⟩
  | succ n ih =>
    intro c hn
    obtain ⟨l, c', hgo, hl, hc', hlm, hcm⟩ := ih c (by omega)
    obtain ⟨x, c'', hs, hc'', hx, hc''m⟩ := seq_remove_zero_mem c' (by omega)
    have hcall : ∀ k, core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
        inst c' k = .ok (x, c'') := by
      intro k
      unfold core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      simp [hs]
    refine ⟨l ++ [x], c'', ?_, by simp [hl], by omega, ?_, fun y hy => hcm y (hc''m y hy)⟩
    · unfold rust_primitives.slice.array_from_fn_go
      simp [hgo, hcall]
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hlm y hy
      · rw [List.mem_singleton.mp hy]; exact hcm x hx

/-- A `mapM` of a function that returns its argument returns the list. -/
theorem mapM_ok_self {α : Type} (f : α → RustM α) (hf : ∀ x, f x = .ok x) :
    ∀ l : List α, l.mapM f = .ok l := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, hf a, ih, bind_tc_ok]
    rfl

/-- `core::array::repeat n x`, for a type whose clone returns its argument, never fails, and
every element of the array it returns is `x`. -/
theorem array_repeat_eq {T : Type} (N : Std.Usize) (inst : core.clone.Clone T)
    (hclone : ∀ x, inst.clone x = .ok x) (x : T) :
    ∃ a, core.array.repeat N inst x = .ok a ∧ ∀ y ∈ a.val, y = x := by
  have hs : ∃ s, rust_primitives.sequence.seq_create inst x N = .ok s ∧
      s.val.length = N.val ∧ ∀ y ∈ s.val, y = x := by
    unfold rust_primitives.sequence.seq_create
    split
    · exact ⟨Slice.new T, rfl, by simp_all, by simp⟩
    · have hmax : N.val ≤ Usize.max := by scalar_tac
      have hn : (List.replicate (N.val - 1) x ++ [x]).length ≤ Usize.max := by simp; omega
      rw [mapM_ok_self inst.clone hclone]
      simp only [RustM.match.ok]
      split
      · refine ⟨_, rfl, by simp; omega, ?_⟩
        intro y hy
        simp only [Slice.from_val, List.mem_append, List.mem_replicate, List.mem_singleton] at hy
        rcases hy with ⟨-, h⟩ | h <;> exact h
      · contradiction
  obtain ⟨s, hs, hslen, hsx⟩ := hs
  obtain ⟨l, c', hgo, hl, -, hlm, -⟩ := repeat_go_mem (N := N) inst N.val s (by omega)
  refine ⟨Array.from l (by rw [hl]), ?_, ?_⟩
  · unfold core.array.repeat rust_primitives.slice.array_from_fn
    simp [hs, hgo, hl]
  · intro y hy
    rw [Array.from_val] at hy
    exact hsx y (hlm y hy)

/-- A loop that writes `f input[i]` into `output[i]` for `i` from its start to `N`
meets `R` elementwise, given that `f` meets `R` and the prefix already does. -/
theorem elementwise_loop {α β : Type} {N : Std.Usize} (f : α → RustM β) (R : α → β → Prop)
    (hf : ∀ x, f x ⦃ r => R x r ⦄) (input : Array α N) (output : Array β N) (i : Std.Usize)
    (hi : i.val ≤ N.val)
    (hpre : List.Forall₂ R (input.val.take i.val) (output.val.take i.val)) :
    loop (fun (s : Array β N × Std.Usize) => do
      if s.2 < N then
        let x ← Array.index_usize input s.2
        let y ← f x
        let o ← Array.update s.1 s.2 y
        let k ← s.2 + 1#usize
        RustM.ok (ControlFlow.cont (o, k))
      else RustM.ok (ControlFlow.done s.1)) (output, i)
      ⦃ r => List.Forall₂ R input.val r.val ⦄ := by
  apply loop.spec_decr_nat (fun s => N.val - s.2.val)
    (fun s => s.2.val ≤ N.val ∧ List.Forall₂ R (input.val.take s.2.val) (s.1.val.take s.2.val))
  · rintro ⟨o, k⟩ ⟨hk, hfa⟩
    simp only
    split
    · step as ⟨ x, hx, hxv ⟩
      step with hf x as ⟨ y, hy ⟩
      step as ⟨ o', ho' ⟩
      step as ⟨ k', hk' ⟩
      have hkN : k.val < N.val := by scalar_tac
      have hko : k.val < o.val.length := by rw [o.property]; exact hkN
      refine ⟨by omega, ?_, by omega⟩
      have hset : o'.val = o.val.set k.val y := by rw [ho']; simp
      rw [hk', List.take_add_one, List.take_add_one, hset, List.take_set_of_le (le_refl _)]
      simp only [List.getElem?_set_self hko, List.getElem?_eq_getElem hx, Option.toList_some]
      exact List.rel_append hfa (List.Forall₂.cons (hxv ▸ hy) .nil)
    · have hkN : k.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      have h1 : input.val.take k.val = input.val := by rw [hkN, ← input.property, List.take_length]
      have h2 : o.val.take k.val = o.val := by rw [hkN, ← o.property, List.take_length]
      simpa [h1, h2] using hfa
  · exact ⟨hi, hpre⟩

end Plonky3Lean.Lib
