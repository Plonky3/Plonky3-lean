module

public import Plonky3Lean.Proofs.Symmetric.Online

@[expose] public section

/-!
# Which inputs the sponges send to the same digest

Without padding, two kinds of input collide for every permutation.

* A message that ends inside a block, extended by the values the rate already holds at those positions.

  In the first block those values are zeros.

* The empty message, whose digest is the zero state, not touched by the permutation.

With 10-padding, the padded blocks and the separator flag determine the message.
-/

namespace Plonky3Lean.Proofs.Symmetric

open Plonky3Lean.Spec.Sponge

variable {T : Type}

theorem blocks_append (r : ℕ) (hr : 0 < r) :
    ∀ (q : ℕ) (a b : List T), a.length = r * q → blocks r (a ++ b) = blocks r a ++ blocks r b := by
  intro q
  induction q with
  | zero =>
    intro a b ha
    rw [Nat.mul_zero, List.length_eq_zero_iff] at ha
    subst ha
    simp [blocks_nil]
  | succ q ih =>
    intro a b ha
    have hne : a ≠ [] := by rintro rfl; simp at ha; rw [Nat.mul_succ] at ha; omega
    have hra : r ≤ a.length := by rw [ha, Nat.mul_succ]; omega
    rw [blocks_cons r _ hr (by simp [hne]), blocks_cons r a hr hne, List.take_append_of_le_length hra,
      List.drop_append_of_le_length hra, ih _ b (by simp [ha, Nat.mul_succ])]
    rfl

/-- The empty message hashes to the first `out` cells of the zero state: the permutation never runs. -/
theorem paddingFree_nil (f : List T → List T) (zero : T) (w r out : ℕ) :
    paddingFree f zero w r out [] = (List.replicate w zero).take out := by
  simp [paddingFree, blocks_nil]

/-- A message that ends inside a block collides with its extension by whatever the rate already holds there.

`s` is the state after the whole blocks; the message ends with a short block `b`; the extension `x` copies `s` at the positions after `b`.

```text
    s:          [ s_0 ... s_{j-1} | s_j ... s_{j+k-1} | ... ]
    m:          [ b_0 ... b_{j-1} ]
    m ++ x:     [ b_0 ... b_{j-1} | s_j ... s_{j+k-1} ]
                  same overwritten state, same digest
```
-/
theorem paddingFree_extend (f : List T → List T) (zero : T) (w r out : ℕ) (hr : 0 < r)
    (pre b x : List T) (q : ℕ) (hpre : pre.length = r * q) (hb : b ≠ [])
    (hbx : b.length + x.length ≤ r)
    (hx : x = ((((blocks r pre).foldl (absorb f) (List.replicate w zero)).drop b.length).take
      x.length)) :
    paddingFree f zero w r out (pre ++ b ++ x) = paddingFree f zero w r out (pre ++ b) := by
  have hbx0 : b ++ x ≠ [] := by simp [hb]
  simp only [paddingFree, List.append_assoc]
  rw [blocks_append r hr q pre _ hpre, blocks_append r hr q pre _ hpre,
    blocks_of_lt r _ (by simpa using hbx) hbx0, blocks_of_lt r b (by omega) hb]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, absorb]
  congr 2
  generalize (blocks r pre).foldl (absorb f) (List.replicate w zero) = s at hx
  simp only [overwrite, List.length_append, List.append_assoc]
  rw [hx]
  congr 1
  rw [show ∀ n, List.drop (b.length + n) s = List.drop n (List.drop b.length s) from
    fun n => by rw [List.drop_drop]]
  generalize s.drop b.length = D
  rcases Nat.le_total x.length D.length with h | h
  · simp only [List.length_take, Nat.min_eq_left h, List.take_append_drop]
  · simp only [List.take_of_length_le h, List.drop_length,
      List.append_nil]

/-- In the first block, trailing zeros are invisible: a nonempty message collides with itself followed by zeros up to the rate. -/
theorem paddingFree_trailing_zeros (f : List T → List T) (zero : T) (w r out : ℕ) (hr : 0 < r)
    (m : List T) (k : ℕ) (hm : m ≠ []) (hk : m.length + k ≤ r) (hw : r ≤ w) :
    paddingFree f zero w r out (m ++ List.replicate k zero) = paddingFree f zero w r out m := by
  have := paddingFree_extend f zero w r out hr [] m (List.replicate k zero) 0 rfl hm
    (by simpa using hk) (by
      simp only [blocks_nil, List.foldl_nil, List.length_replicate, List.drop_replicate,
        List.take_replicate]
      congr 1
      omega)
  simpa using this

/-- The 10-padding is injective: the padded blocks and the separator flag determine the message.

It needs only that the sentinel `d(0)` is not zero.
-/
theorem replicate_sentinel_inj (zero d0 : T) (hd : d0 ≠ zero) :
    ∀ (a a' : ℕ) (l l' : List T),
      List.replicate a zero ++ d0 :: l = List.replicate a' zero ++ d0 :: l' → l = l' := by
  intro a
  induction a with
  | zero =>
    intro a' l l' h
    rcases a' with _ | a'
    · simpa using h
    · simp [List.replicate_succ] at h
      exact absurd h.1 hd
  | succ a ih =>
    intro a' l l' h
    rcases a' with _ | a'
    · simp [List.replicate_succ] at h
      exact absurd h.1.symm hd
    · simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
      exact ih a' l l' h.2

theorem pad_sentinel_inj (zero d0 : T) (hd : d0 ≠ zero) (R R' : List T) (a a' : ℕ)
    (h : R ++ d0 :: List.replicate a zero = R' ++ d0 :: List.replicate a' zero) : R = R' := by
  have h' := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] at h'
  simpa using replicate_sentinel_inj zero d0 hd a a' _ _ h'

theorem pad10Blocks_injective (zero d0 : T) (r : ℕ) (hr : 0 < r) (hd : d0 ≠ zero) :
    Function.Injective (pad10Blocks zero d0 r) := by
  intro m m' h
  unfold pad10Blocks at h
  by_cases hA : m ≠ [] ∧ m.length % r = 0 <;> by_cases hA' : m' ≠ [] ∧ m'.length % r = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_left_of_eq_true _ _ (eq_true hA')] at h
    rw [← flatten_blocks r hr m, (Prod.mk.inj h).1, flatten_blocks r hr m']
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_right_of_eq_false _ _ (eq_false hA')] at h
    exact absurd (congrArg Prod.snd h) (by simp)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hA), ite_eq_left_of_eq_true _ _ (eq_true hA')] at h
    exact absurd (congrArg Prod.snd h) (by simp)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hA), ite_eq_right_of_eq_false _ _ (eq_false hA')] at h
    replace h := (Prod.mk.inj h).1
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    have hR := pad_sentinel_inj zero d0 hd _ _ _ _ h2
    have hT := congrArg List.flatten h1
    rw [flatten_blocks r hr, flatten_blocks r hr] at hT
    rw [← List.take_append_drop (m.length / r * r) m, ← List.take_append_drop (m'.length / r * r) m',
      hT, hR]

/-- Without spare width, anyone who can invert the permutation finds collisions of the truncated permutation.

With `w = n * chunk` the chunks fill the whole state, so no cell is forced to zero.

Pick any output `y` and two different tails `t`, `t'`; the preimages of `y ++ t` and `y ++ t'` are two different inputs with output `y`.

```text
    f^-1( [ y | t  ] )  =  x    ->  compress(x)  = y
    f^-1( [ y | t' ] )  =  x'   ->  compress(x') = y,   x != x'
```

This is why the trait promises collision resistance only in a hash tree, where an input must itself be a compression output.
-/
theorem truncated_collision_of_inverse (f g : List T → List T) (zero : T) (w chunk : ℕ)
    (hfg : ∀ y, y.length = w → f (g y) = y) (hg : ∀ y, y.length = w → (g y).length = w)
    (y t t' : List T) (hy : y.length = chunk) (ht : t.length = w - chunk)
    (ht' : t'.length = w - chunk) (hne : t ≠ t') (hcw : chunk ≤ w)
    (ins ins' : List (List T)) (hins : ins.flatten = g (y ++ t))
    (hins' : ins'.flatten = g (y ++ t')) :
    truncated f zero w chunk ins = y ∧ truncated f zero w chunk ins' = y ∧ ins ≠ ins' := by
  have hl : (y ++ t).length = w := by simp; omega
  have hl' : (y ++ t').length = w := by simp; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [truncated, hins, hg _ hl, Nat.sub_self, List.replicate_zero, List.append_nil,
      hfg _ hl, List.take_left' hy]
  · simp only [truncated, hins', hg _ hl', Nat.sub_self, List.replicate_zero, List.append_nil,
      hfg _ hl', List.take_left' hy]
  · intro h
    apply hne
    have h1 : g (y ++ t) = g (y ++ t') := by rw [← hins, ← hins', h]
    have h2 := congrArg f h1
    rw [hfg _ hl, hfg _ hl'] at h2
    exact List.append_cancel_left h2

end Plonky3Lean.Proofs.Symmetric
