module

public import Plonky3Lean.Proofs.MultiStark.Blocks
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The lookup link

Every declared tuple of every AIR owns one block of the fraction tables.

The block of a tuple on a trace of 2^n rows holds 2^n leaves, one per row:

```text
    numerator    m(y)       the tuple's multiplicity on row y
    denominator  d(y)       its bus prefix minus its payload fingerprint
```

Leaves outside every block are padding, a zero over a one.

The fractional reduction ends at a point q = p ++ s and claims N(q) and D(q).

A challenge theta folds them into one claim:

```text
    N(q) + theta (D(q) - 1)  =  sum_b eq(c_b, p_b) (m_b~(s_b) + theta (d_b~(s_b) - 1))
```

Here c_b is the block's index at its own height, p_b the matching prefix of q and s_b the rest.

The padding drops out, because its numerator is 0 and its shifted denominator is 0.

The zerocheck then rebuilds the right side from the AIR's own columns.

The leaves of the fraction tables sum to the sum, over every block and row, of m(y) / d(y).
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Finset

variable {K : Type _} [Field K]

/-- One block: its height 2^n, its index c at that height, and its two tables. -/
structure FracBlock (K : Type _) where
  n : ℕ
  c : ℕ
  m : ℕ → K
  d : ℕ → K

/-- The numerator table: each block's multiplicities in place, and zero elsewhere. -/
def numTable (bs : List (FracBlock K)) (x : ℕ) : K :=
  (bs.map fun b => blockTable b.n b.c b.m x).sum

/-- The denominator table: each block's denominators in place, and one elsewhere. -/
def denTable (bs : List (FracBlock K)) (x : ℕ) : K :=
  1 + (bs.map fun b => blockTable b.n b.c (fun y => b.d y - 1) x).sum

theorem rowExt_list_sum {ι : Type _} (l : List ι) (f : ι → ℕ → K) (r : List K) :
    rowExt (fun x => (l.map fun i => f i x).sum) r = (l.map fun i => rowExt (f i) r).sum := by
  induction l with
  | nil => simpa using rowExt_zero r
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [rowExt_add, ih]

/-- A block of height 2^n read at the point q: its index at that height selects it on the prefix. -/
def FracBlock.weight (b : FracBlock K) (q : List K) : K :=
  eq (vertex (q.length - b.n) b.c) (q.take (q.length - b.n))

/-- **The link.**

Take blocks that each fit their prefix of the point.

The folded opening of the two tables is the sum of each block's share. -/
theorem link_claim (bs : List (FracBlock K)) (q : List K) (θ : K)
    (hb : ∀ b ∈ bs, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n)) :
    rowExt (numTable bs) q + θ * (rowExt (denTable bs) q - 1) =
      (bs.map fun b => b.weight q *
        (rowExt b.m (q.drop (q.length - b.n)) +
          θ * (rowExt b.d (q.drop (q.length - b.n)) - 1))).sum := by
  have hblock : ∀ b ∈ bs, ∀ g : ℕ → K, rowExt (blockTable b.n b.c g) q =
      b.weight q * rowExt g (q.drop (q.length - b.n)) := fun b hbm g => by
    obtain ⟨h1, h2⟩ := hb b hbm
    have hs : (q.drop (q.length - b.n)).length = b.n := by simp; omega
    have := ext_blockTable g (q.drop (q.length - b.n)) (q.take (q.length - b.n))
      (c := b.c) (by simpa [show min (q.length - b.n) q.length = q.length - b.n by omega] using h2)
    rw [hs, List.take_append_drop] at this
    rw [this, FracBlock.weight]
    simp
  unfold numTable denTable
  rw [rowExt_list_sum, show (fun x => 1 + (bs.map fun b =>
      blockTable b.n b.c (fun y => b.d y - 1) x).sum) =
      fun x => (fun _ => (1 : K)) x + (fun x => (bs.map fun b =>
        blockTable b.n b.c (fun y => b.d y - 1) x).sum) x from rfl, rowExt_add, rowExt_const,
    rowExt_list_sum, add_sub_cancel_left, List.map_congr_left (fun b hbm => hblock b hbm b.m),
    List.map_congr_left (fun b hbm => hblock b hbm _), ← List.sum_map_mul_left, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun b hbm => ?_)
  have hs : ∀ g : ℕ → K, rowExt (fun y => g y - 1) (q.drop (q.length - b.n)) =
      rowExt g (q.drop (q.length - b.n)) - 1 := fun g => by
    rw [show (fun y => g y - 1) = fun y => g y + (fun _ => (-1 : K)) y by funext; ring,
      rowExt_add, rowExt_const]; ring
  rw [hs]; ring

theorem list_sum_map_sub {ι : Type _} (l : List ι) (f g : ι → K) :
    (l.map fun i => f i - g i).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **The numerator opening.**

The opening of the numerator table is the blocks' openings, each times its weight. -/
theorem rowExt_numTable (bs : List (FracBlock K)) (q : List K)
    (hb : ∀ b ∈ bs, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n)) :
    rowExt (numTable bs) q =
      (bs.map fun b => b.weight q * rowExt b.m (q.drop (q.length - b.n))).sum := by
  have h := link_claim bs q 0 hb
  simpa using h

/-- **The denominator opening.**

The opening of the denominator table is the blocks' openings, each times its weight.

The padding adds one minus the sum of the weights. -/
theorem rowExt_denTable (bs : List (FracBlock K)) (q : List K)
    (hb : ∀ b ∈ bs, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n)) :
    rowExt (denTable bs) q =
      (bs.map fun b => b.weight q * rowExt b.d (q.drop (q.length - b.n))).sum +
        (1 - (bs.map fun b => b.weight q).sum) := by
  have h1 := link_claim bs q 1 hb
  have h0 := link_claim bs q 0 hb
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  rw [h0] at h1
  have : rowExt (denTable bs) q - 1 = (bs.map fun b => b.weight q *
      (rowExt b.d (q.drop (q.length - b.n)) - 1)).sum := by
    have h2 : (bs.map fun b => b.weight q * (rowExt b.m (q.drop (q.length - b.n)) +
        (rowExt b.d (q.drop (q.length - b.n)) - 1))).sum =
        (bs.map fun b => b.weight q * rowExt b.m (q.drop (q.length - b.n))).sum +
          (bs.map fun b => b.weight q * (rowExt b.d (q.drop (q.length - b.n)) - 1)).sum := by
      rw [← List.sum_map_add]; congr 1; exact List.map_congr_left fun b _ => by ring
    linear_combination h1 + h2
  have h3 : (bs.map fun b => b.weight q * (rowExt b.d (q.drop (q.length - b.n)) - 1)).sum =
      (bs.map fun b => b.weight q * rowExt b.d (q.drop (q.length - b.n))).sum -
        (bs.map fun b => b.weight q).sum := by
    rw [← list_sum_map_sub]; congr 1; exact List.map_congr_left fun b _ => by ring
  linear_combination this + h3

/-! ## The leaf sum -/

/-- The leaves of the block of index c at height 2^n: c 2^n to c 2^n + 2^n - 1. -/
def leavesOf (n c : ℕ) : Finset ℕ := Ico (c * 2 ^ n) ((c + 1) * 2 ^ n)

/-- The leaves a block owns. -/
def FracBlock.leaves (b : FracBlock K) : Finset ℕ := leavesOf b.n b.c

theorem blockTable_of_mem {b : FracBlock K} {x : ℕ} (hx : x ∈ b.leaves) (g : ℕ → K) :
    blockTable b.n b.c g x = g (x - b.c * 2 ^ b.n) := by
  simp only [FracBlock.leaves, leavesOf, mem_Ico] at hx
  have hd : x / 2 ^ b.n = b.c := Nat.div_eq_of_lt_le hx.1 hx.2
  simp only [blockTable, hd, ↓reduceIte]
  rw [Nat.mod_eq_sub_mul_div, hd, mul_comm]

theorem blockTable_of_not_mem {b : FracBlock K} {x : ℕ} (hx : x ∉ b.leaves) (g : ℕ → K) :
    blockTable b.n b.c g x = 0 := by
  simp only [FracBlock.leaves, leavesOf, mem_Ico, not_and_or, not_le, not_lt] at hx
  simp only [blockTable, ite_eq_right_iff]
  intro hd
  have h1 := Nat.div_mul_le_self x (2 ^ b.n)
  have h2 := Nat.lt_div_mul_add (a := x) (show 0 < 2 ^ b.n by positivity)
  rw [hd] at h1 h2
  rcases hx with h | h <;> nlinarith

/-- Blocks are placed when they fit the table and own disjoint leaves. -/
def Placed (bs : List (FracBlock K)) (M : ℕ) : Prop :=
  (∀ b ∈ bs, b.leaves ⊆ range (2 ^ M)) ∧ bs.Pairwise fun a b => Disjoint a.leaves b.leaves

theorem tables_outside {bs : List (FracBlock K)} {x : ℕ} (hx : ∀ b ∈ bs, x ∉ b.leaves) :
    numTable bs x = 0 ∧ denTable bs x = 1 := by
  have h : ∀ g : FracBlock K → ℕ → K, (bs.map fun b => blockTable b.n b.c (g b) x).sum = 0 :=
    fun g => List.sum_eq_zero fun y hy => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      exact blockTable_of_not_mem (hx b hb) _
  exact ⟨h fun b => b.m, by rw [denTable, h fun b y => b.d y - 1, add_zero]⟩

/-- Each leaf's fraction is its block's fraction, or zero on the padding. -/
theorem frac_point : ∀ {bs : List (FracBlock K)},
    (bs.Pairwise fun a b => Disjoint a.leaves b.leaves) → ∀ x,
    numTable bs x / denTable bs x = (bs.map fun b => if x ∈ b.leaves then
      b.m (x - b.c * 2 ^ b.n) / b.d (x - b.c * 2 ^ b.n) else 0).sum
  | [], _, x => by simp [numTable, denTable]
  | b :: bs, h, x => by
    rw [List.pairwise_cons] at h
    by_cases hx : x ∈ b.leaves
    · have hout : ∀ b' ∈ bs, x ∉ b'.leaves := fun b' hb' hx' =>
        Finset.disjoint_left.mp (h.1 b' hb') hx hx'
      obtain ⟨hn, hd⟩ := tables_outside hout
      have hz : (bs.map fun b => if x ∈ b.leaves then
          b.m (x - b.c * 2 ^ b.n) / b.d (x - b.c * 2 ^ b.n) else 0).sum = 0 :=
        List.sum_eq_zero fun y hy => by
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hy
          simp [hout b' hb']
      simp only [numTable, denTable, List.map_cons, List.sum_cons] at hn hd ⊢
      rw [blockTable_of_mem hx, blockTable_of_mem hx, hn, hz]
      simp only [hx, ↓reduceIte, add_zero]
      generalize (List.map (fun b => blockTable b.n b.c (fun y => b.d y - 1) x) bs).sum = S at hd ⊢
      rw [show 1 + (b.d (x - b.c * 2 ^ b.n) - 1 + S) = b.d (x - b.c * 2 ^ b.n) by
        linear_combination hd]
    · have ih := frac_point h.2 x
      simp only [numTable, denTable, List.map_cons, List.sum_cons, blockTable_of_not_mem hx,
        zero_add, hx, ↓reduceIte] at ih ⊢
      exact ih

/-- **The leaf sum.**

The leaves of placed blocks sum to the sum, over the blocks and their rows, of m / d. -/
theorem leaf_sum {bs : List (FracBlock K)} {M : ℕ} (hp : Placed bs M) :
    ∑ x ∈ range (2 ^ M), numTable bs x / denTable bs x =
      (bs.map fun b => ∑ y ∈ range (2 ^ b.n), b.m y / b.d y).sum := by
  simp_rw [frac_point hp.2]
  have hswap : ∀ (l : List (FracBlock K)) (g : FracBlock K → ℕ → K),
      ∑ x ∈ range (2 ^ M), (l.map fun b => g b x).sum =
        (l.map fun b => ∑ x ∈ range (2 ^ M), g b x).sum := fun l g => by
    induction l with
    | nil => simp
    | cons b l ih => simp [sum_add_distrib, ih]
  rw [hswap]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (hp.1 b hb), FracBlock.leaves, leavesOf,
    sum_Ico_eq_sum_range, show (b.c + 1) * 2 ^ b.n - b.c * 2 ^ b.n = 2 ^ b.n by
      rw [add_mul, one_mul, Nat.add_sub_cancel_left]]
  exact sum_congr rfl fun y _ => by rw [Nat.add_sub_cancel_left]

/-- On placed blocks, every leaf denominator is nonzero exactly when every block's is. -/
theorem leaf_den_iff {bs : List (FracBlock K)} {M : ℕ} (hp : Placed bs M) :
    (∀ x < 2 ^ M, denTable bs x ≠ 0) ↔ ∀ b ∈ bs, ∀ y < 2 ^ b.n, b.d y ≠ 0 := by
  have hden : ∀ b ∈ bs, ∀ x ∈ b.leaves, denTable bs x = b.d (x - b.c * 2 ^ b.n) := by
    intro b hb x hx
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
    have hout : ∀ b' ∈ l1 ++ l2, x ∉ b'.leaves := by
      intro b' hb' hx'
      have hpw := hp.2
      rw [List.pairwise_append, List.pairwise_cons] at hpw
      rcases List.mem_append.mp hb' with h1 | h2
      · exact Finset.disjoint_left.mp (hpw.2.2 b' h1 b List.mem_cons_self) hx' hx
      · exact Finset.disjoint_left.mp (hpw.2.1.1 b' h2) hx hx'
    have h0 := (tables_outside hout).2
    simp only [denTable, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h0 ⊢
    rw [blockTable_of_mem hx]
    linear_combination h0
  constructor
  · intro h b hb y hy
    have hx : b.c * 2 ^ b.n + y ∈ b.leaves := by
      simp only [FracBlock.leaves, leavesOf, mem_Ico]; constructor <;> nlinarith
    have := h _ (mem_range.mp (hp.1 b hb hx))
    rwa [hden b hb _ hx, Nat.add_sub_cancel_left] at this
  · intro h x hx
    by_cases hin : ∃ b ∈ bs, x ∈ b.leaves
    · obtain ⟨b, hb, hxb⟩ := hin
      rw [hden b hb x hxb]
      refine h b hb _ ?_
      simp only [FracBlock.leaves, leavesOf, mem_Ico] at hxb
      have := hxb.2; rw [add_mul, one_mul] at this; omega
    · push Not at hin
      rw [(tables_outside hin).2]; exact one_ne_zero

end Plonky3Lean.Proofs.MultiStark
