module

public import P3MultiStark.Bus
public import Plonky3Lean.Proofs.MultiStark.LookupLink
public import Plonky3Lean.Proofs.MultiStark.Selectors
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# The bus family of the shared sum-check

The product reduction of the bus leaves one claim per side, L(q), at a point q of the product tree.

Each block of the tree holds one declaration's factors, and the padding holds ones.

So L(q) - 1 is a sum over the blocks:

```text
    L(q) - 1  =  sum_b eq(c_b, q_prefix) (f_b~(q_rows) - 1)
```

The shared sum-check proves that sum through one polynomial over its own cube of m variables.

A block of n row variables enters on the rows whose m - n leading bits are all one:

```text
    term_b(y)  =  prod(y_unused) * eq(q_rows, y_rows) * (f_b(y_rows) - 1)
```

The product of the unused coordinates sums to one over the cube, at the all-ones vertex.

So the cube sum of the family is (L_push(q) - 1) + lambda (L_pull(q) - 1).

The verifier's closing value is that polynomial at the bound point, read on the openings.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.bus.mirror p3_multilinear_util.point.mirror Plonky3Lean.Proofs.MultilinearUtil
  Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.MultiStark Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K]

/-! ## The closing value -/

/-- **One share's closing term.**

Take a share whose dimensions agree with the plan, and a factor that evaluates.

Its term is the direction weight, times eq(c, q_prefix), times the product of the unused coordinates.

It is then times eq(q_rows, r_rows) and the factor minus one. -/
theorem shareTerm_eq (H : ℕ) (factor : TerminalShare → List K → Except Unit K) (pp : List K)
    (lam : K) (r : List K) (s : TerminalShare) (hrow : s.row_variables ≤ r.length)
    (hpp : s.prefix_variables + s.row_variables = pp.length) (hidx : s.prefix_index < 2 ^ s.prefix_variables)
    (h64 : s.prefix_index < 2 ^ 64) {f : K}
    (hf : factor s (r.drop (r.length - s.row_variables)) = .ok f) :
    shareTerm H factor pp lam r s = .ok ((if s.pull then lam else 1) *
      eq (vertex s.prefix_variables s.prefix_index) (pp.take s.prefix_variables) *
      (r.take (r.length - s.row_variables)).prod *
      eq (pp.drop s.prefix_variables) (r.drop (r.length - s.row_variables)) * (f - 1)) := by
  have hlen : (pp.take s.prefix_variables).length = s.prefix_variables := by simp; omega
  have hrl : (pp.drop s.prefix_variables).length = (r.drop (r.length - s.row_variables)).length := by
    simp; omega
  simp only [shareTerm, equality_at_vertex_eq _ h64, hlen, hidx, ↓reduceIte,
    show s.prefix_variables ≤ pp.length by omega, decide_true, hrl, ne_eq, not_true_eq_false,
    eval_eq_eq hrl, hf, bind, Except.bind, pure, Except.pure]
  simp [Algebra.algebraMap_self]

/-- A point shorter than the tallest bus table is rejected first. -/
theorem terminal_composition_short (shares : List TerminalShare) {M H : ℕ}
    (factor : TerminalShare → List K → Except Unit K) (pp : List K) (lam : K) {r : List K}
    (h : r.length < M) :
    terminal_composition shares M H factor pp lam r = .error (.CompositionPointDimension M r.length) := by
  simp [terminal_composition, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A product-tree point of the wrong dimension is rejected next. -/
theorem terminal_composition_product (shares : List TerminalShare) {M H : ℕ}
    (factor : TerminalShare → List K → Except Unit K) {pp : List K} (lam : K) {r : List K}
    (h1 : M ≤ r.length) (h2 : pp.length ≠ H) :
    terminal_composition shares M H factor pp lam r = .error (.ProductPointDimension H pp.length) := by
  simp [terminal_composition, show ¬ r.length < M by omega, h2, throw, throwThe, MonadExceptOf.throw,
    bind, Except.bind]

theorem foldlM_add_ok {ι ε : Type _} (step : K → ι → Except ε K) (v : ι → K) :
    ∀ (l : List ι), (∀ acc, ∀ s ∈ l, step acc s = .ok (acc + v s)) → ∀ a : K,
      l.foldlM step a = .ok (a + (l.map v).sum)
  | [], _, a => by simp; rfl
  | s :: l, h, a => by
    rw [List.foldlM_cons, h a s List.mem_cons_self]
    change (l.foldlM step (a + v s) : Except ε K) = _
    rw [foldlM_add_ok step v l (fun acc s' hs' => h acc s' (List.mem_cons_of_mem _ hs')) (a + v s)]
    simp [add_assoc]

/-- **The closing value.**

With the plan's dimensions and every factor evaluating, the closing value is the sum of the share terms.

The push shares come first, then the pull shares. -/
theorem terminal_composition_eq (shares : List TerminalShare) {M H : ℕ}
    (factor : TerminalShare → List K → Except Unit K) {pp : List K} (lam : K) {r : List K}
    (h1 : M ≤ r.length) (h2 : pp.length = H) (v : TerminalShare → K)
    (hv : ∀ s ∈ shares, shareTerm H factor pp lam r s = .ok (v s)) :
    terminal_composition shares M H factor pp lam r =
      .ok (((shares.filter (!·.pull) ++ shares.filter (·.pull)).map v).sum) := by
  simp only [terminal_composition, show ¬ r.length < M by omega, h2, ne_eq, not_true_eq_false,
    ↓reduceIte, bind, Except.bind, pure, Except.pure]
  rw [foldlM_add_ok _ v _ fun acc s hs => by
    rw [hv s (by rcases List.mem_append.mp hs with h | h <;> exact List.mem_of_mem_filter h)]]
  simp

/-! ## The cube sum -/

/-- A block's table sums to its own table's sum, over any cube it fits. -/
theorem sum_blockTable {M n c : ℕ} (hn : n ≤ M) (hc : c < 2 ^ (M - n)) (g : ℕ → K) :
    ∑ b ∈ range (2 ^ M), blockTable n c g b = ∑ x ∈ range (2 ^ n), g x := by
  have hp : Placed [(⟨n, c, g, fun _ => 1⟩ : FracBlock K)] M := by
    refine ⟨fun b hb x hx => ?_, by simp⟩
    simp only [List.mem_singleton] at hb; subst hb
    simp only [FracBlock.leaves, leavesOf, mem_Ico] at hx
    have : (c + 1) * 2 ^ n ≤ 2 ^ M := by
      calc (c + 1) * 2 ^ n ≤ 2 ^ (M - n) * 2 ^ n := Nat.mul_le_mul_right _ hc
        _ = 2 ^ M := by rw [← pow_add]; congr 1; omega
    exact mem_range.mpr (by omega)
  have h := leaf_sum hp
  simpa [numTable, denTable, blockTable] using h

/-- The block a share of n row variables enters the cube of m variables on: all leading bits one. -/
def shareTable (M n : ℕ) (qrow : List K) (f : ℕ → K) : ℕ → K :=
  blockTable n (2 ^ (M - n) - 1) fun x => eq (vertex n x) qrow * (f x - 1)

theorem sum_shareTable {M n : ℕ} (hn : n ≤ M) {qrow : List K} (hq : qrow.length = n) (f : ℕ → K) :
    ∑ b ∈ range (2 ^ M), shareTable M n qrow f b = rowExt f qrow - 1 := by
  rw [shareTable, sum_blockTable hn (by have := Nat.one_le_two_pow (n := M - n); omega)]
  have h1 := sum_eq_vertex qrow
  rw [hq] at h1
  simp only [rowExt, hq, mul_sub, mul_one, sum_sub_distrib, h1]

/-- **The cube sum of the bus family.**

Take placed push and pull blocks in a product tree of 2^H leaves, each a declaration's factor table.

Lift every block onto the shared cube of m variables.

The family sums over the cube to (L_push(q) - 1) + lambda (L_pull(q) - 1), the two product claims. -/
theorem bus_family_sum (push pull : List (FracBlock K)) (q : List K) (lam : K) (M : ℕ)
    (hpush : ∀ b ∈ push, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n) ∧ b.n ≤ M)
    (hpull : ∀ b ∈ pull, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n) ∧ b.n ≤ M) :
    ∑ y ∈ range (2 ^ M),
        ((push.map fun b => b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y).sum +
          lam * (pull.map fun b => b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y).sum) =
      (rowExt (denTable push) q - 1) + lam * (rowExt (denTable pull) q - 1) := by
  have hside : ∀ bs : List (FracBlock K),
      (∀ b ∈ bs, b.n ≤ q.length ∧ b.c < 2 ^ (q.length - b.n) ∧ b.n ≤ M) →
      ∑ y ∈ range (2 ^ M), (bs.map fun b =>
        b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y).sum =
        rowExt (denTable bs) q - 1 := fun bs hbs => by
    rw [rowExt_denTable bs q fun b hb => ⟨(hbs b hb).1, (hbs b hb).2.1⟩]
    have hswap : ∀ (l : List (FracBlock K)) (g : FracBlock K → ℕ → K),
        ∑ y ∈ range (2 ^ M), (l.map fun b => g b y).sum =
          (l.map fun b => ∑ y ∈ range (2 ^ M), g b y).sum := fun l g => by
      induction l with
      | nil => simp
      | cons b l ih => simp [sum_add_distrib, ih]
    rw [hswap]
    have hterm : ∀ b ∈ bs, ∑ y ∈ range (2 ^ M),
        b.weight q * shareTable M b.n (q.drop (q.length - b.n)) b.d y =
          b.weight q * rowExt b.d (q.drop (q.length - b.n)) - b.weight q := fun b hb => by
      have hn := (hbs b hb).1
      rw [← mul_sum, sum_shareTable (hbs b hb).2.2 (by simp; omega)]; ring
    rw [List.map_congr_left hterm, list_sum_map_sub]
    ring
  rw [sum_add_distrib, ← mul_sum, hside push hpush, hside pull hpull]

end Plonky3Lean.Proofs.MultiStark
