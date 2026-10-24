module

public import Plonky3Lean.Proofs.Fri.Query

@[expose] public section

/-!
# The fold chain on honest codewords

Each round of a query's fold chain applies the FRI folding operator of its arity 2^a:

```text
    fold(P, 2^a, beta)(y),     y = x^(2^a)
```

A shorter codeword joins the chain where the fold reaches its height:

```text
    P' = fold(P, 2^a, beta) + beta^(2^a) R
```

On a chain of codewords built this way, the verifier's checks hold at every round.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]
variable (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
include hV hN h2

/-- The row fold of row t of the codeword of P is the fold of P by 2^a at point t of the folded subgroup. -/
theorem fold_row_rowList {P : K[X]} {n a : ℕ} (ha : 1 ≤ a) (hna : n + a ≤ G.adicity) {w : List K}
    (hw : IsCodeword G P (n + a) w) {t : ℕ} (ht : t < 2 ^ n) (β : K) :
    fold_row G t n a β (rowList w a t) = some ((polyFold P (2 ^ a) β).eval (dom G n t)) := by
  rw [rowList, fold_row_eq G hV h2 ha hna, fold_row_codeword G hV hN h2 hna hw ht]

/-- One round of the verifier's fold chain on an honest codeword.

Take the codeword of P at log height n + a, and a queried index.

Take siblings that are its row without the queried value.

The round folds to the fold of P by 2^a at the folded point.

When the next opening sits at log height n, it adds beta^(2^a) times that opening. -/
theorem foldStep_codeword (q : ℕ) {P : K[X]} {n a : ℕ} (ha : 1 ≤ a) (hna : n + a ≤ G.adicity)
    {w : List K} (hw : IsCodeword G P (n + a) w) {idx : ℕ} (hidx : idx < 2 ^ (n + a)) (β : K)
    {sv : List (List K)} (hsv : sv[q]? = some ((rowList w a (idx / 2 ^ a)).eraseIdx (idx % 2 ^ a)))
    (ro : List (ℕ × K)) (acc : List (ℕ × List K)) :
    foldStep G q (idx, w.getD idx 0, n + a, ro, acc) (β, a, sv) =
      some (idx / 2 ^ a,
        (rollIn n β a ((polyFold P (2 ^ a) β).eval (dom G n (idx / 2 ^ a))) ro).1, n,
        (rollIn n β a ((polyFold P (2 ^ a) β).eval (dom G n (idx / 2 ^ a))) ro).2,
        acc ++ [(idx / 2 ^ a, rowList w a (idx / 2 ^ a))]) := by
  have ht : idx / 2 ^ a < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; exact hidx
  have hrow := rebuildRow_eraseIdx (rowList w a (idx / 2 ^ a))
    (p := idx % 2 ^ a) (by rw [length_rowList]; exact Nat.mod_lt _ (by positivity))
  rw [rowList_getElem, length_rowList] at hrow
  simp only [foldStep, hsv, Option.bind_eq_bind, Option.bind_some, hrow, Nat.add_sub_cancel,
    fold_row_rowList G hV hN h2 ha hna hw ht]
  rcases ro with _ | ⟨⟨h1, v⟩, ro'⟩
  · rfl
  · by_cases hh : h1 = n <;> simp [rollIn, hh]

/-- An honest chain from the polynomial P, for query q at index idx:

- each round's word is the codeword of the running polynomial
- each round's siblings are its row without the queried value
- a rolled-in input is the codeword of some R at the folded height, and is zero when absent
- the next running polynomial is fold(P, 2^a, beta) + beta^(2^a) R
- the final word is the codeword of the last running polynomial. -/
def HonestChain (q : ℕ) : ℕ → ℕ → List (Rd K) → List K → K[X] → Prop
  | lh, idx, [], wF, P => lh ≤ G.adicity ∧ IsCodeword G P lh wF ∧ idx < 2 ^ lh
  | lh, idx, r :: rs, wF, P => 1 ≤ r.a ∧ r.a ≤ lh ∧ lh ≤ G.adicity ∧ IsCodeword G P lh r.w ∧ idx < 2 ^ lh ∧
      r.sv[q]? = some ((rowList r.w r.a (idx / 2 ^ r.a)).eraseIdx (idx % 2 ^ r.a)) ∧
      ∃ R : K[X], (match r.roll with
        | some u => IsCodeword G R (lh - r.a) u
        | none => R = 0) ∧
      HonestChain q (lh - r.a) (idx / 2 ^ r.a) rs wF (polyFold P (2 ^ r.a) r.β + C (r.β ^ 2 ^ r.a) * R)

omit h2 in
theorem HonestChain.codeword {q : ℕ} : ∀ {lh idx : ℕ} {rs : List (Rd K)} {wF : List K} {P : K[X]},
    HonestChain G q lh idx rs wF P → lh ≤ G.adicity ∧ IsCodeword G P lh (nextWord rs wF)
  | _, _, [], _, _, ⟨hl, hc, _⟩ => ⟨hl, hc⟩
  | _, _, _ :: _, _, _, ⟨_, _, hl, hc, _⟩ => ⟨hl, hc⟩

/-- An honest chain of codewords satisfies every check of the verifier's fold chain. -/
theorem HonestChain.chainOK {q : ℕ} : ∀ {lh idx : ℕ} {rs : List (Rd K)} {wF : List K} {P : K[X]},
    HonestChain G q lh idx rs wF P → ChainOK G q lh idx rs wF
  | _, _, [], _, _, ⟨_, hc, hidx⟩ => ⟨hc.1, hidx⟩
  | lh, idx, r :: rs, wF, P, ⟨ha1, hal, hla, hc, hidx, hsv, R, hR, hrest⟩ => by
    have ht : idx / 2 ^ r.a < 2 ^ (lh - r.a) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hal]; exact hidx
    have hc' : IsCodeword G P (lh - r.a + r.a) r.w := by rwa [Nat.sub_add_cancel hal]
    have hfold := fold_row_rowList G hV hN h2 ha1 (by omega) hc' ht r.β
    obtain ⟨-, hnext⟩ := hrest.codeword G hV hN
    refine ⟨ha1, hal, hc.1, hidx, hsv, ?_, hrest.chainOK⟩
    rw [hfold, hnext.2 _ ht, eval_add, eval_mul, eval_C]
    congr 1
    unfold rollTerm
    rcases hr : r.roll with _ | u
    · rw [hr] at hR; simp only at hR; subst hR; simp
    · rw [hr] at hR; simp only at hR; simp only [hR.2 _ ht]; ring

end Plonky3Lean.Proofs.Fri
