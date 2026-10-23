module

public import Plonky3Lean.Proofs.Stir.FoldAlgebra
public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# Folding a codeword by arity-2 passes

A codeword of length 2^n is read on the subgroup of order 2^n, entry i at omega^i for omega = G_n.

The fold at beta with arity 2^a returns, at index j < 2^(n - a), the fold of arity 2^a at beta: the interpolant of entries j + l 2^(n - a), l < 2^a, at beta.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The pass formula: (lo + hi)/2 + beta (lo - hi) / (2 omega^j). -/
noncomputable def passVal (ω β : EF) (src : List EF) (j : ℕ) : EF :=
  (src.getD j 0 + src.getD (j + src.length / 2) 0) / 2 +
    β * (src.getD j 0 - src.getD (j + src.length / 2) 0) / (2 * ω ^ j)

theorem fold_pass_eq (G : Gen F) (hG : GenValid G) {n : ℕ} (hn : n ≤ G.adicity) (src : List EF)
    (β : EF) :
    fold_pass G src β n = some ((List.range (src.length / 2)).map
      (passVal (algebraMap F EF (G.gen n)) β src)) := by
  have hg : G.gen n ≠ 0 := (hG n hn).ne_zero (by positivity)
  simp only [fold_pass, gen_get_of_le G hn, p3_stir.mirror.inverse, hg, ite_false,
    Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
  refine List.map_congr_left fun j hj => ?_
  rw [getD_shiftedPowersList _ _ (List.mem_range.1 hj), passVal]
  simp only [map_mul, map_div₀, map_one, map_ofNat, map_pow, map_inv₀, inv_pow]
  field_simp

/-- t passes at beta, beta^2, beta^4, ..., on domains of log size n, n - 1, .... -/
noncomputable def runPasses (G : Gen F) : List EF → EF → ℕ → ℕ → Option (List EF)
  | d, _, _, 0 => some d
  | d, β, n, t + 1 => (fold_pass G d β n).bind fun d' => runPasses G d' (β ^ 2) (n - 1) t

/-- a passes compute the fold of arity 2^a at every index. -/
theorem runPasses_eq (G : Gen F) (hG : GenValid G) (hN : GenNested G) (h2 : (2 : EF) ≠ 0) :
    ∀ (a n : ℕ) (c : List EF) (β : EF), a ≤ n → n ≤ G.adicity → c.length = 2 ^ n →
      runPasses G c β n a = some ((List.range (2 ^ (n - a))).map fun j =>
        foldIdx (algebraMap F EF (G.gen n)) c (2 ^ (n - a)) (2 ^ a) j β) := by
  intro a
  induction a with
  | zero =>
    intro n c β _ _ hc
    simp only [runPasses, Nat.sub_zero, pow_zero, foldIdx_one, Option.some.injEq]
    refine List.ext_getElem (by simp [hc]) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  | succ a ih =>
    intro n c β ha hn hc
    have hn1 : n - 1 + 1 = n := by omega
    simp only [runPasses, fold_pass_eq G hG hn, Option.bind_some]
    set ω := algebraMap F EF (G.gen n)
    set out := (List.range (c.length / 2)).map (passVal ω β c)
    have hlen : c.length / 2 = 2 ^ (n - 1) := by rw [hc, ← hn1, pow_succ]; simp
    rw [ih (n - 1) out (β ^ 2) (by omega) (by omega) (by simp [out, hlen])]
    have hgen : algebraMap F EF (G.gen (n - 1)) = ω ^ 2 := by
      rw [← hN (n - 1) (by omega), hn1, map_pow]
    have hω : IsPrimitiveRoot ω (2 * 2 ^ a * 2 ^ (n - 1 - a)) := by
      rw [show 2 * 2 ^ a * 2 ^ (n - 1 - a) = 2 ^ n by
        rw [← pow_succ', ← pow_add]; congr 1; omega]
      exact (hG n hn).map_of_injective (algebraMap F EF).injective
    rw [hgen, show n - (a + 1) = n - 1 - a by omega]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [show 2 ^ (a + 1) = 2 * 2 ^ a by ring,
      foldIdx_pass hω (by positivity) h2 c out β ?_ (List.mem_range.1 hj)]
    intro i hi
    rw [show 2 ^ a * 2 ^ (n - 1 - a) = 2 ^ (n - 1) by rw [← pow_add]; congr 1; omega] at hi ⊢
    simp only [out]
    rw [getD_map_range _ _ (by omega : i < c.length / 2), passVal, hlen]

/-- The loop of fold_codeword after its first pass: t more passes, each squaring the challenge and shrinking the domain first. -/
theorem fold_codeword_loop (G : Gen F) :
    ∀ (t : ℕ) (d : List EF) (b : EF) (l : ℕ), t ≤ l →
      (List.range t).foldlM (fun (st : List EF × EF × ℕ) _ =>
        (subChecked st.2.2 1).bind fun cur_log_domain =>
          (fold_pass G st.1 (st.2.1 ^ 2) cur_log_domain).bind fun data =>
            some (data, st.2.1 ^ 2, cur_log_domain)) (d, b, l) =
      (runPasses G d (b ^ 2) (l - 1) t).map fun r => (r, b ^ 2 ^ t, l - t) := by
  intro t
  induction t with
  | zero => intro d b l _; simp [runPasses]
  | succ t ih =>
    intro d b l hl
    have hs : subChecked l 1 = some (l - 1) := by simp [subChecked]; omega
    rw [List.range_succ_eq_map, List.foldlM_cons]
    simp only [List.foldlM_map, hs, Option.bind_eq_bind, Option.bind_some, runPasses]
    cases h : fold_pass G d (b ^ 2) (l - 1) with
    | none => rfl
    | some d' =>
      simp only [Option.bind_some]
      rw [ih d' (b ^ 2) (l - 1) (by omega)]
      congr 1; funext r
      rw [← pow_mul, ← pow_succ']; congr 2; omega

/-- The codeword fold at beta with arity 2^a on a codeword of length 2^n, for a <= n <= adicity: entry j < 2^(n - a) is the fold of arity 2^a at index j. -/
theorem fold_codeword_eq (G : Gen F) (hG : GenValid G) (hN : GenNested G) (h2 : (2 : EF) ≠ 0)
    {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity) (c : List EF) (hc : c.length = 2 ^ n) (β : EF) :
    fold_codeword G c β a n = some ((List.range (2 ^ (n - a))).map fun j =>
      foldIdx (algebraMap F EF (G.gen n)) c (2 ^ (n - a)) (2 ^ a) j β) := by
  have hdiv : c.length / 2 ^ a = 2 ^ (n - a) := by
    rw [hc, Nat.pow_div ha two_pos]
  have hres := runPasses_eq G hG hN h2 a n c β ha hn hc
  unfold fold_codeword
  simp only [hdiv, Option.bind_eq_bind, show 2 ^ (n - a) ≠ 0 by positivity, ite_false]
  rcases a with _ | a
  · simpa [runPasses] using hres
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    simp only [runPasses] at hres
    cases h : fold_pass G c β n with
    | none => rw [h] at hres; simp at hres
    | some d =>
      rw [h, Option.bind_some] at hres
      rw [Option.bind_some, fold_codeword_loop G a d β n (by omega), hres]
      simp

end Plonky3Lean.Proofs.Stir
